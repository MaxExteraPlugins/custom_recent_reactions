"""
Fix broken InnerClasses attributes in build-time class jars.

R8 (dex split) sometimes writes the outer class's InnerClasses entry for a
nested class without outer_class_info / inner_name (e.g.
"ReactionsLayoutInBubble$VisibleReaction" listed as a non-member). javac then
refuses to resolve Outer.Inner, so plugin sources cannot compile against these
nested types directly.

This tool appends a Utf8 constant (stable indices) and rewrites the broken
entries in place. Only build inputs are touched - runtime classes come from
the APK and are unaffected.
"""
import struct
import sys
import zipfile

CONSTANT_Utf8 = 1
CONSTANT_Integer = 3
CONSTANT_Float = 4
CONSTANT_Long = 5
CONSTANT_Double = 6
CONSTANT_Class = 7
CONSTANT_String = 8
CONSTANT_Fieldref = 9
CONSTANT_Methodref = 10
CONSTANT_InterfaceMethodref = 11
CONSTANT_NameAndType = 12
CONSTANT_MethodHandle = 15
CONSTANT_MethodType = 16
CONSTANT_Dynamic = 17
CONSTANT_InvokeDynamic = 18
CONSTANT_Module = 19
CONSTANT_Package = 20

TAG_SIZES = {
    7: 2, 8: 2, 15: 3, 16: 2, 19: 2, 20: 2,
    5: 8, 6: 8,  # take two slots
}


def parse_class(data):
    """Return (cp_entries, tail_info) with byte offsets for patching."""
    if data[:4] != b'\xca\xfe\xba\xbe':
        raise ValueError('not a class file')
    cp_count = struct.unpack('>H', data[8:10])[0]
    pos = 10
    entries = []  # list of (tag, raw_bytes) index-1 based
    i = 1
    while i < cp_count:
        tag = data[pos]
        if tag == CONSTANT_Utf8:
            ln = struct.unpack('>H', data[pos + 1:pos + 3])[0]
            raw = data[pos:pos + 3 + ln]
            pos += 3 + ln
        elif tag in (7, 8, 16, 19, 20):
            raw = data[pos:pos + 3]
            pos += 3
        elif tag == 15:
            raw = data[pos:pos + 4]
            pos += 4
        elif tag in (3, 4):
            raw = data[pos:pos + 5]
            pos += 5
        elif tag in (9, 10, 11, 12, 17, 18):
            raw = data[pos:pos + 5]
            pos += 5
        elif tag in (5, 6):
            raw = data[pos:pos + 9]
            pos += 9
            entries.append((tag, raw))
            entries.append(None)  # second slot of 8-byte constants
            i += 2
            continue
        else:
            raise ValueError('unknown tag %d at %d' % (tag, pos))
        entries.append((tag, raw))
        i += 1
    cp_end = pos
    flags = struct.unpack('>H', data[pos:pos + 2])[0]
    this_class = struct.unpack('>H', data[pos + 2:pos + 4])[0]
    return entries, cp_end, cp_count, this_class


def utf8_text(entries, idx):
    if idx < 1 or idx > len(entries):
        return None
    e = entries[idx - 1]
    if not e:
        return None
    tag, raw = e
    if tag != CONSTANT_Utf8:
        return None
    ln = struct.unpack('>H', raw[1:3])[0]
    return raw[3:3 + ln].decode('utf-8', 'replace')


def class_name(entries, class_idx):
    if class_idx < 1 or class_idx > len(entries):
        return None
    e = entries[class_idx - 1]
    if not e:
        return None
    tag, raw = e
    if tag != CONSTANT_Class:
        return None
    name_idx = struct.unpack('>H', raw[1:3])[0]
    return utf8_text(entries, name_idx)


def patch_class(data):
    """Fix member-less InnerClasses entries. Returns patched bytes or None."""
    try:
        entries, cp_end, cp_count, this_class = parse_class(data)
    except (ValueError, IndexError):
        return None
    my_name = class_name(entries, this_class)
    if not my_name:
        return None

    # locate class-level InnerClasses attribute
    pos = cp_end
    pos += 2  # access_flags
    pos += 2  # this_class
    pos += 2  # super_class
    ifc = struct.unpack('>H', data[pos:pos + 2])[0]
    pos += 2 + ifc * 2

    def skip_attributes(p):
        count = struct.unpack('>H', data[p:p + 2])[0]
        p += 2
        for _ in range(count):
            p += 2  # name index
            ln = struct.unpack('>I', data[p:p + 4])[0]
            p += 4 + ln
        return p, count

    for kind in ('fields', 'methods'):
        count = struct.unpack('>H', data[pos:pos + 2])[0]
        pos += 2
        for _ in range(count):
            pos += 6  # access, name, descriptor
            pos, _ = skip_attributes(pos)

    attrs_start = pos
    attr_count = struct.unpack('>H', data[pos:pos + 2])[0]
    pos += 2
    ic_off = None
    for _ in range(attr_count):
        name_idx = struct.unpack('>H', data[pos:pos + 2])[0]
        ln = struct.unpack('>I', data[pos + 2:pos + 6])[0]
        if utf8_text(entries, name_idx) == 'InnerClasses':
            ic_off = pos + 6
            ic_len = ln
        pos += 6 + ln
    if ic_off is None:
        return None

    entry_count = struct.unpack('>H', data[ic_off:ic_off + 2])[0]
    fixes = []  # (offset_in_file, simple_name)
    p = ic_off + 2
    for _ in range(entry_count):
        inner_idx, outer_idx, name_idx, flags = struct.unpack(
            '>HHHH', data[p:p + 8])
        inner = class_name(entries, inner_idx) if inner_idx else None
        if inner and outer_idx == 0 and name_idx == 0 and inner.startswith(my_name + '$'):
            simple = inner[len(my_name) + 1:]
            # only real named members; anonymous/local classes (Outer$1,
            # Outer$Foo$2) must keep their member-less entries
            if '$' not in simple and not simple[:1].isdigit():
                fixes.append((p + 2, simple))
        p += 8
    if not fixes:
        return None

    # append needed Utf8 constants (one per unique simple name)
    out = bytearray(data)
    added = 0
    name_map = {}
    for _, simple in fixes:
        if simple in name_map:
            continue
        # reuse existing Utf8 if present
        found = None
        for ei in range(1, len(entries) + 1):
            if utf8_text(entries, ei) == simple and entries[ei - 1][0] == CONSTANT_Utf8:
                found = ei
                break
        if found is None:
            b = simple.encode('utf-8')
            new_entry = bytes([CONSTANT_Utf8]) + struct.pack('>H', len(b)) + b
            insert_at = cp_end + added  # keep appended entries in index order
            out[insert_at:insert_at] = new_entry
            added += len(new_entry)
            new_idx = cp_count
            cp_count += 1
            name_map[simple] = new_idx
        else:
            name_map[simple] = found

    if added:
        # fix cp_count
        struct.pack_into('>H', out, 8, cp_count)
        # offsets after cp_end shifted by `added`
        ic_off += added

    this_idx = this_class
    for off, simple in fixes:
        off += added  # attribute sits after the pool; entries shifted by inserts
        # entry bytes: inner(kept), outer=this_class, name=utf8(simple), flags
        struct.pack_into('>HH', out, off, this_idx, name_map[simple])
        struct.pack_into('>H', out, off + 4, 0x0009)  # public static
    return bytes(out)


def patch_jar(jar_path, class_filter):
    zin = zipfile.ZipFile(jar_path, 'r')
    items = zin.infolist()
    data = {i.filename: zin.read(i.filename) for i in items}
    zin.close()
    patched = []
    for name in data:
        if not name.endswith('.class') or not class_filter(name):
            continue
        try:
            fixed = patch_class(data[name])
        except Exception as e:
            print('  WARN: %s: %s' % (name, e))
            continue
        if fixed is not None:
            data[name] = fixed
            patched.append(name)
    if patched:
        with zipfile.ZipFile(jar_path, 'w', zipfile.ZIP_DEFLATED) as zout:
            for i in items:
                zout.writestr(i, data[i.filename])
    return patched


if __name__ == '__main__':
    base = sys.argv[1] if len(sys.argv) > 1 else 'bin/classes/exteragram/12.10.6/'
    only = sys.argv[2:] if len(sys.argv) > 2 else None
    jars = ['classes.jar', 'classes2.jar', 'classes3.jar', 'classes4.jar',
            'classes5.jar', 'classes6.jar', 'classes7.jar']
    for j in jars:
        if only:
            flt = lambda n, _only=only: n in _only
        else:
            flt = lambda n: True
        done = patch_jar(base + j, flt)
        if done:
            print('%s: patched %d classes' % (j, len(done)))
            for d in done:
                print('   ' + d)
