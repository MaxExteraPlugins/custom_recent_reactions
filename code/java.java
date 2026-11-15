package com.exteraplugins.custom_recent_reactions;

import android.content.Context;
import android.content.SharedPreferences;
import android.graphics.Canvas;
import android.graphics.Paint;
import android.graphics.RectF;
import android.graphics.Typeface;
import android.graphics.drawable.GradientDrawable;
import android.os.Handler;
import android.os.Looper;
import android.util.TypedValue;
import android.view.Gravity;
import android.view.View;
import android.view.ViewGroup;
import android.widget.FrameLayout;
import android.widget.HorizontalScrollView;
import android.widget.ImageView;
import android.widget.LinearLayout;
import android.widget.TextView;

import androidx.core.graphics.ColorUtils;

import org.json.JSONArray;
import org.json.JSONObject;
import org.telegram.messenger.AndroidUtilities;
import org.telegram.messenger.ApplicationLoader;
import org.telegram.messenger.Emoji;
import org.telegram.messenger.LocaleController;
import org.telegram.messenger.MediaDataController;
import org.telegram.messenger.UserConfig;
import org.telegram.tgnet.TLRPC;
import org.telegram.tgnet.tl.TL_stars;
import org.telegram.ui.ActionBar.AlertDialog;
import org.telegram.ui.ActionBar.Theme;
import org.telegram.ui.Components.AnimatedEmojiDrawable;
import org.telegram.ui.Components.BackupImageView;
import org.telegram.ui.Components.LayoutHelper;
import org.telegram.ui.Components.Reactions.ReactionsLayoutInBubble;
import org.telegram.ui.Components.ReactionsContainerLayout;
import org.telegram.ui.SelectAnimatedEmojiDialog;

import java.lang.reflect.Constructor;
import java.lang.reflect.Field;
import java.lang.reflect.Method;
import java.util.ArrayList;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Locale;
import java.util.Map;
import java.util.Set;
import java.util.WeakHashMap;

import de.robv.android.xposed.XC_MethodHook;
import de.robv.android.xposed.XposedBridge;

/**
 * Custom Recent Reactions — native (DEX) part.
 *
 * All hot-path work lives here on purpose: the hooks never cross the Python
 * bridge, which is what caused freezes in the pure-Python version. The Python
 * side only owns the settings UI and pushes config through pyUpdateConfig().
 */
public class Main {

    private static final String TAG = "CustomRecentReactions";
    private static final String PREFS = "custom_recent_reactions_prefs";
    private static final String PROP_ACTIVE = "exteraplugins.crr.active";
    private static final long LIST_TTL_MS = 60_000L;

    private static final String[] DEFAULT_EMOJI = {
            "\uD83D\uDC4D", "\uD83D\uDC4E", "\u2764", "\uD83D\uDD25", "\uD83E\uDD73", "\uD83D\uDE31", "\uD83D\uDE22"
    };

    // animated emoji cache types (inlined by R8 in the app, so raw ints)
    private static final int EMOJI_CACHE_PREVIEW = 4;
    private static final int EMOJI_CACHE_DEFAULT = 0;

    // ------------------------------------------------------------------
    // config snapshot (volatile, replaced atomically by pyUpdateConfig)
    // ------------------------------------------------------------------
    private static volatile boolean cfgEnabled = true;
    private static volatile boolean cfgExtraRow = false;
    private static volatile boolean cfgShowStandard = true;
    private static volatile List<String> cfgItems; // null = not loaded yet
    private static volatile int cfgGen; // bumped on every config change

    // ------------------------------------------------------------------
    // caches
    // ------------------------------------------------------------------
    private static final Object buildLock = new Object();
    private static ArrayList<ReactionsLayoutInBubble.VisibleReaction> builtList;
    private static int builtGen = -1;
    private static int builtAccount = -1;

    private static List<String> stdEmojiCache;
    private static long stdEmojiCacheAt;
    private static HashSet<String> availableSetCache;
    private static long availableSetCacheAt;

    // ------------------------------------------------------------------
    // hooks / lifecycle
    // ------------------------------------------------------------------
    private static final HashSet<XC_MethodHook.Unhook> hooks = new HashSet<>();
    private static volatile boolean loaded;
    private static Handler mainHandler;

    // reflection, resolved once
    private static Field fType;
    private static Field fGlassBg;
    private static Field fCustomContainer;
    private static Field fPlusIcon;
    private static Field fBgPaint;
    private static Field fRectField;
    private static Field fReactionsWindow;
    private static Field fSkipDraw;
    private static Constructor<?> cHolderView;
    private static Constructor<?> cInternalImageView;
    private static Method mSetReaction;
    private static Method mShowCustomDialog;
    private static Class<?> holderViewClass;
    private static Field fHolderCurrentReaction;
    private static Field fHolderPressedBackup;
    private static Method mPlay;

    // Fast bounds for hookCanvasRoundRect (zero reflection on hot path)
    private static volatile boolean activePanelDrawing;
    private static volatile float activePanelL = -1f;
    private static volatile float activePanelT = -1f;
    private static volatile float activePanelR = -1f;
    private static volatile float activePanelB = -1f;

    // extra-row state per panel (weak: panels are short-lived views)
    private static final Map<ReactionsContainerLayout, ExtraRowState> extraStates = new WeakHashMap<>();
    // panels being dismissed: extra-row work must stop immediately so the
    // collapse animation does not flash the second row back in
    private static final Map<ReactionsContainerLayout, Long> closingPanels = new WeakHashMap<>();
    private static final long CLOSING_WINDOW_MS = 800L;
    // cheap guard for the global hooks: true only while an extra-row panel lives
    private static volatile boolean anyExtraRowActive;
    private static volatile ReactionsContainerLayout lastPanelWithExtraRow;
    // Props instances of active panels' glass background (identity set)
    private static final HashSet<Object> activeBlurProps = new HashSet<>();

    private static final class ExtraRowState {
        boolean pending;
        String keys;
        int savedBgAlpha = 255;
        boolean alphaSaved;
        int targetRclHeight;
        int targetRvHeight;
        int bottomPad;
        int btnHeight;
        int cellWidth;
        int rvTop;
    }

    // ==================================================================
    // lifecycle
    // ==================================================================

    public static void load() {
        if (loaded) {
            return;
        }
        // guards against a second copy loaded from another classloader
        // (engine auto-load + python manual load)
        if ("1".equals(System.getProperty(PROP_ACTIVE))) {
            loaded = true;
            return;
        }
        try {
            System.setProperty(PROP_ACTIVE, "1");
        } catch (Throwable ignore) {
        }
        loaded = true;
        mainHandler = new Handler(Looper.getMainLooper());
        readPrefsIntoConfig();
        initReflection();
        installHooks();
        log("native module loaded");
    }

    public static void load(Context context) {
        load();
    }

    public static void unload() {
        ReactionsContainerLayout[] live;
        synchronized (extraStates) {
            live = extraStates.keySet().toArray(new ReactionsContainerLayout[0]);
        }
        for (ReactionsContainerLayout rcl : live) {
            ExtraRowState st;
            synchronized (extraStates) {
                st = extraStates.get(rcl);
            }
            if (st != null && rcl != null) {
                teardownExtraRow(rcl, st);
            }
        }
        for (XC_MethodHook.Unhook u : hooks) {
            try {
                u.unhook();
            } catch (Throwable ignore) {
            }
        }
        hooks.clear();
        synchronized (extraStates) {
            extraStates.clear();
        }
        synchronized (closingPanels) {
            closingPanels.clear();
        }
        synchronized (activeBlurProps) {
            activeBlurProps.clear();
        }
        anyExtraRowActive = false;
        activePanelDrawing = false;
        activePanelL = activePanelT = activePanelR = activePanelB = -1f;
        lastPanelWithExtraRow = null;
        try {
            System.clearProperty(PROP_ACTIVE);
        } catch (Throwable ignore) {
        }
        loaded = false;
    }

    /** Engine callback (when settings may have changed). */
    public static void pyFlushConfig() {
        readPrefsIntoConfig();
    }

    public static void pyFlushConfigFull() {
        pyFlushConfig();
    }

    // ==================================================================
    // config
    // ==================================================================

    private static SharedPreferences prefs() {
        try {
            Context ctx = ApplicationLoader.applicationContext;
            if (ctx != null) {
                return ctx.getSharedPreferences(PREFS, 0);
            }
        } catch (Throwable ignore) {
        }
        return null;
    }

    private static void readPrefsIntoConfig() {
        SharedPreferences p = prefs();
        if (p == null) {
            return;
        }
        boolean enabled = p.getBoolean("enabled", true);
        boolean extra = p.getBoolean("extra_row", false);
        boolean showStd = p.getBoolean("show_standard", true);
        ArrayList<String> items = new ArrayList<>();
        try {
            String raw = p.getString("reactions", null);
            if (raw != null && !raw.trim().isEmpty()) {
                JSONArray arr = new JSONArray(raw);
                for (int i = 0; i < arr.length(); i++) {
                    String s = arr.optString(i);
                    if (s != null && !s.trim().isEmpty()) {
                        items.add(s.trim());
                    }
                }
            }
        } catch (Throwable ignore) {
        }
        if (items.isEmpty()) {
            for (String e : DEFAULT_EMOJI) {
                items.add("e:" + e);
            }
        }
        cfgEnabled = true;
        cfgExtraRow = extra;
        cfgShowStandard = showStd;
        cfgItems = items;
        cfgGen++;
    }

    /**
     * Python pushes a fresh config:
     * {"enabled":bool,"extra_row":bool,"show_standard":bool,"reactions":[...]}
     */
    public static void pyUpdateConfig(String json) {
        try {
            JSONObject o = new JSONObject(json);
            cfgEnabled = o.optBoolean("enabled", true);
            cfgExtraRow = o.optBoolean("extra_row", false);
            cfgShowStandard = o.optBoolean("show_standard", true);
            ArrayList<String> items = new ArrayList<>();
            JSONArray arr = o.optJSONArray("reactions");
            if (arr != null) {
                for (int i = 0; i < arr.length(); i++) {
                    String s = arr.optString(i);
                    if (s != null && !s.trim().isEmpty()) {
                        items.add(s.trim());
                    }
                }
            }
            if (items.isEmpty()) {
                for (String e : DEFAULT_EMOJI) {
                    items.add("e:" + e);
                }
            }
            cfgItems = items;
            cfgGen++;
        } catch (Throwable t) {
            readPrefsIntoConfig();
        }
    }

    private static void saveReactionsToPrefs(List<String> items) {
        SharedPreferences p = prefs();
        if (p == null || items == null) {
            return;
        }
        try {
            JSONArray arr = new JSONArray(items);
            p.edit().putString("reactions", arr.toString()).apply();
        } catch (Throwable ignore) {
        }
    }

    // ==================================================================
    // reactions list building (fully cached, no allocation on hit)
    // ==================================================================

    private static HashSet<String> availableEmoticons(int account) {
        long now = System.currentTimeMillis();
        HashSet<String> cached = availableSetCache;
        if (cached != null && now - availableSetCacheAt < LIST_TTL_MS) {
            return cached;
        }
        HashSet<String> out = new HashSet<>();
        try {
            List<TLRPC.TL_availableReaction> rl =
                    MediaDataController.getInstance(account).getEnabledReactionsList();
            if (rl != null) {
                for (TLRPC.TL_availableReaction r : rl) {
                    if (r != null && r.reaction != null) {
                        out.add(r.reaction);
                    }
                }
            }
        } catch (Throwable ignore) {
        }
        availableSetCache = out;
        availableSetCacheAt = now;
        return out;
    }

    private static List<String> standardEmojis(int account) {
        long now = System.currentTimeMillis();
        List<String> cached = stdEmojiCache;
        if (cached != null && now - stdEmojiCacheAt < LIST_TTL_MS) {
            return cached;
        }
        ArrayList<String> out = new ArrayList<>();
        try {
            List<TLRPC.TL_availableReaction> rl =
                    MediaDataController.getInstance(account).getEnabledReactionsList();
            if (rl != null) {
                for (TLRPC.TL_availableReaction r : rl) {
                    if (r != null && !r.premium && r.reaction != null && !out.contains(r.reaction)) {
                        out.add(r.reaction);
                    }
                }
            }
        } catch (Throwable ignore) {
        }
        stdEmojiCache = out;
        stdEmojiCacheAt = now;
        return out;
    }

    private static String matchEmoticon(String input, int account) {
        HashSet<String> available = availableEmoticons(account);
        if (available.contains(input)) {
            return input;
        }
        String stripped = input.replace("\uFE0F", "");
        for (String a : available) {
            if (a.equals(stripped) || a.replace("\uFE0F", "").equals(stripped)) {
                return a;
            }
        }
        return input;
    }

    private static ArrayList<ReactionsLayoutInBubble.VisibleReaction> buildReactionsList(int account) {
        List<String> items = cfgItems;
        if (items == null) {
            readPrefsIntoConfig();
            items = cfgItems;
            if (items == null) {
                return null;
            }
        }
        int gen = cfgGen;
        synchronized (buildLock) {
            if (builtList != null && builtGen == gen && builtAccount == account) {
                return builtList;
            }
        }
        ArrayList<ReactionsLayoutInBubble.VisibleReaction> out = new ArrayList<>();
        HashSet<String> seen = new HashSet<>();
        for (int i = 0; i < items.size(); i++) {
            String item = items.get(i);
            if (item == null || item.trim().isEmpty()) {
                continue;
            }
            item = item.trim();
            ReactionsLayoutInBubble.VisibleReaction vr;
            String key;
            if (item.startsWith("doc:")) {
                try {
                    long docId = Long.parseLong(item.substring(4).trim());
                    vr = ReactionsLayoutInBubble.VisibleReaction.fromCustomEmoji(docId);
                    key = "d:" + docId;
                } catch (Throwable t) {
                    continue;
                }
            } else {
                String emoji = item;
                if (emoji.startsWith("e:")) {
                    emoji = emoji.substring(2).trim();
                }
                if (emoji.endsWith("\uFE0F")) {
                    emoji = emoji.substring(0, emoji.length() - 1);
                }
                if (emoji.isEmpty()) {
                    continue;
                }
                String matched = matchEmoticon(emoji, account);
                vr = ReactionsLayoutInBubble.VisibleReaction.fromEmojicon(matched);
                key = "e:" + matched;
            }
            if (vr != null && seen.add(key)) {
                out.add(vr);
            }
        }
        if (cfgShowStandard) {
            List<String> std = standardEmojis(account);
            for (int i = 0; i < std.size(); i++) {
                String se = std.get(i);
                if (se == null) {
                    continue;
                }
                se = se.replace("\uFE0F", "");
                if (se.isEmpty()) {
                    continue;
                }
                boolean dup = false;
                for (String k : seen) {
                    if (k.startsWith("e:") && k.substring(2).replace("\uFE0F", "").equals(se)) {
                        dup = true;
                        break;
                    }
                }
                if (dup) {
                    continue;
                }
                ReactionsLayoutInBubble.VisibleReaction vr =
                        ReactionsLayoutInBubble.VisibleReaction.fromEmojicon(matchEmoticon(se, account));
                if (vr != null) {
                    out.add(vr);
                    seen.add("e:" + se);
                }
            }
        }
        ArrayList<ReactionsLayoutInBubble.VisibleReaction> result = out.isEmpty() ? null : out;
        synchronized (buildLock) {
            builtList = result;
            builtGen = gen;
            builtAccount = account;
        }
        return result;
    }

    // ==================================================================
    // reflection setup
    // ==================================================================

    private static void initReflection() {
        fType = resolveField("type");
        fGlassBg = resolveField("glassBackground");
        fCustomContainer = resolveField("customReactionsContainer");
        fPlusIcon = resolveField("customEmojiReactionsIconView");
        fBgPaint = resolveField("bgPaint");
        fRectField = resolveField("rect");
        fReactionsWindow = resolveField("reactionsWindow");
        fSkipDraw = resolveField("skipDraw");
        try {
            holderViewClass = Class.forName("org.telegram.ui.Components.ReactionsContainerLayout$ReactionHolderView");
            cHolderView = holderViewClass.getDeclaredConstructor(
                    ReactionsContainerLayout.class, Context.class, Boolean.TYPE);
            cHolderView.setAccessible(true);
            fHolderCurrentReaction = holderViewClass.getDeclaredField("currentReaction");
            fHolderCurrentReaction.setAccessible(true);
            fHolderPressedBackup = holderViewClass.getDeclaredField("pressedBackupImageView");
            fHolderPressedBackup.setAccessible(true);
            mSetReaction = holderViewClass.getMethod("-$$Nest$msetReaction", holderViewClass,
                    ReactionsLayoutInBubble.VisibleReaction.class, Integer.TYPE);
            mSetReaction.setAccessible(true);
            try {
                mPlay = holderViewClass.getMethod("play", Integer.TYPE);
                mPlay.setAccessible(true);
            } catch (Throwable ignore) {
                mPlay = null;
            }
        } catch (Throwable ignore) {
            holderViewClass = null;
            cHolderView = null;
            fHolderCurrentReaction = null;
            mSetReaction = null;
            mPlay = null;
        }
        try {
            Class<?> iiv = Class.forName("org.telegram.ui.Components.ReactionsContainerLayout$InternalImageView");
            cInternalImageView = iiv.getDeclaredConstructor(ReactionsContainerLayout.class, Context.class);
            cInternalImageView.setAccessible(true);
        } catch (Throwable ignore) {
            cInternalImageView = null;
        }
        try {
            mShowCustomDialog = ReactionsContainerLayout.class.getDeclaredMethod("showCustomEmojiReactionDialog");
            mShowCustomDialog.setAccessible(true);
        } catch (Throwable ignore) {
            mShowCustomDialog = null;
        }
    }

    private static void startHolderAnimation(View holder, int delay) {
        if (holder == null || mPlay == null) {
            return;
        }
        try {
            mPlay.invoke(holder, Integer.valueOf(delay));
        } catch (Throwable ignore) {
        }
    }

    private static boolean isSkipDraw(ReactionsContainerLayout rcl) {
        if (fSkipDraw == null || rcl == null) {
            return false;
        }
        try {
            return fSkipDraw.getBoolean(rcl);
        } catch (Throwable ignore) {
            return false;
        }
    }

    private static Field resolveField(String name) {
        try {
            Field f = ReactionsContainerLayout.class.getDeclaredField(name);
            f.setAccessible(true);
            return f;
        } catch (Throwable ignore) {
            return null;
        }
    }

    private static Object getField(Field f, Object target) {
        if (f == null) {
            return null;
        }
        try {
            return f.get(target);
        } catch (Throwable t) {
            return null;
        }
    }

    private static int panelType(Object rcl) {
        if (fType == null) {
            return 0;
        }
        try {
            return fType.getInt(rcl);
        } catch (Throwable t) {
            return 0;
        }
    }

    private static boolean isExtraRowTarget(ReactionsContainerLayout rcl) {
        if (!anyExtraRowActive || rcl == null) {
            return false;
        }
        synchronized (extraStates) {
            ExtraRowState st = extraStates.get(rcl);
            return st != null && st.keys != null;
        }
    }

    // ==================================================================
    // hooks
    // ==================================================================

    private static void installHooks() {
        hookSetVisibleReactionsList();
        hookDispatchDraw();
        hookSetGlassBackground();
        hookBlurPropsBuild();
        hookCanvasRoundRect();
        hookWindowContainerDraw();
        hookSetCustomEmojiEnterProgress();
    }

    private static boolean isPanelClosing(ReactionsContainerLayout rcl) {
        return false;
    }

    private static void hookSetVisibleReactionsList() {
        try {
            Set<XC_MethodHook.Unhook> s = XposedBridge.hookAllMethods(
                    ReactionsContainerLayout.class, "setVisibleReactionsList", new XC_MethodHook() {
                        @Override
                        public void beforeHookedMethod(MethodHookParam param) {
                            try {
                                if (!cfgEnabled || param.thisObject == null || param.args == null
                                        || param.args.length == 0 || !(param.args[0] instanceof List)) {
                                    return;
                                }
                                ReactionsContainerLayout rcl = (ReactionsContainerLayout) param.thisObject;
                                if (panelType(rcl) != 0 || rcl.channelReactions) {
                                    return;
                                }
                                int account;
                                try {
                                    account = UserConfig.selectedAccount;
                                } catch (Throwable t) {
                                    account = 0;
                                }
                                List<ReactionsLayoutInBubble.VisibleReaction> list = buildReactionsList(account);
                                if (list != null && !list.isEmpty()) {
                                    param.args[0] = new ArrayList<>(list);
                                }
                            } catch (Throwable t) {
                                log("setList: " + t);
                            }
                        }

                        @Override
                        public void afterHookedMethod(MethodHookParam param) {
                            try {
                                if (param.thisObject == null || param.args == null
                                        || param.args.length == 0 || !(param.args[0] instanceof List)) {
                                    return;
                                }
                                ReactionsContainerLayout rcl = (ReactionsContainerLayout) param.thisObject;
                                if (panelType(rcl) != 0 || rcl.channelReactions) {
                                    return;
                                }
                                // tear down a stale extra row if the mode got switched off
                                if (!cfgExtraRow || !cfgEnabled) {
                                    if (isExtraRowTarget(rcl)) {
                                        ExtraRowState st;
                                        synchronized (extraStates) {
                                            st = extraStates.get(rcl);
                                        }
                                        if (st != null) {
                                            teardownExtraRow(rcl, st);
                                        }
                                    }
                                    return;
                                }
                                List<?> full = (List<?>) param.args[0];
                                if (full.size() <= 7) {
                                    return;
                                }
                                try {
                                    if (!rcl.showCustomEmojiReaction()) {
                                        return;
                                    }
                                } catch (Throwable ignore) {
                                }
                                scheduleExtraRow(rcl, full);
                            } catch (Throwable t) {
                                log("extra: " + t);
                            }
                        }
                    });
            if (s != null) {
                hooks.addAll(s);
            }
        } catch (Throwable t) {
            log("hook setVisibleReactionsList failed: " + t);
        }
    }

    private static void hookDispatchDraw() {
        try {
            Set<XC_MethodHook.Unhook> s = XposedBridge.hookAllMethods(
                    ReactionsContainerLayout.class, "dispatchDraw", new XC_MethodHook() {
                        @Override
                        public void beforeHookedMethod(MethodHookParam param) {
                            try {
                                if (!anyExtraRowActive) {
                                    return;
                                }
                                ReactionsContainerLayout rcl = (ReactionsContainerLayout) param.thisObject;
                                if (rcl == null || !isExtraRowTarget(rcl)) {
                                    return;
                                }
                                ExtraRowState st;
                                synchronized (extraStates) {
                                    st = extraStates.get(rcl);
                                }
                                if (st == null) {
                                    return;
                                }
                                hideNativeNext(rcl);
                                boolean isSkip = isSkipDraw(rcl);
                                Object win = getField(fReactionsWindow, rcl);
                                if (isSkip && win != null) {
                                    return;
                                }
                                activePanelDrawing = true;
                                RectF rectBounds = (RectF) getField(fRectField, rcl);
                                if (rectBounds != null) {
                                    activePanelL = rectBounds.left;
                                    activePanelT = rectBounds.top;
                                    activePanelR = rectBounds.right;
                                    activePanelB = rectBounds.bottom;
                                }
                                // hide the native "+" container while our row owns the plus
                                Object crc = getField(fCustomContainer, rcl);
                                if (crc instanceof View && st.keys != null) {
                                    ((View) crc).setVisibility(View.INVISIBLE);
                                }
                            } catch (Throwable ignore) {
                            }
                        }

                        @Override
                        public void afterHookedMethod(MethodHookParam param) {
                            activePanelDrawing = false;
                            try {
                                if (!anyExtraRowActive) {
                                    return;
                                }
                                ReactionsContainerLayout rcl = (ReactionsContainerLayout) param.thisObject;
                                if (rcl == null) {
                                    return;
                                }
                                hideNativeNext(rcl);
                                boolean isSkip = isSkipDraw(rcl);
                                Object win = getField(fReactionsWindow, rcl);
                                if (isSkip && win != null) {
                                    return;
                                }
                                boolean target = isExtraRowTarget(rcl);
                                if (target) {
                                    syncExtraRow(rcl);
                                    View row2 = rcl.findViewWithTag("crr_row2");
                                    if (row2 != null && row2.getAlpha() != 1f) {
                                        row2.setAlpha(1f);
                                    }
                                    View x8 = rcl.findViewWithTag("crr_x8");
                                    if (x8 != null && x8.getAlpha() != 1f) {
                                        x8.setAlpha(1f);
                                    }
                                }
                                if (target) {
                                    // keep the moved plus button visible in its cell
                                    View row2 = rcl.findViewWithTag("crr_row2");
                                    if (row2 instanceof ViewGroup) {
                                        View plus2 = row2.findViewWithTag("crr_plus2");
                                        if (plus2 != null && plus2.getVisibility() != View.VISIBLE) {
                                            plus2.setVisibility(View.VISIBLE);
                                        }
                                    }
                                }
                            } catch (Throwable ignore) {
                            }
                        }
                    });
            if (s != null) {
                hooks.addAll(s);
            }
        } catch (Throwable t) {
            log("hook dispatchDraw failed: " + t);
        }
    }

    private static void hookSetGlassBackground() {
        try {
            Set<XC_MethodHook.Unhook> s = XposedBridge.hookAllMethods(
                    ReactionsContainerLayout.class, "setGlassBackground", new XC_MethodHook() {
                        @Override
                        public void afterHookedMethod(MethodHookParam param) {
                            try {
                                if (!cfgExtraRow || !cfgEnabled || param.thisObject == null) {
                                    return;
                                }
                                ReactionsContainerLayout rcl = (ReactionsContainerLayout) param.thisObject;
                                if (panelType(rcl) != 0 || rcl.channelReactions) {
                                    return;
                                }
                                registerBlurProps(rcl);
                            } catch (Throwable ignore) {
                            }
                        }
                    });
            if (s != null) {
                hooks.addAll(s);
            }
        } catch (Throwable t) {
            log("hook setGlassBackground failed: " + t);
        }
    }

    /** remember the Props instance bound to an active panel's glass background */
    private static void registerBlurProps(ReactionsContainerLayout rcl) {
        try {
            Object glass = getField(fGlassBg, rcl);
            if (glass == null) {
                return;
            }
            Method getBound = null;
            try {
                getBound = glass.getClass().getDeclaredMethod("getBoundProps");
            } catch (Throwable ignore) {
            }
            Object props = null;
            if (getBound != null) {
                try {
                    getBound.setAccessible(true);
                    props = getBound.invoke(glass);
                } catch (Throwable ignore) {
                }
            }
            if (props == null) {
                for (Field f : glass.getClass().getDeclaredFields()) {
                    if (Object.class.isAssignableFrom(f.getType()) && f.getType().getName().endsWith("Props")) {
                        try {
                            f.setAccessible(true);
                            Object v = f.get(glass);
                            if (v != null) {
                                props = v;
                                break;
                            }
                        } catch (Throwable ignore) {
                        }
                    }
                }
            }
            if (props != null) {
                synchronized (activeBlurProps) {
                    if (activeBlurProps.size() > 8) {
                        activeBlurProps.clear();
                    }
                    activeBlurProps.add(props);
                }
            }
        } catch (Throwable ignore) {
        }
    }

    private static void hookBlurPropsBuild() {
        try {
            Class<?> propsCls = Class.forName(
                    "org.telegram.ui.Components.blur3.drawable.BlurredBackgroundDrawable$Props");
            Set<XC_MethodHook.Unhook> s = XposedBridge.hookAllMethods(propsCls, "build", new XC_MethodHook() {
                @Override
                public void beforeHookedMethod(MethodHookParam param) {
                    if (!anyExtraRowActive || param.thisObject == null) {
                        return;
                    }
                    boolean mine;
                    synchronized (activeBlurProps) {
                        mine = activeBlurProps.contains(param.thisObject);
                    }
                    if (!mine) {
                        return;
                    }
                    clampRadii(param.thisObject, "radii");
                    clampRadii(param.thisObject, "shaderRadii");
                }
            });
            if (s != null) {
                hooks.addAll(s);
            }
        } catch (Throwable t) {
            log("hook Props.build failed: " + t);
        }
    }

    private static void clampRadii(Object props, String field) {
        try {
            Field f = props.getClass().getDeclaredField(field);
            f.setAccessible(true);
            float[] arr = (float[]) f.get(props);
            if (arr == null) {
                return;
            }
            float target = AndroidUtilities.dp(4f);
            for (int i = 0; i < arr.length; i++) {
                if (arr[i] > target) {
                    arr[i] = target;
                }
            }
        } catch (Throwable ignore) {
        }
    }

    /** global hook, but the inactive path is a single volatile read */
    private static void hookCanvasRoundRect() {
        try {
            for (Method m : Canvas.class.getDeclaredMethods()) {
                Class<?>[] pt = m.getParameterTypes();
                if (!m.getName().equals("drawRoundRect") || pt.length != 4 || pt[0] != RectF.class
                        || pt[1] != float.class || pt[2] != float.class || pt[3] != Paint.class) {
                    continue;
                }
                XC_MethodHook.Unhook u = XposedBridge.hookMethod(m, new XC_MethodHook() {
                    @Override
                    public void beforeHookedMethod(MethodHookParam param) {
                        if (!activePanelDrawing) {
                            return;
                        }
                        try {
                            RectF rect = (RectF) param.args[0];
                            if (rect == null) {
                                return;
                            }
                            float rx = (Float) param.args[1];
                            float target = AndroidUtilities.dp(4f);
                            if (rx <= target) {
                                return;
                            }
                            if (Math.abs(rect.left - activePanelL) <= 2f && Math.abs(rect.top - activePanelT) <= 2f
                                    && Math.abs(rect.right - activePanelR) <= 2f
                                    && Math.abs(rect.bottom - activePanelB) <= 2f) {
                                param.args[1] = target;
                                param.args[2] = target;
                            }
                        } catch (Throwable ignore) {
                        }
                    }
                });
                if (u != null) {
                    hooks.add(u);
                }
                break;
            }
        } catch (Throwable t) {
            log("hook drawRoundRect failed: " + t);
        }
    }

    private static void hookSetCustomEmojiEnterProgress() {
        try {
            Set<XC_MethodHook.Unhook> s = XposedBridge.hookAllMethods(
                    ReactionsContainerLayout.class, "setCustomEmojiEnterProgress", new XC_MethodHook() {
                        @Override
                        public void afterHookedMethod(MethodHookParam param) {
                            try {
                                if (!anyExtraRowActive || param.thisObject == null || param.args == null || param.args.length == 0) {
                                    return;
                                }
                                ReactionsContainerLayout rcl = (ReactionsContainerLayout) param.thisObject;
                                if (!isExtraRowTarget(rcl)) {
                                    return;
                                }
                                float progress = (Float) param.args[0];
                                float alpha = 1f - progress;
                                if (alpha < 0f) {
                                    alpha = 0f;
                                } else if (alpha > 1f) {
                                    alpha = 1f;
                                }
                                View row2 = rcl.findViewWithTag("crr_row2");
                                if (row2 != null) {
                                    row2.setAlpha(alpha);
                                }
                                View x8 = rcl.findViewWithTag("crr_x8");
                                if (x8 != null) {
                                    x8.setAlpha(alpha);
                                }
                            } catch (Throwable ignore) {
                            }
                        }
                    });
            if (s != null) {
                hooks.addAll(s);
            }
        } catch (Throwable t) {
            log("hook setCustomEmojiEnterProgress failed: " + t);
        }
    }

    private static void hookWindowContainerDraw() {
        try {
            Class<?> winClass = Class.forName(
                    "org.telegram.ui.Components.Reactions.CustomEmojiReactionsWindow");
            Class<?> containerClass = Class.forName(
                    "org.telegram.ui.Components.Reactions.CustomEmojiReactionsWindow$ContainerView");
            final Field fThis0 = containerClass.getDeclaredField("this$0");
            fThis0.setAccessible(true);
            final Field fRcl = winClass.getDeclaredField("reactionsContainerLayout");
            fRcl.setAccessible(true);
            final Field fDrawingRect = winClass.getDeclaredField("drawingRect");
            fDrawingRect.setAccessible(true);
            final Field fEnterProgress = winClass.getDeclaredField("enterTransitionProgress");
            fEnterProgress.setAccessible(true);

            Set<XC_MethodHook.Unhook> sTrans = XposedBridge.hookAllMethods(
                    winClass, "createTransition", new XC_MethodHook() {
                        @Override
                        public void afterHookedMethod(MethodHookParam param) {
                            try {
                                Object win = param.thisObject;
                                if (win == null || !anyExtraRowActive) {
                                    return;
                                }
                                ReactionsContainerLayout rcl = (ReactionsContainerLayout) fRcl.get(win);
                                if (rcl != null && isExtraRowTarget(rcl)) {
                                    hideNativeNext(rcl);
                                }
                            } catch (Throwable ignore) {
                            }
                        }
                    });
            if (sTrans != null) {
                hooks.addAll(sTrans);
            }

            Set<XC_MethodHook.Unhook> sDraw = XposedBridge.hookAllMethods(
                    containerClass, "dispatchDraw", new XC_MethodHook() {
                        @Override
                        public void afterHookedMethod(MethodHookParam param) {
                            try {
                                if (!anyExtraRowActive) {
                                    return;
                                }
                                Object container = param.thisObject;
                                Canvas canvas = (Canvas) param.args[0];
                                if (container == null || canvas == null) {
                                    return;
                                }
                                Object win = fThis0.get(container);
                                if (win == null) {
                                    return;
                                }
                                ReactionsContainerLayout rcl = (ReactionsContainerLayout) fRcl.get(win);
                                if (rcl == null || !isExtraRowTarget(rcl)) {
                                    return;
                                }
                                float progress = fEnterProgress.getFloat(win);
                                float alpha = 1f - progress;
                                if (alpha <= 0.01f) {
                                    return;
                                }
                                if (alpha > 1f) {
                                    alpha = 1f;
                                }
                                RectF dRect = (RectF) fDrawingRect.get(win);
                                if (dRect == null) {
                                    return;
                                }
                                View row2 = rcl.findViewWithTag("crr_row2");
                                View x8 = rcl.findViewWithTag("crr_x8");
                                RectF rectBounds = (RectF) getField(fRectField, rcl);
                                float rclLeft = rectBounds != null ? rectBounds.left : rcl.getPaddingLeft();
                                float rclTop = rectBounds != null ? rectBounds.top : rcl.getPaddingTop();
                                float rclBottom = rectBounds != null ? rectBounds.bottom : rcl.getHeight();

                                int sc = canvas.save();
                                canvas.clipRect(dRect);
                                if (row2 != null && row2.getWidth() > 0 && row2.getHeight() > 0) {
                                    float x = dRect.left + (row2.getLeft() - rclLeft);
                                    float y = dRect.bottom - (rclBottom - row2.getTop());
                                    row2.setAlpha(alpha);
                                    int sc2 = canvas.save();
                                    canvas.translate(x, y);
                                    row2.draw(canvas);
                                    canvas.restoreToCount(sc2);
                                }
                                if (x8 != null && x8.getWidth() > 0 && x8.getHeight() > 0) {
                                    float x8X = dRect.left + (x8.getLeft() - rclLeft);
                                    float x8Y = dRect.top + (x8.getTop() - rclTop);
                                    x8.setAlpha(alpha);
                                    int sc2 = canvas.save();
                                    canvas.translate(x8X, x8Y);
                                    x8.draw(canvas);
                                    canvas.restoreToCount(sc2);
                                }
                                canvas.restoreToCount(sc);
                            } catch (Throwable ignore) {
                            }
                        }
                    });
            if (sDraw != null) {
                hooks.addAll(sDraw);
            }
        } catch (Throwable t) {
            log("hookWindowContainerDraw failed: " + t);
        }
    }

    // ==================================================================
    // extra row ("one more row" mode, up to 14 reactions)
    // ==================================================================

    private static String vrKeys(List<ReactionsLayoutInBubble.VisibleReaction> vrs) {
        StringBuilder sb = new StringBuilder();
        for (int i = 0; i < vrs.size(); i++) {
            ReactionsLayoutInBubble.VisibleReaction vr = vrs.get(i);
            if (vr != null && vr.emojicon != null) {
                sb.append('e').append(vr.emojicon).append('|');
            } else if (vr != null) {
                sb.append('d').append(vr.documentId).append('|');
            }
        }
        return sb.toString();
    }

    private static String vrKeysOfRow(ViewGroup row) {
        if (row == null || fHolderCurrentReaction == null) {
            return "";
        }
        try {
            StringBuilder sb = new StringBuilder();
            for (int i = 0; i < row.getChildCount(); i++) {
                View c = row.getChildAt(i);
                if (c != null && holderViewClass.isInstance(c)) {
                    Object r = fHolderCurrentReaction.get(c);
                    if (r instanceof ReactionsLayoutInBubble.VisibleReaction) {
                        ReactionsLayoutInBubble.VisibleReaction vr =
                                (ReactionsLayoutInBubble.VisibleReaction) r;
                        if (vr.emojicon != null) {
                            sb.append('e').append(vr.emojicon).append('|');
                        } else {
                            sb.append('d').append(vr.documentId).append('|');
                        }
                    }
                }
            }
            return sb.toString();
        } catch (Throwable t) {
            return "";
        }
    }

    private static void scheduleExtraRow(ReactionsContainerLayout rcl, List<?> full) {
        if (isPanelClosing(rcl)) {
            return; // panel is dismissing — do not flash the second row back
        }
        int n = Math.min(full.size(), 15);
        if (n <= 7) {
            return;
        }
        final ArrayList<ReactionsLayoutInBubble.VisibleReaction> items = new ArrayList<>(n - 8);
        for (int i = 8; i < n; i++) {
            Object o = full.get(i);
            if (o instanceof ReactionsLayoutInBubble.VisibleReaction) {
                items.add((ReactionsLayoutInBubble.VisibleReaction) o);
            }
        }
        final ReactionsLayoutInBubble.VisibleReaction vr8 =
                full.get(7) instanceof ReactionsLayoutInBubble.VisibleReaction
                        ? (ReactionsLayoutInBubble.VisibleReaction) full.get(7) : null;

        final ExtraRowState st;
        synchronized (extraStates) {
            ExtraRowState s = extraStates.get(rcl);
            if (s == null) {
                s = new ExtraRowState();
                extraStates.put(rcl, s);
            }
            if (extraStates.size() > 24) {
                Iterator<Map.Entry<ReactionsContainerLayout, ExtraRowState>> it =
                        extraStates.entrySet().iterator();
                while (it.hasNext() && extraStates.size() > 12) {
                    Map.Entry<ReactionsContainerLayout, ExtraRowState> e = it.next();
                    if (e.getKey() == null || !e.getKey().isAttachedToWindow()) {
                        it.remove();
                    }
                }
            }
            st = s;
            st.pending = true;
            st.keys = vrKeys(items);
        }
        anyExtraRowActive = true;
        registerBlurProps(rcl);
        if (mainHandler == null) {
            mainHandler = new Handler(Looper.getMainLooper());
        }
        final ReactionsContainerLayout panel = rcl;
        panel.post(new Runnable() {
            @Override
            public void run() {
                finishExtraRow(panel, items, vr8, 0);
            }
        });
    }

    private static void finishExtraRow(final ReactionsContainerLayout rcl,
                                       final ArrayList<ReactionsLayoutInBubble.VisibleReaction> items,
                                       final ReactionsLayoutInBubble.VisibleReaction vr8,
                                       final int tries) {
        try {
            ExtraRowState st;
            synchronized (extraStates) {
                st = extraStates.get(rcl);
            }
            if (st == null) {
                return;
            }
            if (isPanelClosing(rcl)) {
                synchronized (extraStates) {
                    extraStates.remove(rcl);
                }
                return;
            }
            if (!rcl.isAttachedToWindow()) {
                st.pending = false;
                return;
            }
            ViewGroup rv = rcl.recyclerListView;
            if (rv == null) {
                st.pending = false;
                return;
            }
            if (rcl.getPullingLeftProgress() > 0f) {
                if (tries < 10) {
                    repostExtra(rcl, items, vr8, tries);
                }
                return;
            }
            if (items.isEmpty()) {
                teardownExtraRow(rcl, st);
                return;
            }
            int rowH = rv.getMeasuredHeight();
            int hCur = rcl.getMeasuredHeight();
            View btn = rv.getChildCount() > 0 ? rv.getChildAt(0) : null;
            int btnH = (btn != null && btn.getHeight() > 0) ? btn.getHeight() : rowH;
            int cellW = AndroidUtilities.dp(36);
            if (rowH <= 0 || hCur <= 0 || btnH <= 0
                    || btnH > AndroidUtilities.dp(90) || hCur > AndroidUtilities.dp(800)) {
                if (tries < 10) {
                    repostExtra(rcl, items, vr8, tries);
                }
                return;
            }
            ViewGroup prev = rcl.findViewWithTag("crr_row2") instanceof ViewGroup
                    ? (ViewGroup) rcl.findViewWithTag("crr_row2") : null;
            if (prev != null && st.keys != null && !st.keys.equals(vrKeysOfRow(prev))) {
                try {
                    rcl.removeView(prev);
                } catch (Throwable ignore) {
                }
                View x8old = rcl.findViewWithTag("crr_x8");
                if (x8old != null) {
                    try {
                        rcl.removeView(x8old);
                    } catch (Throwable ignore) {
                    }
                }
                prev = null;
            }
            if (prev == null && cHolderView != null && mSetReaction != null) {
                LinearLayout row2 = createRow2(rcl, items, cellW, btnH);
                if (row2 != null) {
                    rcl.addView(row2, new FrameLayout.LayoutParams(-2, btnH, Gravity.BOTTOM));
                    for (int i = 0; i < row2.getChildCount(); i++) {
                        View child = row2.getChildAt(i);
                        if (child != null && holderViewClass != null && holderViewClass.isInstance(child)) {
                            startHolderAnimation(child, (i + 1) * 30);
                        }
                    }
                    final LinearLayout fRow2 = row2;
                    mainHandler.post(new Runnable() {
                        @Override
                        public void run() {
                            if (fRow2 != null) {
                                for (int i = 0; i < fRow2.getChildCount(); i++) {
                                    View child = fRow2.getChildAt(i);
                                    if (child != null && holderViewClass != null && holderViewClass.isInstance(child)) {
                                        startHolderAnimation(child, (i + 1) * 30);
                                    }
                                }
                            }
                        }
                    });
                }
            }
            int rvTop = rv.getTop();
            int btnTop = btn != null ? btn.getTop() : 0;
            int row2Top = rvTop + btnTop + btnH;
            int bottomPad = hCur - rvTop - rowH;
            if (bottomPad <= 0 || bottomPad > AndroidUtilities.dp(100)) {
                bottomPad = st.bottomPad > 0 ? st.bottomPad : AndroidUtilities.dp(66);
            }
            // cells are tall but emojis are small: pull the rows closer together
            int rowGapReduce = AndroidUtilities.dp(14);
            int targetRclH = row2Top + btnH + bottomPad - rowGapReduce;

            ViewGroup.LayoutParams rvLp = rv.getLayoutParams();
            rvLp.height = rowH;
            rv.setLayoutParams(rvLp);
            ViewGroup.LayoutParams rclLp = rcl.getLayoutParams();
            rclLp.height = targetRclH;
            rcl.setLayoutParams(rclLp);
            rcl.requestLayout();
            try {
                if (rcl.getParent() instanceof View) {
                    ((View) rcl.getParent()).requestLayout();
                }
            } catch (Throwable ignore) {
            }
            restoreRow1(rcl);
            reclipRow2(rcl);
            View row2v = rcl.findViewWithTag("crr_row2");
            if (row2v instanceof LinearLayout) {
                movePlusToRow2(rcl, (LinearLayout) row2v, cellW, btnH);
            }
            if (vr8 != null) {
                ensureX8(rcl, vr8, cellW, btnH);
            }
            st.targetRclHeight = targetRclH;
            st.targetRvHeight = rowH;
            st.bottomPad = bottomPad;
            st.btnHeight = btnH;
            st.cellWidth = cellW;
            st.rvTop = rvTop;
            st.pending = false;
            anyExtraRowActive = true;
            lastPanelWithExtraRow = rcl;
            hideNativeNext(rcl);
        } catch (Throwable t) {
            log("finishExtraRow: " + t);
            synchronized (extraStates) {
                ExtraRowState st = extraStates.get(rcl);
                if (st != null) {
                    st.pending = false;
                }
            }
        }
    }

    private static void repostExtra(final ReactionsContainerLayout rcl,
                                    final ArrayList<ReactionsLayoutInBubble.VisibleReaction> items,
                                    final ReactionsLayoutInBubble.VisibleReaction vr8,
                                    final int tries) {
        mainHandler.postDelayed(new Runnable() {
            @Override
            public void run() {
                finishExtraRow(rcl, items, vr8, tries + 1);
            }
        }, 16);
    }

    /**
     * The holder's middle layer (pressedBackupImageView) always gets the same
     * reaction animation; natively the panel's dispatchDraw hides it, but that
     * bookkeeping only covers recycler children. For holders we create
     * ourselves it would draw a duplicated, desynced reaction underneath.
     */
    private static void hidePressedBackup(Object holder) {
        try {
            Object pressed = fHolderPressedBackup.get(holder);
            if (pressed instanceof View) {
                ((View) pressed).setVisibility(View.GONE);
            }
        } catch (Throwable ignore) {
        }
    }

    private static LinearLayout createRow2(final ReactionsContainerLayout rcl,
                                           ArrayList<ReactionsLayoutInBubble.VisibleReaction> items,
                                           int cellW, int btnH) {
        try {
            Context ctx = rcl.getContext();
            LinearLayout row2 = new LinearLayout(ctx);
            row2.setOrientation(LinearLayout.HORIZONTAL);
            row2.setTag("crr_row2");
            row2.setPadding(AndroidUtilities.dp(8), 0, 0, 0);
            for (int i = 0; i < items.size(); i++) {
                final ReactionsLayoutInBubble.VisibleReaction vr = items.get(i);
                View holder = (View) cHolderView.newInstance(rcl, ctx, Boolean.TRUE);
                mSetReaction.invoke(null, holder, vr, Integer.valueOf(i + 8));
                hidePressedBackup(holder);
                holder.setOnClickListener(new View.OnClickListener() {
                    @Override
                    public void onClick(View v) {
                        try {
                            Object cr = fHolderCurrentReaction.get(v);
                            if (cr instanceof ReactionsLayoutInBubble.VisibleReaction) {
                                rcl.onReactionClicked(v,
                                        (ReactionsLayoutInBubble.VisibleReaction) cr, false);
                            }
                        } catch (Throwable ignore) {
                        }
                    }
                });
                row2.addView(holder, new FrameLayout.LayoutParams(cellW, btnH));
            }
            return row2;
        } catch (Throwable t) {
            log("createRow2: " + t);
            return null;
        }
    }

    private static void reclipRow2(ReactionsContainerLayout rcl) {
        try {
            View row2 = rcl.findViewWithTag("crr_row2");
            if (row2 == null) {
                return;
            }
            GradientDrawable gd = new GradientDrawable();
            gd.setColor(0);
            gd.setCornerRadius(AndroidUtilities.dp(16));
            row2.setBackground(gd);
            row2.setClipToOutline(true);
        } catch (Throwable ignore) {
        }
    }

    private static void restoreRow1(ReactionsContainerLayout rcl) {
        try {
            ViewGroup rv = rcl.recyclerListView;
            if (!(rv instanceof ViewGroup)) {
                return;
            }
            ViewGroup vg = (ViewGroup) rv;
            int w = AndroidUtilities.dp(36);
            for (int i = 0; i < vg.getChildCount(); i++) {
                View c = vg.getChildAt(i);
                ViewGroup.LayoutParams lp = c.getLayoutParams();
                if (lp == null) {
                    continue;
                }
                boolean changed = false;
                if (lp.width != w) {
                    lp.width = w;
                    changed = true;
                }
                if (lp instanceof FrameLayout.LayoutParams
                        && ((FrameLayout.LayoutParams) lp).leftMargin != 0) {
                    ((FrameLayout.LayoutParams) lp).leftMargin = 0;
                    changed = true;
                }
                if (changed) {
                    c.setLayoutParams(lp);
                }
            }
        } catch (Throwable ignore) {
        }
    }

    private static View plusButton(ReactionsContainerLayout rcl) {
        Object o = getField(fPlusIcon, rcl);
        return o instanceof View ? (View) o : null;
    }

    private static void movePlusToRow2(ReactionsContainerLayout rcl, LinearLayout row2, int cellW, int btnH) {
        try {
            if (row2 == null) {
                return;
            }
            View existingPlus = row2.findViewWithTag("crr_plus2");
            if (existingPlus != null && existingPlus.getParent() == row2) {
                return;
            }
            Context ctx = rcl.getContext();
            if (cInternalImageView == null) {
                return;
            }
            ImageView plus2 = (ImageView) cInternalImageView.newInstance(rcl, ctx);
            plus2.setTag("crr_plus2");
            View orig = plusButton(rcl);
            if (orig instanceof ImageView) {
                try {
                    android.graphics.drawable.Drawable d = ((ImageView) orig).getDrawable();
                    if (d != null) {
                        plus2.setImageDrawable(d);
                    }
                    plus2.setScaleType(((ImageView) orig).getScaleType());
                    android.graphics.ColorFilter cf = ((ImageView) orig).getColorFilter();
                    if (cf != null) {
                        plus2.setColorFilter(cf);
                    }
                } catch (Throwable ignore) {
                }
            }
            try {
                GradientDrawable circle = new GradientDrawable();
                circle.setShape(GradientDrawable.OVAL);
                int c1 = Theme.getColor(Theme.key_actionBarDefaultSubmenuItemIcon);
                int c2 = Theme.getColor(Theme.key_dialogBackground);
                circle.setColor(ColorUtils.blendARGB(c1, c2, 0.7f));
                plus2.setBackground(circle);
            } catch (Throwable ignore) {
            }
            int dia = cellW - AndroidUtilities.dp(6);
            if (dia < AndroidUtilities.dp(20)) {
                dia = cellW;
            }
            FrameLayout plusCell = new FrameLayout(ctx);
            plusCell.setTag("crr_plus2_cell");
            plusCell.addView(plus2, new FrameLayout.LayoutParams(dia, dia, Gravity.CENTER));
            row2.addView(plusCell, new FrameLayout.LayoutParams(cellW, btnH));
            plus2.setVisibility(View.VISIBLE);
            bindPlusClick(plus2, rcl);
        } catch (Throwable t) {
            log("movePlus: " + t);
        }
    }

    private static void bindPlusClick(View plus2, final ReactionsContainerLayout rcl) {
        if (plus2 == null || plus2.hasOnClickListeners()) {
            return;
        }
        plus2.setOnClickListener(new View.OnClickListener() {
            @Override
            public void onClick(View v) {
                try {
                    if (mShowCustomDialog != null) {
                        mShowCustomDialog.invoke(rcl);
                    }
                } catch (Throwable ignore) {
                    // fall back to the native click behaviour
                    try {
                        rcl.performClick();
                    } catch (Throwable ignore2) {
                    }
                }
            }
        });
    }

    private static void ensureX8(final ReactionsContainerLayout rcl,
                                 ReactionsLayoutInBubble.VisibleReaction vr8,
                                 int cellW, int btnH) {
        try {
            if (rcl.findViewWithTag("crr_x8") != null || cHolderView == null || mSetReaction == null) {
                return;
            }
            Context ctx = rcl.getContext();
            final View x8 = (View) cHolderView.newInstance(rcl, ctx, Boolean.TRUE);
            x8.setTag("crr_x8");
            mSetReaction.invoke(null, x8, vr8, Integer.valueOf(-1));
            hidePressedBackup(x8);
            x8.setOnClickListener(new View.OnClickListener() {
                @Override
                public void onClick(View v) {
                    try {
                        Object cr = fHolderCurrentReaction.get(x8);
                        if (cr instanceof ReactionsLayoutInBubble.VisibleReaction) {
                            rcl.onReactionClicked(v,
                                    (ReactionsLayoutInBubble.VisibleReaction) cr, false);
                        }
                    } catch (Throwable ignore) {
                    }
                }
            });
            rcl.addView(x8, new FrameLayout.LayoutParams(cellW, btnH, Gravity.TOP | Gravity.LEFT));
            startHolderAnimation(x8, 210);
            mainHandler.post(new Runnable() {
                @Override
                public void run() {
                    positionX8(rcl);
                    startHolderAnimation(x8, 210);
                }
            });
        } catch (Throwable t) {
            log("ensureX8: " + t);
        }
    }

    private static void positionX8(ReactionsContainerLayout rcl) {
        try {
            View x8 = rcl.findViewWithTag("crr_x8");
            if (x8 == null) {
                return;
            }
            Object crc = getField(fCustomContainer, rcl);
            ViewGroup rv = rcl.recyclerListView;
            if (rv == null) {
                return;
            }
            View anchor = crc instanceof View && ((View) crc).getWidth() > 0
                    && ((View) crc).getHeight() > 0 ? (View) crc : null;
            if (anchor == null && rv.getChildCount() > 7) {
                View c8 = rv.getChildAt(7);
                if (c8 != null && c8.getWidth() > 0 && c8.getHeight() > 0) {
                    anchor = c8;
                }
            }
            if (anchor == null) {
                return;
            }
            ViewGroup.LayoutParams lpRaw = x8.getLayoutParams();
            if (!(lpRaw instanceof FrameLayout.LayoutParams)) {
                return;
            }
            FrameLayout.LayoutParams lp = (FrameLayout.LayoutParams) lpRaw;
            int nl = rv.getLeft() - rcl.getPaddingLeft() + anchor.getLeft();
            int nt = rv.getTop() - rcl.getPaddingTop() + anchor.getTop();
            if (lp.leftMargin != nl || lp.topMargin != nt
                    || lp.width != anchor.getWidth() || lp.height != anchor.getHeight()) {
                lp.leftMargin = nl;
                lp.topMargin = nt;
                lp.width = anchor.getWidth();
                lp.height = anchor.getHeight();
                lp.gravity = Gravity.TOP | Gravity.LEFT;
                x8.setLayoutParams(lp);
            }
            if (x8.getVisibility() != View.VISIBLE) {
                x8.setVisibility(View.VISIBLE);
            }
        } catch (Throwable ignore) {
        }
    }

    private static void hideNativeNext(ReactionsContainerLayout rcl) {
        if (rcl == null) {
            return;
        }
        try {
            View x = rcl.nextRecentReaction;
            if (x != null && x.getVisibility() != View.GONE) {
                x.setVisibility(View.GONE);
            }
            rcl.isHiddenNextReaction = true;
        } catch (Throwable ignore) {
        }
    }

    private static void syncExtraRow(ReactionsContainerLayout rcl) {
        try {
            ExtraRowState st;
            synchronized (extraStates) {
                st = extraStates.get(rcl);
            }
            if (st == null || st.pending || st.keys == null || st.btnHeight <= 0) {
                return;
            }
            ViewGroup rv = rcl.recyclerListView;
            if (rv == null) {
                return;
            }
            View row2 = rcl.findViewWithTag("crr_row2");
            if (row2 == null || row2.getWidth() <= 0 || row2.getHeight() <= 0) {
                return;
            }
            try {
                if (rcl.getPullingLeftProgress() > 0f) {
                    return;
                }
            } catch (Throwable ignore) {
            }
            ViewGroup.LayoutParams lp = rcl.getLayoutParams();
            if (lp != null && lp.height != st.targetRclHeight) {
                lp.height = st.targetRclHeight;
                rcl.setLayoutParams(lp);
            }
            ViewGroup.LayoutParams rvLp = rv.getLayoutParams();
            if (rvLp != null && rvLp.height != st.targetRvHeight) {
                rvLp.height = st.targetRvHeight;
                rv.setLayoutParams(rvLp);
            }
            positionX8(rcl);
            hideNativeNext(rcl);
        } catch (Throwable ignore) {
        }
    }

    private static void teardownExtraRow(ReactionsContainerLayout rcl, ExtraRowState st) {
        try {
            View prev2 = rcl.findViewWithTag("crr_row2");
            if (prev2 != null) {
                try {
                    View x = rcl.nextRecentReaction;
                    if (x != null && x.getParent() == prev2) {
                        ((ViewGroup) prev2).removeView(x);
                        rcl.addView(x, new FrameLayout.LayoutParams(AndroidUtilities.dp(36), -1));
                    }
                } catch (Throwable ignore) {
                }
                try {
                    rcl.removeView(prev2);
                } catch (Throwable ignore) {
                }
                try {
                    ViewGroup.LayoutParams lp = rcl.getLayoutParams();
                    if (lp != null) {
                        lp.height = -2;
                        rcl.setLayoutParams(lp);
                        rcl.requestLayout();
                    }
                } catch (Throwable ignore) {
                }
            }
            try {
                View x8 = rcl.findViewWithTag("crr_x8");
                if (x8 != null) {
                    rcl.removeView(x8);
                }
            } catch (Throwable ignore) {
            }
            // return "+" to its native container
            try {
                Object crcO = getField(fCustomContainer, rcl);
                View plus = plusButton(rcl);
                if (crcO instanceof ViewGroup && plus != null) {
                    ViewGroup crc = (ViewGroup) crcO;
                    ViewGroup parent = plus.getParent() instanceof ViewGroup
                            ? (ViewGroup) plus.getParent() : null;
                    if (parent != null && parent != crc) {
                        parent.removeView(plus);
                    }
                    if (plus.getParent() == null) {
                        crc.addView(plus, new FrameLayout.LayoutParams(
                                AndroidUtilities.dp(30), AndroidUtilities.dp(30), Gravity.CENTER));
                    }
                    crc.setVisibility(View.VISIBLE);
                }
            } catch (Throwable ignore) {
            }
            try {
                if (rcl.nextRecentReaction != null) {
                    rcl.nextRecentReaction.setVisibility(View.VISIBLE);
                    rcl.isHiddenNextReaction = false;
                }
            } catch (Throwable ignore) {
            }
            st.keys = null;
            restoreRow1(rcl);
            mainHandler.postDelayed(new Runnable() {
                @Override
                public void run() {
                    restoreRow1(rcl);
                }
            }, 250);
            synchronized (extraStates) {
                extraStates.remove(rcl);
                if (extraStates.isEmpty()) {
                    anyExtraRowActive = false;
                }
            }
        } catch (Throwable t) {
            log("teardown: " + t);
        }
    }

    // ==================================================================
    // localization (ru / en, follows the app language)
    // ==================================================================

    private static boolean isRu() {
        try {
            LocaleController lc = LocaleController.getInstance();
            if (lc != null) {
                Locale l = lc.getCurrentLocale();
                if (l != null && l.getLanguage() != null && l.getLanguage().toLowerCase().startsWith("ru")) {
                    return true;
                }
                Locale sysL = lc.getSystemDefaultLocale();
                if (sysL != null && sysL.getLanguage() != null && sysL.getLanguage().toLowerCase().startsWith("ru")) {
                    return true;
                }
            }
        } catch (Throwable ignore) {
        }
        try {
            Locale l = Locale.getDefault();
            if (l != null && l.getLanguage() != null && l.getLanguage().toLowerCase().startsWith("ru")) {
                return true;
            }
        } catch (Throwable ignore) {
        }
        return false;
    }

    private static String loc(String en, String ru) {
        return isRu() ? ru : en;
    }

    // ==================================================================
    // picker (native, SelectAnimatedEmojiDialog-based, TG-channel style)
    // ==================================================================

    public static void pyShowPicker(Object contextObj) {
        try {
            Context context;
            if (contextObj instanceof Context) {
                context = (Context) contextObj;
            } else {
                context = ApplicationLoader.applicationContext;
            }
            if (context == null) {
                return;
            }
            showPicker(context);
        } catch (Throwable t) {
            log("pyShowPicker: " + t);
        }
    }

    private static void showPicker(final Context context) {
        final int account;
        try {
            account = UserConfig.selectedAccount;
        } catch (Throwable t) {
            return;
        }

        // current selection (ordered)
        final ArrayList<String> selected = new ArrayList<>();
        List<String> cfg = cfgItems;
        if (cfg == null) {
            readPrefsIntoConfig();
            cfg = cfgItems;
        }
        if (cfg != null) {
            for (String s : cfg) {
                if (s != null && !s.trim().isEmpty()) {
                    selected.add(normalizeItem(s));
                }
            }
        }

        LinearLayout root = new LinearLayout(context);
        root.setOrientation(LinearLayout.VERTICAL);

        // ---- header: title + count chip ----
        LinearLayout header = new LinearLayout(context);
        header.setOrientation(LinearLayout.HORIZONTAL);
        header.setGravity(Gravity.CENTER_VERTICAL);
        header.setPadding(AndroidUtilities.dp(20), AndroidUtilities.dp(12),
                AndroidUtilities.dp(20), AndroidUtilities.dp(4));

        TextView title = new TextView(context);
        title.setText(loc("Pick reactions", "Выбор реакций"));
        title.setTextSize(TypedValue.COMPLEX_UNIT_DIP, 18);
        title.setTypeface(Typeface.DEFAULT_BOLD);
        title.setTextColor(Theme.getColor(Theme.key_dialogTextBlack));

        final TextView chip = new TextView(context);
        chip.setTextSize(TypedValue.COMPLEX_UNIT_DIP, 14);
        chip.setTypeface(Typeface.DEFAULT_BOLD);
        chip.setGravity(Gravity.CENTER);
        chip.setMinWidth(AndroidUtilities.dp(34));
        chip.setPadding(AndroidUtilities.dp(10), AndroidUtilities.dp(3),
                AndroidUtilities.dp(10), AndroidUtilities.dp(3));
        chip.setTextColor(0xFFFFFFFF);
        chip.setBackground(Theme.createRoundRectDrawable(
                Theme.getColor(Theme.key_featuredStickers_buttonText), AndroidUtilities.dp(12)));

        header.addView(title);
        header.addView(new View(context), new LinearLayout.LayoutParams(0, 1, 1f));
        header.addView(chip);
        root.addView(header, new LinearLayout.LayoutParams(-1, -2));

        // ---- preview strip ----
        FrameLayout previewContainer = new FrameLayout(context);
        previewContainer.setBackground(Theme.createRoundRectDrawable(
                Theme.getColor(Theme.key_chat_inReactionButtonBackground), AndroidUtilities.dp(16)));
        HorizontalScrollView previewScroll = new HorizontalScrollView(context);
        previewScroll.setHorizontalScrollBarEnabled(false);
        final LinearLayout previewRow = new LinearLayout(context);
        previewRow.setOrientation(LinearLayout.HORIZONTAL);
        previewRow.setGravity(Gravity.CENTER_VERTICAL);
        previewRow.setPadding(AndroidUtilities.dp(8), 0, AndroidUtilities.dp(8), 0);
        previewScroll.addView(previewRow);
        previewContainer.addView(previewScroll,
                new FrameLayout.LayoutParams(-1, AndroidUtilities.dp(44)));
        root.addView(previewContainer, new LinearLayout.LayoutParams(-1, AndroidUtilities.dp(52)));

        TextView subHint = new TextView(context);
        subHint.setText(loc("Tap to move cursor, hold to remove reaction",
                            "Нажатие — перемещение курсора, удерживание — удаление реакции"));
        subHint.setTextSize(TypedValue.COMPLEX_UNIT_DIP, 12);
        subHint.setTextColor(Theme.getColor(Theme.key_windowBackgroundWhiteGrayText));
        subHint.setGravity(Gravity.CENTER_HORIZONTAL);
        subHint.setPadding(AndroidUtilities.dp(16), AndroidUtilities.dp(4),
                AndroidUtilities.dp(16), AndroidUtilities.dp(6));
        root.addView(subHint, new LinearLayout.LayoutParams(-1, -2));

        // ---- native emoji picker ----
        final SelectAnimatedEmojiDialog[] dialogRef = new SelectAnimatedEmojiDialog[1];
        final Runnable[] refreshRef = new Runnable[1];
        // insertion cursor: index in `selected` where the next tapped
        // reaction will be inserted (tap a preview item to move it)
        final int[] insIdx = new int[1];
        insIdx[0] = selected.size();
        final Runnable refreshUi = new Runnable() {
            @Override
            public void run() {
                chip.setText(String.valueOf(selected.size()));
                previewRow.removeAllViews();
                if (selected.isEmpty()) {
                    insIdx[0] = 0;
                    TextView hint = new TextView(context);
                    hint.setText(loc("Tap emoji to add — no limit", "Нажимайте на эмодзи, чтобы добавить — без ограничений"));
                    hint.setTextSize(TypedValue.COMPLEX_UNIT_DIP, 14);
                    hint.setGravity(Gravity.CENTER);
                    hint.setTextColor(Theme.getColor(Theme.key_windowBackgroundWhiteGrayText));
                    previewRow.addView(hint, new LinearLayout.LayoutParams(-1, -2));
                } else {
                    if (insIdx[0] > selected.size()) {
                        insIdx[0] = selected.size();
                    }
                    for (int i = 0; i < selected.size(); i++) {
                        if (i == insIdx[0]) {
                            previewRow.addView(makeCursorView(context),
                                    new LinearLayout.LayoutParams(AndroidUtilities.dp(14), AndroidUtilities.dp(40)));
                        }
                        final String item = selected.get(i);
                        final int at = i;
                        View cell = makePreviewCell(context, item, account,
                                new Runnable() {
                                    @Override
                                    public void run() { // tap: move cursor before this item
                                        insIdx[0] = at;
                                        refreshRef[0].run();
                                    }
                                },
                                new Runnable() {
                                    @Override
                                    public void run() { // long-press: remove
                                        int p = selected.indexOf(item);
                                        if (p >= 0) {
                                            selected.remove(p);
                                            if (insIdx[0] > p) {
                                                insIdx[0]--;
                                            }
                                        }
                                        syncDialogSelection(dialogRef[0], selected, account);
                                        refreshRef[0].run();
                                    }
                                });
                        previewRow.addView(cell,
                                new LinearLayout.LayoutParams(AndroidUtilities.dp(40), AndroidUtilities.dp(40)));
                    }
                    if (insIdx[0] >= selected.size()) {
                        previewRow.addView(makeCursorView(context),
                                new LinearLayout.LayoutParams(AndroidUtilities.dp(14), AndroidUtilities.dp(40)));
                    }
                }
                syncDialogSelection(dialogRef[0], selected, account);
                // keep the cursor visible in the strip
                previewScroll.post(new Runnable() {
                    @Override
                    public void run() {
                        try {
                            int x = insIdx[0] * AndroidUtilities.dp(40) + AndroidUtilities.dp(8);
                            previewScroll.scrollTo(Math.max(0, x - previewScroll.getWidth() / 2), 0);
                        } catch (Throwable ignore) {
                        }
                    }
                });
            }
        };
        refreshRef[0] = refreshUi;

        SelectAnimatedEmojiDialog emojiDialog = new SelectAnimatedEmojiDialog(
                null, context, false, null,
                1 /* TYPE_REACTIONS — same as the native "+" reaction window */,
                true, null, 16) {
            @Override
            public void onReactionClick(SelectAnimatedEmojiDialog.ImageViewEmoji emoji,
                                        ReactionsLayoutInBubble.VisibleReaction reaction) {
                if (reaction == null || reaction.isStar) {
                    return;
                }
                if (reaction.emojicon != null) {
                    toggleAt("e:" + reaction.emojicon.replace("\uFE0F", ""), selected, insIdx);
                    refreshUi.run();
                }
            }

            @Override
            public void onEmojiSelected(View view, Long documentId, TLRPC.Document document,
                                        TL_stars.TL_starGiftUnique gift, Integer until) {
                if (documentId != null && documentId != 0) {
                    toggleAt("doc:" + documentId, selected, insIdx);
                    refreshUi.run();
                }
            }

            @Override
            public void onEmojiSelected(View view, Long documentId, TLRPC.Document document,
                                        TL_stars.TL_starGiftUnique gift, Integer until, String emoticon) {
                if (documentId != null && documentId != 0) {
                    toggleAt("doc:" + documentId, selected, insIdx);
                    refreshUi.run();
                }
            }

            @Override
            public void onMeasure(int widthMeasureSpec, int heightMeasureSpec) {
                // The native dialog measures itself to a fixed ~324dp width;
                // keep that (the bubble design), but take the height the
                // parent gives us instead of the native AT_MOST cap.
                int w = (int) Math.min(AndroidUtilities.dp(340 - 16),
                        AndroidUtilities.displaySize.x * 0.95f);
                super.onMeasure(
                        View.MeasureSpec.makeMeasureSpec(w, View.MeasureSpec.EXACTLY),
                        heightMeasureSpec);
            }
        };
        dialogRef[0] = emojiDialog;
        // drawBackground stays true (the ctor param is never applied to the
        // field) — the dialog paints its native bubble and onShow() below
        // runs the reveal animation that makes tabs and cells visible.

        // rows on top: current picks, then every standard enabled reaction
        ArrayList<ReactionsLayoutInBubble.VisibleReaction> recents = new ArrayList<>();
        LinkedHashSet<String> seenRecent = new LinkedHashSet<>();
        for (int i = 0; i < selected.size(); i++) {
            ReactionsLayoutInBubble.VisibleReaction vr = itemToVr(selected.get(i), account);
            if (vr != null && seenRecent.add(keyOf(vr))) {
                recents.add(vr);
            }
        }
        List<String> std = standardEmojis(account);
        for (int i = 0; i < std.size(); i++) {
            String se = std.get(i);
            if (se == null || se.isEmpty()) {
                continue;
            }
            ReactionsLayoutInBubble.VisibleReaction vr = ReactionsLayoutInBubble.VisibleReaction
                    .fromEmojicon(matchEmoticon(se, account));
            if (vr != null && seenRecent.add(keyOf(vr))) {
                recents.add(vr);
            }
        }
        try {
            emojiDialog.setRecentReactions(recents);
        } catch (Throwable ignore) {
        }
        syncDialogSelection(emojiDialog, selected, account);

        int pickH = Math.max(AndroidUtilities.dp(280),
                Math.min(AndroidUtilities.dp(430),
                        AndroidUtilities.displaySize.y - AndroidUtilities.dp(250)));
        // The dialog forces its own fixed width, so center it inside the sheet
        FrameLayout dialogWrap = new FrameLayout(context);
        dialogWrap.addView(emojiDialog,
                new FrameLayout.LayoutParams(-2, -2, Gravity.CENTER_HORIZONTAL));
        root.addView(dialogWrap, new LinearLayout.LayoutParams(-1, pickH));

        AlertDialog.Builder builder = new AlertDialog.Builder(context);
        builder.setView(root);
        builder.setPositiveButton(loc("Done", "Готово"), new AlertDialog.OnButtonClickListener() {
            @Override
            public void onClick(AlertDialog dialog, int which) {
                try {
                    saveReactionsToPrefs(selected);
                    readPrefsIntoConfig();
                } catch (Throwable ignore) {
                }
            }
        });
        builder.setNegativeButton(loc("Cancel", "Отмена"), null);
        AlertDialog dialog = builder.create();
        try {
            if (dialog.getWindow() != null) {
                dialog.getWindow().setSoftInputMode(
                        android.view.WindowManager.LayoutParams.SOFT_INPUT_ADJUST_RESIZE);
            }
        } catch (Throwable ignore) {
        }
        dialog.show();
        // Native flow always calls onShow() after the dialog is visible —
        // it starts the reveal animation; without it tabs stay at scale 0
        // and the picker appears blank (but still clickable).
        try {
            emojiDialog.onShow(new Runnable() {
                @Override
                public void run() {
                    try {
                        dialog.dismiss();
                    } catch (Throwable ignore) {
                    }
                }
            });
        } catch (Throwable ignore) {
        }
        refreshUi.run();
    }

    private static void syncDialogSelection(SelectAnimatedEmojiDialog dialog,
                                            ArrayList<String> selected, int account) {
        if (dialog == null) {
            return;
        }
        HashSet<ReactionsLayoutInBubble.VisibleReaction> set = new HashSet<>();
        for (int i = 0; i < selected.size(); i++) {
            ReactionsLayoutInBubble.VisibleReaction vr = itemToVr(selected.get(i), account);
            if (vr != null) {
                set.add(vr);
            }
        }
        try {
            dialog.setSelectedReactions(set);
            dialog.notifyDataSetChanged();
        } catch (Throwable ignore) {
        }
    }

    private static String normalizeItem(String s) {
        s = s.trim();
        if (s.startsWith("doc:")) {
            return s;
        }
        if (s.startsWith("e:")) {
            s = s.substring(2).trim();
        }
        if (s.endsWith("\uFE0F")) {
            s = s.substring(0, s.length() - 1);
        }
        return s.isEmpty() ? s : "e:" + s;
    }

    private static ReactionsLayoutInBubble.VisibleReaction itemToVr(String item, int account) {
        try {
            if (item.startsWith("doc:")) {
                return ReactionsLayoutInBubble.VisibleReaction.fromCustomEmoji(
                        Long.parseLong(item.substring(4).trim()));
            }
            String emoji = item.startsWith("e:") ? item.substring(2) : item;
            emoji = emoji.replace("\uFE0F", "");
            if (emoji.isEmpty()) {
                return null;
            }
            return ReactionsLayoutInBubble.VisibleReaction.fromEmojicon(matchEmoticon(emoji, account));
        } catch (Throwable t) {
            return null;
        }
    }

    private static String keyOf(ReactionsLayoutInBubble.VisibleReaction vr) {
        if (vr.emojicon != null) {
            return "e:" + vr.emojicon.replace("\uFE0F", "");
        }
        return "d:" + vr.documentId;
    }

    /** Toggle a reaction, inserting at the cursor when adding. */
    private static void toggleAt(String key, ArrayList<String> selected, int[] insIdx) {
        int existing = selected.indexOf(key);
        if (existing >= 0) {
            selected.remove(existing);
            if (insIdx[0] > existing) {
                insIdx[0]--;
            }
        } else {
            int pos = Math.min(insIdx[0], selected.size());
            selected.add(pos, key);
            insIdx[0] = pos + 1;
        }
    }

    /** "|" indicator marking where the next reaction will be inserted. */
    private static View makeCursorView(Context context) {
        TextView cursor = new TextView(context);
        cursor.setText("|");
        cursor.setTag("crr_picker_cursor");
        cursor.setTextSize(TypedValue.COMPLEX_UNIT_DIP, 24);
        cursor.setTypeface(Typeface.DEFAULT_BOLD);
        cursor.setGravity(Gravity.CENTER);
        cursor.setTextColor(Theme.getColor(Theme.key_featuredStickers_addButton));
        return cursor;
    }

    private static View makePreviewCell(Context context, final String item, int account,
                                        final Runnable onTap, final Runnable onRemove) {
        FrameLayout cell = new FrameLayout(context);
        try {
            if (item.startsWith("doc:")) {
                try {
                    long docId = Long.parseLong(item.substring(4).trim());
                    BackupImageView img = new BackupImageView(context);
                    AnimatedEmojiDrawable aed = null;
                    try {
                        aed = new AnimatedEmojiDrawable(EMOJI_CACHE_PREVIEW, account, docId);
                    } catch (Throwable ignore) {
                    }
                    if (aed == null) {
                        aed = new AnimatedEmojiDrawable(EMOJI_CACHE_DEFAULT, account, docId);
                    }
                    img.setAnimatedEmojiDrawable(aed);
                    cell.addView(img, LayoutHelper.createFrame(24, 24, Gravity.CENTER));
                } catch (Throwable ignore) {
                    addFallbackStar(cell, context);
                }
            } else {
                String emoji = item.startsWith("e:") ? item.substring(2) : item;
                android.graphics.drawable.Drawable d = null;
                try {
                    d = Emoji.getEmojiDrawable(emoji);
                } catch (Throwable ignore) {
                }
                if (d != null) {
                    ImageView iv = new ImageView(context);
                    iv.setImageDrawable(d);
                    iv.setScaleType(ImageView.ScaleType.FIT_CENTER);
                    cell.addView(iv, LayoutHelper.createFrame(24, 24, Gravity.CENTER));
                } else {
                    TextView tv = new TextView(context);
                    try {
                        tv.setText(Emoji.replaceEmoji(emoji, tv.getPaint().getFontMetricsInt(), false));
                    } catch (Throwable t) {
                        tv.setText(emoji);
                    }
                    tv.setTextSize(TypedValue.COMPLEX_UNIT_DIP, 20);
                    tv.setGravity(Gravity.CENTER);
                    tv.setTextColor(Theme.getColor(Theme.key_dialogTextBlack));
                    cell.addView(tv, LayoutHelper.createFrame(28, 28, Gravity.CENTER));
                }
            }
        } catch (Throwable ignore) {
        }
        // tap moves the insertion cursor, long-press removes the reaction
        cell.setOnClickListener(new View.OnClickListener() {
            @Override
            public void onClick(View v) {
                onTap.run();
            }
        });
        cell.setOnLongClickListener(new View.OnLongClickListener() {
            @Override
            public boolean onLongClick(View v) {
                onRemove.run();
                return true;
            }
        });
        cell.setBackground(Theme.createSelectorDrawable(Theme.getColor(Theme.key_listSelector), 16));
        return cell;
    }

    private static void addFallbackStar(FrameLayout cell, Context context) {
        TextView tv = new TextView(context);
        tv.setText("\u2B50");
        tv.setTextSize(TypedValue.COMPLEX_UNIT_DIP, 16);
        tv.setGravity(Gravity.CENTER);
        tv.setTextColor(Theme.getColor(Theme.key_dialogTextBlack));
        cell.addView(tv, LayoutHelper.createFrame(24, 24, Gravity.CENTER));
    }

    // ==================================================================

    private static void log(String msg) {
        try {
            android.util.Log.d(TAG, msg);
        } catch (Throwable ignore) {
        }
    }
}
