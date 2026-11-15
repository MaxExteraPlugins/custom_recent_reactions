@echo off
call "%~dp0bin\tools\build_core.bat" "%~dp0" < nul
exit /b %ERRORLEVEL%
