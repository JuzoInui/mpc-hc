@ECHO OFF
SETLOCAL
PUSHD "%~dp0"

CALL build.bat Build x64 Main Release Lite
SET "TABLET_BUILD_RESULT=%ERRORLEVEL%"

IF NOT "%TABLET_BUILD_RESULT%" == "0" (
  ECHO.
  ECHO Tablet build failed. Check docs\Compilation.md for the required Visual Studio MFC components.
) ELSE (
  ECHO.
  ECHO Tablet build completed. Check bin\mpc-hc_x64 for mpc-hc64.exe.
)

POPD
EXIT /B %TABLET_BUILD_RESULT%
