# MPC-HC Tablet Frame build

This custom build adds a tablet-style hardware frame only to the MPC-HC main
window. It does not install a Windows theme and does not affect other apps.

## Controls

- Left half of the long top rocker: volume down.
- Right half of the long top rocker: volume up.
- Short top button: play/pause.
- Drag the bezel to move the player.
- Drag a bezel edge or corner to resize the player.

The frame is hidden while the player is minimized, maximized, or using its
main-frame fullscreen mode. Its dimensions are DPI-scaled for Windows 10.

## Build

Use the normal MPC-HC build environment described in `docs/Compilation.md`.
For a quick x64 compile test, select `Release Lite|x64` in Visual Studio. A
full release additionally needs the codec and assembler dependencies listed in
the upstream compilation guide.

After installing the required Visual Studio C++ and MFC components, the same
quick build can be started from a Developer Command Prompt with:

```bat
build-tablet-x64.bat
```

The `Build MPC-HC Tablet x64` GitHub Actions workflow performs the same build
on a Windows runner and publishes `mpc-hc-tablet-win10-x64` as a downloadable
artifact.
