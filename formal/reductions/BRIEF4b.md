# Fourth pass, resumed

The previous run stopped because `build.ps1` refused to compile while other `lean` processes were running. Those belong to other Codex runs on this machine (`E:\lean\se20-insertion`, `E:\lean\se20-fractional`) and they will not pause; you do not need them to. The guard in `build.ps1` now allows up to two other `lean` processes. If it still refuses, wait and retry with a delay; do not stop and do not ask. Use `-j1`.

Read `BRIEF4.md` and the Fourth pass section of `REPORT.md`, verify the pending draft modules, and continue with the targets in order. Run the whole build before finishing. Same rules.
