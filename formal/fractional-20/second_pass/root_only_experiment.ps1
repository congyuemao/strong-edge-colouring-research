. "$PSScriptRoot\..\independent\env.ps1"
$ErrorActionPreference = 'Stop'
# A computational experiment only. This does not establish a Lean theorem.
# Retain the original exact gates and all graph constraints, but replace the
# root-neighbour pattern and lexicographic clauses by the sole unit Q_01.
$source = Get-Content -Raw -Encoding utf8 "$PSScriptRoot\..\independent\encode.cpp"
$begin = $source.IndexOf('  // Select any Q edge')
$end = $source.IndexOf('f.save(out+".cnf");', $begin)
if ($begin -lt 0 -or $end -lt 0) { throw 'Encoder markers missing' }
$source = $source.Substring(0,$begin) + "  f.add({q[0][1]});`n  " + $source.Substring($end)
$source = $source.Replace('selectors.size()', '1')
[IO.File]::WriteAllText("$PSScriptRoot\encode_root_only.cpp", $source, [Text.UTF8Encoding]::new($false))
& 'E:\Qt\Tools\mingw1310_64\bin\g++.exe' -std=c++17 -O2 -static "$PSScriptRoot\encode_root_only.cpp" -o "$PSScriptRoot\encode_root_only.exe"
if ($LASTEXITCODE -ne 0) { throw 'Compilation failed' }
& "$PSScriptRoot\encode_root_only.exe" 23 16 4 "$PSScriptRoot\root_only" > "$PSScriptRoot\root_only-encode.log"
if ($LASTEXITCODE -ne 0) { throw 'Encoding failed' }
$timer = [Diagnostics.Stopwatch]::StartNew()
$solver = Start-Process -FilePath "$ToolBin\cadical.exe" -ArgumentList @('--lrat', "$PSScriptRoot\root_only.cnf", "$PSScriptRoot\root_only.lrat") -WindowStyle Hidden -PassThru -RedirectStandardOutput "$PSScriptRoot\root_only-solver.log" -RedirectStandardError "$PSScriptRoot\root_only-solver.err"
$finished = $solver.WaitForExit(120000)
if (!$finished) { $solver.Kill(); $solver.WaitForExit() }
$timer.Stop()
"finished=$finished exit=$($solver.ExitCode) elapsed_seconds=$($timer.Elapsed.TotalSeconds)" | Set-Content "$PSScriptRoot\root_only-timing.txt"
