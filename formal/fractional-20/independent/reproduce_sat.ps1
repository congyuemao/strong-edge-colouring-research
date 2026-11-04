. "$PSScriptRoot\env.ps1"
$ErrorActionPreference = 'Stop'
& "$PSScriptRoot\build.ps1"
& "$PSScriptRoot\checker_tests.ps1"
foreach ($case in @(@('control15',12,15,4), @('control20',10,20,5), @('d16',23,16,4))) {
  $prefix = "independent\$($case[0])"
  & .\independent\encode.exe $case[1] $case[2] $case[3] $prefix
  if ($LASTEXITCODE -ne 0) { throw 'Encoder failed' }
  $timer = [Diagnostics.Stopwatch]::StartNew()
  & "$ToolBin\cadical.exe" --lrat --no-binary -w "$prefix.model" "$prefix.cnf" "$prefix.lrat" > "$prefix.log"
  $solverExit = $LASTEXITCODE
  $timer.Stop()
  "solver_exit=$solverExit wall_seconds=$($timer.Elapsed.TotalSeconds)" | Set-Content "$prefix.timing.txt"
  if ($case[0] -eq 'd16') {
    if ($solverExit -ne 20) { throw 'Expected full instance to be UNSAT' }
    & .\independent\check_lrat.exe "$prefix.cnf" "$prefix.lrat" > "$prefix.check.log"
    if ($LASTEXITCODE -ne 0) { throw 'Independent certificate check failed' }
    & "$ToolBin\lean.exe" --run independent\CheckLRAT.lean "$prefix.cnf" "$prefix.lrat" > "$prefix.std-check.log"
    if ($LASTEXITCODE -ne 0) { throw 'Std LRAT check failed' }
  } else {
    if ($solverExit -ne 10) { throw 'Expected positive control to be SAT' }
    & .\independent\check_model.exe $prefix "$prefix.graph.txt"
    if ($LASTEXITCODE -ne 0) { throw 'Graph-level control validation failed' }
  }
}
