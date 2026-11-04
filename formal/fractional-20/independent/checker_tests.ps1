. "$PSScriptRoot\env.ps1"
$ErrorActionPreference = 'Stop'
$testdir = Join-Path $PSScriptRoot 'checker-tests'
New-Item -ItemType Directory -Force -Path $testdir | Out-Null
Set-Content -Encoding ascii "$testdir\unsat.cnf" @('p cnf 1 2', '1 0', '-1 0')
Set-Content -Encoding ascii "$testdir\sat.cnf" @('p cnf 1 1', '1 0')
Set-Content -Encoding ascii "$testdir\valid.lrat" '3 0 1 2 0'
Set-Content -Encoding ascii "$testdir\invalid.lrat" '2 0 1 0'
Set-Content -Encoding ascii "$testdir\missing.lrat" '3 0 1 9 0'
Set-Content -Encoding ascii "$testdir\deleted.lrat" @('2 d 2 0','3 0 1 2 0')
Set-Content -Encoding ascii "$testdir\incomplete.lrat" '3 1 0 1 0'
$exe = Join-Path $PSScriptRoot 'check_lrat.exe'
& $exe "$testdir\unsat.cnf" "$testdir\valid.lrat"
if ($LASTEXITCODE -ne 0) { throw 'Valid proof rejected' }
foreach ($name in @('invalid','missing','deleted','incomplete')) {
  $cnf = if ($name -eq 'invalid') { 'sat' } else { 'unsat' }
  $ErrorActionPreference = 'Continue'
  & $exe "$testdir\$cnf.cnf" "$testdir\$name.lrat" 2>&1 | ForEach-Object { "${name}: $_" }
  $ErrorActionPreference = 'Stop'
  if ($LASTEXITCODE -eq 0) { throw "Invalid proof accepted: $name" }
}
'All checker tests passed.'
