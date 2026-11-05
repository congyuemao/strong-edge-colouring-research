param([string[]]$Only = @())
$ErrorActionPreference = 'Stop'
$env:ELAN_HOME = 'E:\lean\elan'
$env:XDG_CACHE_HOME = 'E:\lean\cache'
$env:TEMP = 'E:\lean\tmp'
$env:TMP = 'E:\lean\tmp'
$env:GIT_CONFIG_COUNT = '1'
$env:GIT_CONFIG_KEY_0 = 'safe.directory'
$env:GIT_CONFIG_VALUE_0 = '*'
Set-Location $PSScriptRoot
New-Item -ItemType Directory -Force '.lake\build\lib\lean\Se20Part' | Out-Null
# Deliberately do not invoke Lake or elan: even `lake env` can fetch packages.
# Read the already installed compiler and all existing dependency oleans directly.
$leanExe = 'E:\lean\elan\toolchains\leanprover--lean4---v4.35.0-rc4\bin\lean.exe'
$packageRoot = 'E:\lean\sep19\route-c\lean\.lake\packages'
$libraryPaths = @((Join-Path $PSScriptRoot '.lake\build\lib\lean'))
$libraryPaths += Get-ChildItem -LiteralPath $packageRoot -Directory | ForEach-Object {
    Join-Path $_.FullName '.lake\build\lib\lean'
}
$env:LEAN_PATH = $libraryPaths -join ';'
$modules = @(
    'Definitions', 'GraphBasics', 'ForestL2', 'ChordalFan',
    'ConflictBounds', 'Kempe', 'Recolour', 'Counting', 'Triangle',
    'TriangleInsertion', 'Greedy', 'Partitions', 'CycleLength',
    'GirthDegree', 'RouteQ', 'DegreeProfiles', 'MaximumCut',
    'ColourAssembly', 'Packing', 'TightComponents', 'Critical',
    'LocalInjection', 'Transversal', 'AuditExamples', 'AxiomAudit'
)
if ($Only.Count -gt 0) { $modules = $Only }
foreach ($module in $modules) {
    Write-Output "Checking Se20Part.$module"
    & $leanExe -o ".lake\build\lib\lean\Se20Part\$module.olean" "Se20Part\$module.lean"
    if ($LASTEXITCODE -ne 0) { exit $LASTEXITCODE }
}
if ($Only.Count -eq 0) { & $leanExe -o '.lake\build\lib\lean\Se20Part.olean' 'Se20Part.lean' }
exit $LASTEXITCODE
