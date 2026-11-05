param([string[]]$Only = @(), [switch]$CheckRoot)
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
    'LocalInjection', 'Transversal', 'DegreeTwo', 'Residual',
    'ComponentExchange', 'EvenPathExchange', 'PathEndpointDegree',
    'CompactExchange', 'CompactGeometry', 'CompactTriangles',
    'WeightedExchange', 'WeightedHubs', 'MatchingTriangle', 'ConditionalTwenty',
    'WeightedComponents', 'ComponentConditional',
    'PackingCases', 'PackingTightness', 'PackingAdditivity', 'PackingEqualityComponents',
    'CriticalSizeChecks', 'CriticalEndpointDegree', 'PetersenMinusHypothesis', 'AuditExamples'
)
$modules += Get-Content -Encoding utf8 (Join-Path $PSScriptRoot 'LEGACY_MODULES.txt')
$modules += @('LegacyBridge', 'High24Seven', 'GirthCliques', 'DegreeTwoCliques', 'F01', 'F09Endpoints', 'ThirteenKernel', 'AxiomAudit')
if ($Only.Count -gt 0) { $modules = $Only }
# Windows can transiently fail to map a dependency olean under memory pressure.
# Retry only those runtime failures, never proof errors. All retries stay visible.
function Invoke-LeanChecked {
    param([string]$SourcePath, [string]$ObjectPath)
    for ($attempt = 1; $attempt -le 4; $attempt++) {
        $ErrorActionPreference = 'Continue'
        $lines = @(& $leanExe -j 1 -s 65536 -o $ObjectPath $SourcePath 2>&1)
        $resultCode = $LASTEXITCODE
        $ErrorActionPreference = 'Stop'
        $lines | ForEach-Object { Write-Output $_.ToString() }
        if ($resultCode -eq 0) { return }
        $runtimeFailure = ($lines -join "`n") -match 'failed to read file|std::bad_alloc'
        if (-not $runtimeFailure -or $attempt -eq 4) { exit $resultCode }
        Write-Warning "Runtime import/memory failure; retry $attempt of 3 for $SourcePath"
        Start-Sleep -Seconds 1
    }
}
foreach ($module in $modules) {
    Write-Output "Checking Se20Part.$module"
    $modulePath = $module.Replace('.', '\')
    $objectPath = ".lake\build\lib\lean\Se20Part\$modulePath.olean"
    [IO.Directory]::CreateDirectory([IO.Path]::GetDirectoryName((Join-Path $PSScriptRoot $objectPath))) | Out-Null
    Invoke-LeanChecked -SourcePath "Se20Part\$modulePath.lean" -ObjectPath $objectPath
}
if ($Only.Count -eq 0 -or $CheckRoot) {
    Write-Output 'Checking Se20Part'
    Invoke-LeanChecked -SourcePath 'Se20Part.lean' -ObjectPath '.lake\build\lib\lean\Se20Part.olean'
}
exit 0
