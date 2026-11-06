param([string[]]$Modules = @(
    'Definitions', 'External', 'Assembly', 'Contraction', 'Split',
    'ColouringTheorems', 'Domination', 'SeedReduction', 'Balls', 'Selection', 'Numerics',
    'OverlapAudit', 'LocalGeometry', 'OpenStatements', 'Decomposition', 'CycleSelection',
    'LocalDominators', 'TheoremB', 'DeadEdges', 'TreeLemma', 'TaggedSelection', 'Pseudoforest',
    'OptionGraph', 'ConcreteTagged', 'SpanningGeometry', 'GeodesicProjection', 'SpanningFamily',
    'TransferMatrix', 'VariableLocalLemma', 'LocalLemma', 'RandomTransversal', 'BadFamilies', 'TheoremBPlus',
    'Haxell', 'HaxellConsequences', 'CertificateEntries', 'TransferCertificate', 'TransferEstimate',
    'TransferFineCertificate', 'TransferFineEstimate', 'ThirdPassConsequences',
    'TransferAutomaton', 'TransferRuns', 'TransferCounting', 'SpanningPatterns',
    'RootedPatterns', 'EmbeddingCounts', 'PathCounting', 'SegmentCounting', 'PatternProducts',
    'DecorationCounting', 'FamilyEncoding', 'EmbeddedFamilyBound', 'CompletedTheorems',
    'TreeBallCodes', 'TreeBalls', 'AxiomAudit'
), [int]$Threads = 0)
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
# No Lake invocation: `lake env` can materialize missing transitive dependencies.
# Read only already installed compiler/dependency artifacts, with no fetch path.
$packageRoot = 'E:\lean\sep19\route-c\lean\.lake\packages'
$localLibs = @(Join-Path $PSScriptRoot '.lake\build\lib\lean')
$localLibs += Get-ChildItem -LiteralPath $packageRoot -Directory | ForEach-Object {
    Join-Path $_.FullName '.lake\build\lib\lean'
} | Where-Object { Test-Path -LiteralPath $_ }
$env:LEAN_PATH = $localLibs -join ';'
$compiler = 'E:\lean\elan\toolchains\leanprover--lean4---v4.35.0-rc4\bin\lean.exe'
if (-not (Test-Path -LiteralPath $compiler)) { throw "Installed compiler missing: $compiler" }
$threadArgs = @()
if ($Threads -gt 0) { $threadArgs = @("-j$Threads") }
foreach ($module in $Modules) {
    Write-Output "Checking Se20Part.$module"
    & $compiler @threadArgs -o ".lake\build\lib\lean\Se20Part\$module.olean" "Se20Part\$module.lean"
    if ($LASTEXITCODE -ne 0) { exit $LASTEXITCODE }
}
& $compiler @threadArgs -o '.lake\build\lib\lean\Se20Part.olean' 'Se20Part.lean'
exit $LASTEXITCODE
