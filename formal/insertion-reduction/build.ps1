$ErrorActionPreference = 'Stop'
$env:ELAN_HOME = 'E:\lean\elan'
$env:XDG_CACHE_HOME = 'E:\lean\cache'
$env:TEMP = 'E:\lean\tmp'
$env:TMP = 'E:\lean\tmp'
$env:GIT_CONFIG_COUNT = '1'
$env:GIT_CONFIG_KEY_0 = 'safe.directory'
$env:GIT_CONFIG_VALUE_0 = '*'
Set-Location $PSScriptRoot
New-Item -ItemType Directory -Force '.lake\build\lib\lean\Se20Insertion' | Out-Null
# Compile only this project's sources. Dependencies are read from their existing
# local oleans; Lake is used only to supply the environment, never to build/fetch them.
# A Windows dependency read can fail transiently even when the file exists.
# Retry only that specific I/O error, retaining every diagnostic in the log.
# Proof/type errors still fail immediately, and no failed check is skipped.
# One project-owned Lean process; unrelated workloads do not block this build.
function Invoke-ProjectLean([string]$ObjectPath, [string]$SourcePath) {
    for ($readAttempt = 1; ; $readAttempt++) {
        $leanOutput = & lake env lean -j1 -o $ObjectPath $SourcePath 2>&1
        $leanExit = $LASTEXITCODE
        $leanOutput | Write-Output
        if ($leanExit -eq 0) { return }
        $readErrors = @($leanOutput | Where-Object { "$_" -match '(^|: )error(?:\([^)]*\))?:' })
        $onlyReadErrors = $readErrors.Count -gt 0 -and
            @($readErrors | Where-Object { "$_" -notmatch ': error: failed to read file' }).Count -eq 0
        if (-not $onlyReadErrors) { exit $leanExit }
        Write-Output "Retrying $SourcePath after a dependency read failure (attempt $readAttempt)."
        Start-Sleep -Seconds 5
    }
}
$modules = @(
    'Definitions', 'Kempe', 'Insertion', 'GraphBasics', 'Fragmentation',
    'ConflictBounds', 'Counting', 'Triangle', 'TriangleInsertion', 'Greedy',
    'Exceptional', 'VertexDeletion', 'Suppression', 'RegularCompletion',
    'StarReduction', 'HoleMoves', 'GroupedInsertion', 'SupportCounts',
    'AuditExamples', 'DoubleHole', 'GirthGeometry', 'GirthBounds',
    'ReachabilityCounting', 'Theorem1144', 'ComponentBounds', 'BicolourCounts',
    'ColourSetCore', 'ColourSetPeeling', 'ColourSetSpecialCases', 'ColourSetCounting',
    'ForestL2', 'ChordalFan', 'Neighbourhood87', 'FanLemma',
    'LocalRepairs', 'SingleChains', 'LowDegree', 'ListExtensions', 'SwapCriteria',
    'CriticalStructure', 'RimCounting', 'Covering', 'ChainObstructions',
    'ForestSeparation', 'ParametricCore', 'ParametricCounting', 'ParametricRatio',
    'StarGeometry', 'DegreeThreeRigidity', 'ShortCycleReduction', 'ListRigidity',
    'StarListRigidity', 'CliqueBoundary', 'CliqueReduction', 'ComponentInsertion',
    'RecolourGain', 'TreePattern', 'ShellChains', 'InfiniteForest', 'CriticalLists',
    'HoleCycleRank', 'MultiplicityIdentity', 'P2Identity', 'P2Geometry',
    'PatternVerification', 'ShellCover', 'LoopChains',
    'HoleStateEquivalence', 'TwoStepSaturation', 'ClassSquarePotential',
    'PotentialReachability', 'PatternGeometry', 'GeometricLoopChains', 'IncidentPalettes',
    'DegreeListTools', 'DegreeListReduction', 'NonseparatingPair', 'RemainingImplications',
    'SeventhPassExamples', 'StaticDynamicExample',
    'LongChainCounts', 'P6Construction', 'P6Geometry', 'P6Sizes', 'P6Core', 'P6Colouring', 'P6Route',
    'DegreeListInduced', 'DegreeListBrooks', 'FiniteNonseparating', 'RegularCycle', 'Gallai',
    'EighthPassExamples', 'AxiomAudit'
)
foreach ($module in $modules) {
    Write-Output "Checking Se20Insertion.$module"
    Invoke-ProjectLean ".lake\build\lib\lean\Se20Insertion\$module.olean" "Se20Insertion\$module.lean"
}
Write-Output 'Checking Se20Insertion'
Invoke-ProjectLean '.lake\build\lib\lean\Se20Insertion.olean' 'Se20Insertion.lean'
Write-Output "Build succeeded: $($modules.Count) modules plus Se20Insertion, all checked serially with -j1."
exit 0
