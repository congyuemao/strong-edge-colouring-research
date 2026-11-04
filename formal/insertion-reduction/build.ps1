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
$modules = @(
    'Definitions', 'Kempe', 'Insertion', 'GraphBasics', 'Fragmentation',
    'ConflictBounds', 'Counting', 'Triangle', 'TriangleInsertion', 'Greedy',
    'Exceptional', 'VertexDeletion', 'Suppression', 'RegularCompletion',
    'StarReduction', 'HoleMoves', 'GroupedInsertion', 'SupportCounts',
    'AuditExamples', 'AxiomAudit'
)
foreach ($module in $modules) {
    Write-Output "Checking Se20Insertion.$module"
    & lake env lean -o ".lake\build\lib\lean\Se20Insertion\$module.olean" "Se20Insertion\$module.lean"
    if ($LASTEXITCODE -ne 0) { exit $LASTEXITCODE }
}
& lake env lean -o '.lake\build\lib\lean\Se20Insertion.olean' 'Se20Insertion.lean'
exit $LASTEXITCODE
