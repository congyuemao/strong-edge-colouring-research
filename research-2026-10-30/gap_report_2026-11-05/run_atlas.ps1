param([int]$Colours = 3, [switch]$Kempe, [int]$MaxN = 7, [switch]$DoubleOnly)
$ErrorActionPreference = 'Stop'
$env:TEMP = $PSScriptRoot
$env:TMP = $PSScriptRoot
Add-Type -TypeDefinition (Get-Content -Raw -LiteralPath (Join-Path $PSScriptRoot 'StateAudit.cs'))
$atlasPath = 'C:\Users\21161\Documents\ChatGPT\se20-ideas\.venv\Lib\site-packages\networkx\generators\atlas.dat.gz'
$kind = if ($Kempe) { 'kempe' } else { 'hole' }
if ($DoubleOnly) { $kind += '_double' }
$outputPath = Join-Path $PSScriptRoot "atlas_counterexample_k${Colours}_${kind}.json"
[StateAudit]::Atlas($atlasPath, $Colours, [bool]$Kempe, $MaxN, $outputPath, [bool]$DoubleOnly)
