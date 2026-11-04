param([string]$Mode = 'geometry', [int]$Seconds = 120, [int]$Seed = 1, [switch]$AllVertices, [int]$Samples = 20, [int]$Centres = 40, [string]$InputFile = 'gq_hunt_1.json')
$ErrorActionPreference = 'Stop'
$env:TEMP = $PSScriptRoot
$env:TMP = $PSScriptRoot
Add-Type -TypeDefinition (Get-Content -Raw -LiteralPath (Join-Path $PSScriptRoot 'Experiments.cs'))
switch ($Mode) {
    'geometry' { [Experiments]::Geometry() }
    'hunt' { [Experiments]::Hunt($Seconds, $Seed, (Join-Path $PSScriptRoot "gq_hunt_${Seed}.json"), [bool]$AllVertices) }
    'random' { [Experiments]::RandomChecks($Samples, $Seed, (Join-Path $PSScriptRoot "gq_random_${Seed}.json")) }
    'paired' { [Experiments]::Paired($Centres, $Seed, (Join-Path $PSScriptRoot "paired_shadow_${Seed}.json")) }
    'audit' {
        $data = Get-Content -Raw -LiteralPath (Join-Path $PSScriptRoot $InputFile) | ConvertFrom-Json
        $edges = New-Object 'System.Collections.Generic.List[int[]]'
        foreach ($edge in $data.edges) { $edges.Add([int[]]$edge) }
        $stem = [IO.Path]::GetFileNameWithoutExtension($InputFile)
        [Experiments]::Audit($edges, [int[]]$data.colouring, (Join-Path $PSScriptRoot "${stem}_trace.json"), (Join-Path $PSScriptRoot "${stem}_transport.json"))
    }
    default { throw "Unknown mode: $Mode" }
}
