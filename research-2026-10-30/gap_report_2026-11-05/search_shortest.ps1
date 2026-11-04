param([int]$FirstSeed = 3, [int]$LastSeed = 50)
$ErrorActionPreference = 'Stop'
$env:TEMP = $PSScriptRoot
$env:TMP = $PSScriptRoot
Add-Type -TypeDefinition (Get-Content -Raw -LiteralPath (Join-Path $PSScriptRoot 'Experiments.cs'))
$trialPath = Join-Path $PSScriptRoot 'search_trial.json'
$tracePath = Join-Path $PSScriptRoot 'search_trial_trace.json'
$transportPath = Join-Path $PSScriptRoot 'search_trial_transport.json'
for ($seed = $FirstSeed; $seed -le $LastSeed; $seed++) {
    $previousWriter = [Console]::Out
    $capture = New-Object IO.StringWriter
    try {
        [Console]::SetOut($capture)
        [Experiments]::Hunt(2, $seed, $trialPath, $false)
        $data = Get-Content -Raw -LiteralPath $trialPath | ConvertFrom-Json
        if ($data.seed -ne $seed) { continue }
        $edges = New-Object 'System.Collections.Generic.List[int[]]'
        foreach ($edge in $data.edges) { $edges.Add([int[]]$edge) }
        [Experiments]::Audit($edges, [int[]]$data.colouring, $tracePath, $transportPath)
    } finally {
        [Console]::SetOut($previousWriter)
    }
    $capture.ToString() | Add-Content -LiteralPath (Join-Path $PSScriptRoot 'search_shortest.log')
    $transport = Get-Content -Raw -LiteralPath $transportPath | ConvertFrom-Json
    Write-Output "seed=$seed shortest=$($transport.shortest_static_path)"
    if ($transport.shortest_static_path) {
        Copy-Item -LiteralPath $trialPath -Destination (Join-Path $PSScriptRoot 'gq_hard_shortest.json')
        Copy-Item -LiteralPath $tracePath -Destination (Join-Path $PSScriptRoot 'gq_hard_shortest_trace.json')
        Copy-Item -LiteralPath $transportPath -Destination (Join-Path $PSScriptRoot 'gq_hard_shortest_transport.json')
        Write-Output $capture.ToString()
        break
    }
}
