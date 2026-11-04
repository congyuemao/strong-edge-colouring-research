$ErrorActionPreference = 'Stop'
$env:TEMP = $PSScriptRoot
$env:TMP = $PSScriptRoot
Add-Type -TypeDefinition (Get-Content -Raw -LiteralPath (Join-Path $PSScriptRoot 'IndependentVerifier.cs'))
function New-Verifier($data) {
    $edges = New-Object 'System.Collections.Generic.List[int[]]'
    foreach ($edge in $data.edges) { $edges.Add([int[]]$edge) }
    New-Object IndependentVerifier -ArgumentList $edges,([int[]]$data.colouring)
}
foreach ($stem in @('gq_hunt_1', 'gq_hard_shortest', 'paired_shadow_1')) {
    $data = Get-Content -Raw -LiteralPath (Join-Path $PSScriptRoot "${stem}.json") | ConvertFrom-Json
    $checker = New-Verifier $data
    if (-not $checker.Blocked()) { throw 'Initial hole not blocked' }
    $depth = $checker.MinimumHoleDepthTwo()
    if ($stem -eq 'paired_shadow_1') { $checker.PairedConstruction([int]$data.t) }
    Write-Output "$stem girth=$($checker.Girth) depth=$depth $($checker.PairSummary())"
    $trace = Get-Content -Raw -LiteralPath (Join-Path $PSScriptRoot "${stem}_trace.json") | ConvertFrom-Json
    $checker = New-Verifier $trace
    foreach ($action in $trace.actions) {
        switch ($action.type) {
            'hole' { $checker.Hole([int]$action.from,[int]$action.to,[int]$action.colour) }
            'kempe' { $checker.Kempe([int[]]$action.vertices,[int]$trace.protected_pair[0],[int]$trace.protected_pair[1]) }
            'fill' { $checker.Fill([int]$action.vertex,[int]$action.colour) }
            default { throw 'Unknown action' }
        }
    }
    $checker.Expected([int[]]$trace.final_colouring)
    if ($checker.Colours -contains -1) { throw 'Trace incomplete' }
    $transport = Get-Content -Raw -LiteralPath (Join-Path $PSScriptRoot "${stem}_transport.json") | ConvertFrom-Json
    $checker = New-Verifier $transport
    $g,$f,$w = [int[]]$transport.double
    if (-not $checker.Double($g,$f,$w)) { throw 'Original double missing' }
    if (($transport.path -contains $f) -or ($transport.path -contains $w)) { throw 'Path hits partners' }
    $distance = $checker.StaticDistance([int]$transport.path[0],$g)
    if ($transport.shortest_static_path -and $distance -ne ($transport.path.Count-1)) { throw 'Path not shortest' }
    for ($i=1; $i -lt $transport.path.Count; $i++) {
        $source = [int]$transport.path[$i-1]
        $target = [int]$transport.path[$i]
        $checker.Hole($source,$target,$checker.Colours[$target])
    }
    $checker.Expected([int[]]$transport.after_path)
    if ($checker.Double($g,$f,$w)) { throw 'Double survived' }
    Write-Output "$stem trace and transport independently verified; static distance=$distance"
}
Write-Output 'All independent checks passed.'
