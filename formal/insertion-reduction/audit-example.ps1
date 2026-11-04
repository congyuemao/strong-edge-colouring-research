# Independent, fully explicit verification of the triangle proof counterexample.
$edges = @(
    @(0,1), @(0,2), @(1,2), @(0,3), @(0,4), @(1,5), @(1,6), @(2,7), @(2,8),
    @(3,9), @(3,10), @(3,11), @(4,12), @(4,13), @(4,14),
    @(5,7), @(5,15), @(5,16), @(6,17), @(6,18), @(6,19)
)
$adjacency = [bool[,]]::new(20,20)
$degrees = [int[]]::new(20)
foreach ($edge in $edges) {
    $u = $edge[0]
    $v = $edge[1]
    if ($u -eq $v -or $adjacency[$u,$v]) { throw 'Not a simple graph.' }
    $adjacency[$u,$v] = $true
    $adjacency[$v,$u] = $true
    $degrees[$u]++
    $degrees[$v]++
}
function Test-Conflict([int]$i, [int]$j) {
    if ($i -eq $j) { return $false }
    foreach ($u in $edges[$i]) {
        foreach ($v in $edges[$j]) {
            if ($u -eq $v -or $adjacency[$u,$v]) { return $true }
        }
    }
    return $false
}
$conflictsE = @(0..20 | Where-Object { Test-Conflict 0 $_ })
$conflictsUWInside = @($conflictsE | Where-Object { Test-Conflict 1 $_ })
$Z = @(0..20 | Where-Object {
    (($edges[$_] -contains 7) -or ($edges[$_] -contains 8)) -and
    -not ($edges[$_] -contains 2)
})
$colours = @{}
foreach ($i in 1..20) { $colours[$i] = $i - 1 }
foreach ($i in 1..20) {
    foreach ($j in 1..20) {
        if ((Test-Conflict $i $j) -and $colours[$i] -eq $colours[$j]) {
            throw 'Partial colouring is not proper.'
        }
    }
}
if (($degrees | Measure-Object -Maximum).Maximum -ne 4) { throw 'Wrong maximum degree.' }
if ($conflictsE.Count -ne 20) { throw 'The hole is not saturated.' }
if ($conflictsUWInside.Count -ne 14) { throw 'Unexpected uw count.' }
[ordered]@{
    Vertices = '0..19'
    Edges = @($edges | ForEach-Object { "$($_[0])-$($_[1])" })
    Degrees = $degrees
    UncolouredEdge = '0-1'
    ColourRule = 'Edge at list index i (1..20) has colour i-1.'
    ConflictsOfHole = $conflictsE.Count
    ConflictsOfUWInsideHoleNeighbourhood = $conflictsUWInside.Count
    Z = @($Z | ForEach-Object { "$($edges[$_][0])-$($edges[$_][1])" })
    VerifiedProper = $true
} | ConvertTo-Json -Depth 4
