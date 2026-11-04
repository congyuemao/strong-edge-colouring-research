. "$PSScriptRoot\env.ps1"
$ErrorActionPreference = 'Stop'
# Build each target separately so that no two Mathlib-importing processes run together.
foreach ($target in @('Se20Fractional.Definitions','Se20Fractional.DegreeFormula',
    'Se20Fractional.Peeling','Se20Fractional.LocalReed','Se20Fractional.TheoremF','Se20Fractional')) {
  lake --no-cache build $target
  if ($LASTEXITCODE -ne 0) { throw "Lean build failed: $target" }
}
