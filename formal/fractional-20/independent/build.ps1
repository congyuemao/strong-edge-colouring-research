. "$PSScriptRoot\env.ps1"
$ErrorActionPreference = 'Stop'
$compiler = 'E:\Qt\Tools\mingw1310_64\bin\g++.exe'
foreach ($name in @('encode','check_model','check_lrat')) {
  & $compiler -std=c++17 -O2 -static "independent\$name.cpp" -o "independent\$name.exe"
  if ($LASTEXITCODE -ne 0) { throw "Compilation failed: $name" }
}
