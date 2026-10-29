#!/bin/bash
# usage: run9.sh R cfg1 cfg2 ...   (one process per (cfg, position))
R=$1; shift
names=("S(u),S(u)" "S(u),S(v)" "S(u),T(a same)" "S(u),T(a other)" "S(u),T(b)" "T(a1),T(a1)" "T(a1),T(a2)" "T(a),T(b)")
for cfg in "$@"; do
  for i in "${!names[@]}"; do
    .venv/Scripts/python.exe exp9_potentials.py 10 $R "$cfg" "${names[$i]}" > "logs9/R${R}_${cfg}_$i.log" 2>&1 &
  done
done
wait
