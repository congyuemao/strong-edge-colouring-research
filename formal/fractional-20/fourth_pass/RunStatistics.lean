import fourth_pass.SearchStatistics
open Se20Fractional.FourthPass.Packed
#eval (do
  for (d,s) in [(3,3),(4,3),(4,4)] do
    let start ← IO.monoMsNow
    let c := rootStats d s 9
    IO.println s!"d={d} s={s} {repr c} elapsed_ms={(← IO.monoMsNow)-start}" : IO Unit)
