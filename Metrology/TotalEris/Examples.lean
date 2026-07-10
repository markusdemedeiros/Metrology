module

public import Metrology.TotalEris.Examples.Basic
public import Metrology.TotalEris.Examples.GeometricTotal
public import Metrology.TotalEris.Examples.RandomWalk
public import Metrology.TotalEris.Examples.Samplers

@[expose] public section

/-!
# TotalEris examples

Aggregator for the total-Eris worked examples. Imported from the top-level
`Metrology` library so the examples are part of the default build target and
cannot silently bit-rot (they previously were in no build target). Note:
`Examples.RandomWalk` still contains one intended `sorry`
(`unif_rw_1d_terminate`); see its module docstring.
-/
