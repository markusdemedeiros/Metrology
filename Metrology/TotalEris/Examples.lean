module

public import Metrology.TotalEris.Examples.Basic
public import Metrology.TotalEris.Examples.GeometricTotal
public import Metrology.TotalEris.Examples.Irrational
public import Metrology.TotalEris.Examples.RandomWalk
public import Metrology.TotalEris.Examples.Samplers
public import Metrology.TotalEris.Examples.SteppingDisplayTest
public import Metrology.TotalEris.Examples.WpTacticsTest

@[expose] public section

/-!
# TotalEris examples

Aggregator for the total-Eris worked examples. Imported from the top-level
`Metrology` library so every example is part of the default build target and
cannot silently bit-rot. This includes the two regression suites:
`Examples.SteppingDisplayTest` pins the rendered form of stepped goals via
`#guard_msgs`, and `Examples.WpTacticsTest` exercises the `twp_*` tactics.

`Examples.RandomWalk` contains one intended `sorry` (`unifRw1d_terminate`);
see its module docstring.
-/
