module

public import Metrology.LiveEris.Credits
public import Metrology.LiveEris.Glm
public import Metrology.LiveEris.GS
public import Metrology.LiveEris.Weakestpre
public import Metrology.LiveEris.Lifting
public import Metrology.LiveEris.PrimitiveLaws
public import Metrology.LiveEris.CreditRules
public import Metrology.LiveEris.Tactics
public import Metrology.LiveEris.Examples
public import Metrology.LiveEris.Adequacy

@[expose] public section

/-!
# LiveEris

A probabilistic separation logic for programs that may run forever. Error credits `↯` bound the
probability of failure; divergence credits `↻` bound the probability of running forever without
progress. The weakest precondition is a guarded fixpoint around a least fixpoint, whose `▷`
checkpoints are free on progress steps and excused once the total budget reaches 1.
-/
