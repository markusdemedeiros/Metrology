module

import all Mathlib.Tactic.DeriveCountable
public import Metrology.ProbLang.Measure
public import Metrology.ProbLang.Syntax.Syntax
public import Metrology.ProbLang.CoreMeasures.Exp

meta import Metrology.Meta

@[expose] public section

/-## ProbLang Measure theory -/

-- TODO move this to the semantics file once we have that (leave here until then though,
-- during drop-in step, so we can prove discreteness assuming discrete R type)

-- NOTE Tecnically speaking this is a strict extension: we can instanstiate the reals type
-- with Unit and then I guess also make the ops trivial? Perhaps I need a class with
-- all of this stuff. I do NOT want to have to do the whole thing at once, so I need
-- the option to take the discrete measure over whatever the reals type is

-- NOTE This actually could be a good thing to be honest, since I can also instanstiate
-- reals with floats? Pog?

noncomputable section ProbLangMeasures

open Classical MeasureTheory ProbabilityTheory Measure ProbLang

/-# Measure space on values.

`Val α = (e : Exp α) × IsVal e` is a Sigma type whose witness `IsVal e` is a subsingleton
(see `ProbLang.IsVal.subsingleton`), so the witness carries no information. We give `IsVal`
the discrete (top) σ-algebra, induce the `Sigma` σ-algebra on `Val`, and check that the
constructors and `Exp.toVal?` behave measurably. The σ-algebra ends up being the pullback
through `.fst : Val α → Exp α`. -/

namespace ProbLang

instance instMeasurableSpaceIsVal {α : Type _} {e : Exp α} : MeasurableSpace (IsVal e) := ⊤

instance instMeasurableSpaceVal {α : Type _} [MeasurableSpace α] : MeasurableSpace (Val α) :=
  Sigma.instMeasurableSpace

namespace Val

end Val
end ProbLang
end ProbLangMeasures
