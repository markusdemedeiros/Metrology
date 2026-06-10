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

/-- The σ-algebra on `Val α` is the **subtype σ-algebra** pulled back through
`Val.fst : Val α → Exp α`. Equivalently: a set `T ⊆ Val α` is measurable iff
`T = Val.fst ⁻¹' U` for some measurable `U ⊆ Exp α`.

We do NOT use `Sigma.instMeasurableSpace` here because, with `IsVal e := ⊤`,
that σ-algebra collapses to the discrete (`⊤`) σ-algebra on `Val α` (every set
becomes measurable), which would break `Exp.toVal?.measurable`: arbitrary sets
in `Val α` would have arbitrary (non-measurable) preimages in `Exp α`. The
comap σ-alg via `Val.fst` is the strictly finer "morally correct" choice and
keeps `Val α` faithfully embedded in `Exp α` as a measurable space.

For this instance to actually be the one picked by TC resolution (rather than
`Sigma.instMeasurableSpace`), `Val α` is defined as a `structure` (not a `def`
that reduces to `Sigma`). See `Metrology/ProbLang/Syntax/Syntax.lean`. -/
instance (priority := 10000) instMeasurableSpaceVal {α : Type _} [MeasurableSpace α] :
    MeasurableSpace (Val α) :=
  MeasurableSpace.comap Val.fst inferInstance

namespace Val

/-! ### Constructor / projection measurability. -/

/-- The first projection `Val α → Exp α` is measurable.
Immediate from the definition of the comap σ-algebra. -/
@[fun_prop]
theorem fst.measurable {α : Type _} [MeasurableSpace α] :
    Measurable (Val.fst : Val α → Exp α) :=
  fun _ hS => MeasurableSpace.measurableSet_comap.mpr ⟨_, hS, rfl⟩

/-- `Exp.ofVal = Val.fst` (definitional). Tagged for `fun_prop`. -/
@[fun_prop]
theorem _root_.ProbLang.Exp.ofVal.measurable {α : Type _} [MeasurableSpace α] :
    Measurable (Exp.ofVal : Val α → Exp α) :=
  Val.fst.measurable

/-- The dependent constructor `Val.mk e w : Val α` (from `e : Exp α` and
`w : IsVal e`) is measurable in the Sigma-typed input. Reduces to measurability
of `Sigma.fst : (Σ e, IsVal e) → Exp α` in the standard Sigma σ-alg on the source. -/
@[fun_prop]
theorem mk.measurable {α : Type _} [MeasurableSpace α] :
    Measurable (fun (p : Σ e : Exp α, IsVal e) => (Val.mk p.1 p.2 : Val α)) := by
  intro T hT
  obtain ⟨U, hU, hUeq⟩ : ∃ U : Set (Exp α), MeasurableSet U ∧ Val.fst ⁻¹' U = T :=
    MeasurableSpace.measurableSet_comap.mp hT
  subst hUeq
  apply MeasurableSpace.measurableSet_iInf.mpr
  intro e
  show MeasurableSet[⊤] _
  trivial

/-! ### Singleton-class for `Val α` (lifted from `MeasurableSingletonClass α`).

Was previously in `Discrete.lean`; moved here so every stamped file carries its own
singleton section. `Val` has no cylinder construction — its σ-algebra is the comap of
`Val.fst : Val α → Exp α`, and a singleton `{v}` equals `Val.fst ⁻¹' {v.fst}` because
`Val.fst` is injective (the witness field is determined by `IsVal.subsingleton`), so
singletons are measurable whenever singletons in `Exp α` are. This is the comap-singleton
prerequisite pattern (cf. `Exp.instMeasurableSingletonClass`). -/
instance instMeasurableSingletonClass
    {α : Type _} [MeasurableSpace α] [MeasurableSingletonClass α] :
    MeasurableSingletonClass (Val α) where
  measurableSet_singleton v := by
    -- `{v} = Val.fst ⁻¹' {v.fst}` since `Val.fst` is injective.
    have heq : ({v} : Set (Val α)) = Val.fst ⁻¹' {v.fst} := by
      ext v'
      simp only [Set.mem_singleton_iff, Set.mem_preimage]
      exact ⟨fun h => by rw [h], fun h => Val.ext h⟩
    rw [heq]
    exact Val.fst.measurable (MeasurableSet.singleton v.fst)

end Val
end ProbLang
end ProbLangMeasures
