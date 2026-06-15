module

import all Mathlib.Tactic.DeriveCountable
public import Metrology.ProbLang.CoreMeasures

@[expose] public section

/-! # Discreteness lifting for ProbLang measure spaces

If the real-type `rT` (or, for the syntactic types built on top of it, the parameter `α`) is
discrete in the sense of `MeasurableSingletonClass`, then the measure spaces built in
`CoreMeasures` are also discrete.

The proofs all share the same shape: build a "singleton cylinder" that has the given inhabitant
as its sole flatten-image, observe it has measurable leaves (singletons are measurable in a
`MeasurableSingletonClass`), and conclude via `MeasurableSpace.measurableSet_generateFrom`.

The chain is BaseLit → Pat → Exp → Val → EctxItem. -/

noncomputable section ProbLangDiscrete

open Classical MeasureTheory ProbabilityTheory ProbLang

namespace ProbLang

/-! ## BaseLit

The `MeasurableSingletonClass (BaseLit rT)` instance and supporting cylinder
helpers (`singletonCyl`, `singletonCyl_flatten`, `singletonCyl_hasMeasurableLeaves`)
were moved to `CoreMeasures/BaseLit.lean` so that `Recurrences.lean`'s
`liftEq.measurable` can use them directly. -/

/-! ## Pat

`MeasurableSingletonClass (Pat rT)` and supporting cylinder helpers were moved to
`CoreMeasures/Pat.lean` so that `Recurrences.lean`'s `tryMatch.measurable` can use them. -/

/-! ## Exp

`MeasurableSingletonClass (Exp rT)` and supporting cylinder helpers were moved to
`CoreMeasures/Exp.lean` so that every stamped file carries its own singleton section. -/

/-! ## Val

`MeasurableSingletonClass (Val α)` (the comap-singleton instance through
`Val.fst : Val α → Exp α`) was moved to `CoreMeasures/Val.lean`. -/

/-! ## EctxItem

`MeasurableSingletonClass (EctxItem α)` and supporting cylinder helpers were moved to
`CoreMeasures/EctxItem.lean`. -/

/-! ## Option, LocHeap, Tape, State, Cfg

When the underlying real-type `rT` (or, for the parts of the state that store values, the
type parameter `α`) is discrete, the heap- and configuration-level measure spaces are too.

The chain is `Option α → LocHeap (Val α) → State α → Cfg α`, with `Tape` discrete on its
own (no `α` dependence). -/

instance _root_.Option.instMeasurableSingletonClass
    {α : Type _} [MeasurableSpace α] [MeasurableSingletonClass α] :
    MeasurableSingletonClass (Option α) where
  measurableSet_singleton
    | none => MeasurableSet.singleton_none
    | some x => by
        rw [show ({some x} : Set (Option α)) = (some : α → Option α) '' {x} by simp]
        exact MeasurableSet.image_some (MeasurableSet.singleton x)

instance LocHeap.instMeasurableSingletonClass
    {V : Type _} [MeasurableSpace V] [MeasurableSingletonClass V] :
    MeasurableSingletonClass (LocHeap V) where
  measurableSet_singleton m := by
    have hsing : ({m} : Set (LocHeap V))
                  = (fun (n : LocHeap V) (ℓ : Loc) => n[ℓ]?) ⁻¹' {fun ℓ => m[ℓ]?} := by
      ext n
      refine ⟨fun h => h ▸ rfl, fun h => ?_⟩
      apply Std.ExtTreeMap.ext_getElem?
      intro k; exact congrFun h k
    rw [hsing]
    exact (Measurable.of_comap_le le_rfl) (MeasurableSet.singleton _)

instance State.instMeasurableSingletonClass
    {α : Type _} [MeasurableSpace α] [MeasurableSingletonClass α] :
    MeasurableSingletonClass (State α) where
  measurableSet_singleton σ := by
    have hsing : ({σ} : Set (State α))
                  = (fun τ : State α => (τ.heap, τ.tapes)) ⁻¹' {(σ.heap, σ.tapes)} := by
      ext τ
      refine ⟨fun h => h ▸ rfl, fun h => ?_⟩
      obtain ⟨hh, ht⟩ := Prod.mk.inj h
      cases σ; cases τ; congr
    rw [hsing]
    exact (Measurable.of_comap_le le_rfl) (MeasurableSet.singleton _)

instance Cfg.instMeasurableSingletonClass
    {α : Type _} [MeasurableSpace α] [MeasurableSingletonClass α] :
    MeasurableSingletonClass (Cfg α) where
  measurableSet_singleton c := by
    have hsing : ({c} : Set (Cfg α))
                  = (fun c' : Cfg α => (c'.expr, c'.state)) ⁻¹' {(c.expr, c.state)} := by
      ext c'
      refine ⟨fun h => h ▸ rfl, fun h => ?_⟩
      obtain ⟨he, hs⟩ := Prod.mk.inj h
      cases c; cases c'; congr
    rw [hsing]
    exact (Measurable.of_comap_le le_rfl) (MeasurableSet.singleton _)

end ProbLang

/-! ## Sanity check: `DiscreteMeasurableSpace` synthesizes -/

section SynthCheck
variable {rT : Type _} [MeasurableSpace rT] [MeasurableSingletonClass rT] [Countable rT]

example : DiscreteMeasurableSpace (ProbLang.BaseLit rT) := inferInstance
example : DiscreteMeasurableSpace (ProbLang.Pat rT)     := inferInstance
example : DiscreteMeasurableSpace (ProbLang.Exp rT)     := inferInstance
example : DiscreteMeasurableSpace (ProbLang.Val rT)     := inferInstance
example : DiscreteMeasurableSpace (ProbLang.EctxItem rT) := inferInstance
example : DiscreteMeasurableSpace (ProbLang.LocHeap (ProbLang.Val rT)) := inferInstance
example : DiscreteMeasurableSpace (ProbLang.LocHeap ProbLang.Tape) := inferInstance
example : DiscreteMeasurableSpace (ProbLang.State rT) := inferInstance
example : DiscreteMeasurableSpace (ProbLang.Cfg rT)   := inferInstance
end SynthCheck

/-! ## Default `ProbLangℝ` instance on `Int`

Downstream Iris / Approxis / TotalEris layers currently instantiate `rT := Int`. Provide a
single canonical `ProbLangℝ Int` instance here so they all share one definition (avoiding
duplicate-name collisions when one file transitively imports two of them). -/
instance instProbLangℝInt : ProbLang.ProbLangℝ Int where
  instDecidableEq := inferInstance
  -- The integer "unit interval" `[0,1] ∩ ℤ = {0,1}`, sampled uniformly.
  unifUnit := (PMF.uniformOfFinset ({0, 1} : Finset Int) (by decide)).toMeasure
  unifUnit_isProbabilityMeasure := PMF.toMeasure.isProbabilityMeasure _

end ProbLangDiscrete
