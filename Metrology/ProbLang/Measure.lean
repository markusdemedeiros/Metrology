import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Probability.Kernel.Defs
import Mathlib.Probability.Distributions.Uniform

noncomputable section
open Classical MeasureTheory ProbabilityTheory Measure

-- FIXME: Is this really necessary? This has got to be proven somewhere...
theorem measure_pos_of_singleton_pos {α : Type _} [MeasurableSpace α] [MeasurableSingletonClass α]
    [Countable α] (μ : Measure α) (S : Set α) (hS : 0 < μ S) :
    ∃ x ∈ S, 0 < μ {x} := by
  by_contra!
  have HSingle : S = ⋃₀ { {x} | x ∈ S } := by
    refine Set.ext_iff.mpr (fun x => ⟨?_, ?_⟩)
    · intro _
      refine Set.mem_sUnion.mpr ?_
      exists {x}
      exact ⟨by simpa, Set.mem_singleton x⟩
    · intro H
      have ⟨t, Ht1, Ht2⟩ := Set.mem_sUnion.mp H
      obtain ⟨x', Hx'1, Hx'2⟩ := Ht1
      simp only [← Hx'2, Set.mem_singleton_iff] at Ht2
      exact Ht2 ▸ Hx'1
  suffices Hμ : μ S = 0 by simp [Hμ] at hS
  rw [HSingle]
  rw [MeasureTheory.measure_sUnion ?GCount ?GDisj ?GMeas]
  case GCount =>
    let f_forget : {(x : Set α) | ∃ x_1 ∈ S, {x_1} = x} → {(x : Set α) | ∃ x_1, {x_1} = x} :=
      fun ⟨e, He⟩ => ⟨e, by simp at He ⊢; obtain ⟨x, _, Hx⟩ := He; exists x⟩
    have Hf_forget : Function.Injective f_forget := by
      intro _ _
      simp [f_forget]
      exact Subtype.ext
    let f_ofSingle : {(x : Set α) | ∃ x_1, {x_1} = x} → α :=
      fun ⟨_, He⟩ => (Set.mem_setOf_eq ▸ He).choose
    have Hf_ofSingle : Function.Injective f_ofSingle := by rintro ⟨S1, H1⟩ ⟨S2, H2⟩; grind
    let f_count : α → Nat := Countable.exists_injective_nat'.choose
    have Hf_count : Function.Injective f_count := choose_spec _
    exists (fun S => f_count <| f_ofSingle <| f_forget S)
    intros S1 S2 Heq
    simp at Heq
    exact SetCoe.ext (congrArg Subtype.val (Hf_forget (Hf_ofSingle (Hf_count Heq))))
  case GDisj =>
    intro S1 HS1 S2 HS2 Hne
    simp only [Set.mem_setOf_eq] at HS1 HS2
    obtain ⟨_, _, rfl⟩ := HS1
    obtain ⟨_, _, rfl⟩ := HS2
    exact Set.disjoint_singleton.mpr fun a ↦ Hne (congrArg singleton a)
  case GMeas => exact fun s a ↦ DiscreteMeasurableSpace.forall_measurableSet s
  simp
  exact fun a Ha => nonpos_iff_eq_zero.mp (this a Ha)
