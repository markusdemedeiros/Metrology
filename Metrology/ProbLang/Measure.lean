import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Probability.Kernel.Defs
import Mathlib.Probability.Distributions.Uniform

noncomputable section
open Classical MeasureTheory ProbabilityTheory Measure

theorem measure_pos_of_singleton_pos {α : Type _} [MeasurableSpace α] [MeasurableSingletonClass α]
    [Countable α] (μ : Measure α) (S : Set α) (hS : 0 < μ S) :
    ∃ x ∈ S, 0 < μ {x} := by
  by_contra! h
  have : μ (⋃ x ∈ S, {x}) = 0 :=
    (measure_biUnion_null_iff (Set.to_countable S)).mpr fun x _ =>
      nonpos_iff_eq_zero.mp (h x ‹_›)
  rw [Set.biUnion_of_singleton] at this
  exact absurd this (ne_of_gt hS)

theorem map_singleton_pos {α β : Type _}
    [MeasurableSpace α] [MeasurableSpace β]
    [DiscreteMeasurableSpace α] [DiscreteMeasurableSpace β] [Countable α]
    {f : α → β} {μ : Measure α} {b : β}
    (h : 0 < (μ.map f) {b}) :
    ∃ a, f a = b ∧ 0 < μ {a} := by
  rw [Measure.map_apply .of_discrete .of_discrete] at h
  obtain ⟨a, ha, hpos⟩ := measure_pos_of_singleton_pos μ _ h
  simp [Set.mem_preimage, Set.mem_singleton_iff] at ha
  exact ⟨a, ha, hpos⟩

theorem Measure.bind_map {α β γ : Type} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    [DiscreteMeasurableSpace β] {μ : Measure α} {f : α → β} {g : β → Measure γ}
    (hf : Measurable f) (hg : Measurable g) : g ∘ₘ (μ.map f) = (g ∘ f) ∘ₘ μ := by
  refine ext fun S HS => ?_
  unfold Measure.bind
  rw [map_map hg hf]

abbrev count (f : α → ENNReal) [MeasurableSpace α] := Measure.count.withDensity f

theorem count_singleton [MeasurableSpace T] [MeasurableSingletonClass T]
    (f : T → ENNReal) (t : T) : count f {t} = f t := by simp
