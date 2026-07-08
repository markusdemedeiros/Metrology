module

public import Metrology.ProbLang.Syntax.Syntax
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Measure.Restrict

/-! # The continuous `ProbLangℝ ℝ` instance -/
namespace ProbLang

open MeasureTheory


/-- ProbLang's real parameter instantiated with `ℝ`, the continuous semantics.
The measurable structure is the Borel σ-algebra; `unifUnit` is `Uniform[0,1]`. -/
public noncomputable instance instProbLangℝReal : ProbLangℝ ℝ where
  -- `BEq`/`LawfulBEq` via classical decidable equality on `ℝ`.
  beq a b := decide (a = b)
  eq_of_beq h := of_decide_eq_true h
  rfl := by exact decide_eq_true (Eq.refl _)
  -- `MeasurableEq ℝ`: the diagonal of `ℝ × ℝ` is closed (ℝ is `T2`), hence measurable.
  measurableSet_diagonal := isClosed_diagonal.measurableSet
  instDecidableEq := inferInstance
  -- The unit-interval sampling measure: `Uniform[0,1] = volume ∣ [0,1]`.
  unifUnit := volume.restrict (Set.Icc (0 : ℝ) 1)
  unifUnit_isProbabilityMeasure := by
    constructor
    rw [Measure.restrict_apply_univ, Real.volume_Icc]
    simp
  -- Concentration set: the *open* interval `(0,1)`. `unifUnitSupport` need only be a
  -- measurable set on whose complement the measure vanishes; the two endpoints carry no
  -- `volume`, so `(0,1)` qualifies and gives callers the strict range `0 < r < 1`.
  unifUnitSupport := Set.Ioo (0 : ℝ) 1
  unifUnitSupportMeasurable := measurableSet_Ioo
  -- `Uniform[0,1]` puts no mass outside `(0,1)`: restricting to `[0,1]` measures
  -- `· ∩ [0,1]`, and `(0,1)ᶜ ∩ [0,1] ⊆ {0, 1}`, a null (countable) set.
  unifUnitIsConcentrated := by
    rw [Measure.restrict_apply' measurableSet_Icc]
    refine measure_mono_null (t := ({0, 1} : Set ℝ)) ?_ ?_
    · rintro x ⟨hx, h0, h1⟩
      simp only [Set.mem_compl_iff, Set.mem_Ioo, not_and, not_lt] at hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      rcases eq_or_lt_of_le h0 with h | h
      · exact Or.inl h.symm
      · exact Or.inr (le_antisymm h1 (hx h))
    · exact ((Set.finite_singleton (1 : ℝ)).insert 0).countable.measure_zero volume
  -- Real comparison is classical decidable `<`/`≤`; measurable since `{p | p.1 < p.2}`
  -- and `{p | p.1 ≤ p.2}` are Borel-measurable in `ℝ × ℝ`.
  realLt a b := decide (a < b)
  realLe a b := decide (a ≤ b)
  measurable_realLt := by
    apply measurable_to_bool
    have h : (Function.uncurry (fun a b : ℝ => decide (a < b)) ⁻¹' {true})
        = {p : ℝ × ℝ | p.1 < p.2} := by
      ext p; simp [Function.uncurry, decide_eq_true_eq]
    rw [h]; exact measurableSet_lt measurable_fst measurable_snd
  measurable_realLe := by
    apply measurable_to_bool
    have h : (Function.uncurry (fun a b : ℝ => decide (a ≤ b)) ⁻¹' {true})
        = {p : ℝ × ℝ | p.1 ≤ p.2} := by
      ext p; simp [Function.uncurry, decide_eq_true_eq]
    rw [h]; exact measurableSet_le measurable_fst measurable_snd

/-- For the `ℝ` instance, `unifUnitSupport` is the open interval `(0,1)`, so membership
unpacks to the strict range `0 < r < 1`. Used by `urand` samplers to read off sample
bounds from the strengthened `twp_urand_exp'` continuation. -/
public theorem mem_unifUnitSupport_real {r : ℝ} :
    r ∈ ProbLangℝ.unifUnitSupport (T := ℝ) ↔ 0 < r ∧ r < 1 := Set.mem_Ioo

end ProbLang
