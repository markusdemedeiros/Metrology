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
  unifUnitSupport := Set.Icc (0 : ℝ) 1
  unifUnitSupportMeasurable := by measurability
  -- `Uniform[0,1]` puts no mass outside `[0,1]`: restricting to `[0,1]` measures
  -- `· ∩ [0,1]`, and `[0,1]ᶜ ∩ [0,1] = ∅`.
  unifUnitIsConcentrated := by
    rw [Measure.restrict_apply' measurableSet_Icc, Set.compl_inter_self, measure_empty]
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

end ProbLang
