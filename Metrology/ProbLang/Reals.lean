module

public import Metrology.ProbLang.Syntax.Syntax
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# The continuous `ProbLangℝ ℝ` instance

Instantiates the ProbLang real-type parameter with the genuine reals `ℝ`, giving
ProbLang a *continuous* semantics. The unit-interval sampling measure
`unifUnit` is the uniform distribution on `[0,1]` (`volume` restricted to
`Set.Icc 0 1`, a probability measure since `volume (Icc 0 1) = 1`).

With this instance the continuous error-credit rule `TotalEris.twp_urand_exp`
(and `Exp.urand` generally) specialises to `rT := ℝ`. The instance is
`noncomputable` because equality on `ℝ` is only classically decidable. -/

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

end ProbLang
