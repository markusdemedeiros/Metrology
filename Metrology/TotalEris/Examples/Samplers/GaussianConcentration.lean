module

public import Metrology.TotalEris.Examples.Samplers.GaussianAdequacy
public import Mathlib.Probability.Moments.SubGaussian

@[expose] public section

/-! # Concentration bounds for the standard Gaussian sampler

`Gauss` returns a real distributed as `gaussianReal 0 1` (`Gaussian.lean`). This
file bounds its tail three ways, each stated at the credit level — the composable
artifact, where a client pays error credit and may then assume its sample is
bounded — and at the probability level over `limExec`.

For `t > 0`, writing `Z` for the sampled real:

| bound | `Pr[|Z| ≥ t]` | at `t = 3` |
| --- | --- | --- |
| Chebyshev  | `1 / t²`                | `0.111` |
| Chernoff   | `2·exp(-t²/2)`          | `0.022` |
| Mills      | `√(2/π)·exp(-t²/2) / t` | `0.0030` |

(the true tail at `t = 3` is `0.0027`). Mills dominates for `t ≳ 0.8`; the other
two are kept because they are cheaper to state and Chernoff carries the
sub-Gaussian API with it.

* Chebyshev: `gaussianReal_abs_ge_le`, `twp_Gauss_tail`, `gauss_std_tail_prob`.
  Markov applied to `y²`, fed by `stdSecondMoment_le_one`.
* Chernoff: `gaussianReal_abs_ge_le_chernoff`, `twp_Gauss_tail_chernoff`,
  `gauss_std_tail_prob_chernoff`, from `hasSubgaussianMGF_id_gaussianReal` — which
  also hands over `HasSubgaussianMGF.const_mul` and the Hoeffding /
  independent-sum lemmas for composition over many samples.
* Mills: `gaussianReal_abs_ge_le_mills`, `twp_Gauss_tail_mills`,
  `gauss_std_tail_prob_mills`. Dominating the density by `(y/t)·exp(-y²/2)` on
  `[t,∞)` makes the tail integral elementary.

The credit-level lemmas all instantiate `twp_Gauss_tail_of_le`, which is
parameterised by any bound on the tail mass; a new bound needs only its
`stdTailErr_credit_le_*` lemma.

Every bound is informative only where it falls below `1`; elsewhere it is
vacuously true, since `↯ε` with `1 ≤ ε` is already `False`.

## Half-normal infrastructure

The `G2` sampler's own law `halfNormal` (the half-normal) appears here only as
scaffolding for the results above — no tail bound is stated for it:

* `halfNormalSecondMoment_le_one` — `∫⁻ y², dhalfNormal ≤ 1`, by integration by
  parts on each `[0, n]` with the boundary term dropped. `stdSecondMoment_le_one`
  transports it across the symmetrisation.
* `halfNormal_Ici_le_mills` — the Mills estimate, proved on the half-line.
* `gaussianReal_abs_ge_eq_halfNormal_Ici` — the two-sided Gaussian tail *equals*
  the one-sided half-normal tail, which is what carries the previous item over.
-/
open Iris Iris.BI Iris.ProofMode ProbLang ProbLang.TotalEris ProbLang.TotalEris.Examples
  ProbLang.TotalEris.ErisWpGS
open scoped AppGS ENNReal NNReal

namespace ProbLang
namespace TotalEris
namespace Examples

noncomputable section

section secondMoment

/-- `z ↦ exp (-z² / 2)` has derivative `-(y * exp (-y² / 2))`: the antiderivative
behind the integration by parts below. -/
theorem hasDerivAt_exp_neg_sq_half (y : ℝ) :
    HasDerivAt (fun z : ℝ => Real.exp (-z ^ 2 / 2)) (-(y * Real.exp (-y ^ 2 / 2))) y := by
  have hsq : HasDerivAt (fun z : ℝ => -z ^ 2 / 2) (-y) y :=
    ((hasDerivAt_pow 2 y).neg.div_const 2).congr_deriv (by ring)
  exact hsq.exp.congr_deriv (by ring)

open MeasureTheory in
/-- Integration by parts for the second-moment integrand on `[0, b]`. -/
theorem integral_sq_exp_eq (b : ℝ) :
    (∫ y in (0 : ℝ)..b, y ^ 2 * Real.exp (-y ^ 2 / 2))
      = (∫ y in (0 : ℝ)..b, Real.exp (-y ^ 2 / 2)) - b * Real.exp (-b ^ 2 / 2) := by
  have hIBP := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (u := fun y : ℝ => y) (u' := fun _ : ℝ => (1 : ℝ))
    (v := fun y : ℝ => Real.exp (-y ^ 2 / 2))
    (v' := fun y : ℝ => -(y * Real.exp (-y ^ 2 / 2))) (a := 0) (b := b)
    (fun _ _ => hasDerivAt_id' ..) (fun x _ => hasDerivAt_exp_neg_sq_half x)
    intervalIntegrable_const (Continuous.intervalIntegrable (by fun_prop) _ _)
  have hlhs : (∫ y in (0 : ℝ)..b, y * -(y * Real.exp (-y ^ 2 / 2)))
      = -∫ y in (0 : ℝ)..b, y ^ 2 * Real.exp (-y ^ 2 / 2) := by
    rw [← intervalIntegral.integral_neg]
    exact intervalIntegral.integral_congr (fun y _ => by ring)
  rw [hlhs] at hIBP
  simp only [one_mul, zero_mul, sub_zero] at hIBP
  linarith [hIBP]

open MeasureTheory in
/-- On every `[0, b]` the second-moment integrand integrates to at most the
density: the integration-by-parts boundary term only subtracts. -/
theorem integral_sq_exp_le {b : ℝ} (hb : 0 ≤ b) :
    (∫ y in (0 : ℝ)..b, y ^ 2 * Real.exp (-y ^ 2 / 2))
      ≤ ∫ y in (0 : ℝ)..b, Real.exp (-y ^ 2 / 2) := by
  rw [integral_sq_exp_eq]
  have hbd : 0 ≤ b * Real.exp (-b ^ 2 / 2) := mul_nonneg hb (Real.exp_pos _).le
  linarith

open MeasureTheory in
/-- Partial integrals of the density are bounded by its total mass `Norm2`. -/
theorem integral_exp_le_Norm2 (n : ℕ) :
    (∫ y in (0 : ℝ)..(n : ℝ), Real.exp (-y ^ 2 / 2)) ≤ Norm2 := by
  have hsplit : ∑ k ∈ Finset.range n, (∫ x in (0 : ℝ)..1, Real.exp (-(x + (k : ℝ)) ^ 2 / 2))
      = ∫ y in (0 : ℝ)..(n : ℝ), Real.exp (-y ^ 2 / 2) := by
    have h := intervalIntegral.sum_integral_adjacent_intervals
      (f := fun y : ℝ => Real.exp (-y ^ 2 / 2)) (μ := volume) (a := fun k : ℕ => (k : ℝ)) (n := n)
      (fun k _ => Continuous.intervalIntegrable (by fun_prop) _ _)
    simp only [Nat.cast_zero, Nat.cast_add, Nat.cast_one] at h
    rw [← h]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    have hshift := intervalIntegral.integral_comp_add_right (a := (0 : ℝ)) (b := 1)
      (f := fun y : ℝ => Real.exp (-y ^ 2 / 2)) (k : ℝ)
    simpa [add_comm] using hshift
  rw [← hsplit, Norm2_eq_tsum]
  exact Norm2_summand_summable.sum_le_tsum _
    (fun k _ => intervalIntegral.integral_nonneg (by norm_num)
      (fun x _ => (Real.exp_pos _).le))

/-- Unit-interval pieces of the half-normal second moment: `Moment2Summand k` is
the mass `∫ y² exp(-y²/2)` over `[k, k+1]`, written in the shifted coordinates
`y = x + k` used by `G2pdf`. -/
def Moment2Summand (k : ℕ) : ℝ :=
  ∫ x in (0 : ℝ)..1, (x + (k : ℝ)) ^ 2 * Real.exp (-(x + (k : ℝ)) ^ 2 / 2)

theorem Moment2Summand_nonneg (k : ℕ) : 0 ≤ Moment2Summand k :=
  intervalIntegral.integral_nonneg (by norm_num) (fun x _ => by positivity)

open MeasureTheory in
theorem Moment2Summand_eq_interval (k : ℕ) :
    Moment2Summand k = ∫ y in (k : ℝ)..((k : ℝ) + 1), y ^ 2 * Real.exp (-y ^ 2 / 2) := by
  have hshift := intervalIntegral.integral_comp_add_right (a := (0 : ℝ)) (b := 1)
    (f := fun y : ℝ => y ^ 2 * Real.exp (-y ^ 2 / 2)) (k : ℝ)
  simpa [Moment2Summand, add_comm] using hshift

open MeasureTheory in
theorem Moment2Summand_sum_range_le (n : ℕ) : ∑ k ∈ Finset.range n, Moment2Summand k ≤ Norm2 := by
  have hsplit : ∑ k ∈ Finset.range n, Moment2Summand k
      = ∫ y in (0 : ℝ)..(n : ℝ), y ^ 2 * Real.exp (-y ^ 2 / 2) := by
    have h := intervalIntegral.sum_integral_adjacent_intervals
      (f := fun y : ℝ => y ^ 2 * Real.exp (-y ^ 2 / 2)) (μ := volume)
      (a := fun k : ℕ => (k : ℝ)) (n := n)
      (fun k _ => Continuous.intervalIntegrable (by fun_prop) _ _)
    simp only [Nat.cast_zero, Nat.cast_add, Nat.cast_one] at h
    rw [← h]
    exact Finset.sum_congr rfl (fun k _ => Moment2Summand_eq_interval k)
  rw [hsplit]
  exact (integral_sq_exp_le (Nat.cast_nonneg n)).trans (integral_exp_le_Norm2 n)

theorem Moment2Summand_summable : Summable Moment2Summand :=
  summable_of_sum_range_le Moment2Summand_nonneg Moment2Summand_sum_range_le

theorem Moment2Summand_tsum_le_Norm2 : ∑' k : ℕ, Moment2Summand k ≤ Norm2 :=
  Real.tsum_le_of_sum_range_le Moment2Summand_nonneg Moment2Summand_sum_range_le

open MeasureTheory in
/-- The `k`-th piece of the second moment, as `G2`'s credit functional sees it. -/
theorem gauss_moment2_lintegral (k : ℕ) :
    ∫⁻ x, G2pdf k x * ENNReal.ofReal ((x + (k : ℝ)) ^ 2) ∂(ProbLangℝ.unifUnit (T := ℝ))
      = ENNReal.ofReal (Moment2Summand k / Norm2) := by
  show ∫⁻ x in Set.Icc (0 : ℝ) 1, G2pdf k x * ENNReal.ofReal ((x + (k : ℝ)) ^ 2) ∂volume = _
  have hpt : ∀ x : ℝ, G2pdf k x * ENNReal.ofReal ((x + (k : ℝ)) ^ 2)
      = ENNReal.ofReal ((x + (k : ℝ)) ^ 2 * Real.exp (-(x + (k : ℝ)) ^ 2 / 2) / Norm2) := by
    intro x
    rw [G2pdf, ← ENNReal.ofReal_mul (div_nonneg (Real.exp_pos _).le Norm2_pos.le)]
    congr 1
    ring
  rw [lintegral_congr hpt,
    lintegral_ofReal_Icc (by norm_num) (by fun_prop)
      (fun r _ => div_nonneg (by positivity) Norm2_pos.le),
    intervalIntegral.integral_div]
  rfl

open MeasureTheory in
/-- Second moment of the half-normal law realised by `G2`. -/
def halfNormalSecondMoment : ℝ≥0∞ := ∫⁻ y, ENNReal.ofReal (y ^ 2) ∂halfNormal

open MeasureTheory in
/-- **Second moment bound**: `E[Y²] ≤ 1` for `Y` the value sampled by `G2`.
(The exact value is `1`; the inequality is all the tail bound needs.) -/
theorem halfNormalSecondMoment_le_one : halfNormalSecondMoment ≤ 1 := by
  rw [halfNormalSecondMoment, halfNormal_credit_eq (fun y => ENNReal.ofReal (y ^ 2)) (by fun_prop),
    G2CreditV, tsum_congr gauss_moment2_lintegral,
    ← ENNReal.ofReal_tsum_of_nonneg
      (fun k => div_nonneg (Moment2Summand_nonneg k) Norm2_pos.le)
      (Moment2Summand_summable.div_const _),
    tsum_div_const, ← ENNReal.ofReal_one]
  exact ENNReal.ofReal_le_ofReal ((div_le_one Norm2_pos).mpr Moment2Summand_tsum_le_Norm2)

end secondMoment

section stdGaussian

/-! ## The two-sided bound for the standard Gaussian

`Gauss` symmetrises `G2`, so its second moment is the same, and Chebyshev now
bounds the *two-sided* tail `|Z| ≥ t`. -/

open MeasureTheory ProbabilityTheory in
/-- Symmetrising does not change the second moment: `E[Z²] ≤ 1` for `Z ~ N(0,1)`
(the exact value is `1`, the variance of the standard Gaussian). -/
theorem stdSecondMoment_le_one :
    ∫⁻ y, ENNReal.ofReal (y ^ 2) ∂(gaussianReal 0 1) ≤ 1 := by
  have hsq : Measurable fun y : ℝ => ENNReal.ofReal (y ^ 2) := by fun_prop
  have hneg : ∫⁻ y, ENNReal.ofReal ((-y) ^ 2) ∂halfNormal
      = ∫⁻ y, ENNReal.ofReal (y ^ 2) ∂halfNormal :=
    lintegral_congr_ae (Filter.Eventually.of_forall fun y => by
      show ENNReal.ofReal ((-y) ^ 2) = ENNReal.ofReal (y ^ 2)
      rw [neg_sq])
  rw [gaussianReal_lintegral_split (fun y => ENNReal.ofReal (y ^ 2)) hsq, hneg,
    ← add_mul, ← ENNReal.ofReal_add (by norm_num) (by norm_num)]
  norm_num
  exact halfNormalSecondMoment_le_one

theorem measurableSet_abs_ge (t : ℝ) : MeasurableSet {y : ℝ | t ≤ |y|} :=
  measurable_abs measurableSet_Ici

open MeasureTheory ProbabilityTheory in
/-- **Chebyshev's inequality for the standard Gaussian**: `Pr[|Z| ≥ t] ≤ 1/t²`. -/
theorem gaussianReal_abs_ge_le {t : ℝ} (ht : 0 < t) :
    (gaussianReal 0 1) {y : ℝ | t ≤ |y|} ≤ ENNReal.ofReal (1 / t ^ 2) := by
  have hsub : {y : ℝ | t ≤ |y|}
      ⊆ {y : ℝ | ENNReal.ofReal (t ^ 2) ≤ ENNReal.ofReal (y ^ 2)} := by
    intro y hy
    have hy' : t ≤ |y| := hy
    refine ENNReal.ofReal_le_ofReal ?_
    nlinarith [sq_abs y, abs_nonneg y]
  have ht2 : ENNReal.ofReal (t ^ 2) ≠ 0 := (ENNReal.ofReal_pos.mpr (by positivity)).ne'
  calc (gaussianReal 0 1) {y : ℝ | t ≤ |y|}
      ≤ (gaussianReal 0 1) {y : ℝ | ENNReal.ofReal (t ^ 2) ≤ ENNReal.ofReal (y ^ 2)} :=
        measure_mono hsub
    _ ≤ (∫⁻ y, ENNReal.ofReal (y ^ 2) ∂(gaussianReal 0 1)) / ENNReal.ofReal (t ^ 2) :=
        meas_ge_le_lintegral_div (by fun_prop) ht2 ENNReal.ofReal_ne_top
    _ ≤ 1 / ENNReal.ofReal (t ^ 2) := ENNReal.div_le_div_right stdSecondMoment_le_one _
    _ = ENNReal.ofReal (1 / t ^ 2) := by
        rw [ENNReal.ofReal_div_of_pos (by positivity), ENNReal.ofReal_one]

/-- The two-sided tail indicator fed to `twp_Gauss`. -/
def stdTailErr (t : ℝ) : ℝ → ℝ≥0∞ := {y : ℝ | t ≤ |y|}.indicator (fun _ => 1)

theorem measurable_stdTailErr (t : ℝ) : Measurable (stdTailErr t) :=
  measurable_const.indicator (measurableSet_abs_ge t)

theorem stdTailErr_of_le {t y : ℝ} (h : t ≤ |y|) : stdTailErr t y = 1 :=
  Set.indicator_of_mem (show y ∈ {y : ℝ | t ≤ |y|} from h) _

open MeasureTheory ProbabilityTheory in
theorem stdTailErr_credit_le {t : ℝ} (ht : 0 < t) :
    GaussCreditV (stdTailErr t) ≤ ENNReal.ofReal (1 / t ^ 2) := by
  have h := gauss_credit_eq_gaussianReal (stdTailErr t) (measurable_stdTailErr t)
  rw [← h, stdTailErr, lintegral_indicator_const (measurableSet_abs_ge t), one_mul]
  exact gaussianReal_abs_ge_le ht

variable {hlc : HasLC} {GF : BundledGFunctors.{0,0,0}} [ErisGS ℝ hlc GF]

/-- **Concentration for `Gauss`, credit level**, parameterised by any bound on
the two-sided tail mass. -/
theorem twp_Gauss_tail_of_le (E : CoPset) {t : ℝ} {ε : ℝ≥0∞}
    (hb : GaussCreditV (stdTailErr t) ≤ ε) :
    ⊢@{IProp GF} ↯ ε -∗
      tglWp E pl(&Gauss #.unit)
        (fun v : Val ℝ => iprop(⌜∃ y : ℝ, v.1 = .lit (.real y) ∧ |y| < t⌝)) := by
  iintro Hε
  iapply (tglWp_wand (Φ := fun v : Val ℝ => iprop(∃ y : ℝ,
    ⌜v.1 = .lit (.real y)⌝ ∗ ↯ (stdTailErr t y))))
  isplitl [Hε]
  · iapply (twp_Gauss E (stdTailErr t) (measurable_stdTailErr t))
    iapply (ErrorCredit.weaken hb)
    iexact Hε
  iintro %v ⟨%y, %hy, Hcr⟩
  by_cases hlt : |y| < t
  · ipureintro
    exact ⟨y, hy, hlt⟩
  · iexfalso
    iapply ErrorCredit.contradict $$ Hcr
    rw [stdTailErr_of_le (not_lt.mp hlt)]

/-- Chebyshev instance: `↯(1/t²)` buys `|y| < t`. -/
theorem twp_Gauss_tail (E : CoPset) {t : ℝ} (ht : 0 < t) :
    ⊢@{IProp GF} ↯ (ENNReal.ofReal (1 / t ^ 2)) -∗
      tglWp E pl(&Gauss #.unit)
        (fun v : Val ℝ => iprop(⌜∃ y : ℝ, v.1 = .lit (.real y) ∧ |y| < t⌝)) :=
  twp_Gauss_tail_of_le E (stdTailErr_credit_le ht)

end stdGaussian

section stdAdequacy

variable {GF : BundledGFunctors.{0,0,0}}

open MeasureTheory ProbabilityTheory in
/-- **Concentration for `Gauss`, probability level**: the sampled real exceeds
`t` in absolute value with probability at most `1 / t²`. -/
theorem gauss_std_tail_prob [AppPreGS ℝ GF] [ECPreGS GF] [InvGpreS GF] {t : ℝ} (ht : 0 < t)
    (σ : State ℝ) :
    (limExec ⟨pl(&Gauss #.unit), σ⟩)
        ((fun ρ : Cfg ℝ => realOfExp ρ.expr) ⁻¹' {y : ℝ | t ≤ |y|})
      ≤ ENNReal.ofReal (1 / t ^ 2) := by
  have hmg : Measurable (fun ρ : Cfg ℝ => realOfExp ρ.expr) :=
    measurable_realOfExp.comp Cfg.measurable_expr
  rw [← Measure.map_apply hmg (measurableSet_abs_ge t), gauss_std_distributed (GF := GF) σ]
  exact gaussianReal_abs_ge_le ht

end stdAdequacy

section subGaussian

/-! ## Sub-Gaussian bridge

`gaussianReal 0 1` is sub-Gaussian with parameter `1`. This is an API bridge
rather than a sharper tail: it yields the Chernoff bound, sub-Gaussianity of
scaled samples (`HasSubgaussianMGF.const_mul`), and the Hoeffding /
independent-sum lemmas that a composition argument over many samples needs. -/

open MeasureTheory ProbabilityTheory in
/-- The standard Gaussian has a sub-Gaussian moment-generating function with
parameter `1`; the bound holds with equality. -/
theorem hasSubgaussianMGF_id_gaussianReal :
    HasSubgaussianMGF id 1 (gaussianReal 0 1) where
  integrable_exp_mul t := integrable_exp_mul_gaussianReal t
  mgf_le t := by rw [mgf_id_gaussianReal]; simp

/- Moment facts (`MemLp`, `Integrable`, mean and variance of `id`) are *already*
in Mathlib for `gaussianReal μ v` — `memLp_id_gaussianReal`,
`integral_id_gaussianReal`, `variance_id_gaussianReal` — so they are not restated
here. What the sub-Gaussian statement adds beyond those is the Chernoff bound
below, `HasSubgaussianMGF.const_mul` for scaled samples, and the
Hoeffding/independent-sum lemmas. -/

open MeasureTheory ProbabilityTheory in
/-- **Chernoff bound** for the standard Gaussian: `Pr[Z ≥ t] ≤ exp (-t²/2)`. -/
theorem gaussianReal_ge_le_chernoff {t : ℝ} (ht : 0 ≤ t) :
    (gaussianReal 0 1) {y : ℝ | t ≤ y} ≤ ENNReal.ofReal (Real.exp (-t ^ 2 / 2)) := by
  have h := hasSubgaussianMGF_id_gaussianReal.measure_ge_le ht
  rw [Measure.real] at h
  refine (ENNReal.le_ofReal_iff_toReal_le (measure_ne_top _ _) (Real.exp_pos _).le).mpr ?_
  refine h.trans (le_of_eq ?_)
  rw [NNReal.coe_one, mul_one]

open MeasureTheory ProbabilityTheory in
/-- The left tail, from sub-Gaussianity of `-Z`. -/
theorem gaussianReal_neg_ge_le_chernoff {t : ℝ} (ht : 0 ≤ t) :
    (gaussianReal 0 1) {y : ℝ | t ≤ -y} ≤ ENNReal.ofReal (Real.exp (-t ^ 2 / 2)) := by
  have h := hasSubgaussianMGF_id_gaussianReal.neg.measure_ge_le ht
  rw [Measure.real] at h
  refine (ENNReal.le_ofReal_iff_toReal_le (measure_ne_top _ _) (Real.exp_pos _).le).mpr ?_
  refine h.trans (le_of_eq ?_)
  rw [NNReal.coe_one, mul_one]

open MeasureTheory ProbabilityTheory in
/-- **Chernoff bound, two-sided**: `Pr[|Z| ≥ t] ≤ 2·exp(-t²/2)`, by a union
bound over the two tails. -/
theorem gaussianReal_abs_ge_le_chernoff {t : ℝ} (ht : 0 ≤ t) :
    (gaussianReal 0 1) {y : ℝ | t ≤ |y|}
      ≤ ENNReal.ofReal (2 * Real.exp (-t ^ 2 / 2)) := by
  have hsub : {y : ℝ | t ≤ |y|} ⊆ {y : ℝ | t ≤ y} ∪ {y : ℝ | t ≤ -y} := by
    intro y hy
    have hy' : t ≤ |y| := hy
    rcases le_total 0 y with hy0 | hy0
    · exact Or.inl (show t ≤ y by rwa [abs_of_nonneg hy0] at hy')
    · exact Or.inr (show t ≤ -y by rwa [abs_of_nonpos hy0] at hy')
  calc (gaussianReal 0 1) {y : ℝ | t ≤ |y|}
      ≤ (gaussianReal 0 1) ({y : ℝ | t ≤ y} ∪ {y : ℝ | t ≤ -y}) := measure_mono hsub
    _ ≤ (gaussianReal 0 1) {y : ℝ | t ≤ y} + (gaussianReal 0 1) {y : ℝ | t ≤ -y} :=
        measure_union_le _ _
    _ ≤ ENNReal.ofReal (Real.exp (-t ^ 2 / 2)) + ENNReal.ofReal (Real.exp (-t ^ 2 / 2)) :=
        add_le_add (gaussianReal_ge_le_chernoff ht) (gaussianReal_neg_ge_le_chernoff ht)
    _ = ENNReal.ofReal (2 * Real.exp (-t ^ 2 / 2)) := by
        rw [← ENNReal.ofReal_add (Real.exp_pos _).le (Real.exp_pos _).le]
        congr 1
        ring

open MeasureTheory ProbabilityTheory in
theorem stdTailErr_credit_le_chernoff {t : ℝ} (ht : 0 ≤ t) :
    GaussCreditV (stdTailErr t) ≤ ENNReal.ofReal (2 * Real.exp (-t ^ 2 / 2)) := by
  have h := gauss_credit_eq_gaussianReal (stdTailErr t) (measurable_stdTailErr t)
  rw [← h, stdTailErr, lintegral_indicator_const (measurableSet_abs_ge t), one_mul]
  exact gaussianReal_abs_ge_le_chernoff ht

section chernoffCredit

variable {hlc : HasLC} {GF : BundledGFunctors.{0,0,0}} [ErisGS ℝ hlc GF]

/-- **Chernoff at the credit level**: `↯(2·exp(-t²/2))` buys `|y| < t`. -/
theorem twp_Gauss_tail_chernoff (E : CoPset) {t : ℝ} (ht : 0 ≤ t) :
    ⊢@{IProp GF} ↯ (ENNReal.ofReal (2 * Real.exp (-t ^ 2 / 2))) -∗
      tglWp E pl(&Gauss #.unit)
        (fun v : Val ℝ => iprop(⌜∃ y : ℝ, v.1 = .lit (.real y) ∧ |y| < t⌝)) :=
  twp_Gauss_tail_of_le E (stdTailErr_credit_le_chernoff ht)

end chernoffCredit

section chernoffAdequacy

variable {GF : BundledGFunctors.{0,0,0}}

open MeasureTheory ProbabilityTheory in
/-- **Chernoff at the probability level.** -/
theorem gauss_std_tail_prob_chernoff [AppPreGS ℝ GF] [ECPreGS GF] [InvGpreS GF] {t : ℝ}
    (ht : 0 ≤ t) (σ : State ℝ) :
    (limExec ⟨pl(&Gauss #.unit), σ⟩)
        ((fun ρ : Cfg ℝ => realOfExp ρ.expr) ⁻¹' {y : ℝ | t ≤ |y|})
      ≤ ENNReal.ofReal (2 * Real.exp (-t ^ 2 / 2)) := by
  have hmg : Measurable (fun ρ : Cfg ℝ => realOfExp ρ.expr) :=
    measurable_realOfExp.comp Cfg.measurable_expr
  rw [← Measure.map_apply hmg (measurableSet_abs_ge t), gauss_std_distributed (GF := GF) σ]
  exact gaussianReal_abs_ge_le_chernoff ht

end chernoffAdequacy

end subGaussian

section mills

/-! ## The Mills-ratio tail bound

Chebyshev is loose in the tail. The sharper estimate comes from dominating the
density by `(y/t)·exp(-y²/2)` on `[t, ∞)`, whose integral is *elementary*:
`y·exp(-y²/2)` has the antiderivative `-exp(-y²/2)`. This gives

    Pr[Z ≥ t] ≤ √(2/π) · exp(-t²/2) / t,

within about 10% of the true Gaussian tail, against a factor ~8 for the
sub-Gaussian bound `exp(-t²/2)` and orders of magnitude for `1/t²`. -/

open MeasureTheory in
theorem integrable_exp_neg_sq_half : Integrable fun y : ℝ => Real.exp (-y ^ 2 / 2) := by
  have h := integrable_exp_neg_mul_sq (b := 1 / 2) (by norm_num)
  refine h.congr (Filter.Eventually.of_forall fun y => ?_)
  show Real.exp (-(1 / 2 : ℝ) * y ^ 2) = Real.exp (-y ^ 2 / 2)
  exact Real.exp_eq_exp.mpr (by ring)

open MeasureTheory in
theorem integrable_mul_exp_neg_sq_half :
    Integrable fun y : ℝ => y * Real.exp (-y ^ 2 / 2) := by
  have h := integrable_mul_exp_neg_mul_sq (b := 1 / 2) (by norm_num)
  refine h.congr (Filter.Eventually.of_forall fun y => ?_)
  show y * Real.exp (-(1 / 2 : ℝ) * y ^ 2) = y * Real.exp (-y ^ 2 / 2)
  rw [Real.exp_eq_exp.mpr (show -(1 / 2 : ℝ) * y ^ 2 = -y ^ 2 / 2 from by ring)]

theorem tendsto_exp_neg_sq_half :
    Filter.Tendsto (fun y : ℝ => Real.exp (-y ^ 2 / 2)) Filter.atTop (nhds 0) := by
  have hsq : Filter.Tendsto (fun y : ℝ => y ^ 2 / 2) Filter.atTop Filter.atTop :=
    (Filter.tendsto_pow_atTop (n := 2) (by norm_num)).atTop_div_const (by norm_num)
  have hneg : Filter.Tendsto (fun y : ℝ => -y ^ 2 / 2) Filter.atTop Filter.atBot := by
    refine (Filter.tendsto_neg_atTop_atBot.comp hsq).congr fun y => ?_
    show -(y ^ 2 / 2) = -y ^ 2 / 2
    ring
  exact Real.tendsto_exp_atBot.comp hneg

open MeasureTheory in
/-- The elementary improper integral behind the Mills bound. -/
theorem integral_Ioi_mul_exp_neg_sq_half (t : ℝ) :
    (∫ y in Set.Ioi t, y * Real.exp (-y ^ 2 / 2)) = Real.exp (-t ^ 2 / 2) := by
  have hderiv : ∀ y ∈ Set.Ici t,
      HasDerivAt (fun z : ℝ => Real.exp (-z ^ 2 / 2)) (-(y * Real.exp (-y ^ 2 / 2))) y :=
    fun y _ => hasDerivAt_exp_neg_sq_half y
  have hint : IntegrableOn (fun y : ℝ => -(y * Real.exp (-y ^ 2 / 2))) (Set.Ioi t) :=
    integrable_mul_exp_neg_sq_half.neg.integrableOn
  have h := integral_Ioi_of_hasDerivAt_of_tendsto' hderiv hint tendsto_exp_neg_sq_half
  rw [integral_neg, zero_sub] at h
  exact neg_injective h

open MeasureTheory in
/-- **Mills' inequality** for the Gaussian density on a ray. -/
theorem integral_Ioi_exp_le_mills {t : ℝ} (ht : 0 < t) :
    (∫ y in Set.Ioi t, Real.exp (-y ^ 2 / 2)) ≤ Real.exp (-t ^ 2 / 2) / t := by
  have hexp : IntegrableOn (fun y : ℝ => Real.exp (-y ^ 2 / 2)) (Set.Ioi t) :=
    integrable_exp_neg_sq_half.integrableOn
  have hmul : IntegrableOn (fun y : ℝ => t⁻¹ * (y * Real.exp (-y ^ 2 / 2))) (Set.Ioi t) :=
    (integrable_mul_exp_neg_sq_half.const_mul _).integrableOn
  have hpt : ∀ y ∈ Set.Ioi t,
      Real.exp (-y ^ 2 / 2) ≤ t⁻¹ * (y * Real.exp (-y ^ 2 / 2)) := by
    intro y hy
    have hy' : t < y := hy
    have h1 : (1 : ℝ) ≤ t⁻¹ * y := by
      rw [← div_eq_inv_mul]
      exact (one_le_div ht).mpr hy'.le
    calc Real.exp (-y ^ 2 / 2) = 1 * Real.exp (-y ^ 2 / 2) := (one_mul _).symm
      _ ≤ (t⁻¹ * y) * Real.exp (-y ^ 2 / 2) :=
          mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
      _ = t⁻¹ * (y * Real.exp (-y ^ 2 / 2)) := by ring
  have hmono := setIntegral_mono_on hexp hmul measurableSet_Ioi hpt
  rwa [integral_const_mul, integral_Ioi_mul_exp_neg_sq_half, inv_mul_eq_div] at hmono

theorem one_div_Norm2 : 1 / Norm2 = Real.sqrt (2 / Real.pi) := by
  have hs : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.mpr (by positivity)
  have hmul : Real.sqrt (2 / Real.pi) * Real.sqrt (2 * Real.pi) = 2 := by
    rw [← Real.sqrt_mul (by positivity),
      show (2 / Real.pi) * (2 * Real.pi) = 4 by field_simp; ring,
      show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  rw [Norm2_eq, one_div_div, div_eq_iff hs.ne']
  exact hmul.symm

open MeasureTheory in
/-- **Mills tail bound for the half-normal**: `Pr[Y ≥ t] ≤ √(2/π)·exp(-t²/2)/t`. -/
theorem halfNormal_Ici_le_mills {t : ℝ} (ht : 0 < t) :
    halfNormal (Set.Ici t)
      ≤ ENNReal.ofReal (Real.sqrt (2 / Real.pi) * Real.exp (-t ^ 2 / 2) / t) := by
  have hset : Set.Ici t ∩ Set.Ioi (0 : ℝ) = Set.Ici t := by
    ext y
    simp only [Set.mem_inter_iff, Set.mem_Ici, Set.mem_Ioi]
    exact ⟨fun h => h.1, fun h => ⟨h, lt_of_lt_of_le ht h⟩⟩
  have hdens : IntegrableOn (fun y : ℝ => Real.exp (-y ^ 2 / 2) / Norm2) (Set.Ioi t) :=
    (integrable_exp_neg_sq_half.div_const _).integrableOn
  rw [halfNormal_eq_withDensity, withDensity_apply _ measurableSet_Ici,
    Measure.restrict_restrict measurableSet_Ici, hset,
    setLIntegral_congr Ioi_ae_eq_Ici.symm]
  show ∫⁻ y in Set.Ioi t, ENNReal.ofReal (Real.exp (-y ^ 2 / 2) / Norm2) ∂volume ≤ _
  rw [← ofReal_integral_eq_lintegral_ofReal hdens
      (ae_restrict_of_forall_mem measurableSet_Ioi
        fun y _ => div_nonneg (Real.exp_pos _).le Norm2_pos.le),
    integral_div]
  refine ENNReal.ofReal_le_ofReal ?_
  calc (∫ y in Set.Ioi t, Real.exp (-y ^ 2 / 2)) / Norm2
      = Real.sqrt (2 / Real.pi) * ∫ y in Set.Ioi t, Real.exp (-y ^ 2 / 2) := by
        rw [← one_div_Norm2]; ring
    _ ≤ Real.sqrt (2 / Real.pi) * (Real.exp (-t ^ 2 / 2) / t) :=
        mul_le_mul_of_nonneg_left (integral_Ioi_exp_le_mills ht) (Real.sqrt_nonneg _)
    _ = Real.sqrt (2 / Real.pi) * Real.exp (-t ^ 2 / 2) / t := by ring

open MeasureTheory ProbabilityTheory in
/-- The two-sided standard-Gaussian tail *equals* the one-sided half-normal tail:
symmetrising splits the mass evenly, and `halfNormal` lives on `(0,∞)`. -/
theorem gaussianReal_abs_ge_eq_halfNormal_Ici {t : ℝ} :
    (gaussianReal 0 1) {y : ℝ | t ≤ |y|} = halfNormal (Set.Ici t) := by
  have hmeas := measurableSet_abs_ge t
  have hF : Measurable ({y : ℝ | t ≤ |y|}.indicator (fun _ => (1 : ℝ≥0∞))) :=
    measurable_const.indicator hmeas
  have hsymm : ∀ y : ℝ, {y : ℝ | t ≤ |y|}.indicator (fun _ => (1 : ℝ≥0∞)) (-y)
      = {y : ℝ | t ≤ |y|}.indicator (fun _ => (1 : ℝ≥0∞)) y := by
    intro y
    by_cases hy : t ≤ |y|
    · rw [Set.indicator_of_mem (show -y ∈ {y : ℝ | t ≤ |y|} by simpa using hy),
        Set.indicator_of_mem (show y ∈ {y : ℝ | t ≤ |y|} from hy)]
    · rw [Set.indicator_of_notMem (by simpa using hy),
        Set.indicator_of_notMem (by simpa using hy)]
  have hneg_eq : ∫⁻ y, {y : ℝ | t ≤ |y|}.indicator (fun _ => (1 : ℝ≥0∞)) (-y) ∂halfNormal
      = ∫⁻ y, {y : ℝ | t ≤ |y|}.indicator (fun _ => (1 : ℝ≥0∞)) y ∂halfNormal :=
    lintegral_congr_ae (Filter.Eventually.of_forall hsymm)
  have hhalf : ENNReal.ofReal (1 / 2) + ENNReal.ofReal (1 / 2) = 1 := by
    rw [← ENNReal.ofReal_add (by norm_num) (by norm_num)]
    norm_num
  -- On `halfNormal`, `{t ≤ |y|}` and `[t, ∞)` agree: the measure lives on `(0,∞)`.
  have hgauss : halfNormal {y : ℝ | t ≤ |y|} = halfNormal (Set.Ici t) := by
    have hint : {y : ℝ | t ≤ |y|} ∩ Set.Ioi (0 : ℝ) = Set.Ici t ∩ Set.Ioi (0 : ℝ) := by
      ext y
      simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_Ici, Set.mem_Ioi]
      constructor
      · rintro ⟨habs, hy0⟩
        exact ⟨by rwa [abs_of_pos hy0] at habs, hy0⟩
      · rintro ⟨hty, hy0⟩
        exact ⟨by rwa [abs_of_pos hy0], hy0⟩
    rw [halfNormal_eq_withDensity, withDensity_apply _ hmeas,
      withDensity_apply _ measurableSet_Ici,
      Measure.restrict_restrict hmeas, Measure.restrict_restrict measurableSet_Ici, hint]
  calc (gaussianReal 0 1) {y : ℝ | t ≤ |y|}
      = ∫⁻ y, {y : ℝ | t ≤ |y|}.indicator (fun _ => (1 : ℝ≥0∞)) y ∂(gaussianReal 0 1) := by
        rw [lintegral_indicator_const hmeas, one_mul]
    _ = ENNReal.ofReal (1 / 2)
          * (∫⁻ y, {y : ℝ | t ≤ |y|}.indicator (fun _ => (1 : ℝ≥0∞)) (-y) ∂halfNormal)
        + ENNReal.ofReal (1 / 2)
          * ∫⁻ y, {y : ℝ | t ≤ |y|}.indicator (fun _ => (1 : ℝ≥0∞)) y ∂halfNormal :=
        gaussianReal_lintegral_split _ hF
    _ = ∫⁻ y, {y : ℝ | t ≤ |y|}.indicator (fun _ => (1 : ℝ≥0∞)) y ∂halfNormal := by
        rw [hneg_eq, ← add_mul, hhalf, one_mul]
    _ = halfNormal {y : ℝ | t ≤ |y|} := by rw [lintegral_indicator_const hmeas, one_mul]
    _ = halfNormal (Set.Ici t) := hgauss

open MeasureTheory ProbabilityTheory in
/-- **Mills tail bound for the standard Gaussian**: two-sided, and sharper than
both the Chebyshev and the sub-Gaussian bounds for `t ≳ 1`. -/
theorem gaussianReal_abs_ge_le_mills {t : ℝ} (ht : 0 < t) :
    (gaussianReal 0 1) {y : ℝ | t ≤ |y|}
      ≤ ENNReal.ofReal (Real.sqrt (2 / Real.pi) * Real.exp (-t ^ 2 / 2) / t) := by
  rw [gaussianReal_abs_ge_eq_halfNormal_Ici]
  exact halfNormal_Ici_le_mills ht

/-! ### Mills at the credit and probability levels -/

open MeasureTheory ProbabilityTheory in
theorem stdTailErr_credit_le_mills {t : ℝ} (ht : 0 < t) :
    GaussCreditV (stdTailErr t)
      ≤ ENNReal.ofReal (Real.sqrt (2 / Real.pi) * Real.exp (-t ^ 2 / 2) / t) := by
  have h := gauss_credit_eq_gaussianReal (stdTailErr t) (measurable_stdTailErr t)
  rw [← h, stdTailErr, lintegral_indicator_const (measurableSet_abs_ge t), one_mul]
  exact gaussianReal_abs_ge_le_mills ht

section millsCredit

variable {hlc : HasLC} {GF : BundledGFunctors.{0,0,0}} [ErisGS ℝ hlc GF]

/-- **Mills at the credit level, standard Gaussian.** Sharper than
`twp_Gauss_tail`: the credit price of a `t`-bounded sample decays like
`exp(-t²/2)/t` instead of `1/t²`. -/
theorem twp_Gauss_tail_mills (E : CoPset) {t : ℝ} (ht : 0 < t) :
    ⊢@{IProp GF} ↯ (ENNReal.ofReal (Real.sqrt (2 / Real.pi) * Real.exp (-t ^ 2 / 2) / t)) -∗
      tglWp E pl(&Gauss #.unit)
        (fun v : Val ℝ => iprop(⌜∃ y : ℝ, v.1 = .lit (.real y) ∧ |y| < t⌝)) :=
  twp_Gauss_tail_of_le E (stdTailErr_credit_le_mills ht)

end millsCredit

section millsAdequacy

variable {GF : BundledGFunctors.{0,0,0}}

open MeasureTheory ProbabilityTheory in
/-- **Mills at the probability level, standard Gaussian.** -/
theorem gauss_std_tail_prob_mills [AppPreGS ℝ GF] [ECPreGS GF] [InvGpreS GF] {t : ℝ}
    (ht : 0 < t) (σ : State ℝ) :
    (limExec ⟨pl(&Gauss #.unit), σ⟩)
        ((fun ρ : Cfg ℝ => realOfExp ρ.expr) ⁻¹' {y : ℝ | t ≤ |y|})
      ≤ ENNReal.ofReal (Real.sqrt (2 / Real.pi) * Real.exp (-t ^ 2 / 2) / t) := by
  have hmg : Measurable (fun ρ : Cfg ℝ => realOfExp ρ.expr) :=
    measurable_realOfExp.comp Cfg.measurable_expr
  rw [← Measure.map_apply hmg (measurableSet_abs_ge t), gauss_std_distributed (GF := GF) σ]
  exact gaussianReal_abs_ge_le_mills ht

end millsAdequacy

end mills

end

end Examples
end TotalEris
end ProbLang
