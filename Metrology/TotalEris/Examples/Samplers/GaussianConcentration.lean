module

public import Metrology.TotalEris.Examples.Samplers.GaussianAdequacy
public import Mathlib.Probability.Moments.SubGaussian

@[expose] public section

open Iris Iris.BI Iris.ProofMode ProbLang ProbLang.TotalEris ProbLang.TotalEris.Examples
  ProbLang.TotalEris.ErisWpGS
open scoped AppGS ENNReal NNReal

namespace ProbLang
namespace TotalEris
namespace Examples

noncomputable section

def stdTailErr (t : ℝ) : ℝ → ℝ≥0∞ := {y : ℝ | t ≤ |y|}.indicator (fun _ => 1)

section Measure
open MeasureTheory ProbabilityTheory

theorem measurableSet_abs_ge (t : ℝ) : MeasurableSet {y : ℝ | t ≤ |y|} :=
  measurable_abs measurableSet_Ici

theorem measurable_stdTailErr (t : ℝ) : Measurable (stdTailErr t) :=
  measurable_const.indicator (measurableSet_abs_ge t)

theorem stdTailErr_of_le {t y : ℝ} (h : t ≤ |y|) : stdTailErr t y = 1 :=
  Set.indicator_of_mem (show y ∈ {y : ℝ | t ≤ |y|} from h) _

theorem stdTailErr_credit_le {t : ℝ} {ε : ℝ≥0∞}
    (h : (gaussianReal 0 1) {y : ℝ | t ≤ |y|} ≤ ε) : GaussCreditV (stdTailErr t) ≤ ε := by
  rw [← gauss_credit_eq_gaussianReal _ (measurable_stdTailErr t), stdTailErr,
    lintegral_indicator_const (measurableSet_abs_ge t), one_mul]
  exact h

theorem abs_ge_le_div {t : ℝ} {g : ℝ → ℝ≥0∞} {c m : ℝ≥0∞} (hg : Measurable g)
    (hc : c ≠ 0) (hct : c ≠ (⊤ : ℝ≥0∞)) (hsub : ∀ y : ℝ, t ≤ |y| → c ≤ g y)
    (hm : ∫⁻ y, g y ∂(gaussianReal 0 1) ≤ m) :
    (gaussianReal 0 1) {y : ℝ | t ≤ |y|} ≤ m / c :=
  (measure_mono fun y hy => hsub y hy).trans
    ((meas_ge_le_lintegral_div hg.aemeasurable hc hct).trans (ENNReal.div_le_div_right hm _))

theorem hasDerivAt_exp_neg_sq_half (y : ℝ) :
    HasDerivAt (fun z : ℝ => Real.exp (-z ^ 2 / 2)) (-(y * Real.exp (-y ^ 2 / 2))) y := by
  have hsq : HasDerivAt (fun z : ℝ => -z ^ 2 / 2) (-y) y :=
    ((hasDerivAt_pow 2 y).neg.div_const 2).congr_deriv (by ring)
  exact hsq.exp.congr_deriv (by ring)

theorem integrable_exp_neg_sq_half : Integrable fun y : ℝ => Real.exp (-y ^ 2 / 2) :=
  (integrable_exp_neg_mul_sq (b := 1 / 2) (by norm_num)).congr
    (.of_forall fun y => Real.exp_eq_exp.mpr (by ring))

theorem integrable_mul_exp_neg_sq_half : Integrable fun y : ℝ => y * Real.exp (-y ^ 2 / 2) :=
  (integrable_mul_exp_neg_mul_sq (b := 1 / 2) (by norm_num)).congr (.of_forall fun y => by
    show y * Real.exp (-(1 / 2 : ℝ) * y ^ 2) = y * Real.exp (-y ^ 2 / 2)
    rw [Real.exp_eq_exp.mpr (show -(1 / 2 : ℝ) * y ^ 2 = -y ^ 2 / 2 from by ring)])

theorem tendsto_exp_neg_sq_half :
    Filter.Tendsto (fun y : ℝ => Real.exp (-y ^ 2 / 2)) Filter.atTop (nhds 0) := by
  have hsq : Filter.Tendsto (fun y : ℝ => y ^ 2 / 2) Filter.atTop Filter.atTop :=
    (Filter.tendsto_pow_atTop (n := 2) (by norm_num)).atTop_div_const (by norm_num : (0:ℝ) < 2)
  exact Real.tendsto_exp_atBot.comp ((Filter.tendsto_neg_atTop_atBot.comp hsq).congr fun y => by
    show -(y ^ 2 / 2) = -y ^ 2 / 2
    ring)

theorem integral_Ioi_mul_exp_neg_sq_half (t : ℝ) :
    (∫ y in Set.Ioi t, y * Real.exp (-y ^ 2 / 2)) = Real.exp (-t ^ 2 / 2) := by
  have h := integral_Ioi_of_hasDerivAt_of_tendsto' (a := t) (fun y _ => hasDerivAt_exp_neg_sq_half y)
    integrable_mul_exp_neg_sq_half.neg.integrableOn tendsto_exp_neg_sq_half
  rw [integral_neg, zero_sub] at h
  exact neg_injective h

theorem integral_Ioi_exp_le_mills {t : ℝ} (ht : 0 < t) :
    (∫ y in Set.Ioi t, Real.exp (-y ^ 2 / 2)) ≤ Real.exp (-t ^ 2 / 2) / t := by
  have h := setIntegral_mono_on integrable_exp_neg_sq_half.integrableOn
    (integrable_mul_exp_neg_sq_half.const_mul t⁻¹).integrableOn measurableSet_Ioi
    fun y (hy : t < y) => by
      have h1 : (1 : ℝ) ≤ t⁻¹ * y := by rw [← div_eq_inv_mul]; exact (one_le_div ht).mpr hy.le
      calc Real.exp (-y ^ 2 / 2) = 1 * Real.exp (-y ^ 2 / 2) := (one_mul _).symm
        _ ≤ (t⁻¹ * y) * Real.exp (-y ^ 2 / 2) :=
            mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
        _ = t⁻¹ * (y * Real.exp (-y ^ 2 / 2)) := by ring
  rwa [integral_const_mul, integral_Ioi_mul_exp_neg_sq_half, inv_mul_eq_div] at h

theorem one_div_Norm2 : 1 / Norm2 = Real.sqrt (2 / Real.pi) := by
  have hs : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.mpr (by positivity)
  rw [Norm2_eq, one_div_div, div_eq_iff hs.ne', ← Real.sqrt_mul (by positivity),
    show (2 / Real.pi) * (2 * Real.pi) = 2 ^ 2 by field_simp, Real.sqrt_sq (by norm_num)]

theorem lintegral_abs_halfNormal :
    ∫⁻ y, ENNReal.ofReal |y| ∂halfNormal = ENNReal.ofReal (Real.sqrt (2 / Real.pi)) := by
  rw [lintegral_halfNormal _ (by fun_prop),
    setLIntegral_congr_fun measurableSet_Ioi (g := fun y => ENNReal.ofReal
      (y * Real.exp (-y ^ 2 / 2) / Norm2)) fun y (hy : 0 < y) => by
        rw [halfDens, ← ENNReal.ofReal_mul (div_nonneg (Real.exp_pos _).le Norm2_pos.le),
          abs_of_pos hy]
        congr 1
        ring,
    ← ofReal_integral_eq_lintegral_ofReal (integrable_mul_exp_neg_sq_half.div_const _).integrableOn
      (ae_restrict_of_forall_mem measurableSet_Ioi fun y (hy : 0 < y) =>
        div_nonneg (mul_nonneg hy.le (Real.exp_pos _).le) Norm2_pos.le),
    integral_div, integral_Ioi_mul_exp_neg_sq_half, ← one_div_Norm2]
  norm_num

theorem gaussianReal_eq_halfNormal_of_neg {S : Set ℝ} (hS : MeasurableSet S)
    (hsymm : ∀ y : ℝ, -y ∈ S ↔ y ∈ S) : (gaussianReal 0 1) S = halfNormal S := by
  have hneg : ∀ y : ℝ, S.indicator (fun _ => (1 : ℝ≥0∞)) (-y)
      = S.indicator (fun _ => (1 : ℝ≥0∞)) y := fun y => by
    by_cases hy : y ∈ S
    · rw [Set.indicator_of_mem ((hsymm y).mpr hy), Set.indicator_of_mem hy]
    · rw [Set.indicator_of_notMem (fun h => hy ((hsymm y).mp h)), Set.indicator_of_notMem hy]
  have h := gaussianReal_lintegral_split (S.indicator (fun _ => (1 : ℝ≥0∞)))
    (measurable_const.indicator hS)
  rw [lintegral_congr_ae (.of_forall hneg), ← add_mul,
    ← ENNReal.ofReal_add (by norm_num) (by norm_num), lintegral_indicator_const hS,
    lintegral_indicator_const hS] at h
  norm_num at h
  exact h

theorem lintegral_abs_gaussianReal :
    ∫⁻ y, ENNReal.ofReal |y| ∂(gaussianReal 0 1) = ENNReal.ofReal (Real.sqrt (2 / Real.pi)) := by
  have hneg : ∫⁻ y, ENNReal.ofReal |(-y)| ∂halfNormal
      = ∫⁻ y, ENNReal.ofReal |y| ∂halfNormal :=
    lintegral_congr_ae (.of_forall fun y => by simp only [abs_neg])
  have h := gaussianReal_lintegral_split (fun y => ENNReal.ofReal |y|) (by fun_prop)
  rw [hneg, ← add_mul, ← ENNReal.ofReal_add (by norm_num) (by norm_num)] at h
  norm_num at h
  rw [h, lintegral_abs_halfNormal]

theorem lintegral_sq_gaussianReal : ∫⁻ y, ENNReal.ofReal (y ^ 2) ∂(gaussianReal 0 1) = 1 := by
  have hL : MemLp (id : ℝ → ℝ) 2 (gaussianReal 0 1) := memLp_id_gaussianReal 2
  have hint : Integrable (fun y : ℝ => y ^ 2) (gaussianReal 0 1) := hL.integrable_sq
  have h : ∫ y : ℝ, y ^ 2 ∂(gaussianReal 0 1) = 1 := by
    have hv := variance_eq_sub hL
    simp only [Pi.pow_apply, id_eq] at hv
    rw [variance_id_gaussianReal, integral_id_gaussianReal] at hv
    simpa using hv.symm
  rw [← ofReal_integral_eq_lintegral_ofReal hint (.of_forall fun y => sq_nonneg y), h,
    ENNReal.ofReal_one]

theorem gaussianReal_abs_ge_le_markov {t : ℝ} (ht : 0 < t) :
    (gaussianReal 0 1) {y : ℝ | t ≤ |y|} ≤ ENNReal.ofReal (Real.sqrt (2 / Real.pi) / t) := by
  rw [ENNReal.ofReal_div_of_pos ht]
  exact abs_ge_le_div (by fun_prop) (ENNReal.ofReal_pos.mpr ht).ne' ENNReal.ofReal_ne_top
    (fun y hy => ENNReal.ofReal_le_ofReal hy) lintegral_abs_gaussianReal.le

theorem gaussianReal_abs_ge_le {t : ℝ} (ht : 0 < t) :
    (gaussianReal 0 1) {y : ℝ | t ≤ |y|} ≤ ENNReal.ofReal (1 / t ^ 2) := by
  rw [ENNReal.ofReal_div_of_pos (by positivity), ENNReal.ofReal_one]
  exact abs_ge_le_div (by fun_prop) (ENNReal.ofReal_pos.mpr (by positivity)).ne'
    ENNReal.ofReal_ne_top
    (fun y hy => ENNReal.ofReal_le_ofReal (by nlinarith [sq_abs y, abs_nonneg y]))
    lintegral_sq_gaussianReal.le

theorem hasSubgaussianMGF_id_gaussianReal : HasSubgaussianMGF id 1 (gaussianReal 0 1) where
  integrable_exp_mul t := integrable_exp_mul_gaussianReal t
  mgf_le t := by rw [mgf_id_gaussianReal]; simp

theorem chernoff_half {X : ℝ → ℝ} (hX : HasSubgaussianMGF X 1 (gaussianReal 0 1)) {t : ℝ}
    (ht : 0 ≤ t) :
    (gaussianReal 0 1) {y : ℝ | t ≤ X y} ≤ ENNReal.ofReal (Real.exp (-t ^ 2 / 2)) := by
  have h := hX.measure_ge_le ht
  rw [Measure.real] at h
  refine (ENNReal.le_ofReal_iff_toReal_le (measure_ne_top _ _) (Real.exp_pos _).le).mpr ?_
  refine h.trans (le_of_eq ?_)
  rw [NNReal.coe_one, mul_one]

theorem gaussianReal_abs_ge_le_chernoff {t : ℝ} (ht : 0 ≤ t) :
    (gaussianReal 0 1) {y : ℝ | t ≤ |y|} ≤ ENNReal.ofReal (2 * Real.exp (-t ^ 2 / 2)) := by
  have hsub : {y : ℝ | t ≤ |y|} ⊆ {y : ℝ | t ≤ id y} ∪ {y : ℝ | t ≤ (-id) y} := fun y hy => by
    have hy' : t ≤ |y| := hy
    rcases le_total 0 y with h | h
    · exact Or.inl (show t ≤ y by rwa [abs_of_nonneg h] at hy')
    · exact Or.inr (show t ≤ -y by rwa [abs_of_nonpos h] at hy')
  calc (gaussianReal 0 1) {y : ℝ | t ≤ |y|}
      ≤ _ := measure_mono hsub
    _ ≤ _ := measure_union_le _ _
    _ ≤ ENNReal.ofReal (Real.exp (-t ^ 2 / 2)) + ENNReal.ofReal (Real.exp (-t ^ 2 / 2)) :=
        add_le_add (chernoff_half hasSubgaussianMGF_id_gaussianReal ht)
          (chernoff_half hasSubgaussianMGF_id_gaussianReal.neg ht)
    _ = ENNReal.ofReal (2 * Real.exp (-t ^ 2 / 2)) := by
        rw [← ENNReal.ofReal_add (Real.exp_pos _).le (Real.exp_pos _).le]; ring_nf

theorem halfNormal_Ici_le_mills {t : ℝ} (ht : 0 < t) :
    halfNormal (Set.Ici t)
      ≤ ENNReal.ofReal (Real.sqrt (2 / Real.pi) * Real.exp (-t ^ 2 / 2) / t) := by
  have hset : Set.Ici t ∩ Set.Ioi (0 : ℝ) = Set.Ici t :=
    Set.inter_eq_self_of_subset_left fun y hy => lt_of_lt_of_le ht hy
  rw [halfNormal_eq_withDensity, withDensity_apply _ measurableSet_Ici,
    Measure.restrict_restrict measurableSet_Ici, hset, setLIntegral_congr Ioi_ae_eq_Ici.symm]
  show ∫⁻ y in Set.Ioi t, ENNReal.ofReal (Real.exp (-y ^ 2 / 2) / Norm2) ∂volume ≤ _
  rw [← ofReal_integral_eq_lintegral_ofReal (integrable_exp_neg_sq_half.div_const _).integrableOn
      (ae_restrict_of_forall_mem measurableSet_Ioi
        fun y _ => div_nonneg (Real.exp_pos _).le Norm2_pos.le), integral_div]
  refine ENNReal.ofReal_le_ofReal ?_
  calc (∫ y in Set.Ioi t, Real.exp (-y ^ 2 / 2)) / Norm2
      = Real.sqrt (2 / Real.pi) * ∫ y in Set.Ioi t, Real.exp (-y ^ 2 / 2) := by
        rw [← one_div_Norm2]; ring
    _ ≤ Real.sqrt (2 / Real.pi) * (Real.exp (-t ^ 2 / 2) / t) :=
        mul_le_mul_of_nonneg_left (integral_Ioi_exp_le_mills ht) (Real.sqrt_nonneg _)
    _ = _ := by ring

theorem gaussianReal_abs_ge_eq_halfNormal_Ici {t : ℝ} :
    (gaussianReal 0 1) {y : ℝ | t ≤ |y|} = halfNormal (Set.Ici t) := by
  rw [gaussianReal_eq_halfNormal_of_neg (measurableSet_abs_ge t) fun y => by simp [abs_neg]]
  have hint : {y : ℝ | t ≤ |y|} ∩ Set.Ioi (0 : ℝ) = Set.Ici t ∩ Set.Ioi (0 : ℝ) := by
    ext y
    simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_Ici, Set.mem_Ioi]
    exact and_congr_left fun hy0 => by rw [abs_of_pos hy0]
  rw [halfNormal_eq_withDensity, withDensity_apply _ (measurableSet_abs_ge t),
    withDensity_apply _ measurableSet_Ici, Measure.restrict_restrict (measurableSet_abs_ge t),
    Measure.restrict_restrict measurableSet_Ici, hint]

theorem gaussianReal_abs_ge_le_mills {t : ℝ} (ht : 0 < t) :
    (gaussianReal 0 1) {y : ℝ | t ≤ |y|}
      ≤ ENNReal.ofReal (Real.sqrt (2 / Real.pi) * Real.exp (-t ^ 2 / 2) / t) :=
  gaussianReal_abs_ge_eq_halfNormal_Ici ▸ halfNormal_Ici_le_mills ht

end Measure

section Credit

variable {hlc : HasLC} {GF : BundledGFunctors.{0,0,0}} [ErisGS ℝ hlc GF]

/-- Any bound on the tail mass is a price for a `t`-bounded sample. -/
theorem twp_Gauss_tail_of_le (E : CoPset) {t : ℝ} {ε : ℝ≥0∞}
    (hb : (ProbabilityTheory.gaussianReal 0 1) {y : ℝ | t ≤ |y|} ≤ ε) :
    ⊢@{IProp GF} ↯ ε -∗
      tglWp E pl(&Gauss #.unit)
        (fun v : Val ℝ => iprop(⌜∃ y : ℝ, v.1 = .lit (.real y) ∧ |y| < t⌝)) := by
  iintro Hε
  iapply (tglWp_wand (Φ := fun v : Val ℝ => iprop(∃ y : ℝ,
    ⌜v.1 = .lit (.real y)⌝ ∗ ↯ (stdTailErr t y))))
  isplitl [Hε]
  · iapply (twp_Gauss E (stdTailErr t) (measurable_stdTailErr t))
    iapply (ErrorCredit.weaken (stdTailErr_credit_le hb))
    iexact Hε
  iintro %v ⟨%y, %hy, Hcr⟩
  by_cases hlt : |y| < t
  · ipureintro
    exact ⟨y, hy, hlt⟩
  · iexfalso
    iapply ErrorCredit.contradict $$ Hcr
    rw [stdTailErr_of_le (not_lt.mp hlt)]

/-- Markov: `↯(√(2/π)/t)` buys `|y| < t`. -/
theorem twp_Gauss_tail_markov (E : CoPset) {t : ℝ} (ht : 0 < t) :
    ⊢@{IProp GF} ↯ (ENNReal.ofReal (Real.sqrt (2 / Real.pi) / t)) -∗
      tglWp E pl(&Gauss #.unit)
        (fun v : Val ℝ => iprop(⌜∃ y : ℝ, v.1 = .lit (.real y) ∧ |y| < t⌝)) :=
  twp_Gauss_tail_of_le E (gaussianReal_abs_ge_le_markov ht)

/-- Chebyshev: `↯(1/t²)` buys `|y| < t`. -/
theorem twp_Gauss_tail (E : CoPset) {t : ℝ} (ht : 0 < t) :
    ⊢@{IProp GF} ↯ (ENNReal.ofReal (1 / t ^ 2)) -∗
      tglWp E pl(&Gauss #.unit)
        (fun v : Val ℝ => iprop(⌜∃ y : ℝ, v.1 = .lit (.real y) ∧ |y| < t⌝)) :=
  twp_Gauss_tail_of_le E (gaussianReal_abs_ge_le ht)

/-- Chernoff: `↯(2·exp(-t²/2))` buys `|y| < t`. -/
theorem twp_Gauss_tail_chernoff (E : CoPset) {t : ℝ} (ht : 0 ≤ t) :
    ⊢@{IProp GF} ↯ (ENNReal.ofReal (2 * Real.exp (-t ^ 2 / 2))) -∗
      tglWp E pl(&Gauss #.unit)
        (fun v : Val ℝ => iprop(⌜∃ y : ℝ, v.1 = .lit (.real y) ∧ |y| < t⌝)) :=
  twp_Gauss_tail_of_le E (gaussianReal_abs_ge_le_chernoff ht)

/-- Mills: `↯(√(2/π)·exp(-t²/2)/t)` buys `|y| < t`, the sharpest of the four. -/
theorem twp_Gauss_tail_mills (E : CoPset) {t : ℝ} (ht : 0 < t) :
    ⊢@{IProp GF} ↯ (ENNReal.ofReal (Real.sqrt (2 / Real.pi) * Real.exp (-t ^ 2 / 2) / t)) -∗
      tglWp E pl(&Gauss #.unit)
        (fun v : Val ℝ => iprop(⌜∃ y : ℝ, v.1 = .lit (.real y) ∧ |y| < t⌝)) :=
  twp_Gauss_tail_of_le E (gaussianReal_abs_ge_le_mills ht)

end Credit

section Adequacy
open MeasureTheory ProbabilityTheory

variable {GF : BundledGFunctors.{0,0,0}}

theorem gauss_std_tail_prob_of_le [AppPreGS ℝ GF] [ECPreGS GF] [InvGpreS GF] {t : ℝ} {ε : ℝ≥0∞}
    (hb : (gaussianReal 0 1) {y : ℝ | t ≤ |y|} ≤ ε) (σ : State ℝ) :
    (limExec ⟨pl(&Gauss #.unit), σ⟩)
        ((fun ρ : Cfg ℝ => realOfExp ρ.expr) ⁻¹' {y : ℝ | t ≤ |y|}) ≤ ε := by
  have hmg : Measurable (fun ρ : Cfg ℝ => realOfExp ρ.expr) :=
    measurable_realOfExp.comp Cfg.measurable_expr
  rw [← Measure.map_apply hmg (measurableSet_abs_ge t), gauss_std_distributed (GF := GF) σ]
  exact hb

theorem gauss_std_tail_prob_markov [AppPreGS ℝ GF] [ECPreGS GF] [InvGpreS GF] {t : ℝ} (ht : 0 < t) (σ : State ℝ) :
    (limExec ⟨pl(&Gauss #.unit), σ⟩)
        ((fun ρ : Cfg ℝ => realOfExp ρ.expr) ⁻¹' {y : ℝ | t ≤ |y|})
      ≤ ENNReal.ofReal (Real.sqrt (2 / Real.pi) / t) :=
  gauss_std_tail_prob_of_le (GF := GF) (gaussianReal_abs_ge_le_markov ht) σ

theorem gauss_std_tail_prob [AppPreGS ℝ GF] [ECPreGS GF] [InvGpreS GF] {t : ℝ} (ht : 0 < t) (σ : State ℝ) :
    (limExec ⟨pl(&Gauss #.unit), σ⟩)
        ((fun ρ : Cfg ℝ => realOfExp ρ.expr) ⁻¹' {y : ℝ | t ≤ |y|})
      ≤ ENNReal.ofReal (1 / t ^ 2) :=
  gauss_std_tail_prob_of_le (GF := GF) (gaussianReal_abs_ge_le ht) σ

theorem gauss_std_tail_prob_chernoff [AppPreGS ℝ GF] [ECPreGS GF] [InvGpreS GF] {t : ℝ} (ht : 0 ≤ t) (σ : State ℝ) :
    (limExec ⟨pl(&Gauss #.unit), σ⟩)
        ((fun ρ : Cfg ℝ => realOfExp ρ.expr) ⁻¹' {y : ℝ | t ≤ |y|})
      ≤ ENNReal.ofReal (2 * Real.exp (-t ^ 2 / 2)) :=
  gauss_std_tail_prob_of_le (GF := GF) (gaussianReal_abs_ge_le_chernoff ht) σ

theorem gauss_std_tail_prob_mills [AppPreGS ℝ GF] [ECPreGS GF] [InvGpreS GF] {t : ℝ} (ht : 0 < t) (σ : State ℝ) :
    (limExec ⟨pl(&Gauss #.unit), σ⟩)
        ((fun ρ : Cfg ℝ => realOfExp ρ.expr) ⁻¹' {y : ℝ | t ≤ |y|})
      ≤ ENNReal.ofReal (Real.sqrt (2 / Real.pi) * Real.exp (-t ^ 2 / 2) / t) :=
  gauss_std_tail_prob_of_le (GF := GF) (gaussianReal_abs_ge_le_mills ht) σ

end Adequacy

end

end Examples
end TotalEris
end ProbLang
