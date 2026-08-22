-- Real decreasing trial — continuous-uniform sampler
module

public import Metrology.TotalEris
public import Metrology.ProbLang.Reals
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series

@[expose] public section

open Std Iris Iris.Std Iris.BI Iris.ProofMode OFE COFE ProbLang ProbLang.TotalEris
  ProbLang.TotalEris.ErisWpGS
open scoped AppGS ENNReal NNReal

namespace ProbLang
namespace TotalEris
namespace Examples

noncomputable section

variable {hlc : HasLC} {GF : BundledGFunctors.{0,0,0}} [ErisGS ℝ hlc GF]

section program

@[pl_fold]
def DecrTrial : Exp ℝ := pl%
  rec trial N x :=
    let y := urand;
    if y < x then trial (N + #1) y else N

end program

section distribution

def RealDecrTrialPMF₀ (x : ℝ) (n : ℕ) : ℝ≥0∞ :=
  .ofReal (x ^ n / n.factorial - x ^ (n + 1) / (n + 1).factorial)

def RealDecrTrialPMF (x : ℝ) (i n : ℕ) : ℝ≥0∞ :=
  if i ≤ n then RealDecrTrialPMF₀ x (n - i) else 0

theorem RealDecrTrialPMF_not_supp {x : ℝ} {i n : ℕ} (h : n < i) :
    RealDecrTrialPMF x i n = 0 := by
  simp only [RealDecrTrialPMF, if_neg (Nat.not_le.mpr h)]

theorem RealDecrTrialPMF_supp {x : ℝ} {i n : ℕ} (h : i ≤ n) :
    RealDecrTrialPMF x i n = RealDecrTrialPMF₀ x (n - i) := by
  simp only [RealDecrTrialPMF, if_pos h]

theorem RealDecrTrialPMF_base {x : ℝ} {n : ℕ} :
    RealDecrTrialPMF x 0 n = RealDecrTrialPMF₀ x n := by
  simp only [RealDecrTrialPMF, Nat.zero_le, if_pos, Nat.sub_zero]

open MeasureTheory in

theorem RealDecrTrialPMF₀_real_integral (m : ℕ) (t : ℝ) :
    ∫ y in (0 : ℝ)..t, (y ^ m / (m.factorial : ℝ) - y ^ (m + 1) / ((m + 1).factorial : ℝ))
      = t ^ (m + 1) / ((m + 1).factorial : ℝ) - t ^ (m + 2) / ((m + 2).factorial : ℝ) := by
  rw [intervalIntegral.integral_sub (Continuous.intervalIntegrable (by fun_prop) _ _)
        (Continuous.intervalIntegrable (by fun_prop) _ _),
      intervalIntegral.integral_div, intervalIntegral.integral_div,
      integral_pow, integral_pow]
  simp only [Nat.factorial_succ]
  push_cast
  field_simp
  ring

theorem RealDecrTrialPMF₀_real_nonneg {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (n : ℕ) :
    0 ≤ x ^ n / (n.factorial : ℝ) - x ^ (n + 1) / ((n + 1).factorial : ℝ) := by
  have hfact : ((n + 1).factorial : ℝ) = ((n : ℝ) + 1) * (n.factorial : ℝ) := by
    rw [Nat.factorial_succ]; push_cast; ring
  have hrw : x ^ (n + 1) / ((n + 1).factorial : ℝ)
      = (x ^ n / (n.factorial : ℝ)) * (x / ((n : ℝ) + 1)) := by
    rw [hfact, pow_succ]; field_simp
  rw [sub_nonneg, hrw]
  have hnn1 : 0 ≤ x ^ n / (n.factorial : ℝ) := by positivity
  have hyle : x / ((n : ℝ) + 1) ≤ 1 := by
    rw [div_le_one (by positivity)]; linarith [Nat.cast_nonneg (α := ℝ) n]
  exact mul_le_of_le_one_right hnn1 hyle

theorem RealDecrTrialPMF₀_real_parity (x : ℝ) :
    (∑' k : ℕ, (x ^ (2 * k) / ((2 * k).factorial : ℝ) - x ^ (2 * k + 1) / ((2 * k + 1).factorial : ℝ))
      = Real.exp (-x))
    ∧ (∑' k : ℕ, (x ^ (2 * k + 1) / ((2 * k + 1).factorial : ℝ)
        - x ^ (2 * k + 2) / ((2 * k + 2).factorial : ℝ)) = 1 - Real.exp (-x)) := by
  have hCe := x.hasSum_cosh.summable
  have hCo := x.hasSum_sinh.summable
  refine ⟨?_, ?_⟩
  ·
    rw [hCe.tsum_sub hCo, ← Real.cosh_eq_tsum, ← Real.sinh_eq_tsum, Real.cosh_sub_sinh]
  ·

    have hinj3 : Function.Injective (fun k : ℕ => 2 * k + 2) := by
      intro i j h; dsimp only at h; omega
    have hC2_summ : Summable (fun k => x ^ (2 * k + 2) / ((2 * k + 2).factorial : ℝ)) :=
      (Real.summable_pow_div_factorial x).comp_injective hinj3
    have hC2 : (∑' k, x ^ (2 * k + 2) / ((2 * k + 2).factorial : ℝ)) = Real.cosh x - 1 := by
      have hsplit := hCe.tsum_eq_zero_add
      simp only [Nat.mul_zero, Nat.factorial_zero, pow_zero] at hsplit
      have hreindex : (∑' n, x ^ (2 * (n + 1)) / ((2 * (n + 1)).factorial : ℝ))
          = ∑' k, x ^ (2 * k + 2) / ((2 * k + 2).factorial : ℝ) :=
        tsum_congr fun k => by rw [Nat.mul_succ]
      rw [Real.cosh_eq_tsum]
      linarith
    rw [hCo.tsum_sub hC2_summ, ← Real.sinh_eq_tsum, hC2]
    linarith [Real.cosh_sub_sinh x]

open MeasureTheory in

theorem RealDecrTrialPMF₀_setLIntegral {x : ℝ} (hx : 0 ≤ x ∧ x ≤ 1) (m : ℕ) :
    ∫⁻ y in Set.Icc 0 x, RealDecrTrialPMF₀ y m ∂volume = RealDecrTrialPMF₀ x (m + 1) := by
  have hcont : Continuous fun y : ℝ =>
      y ^ m / (m.factorial : ℝ) - y ^ (m + 1) / ((m + 1).factorial : ℝ) := by fun_prop
  have hnn : 0 ≤ᵐ[volume.restrict (Set.Icc 0 x)]
      fun y : ℝ => y ^ m / (m.factorial : ℝ) - y ^ (m + 1) / ((m + 1).factorial : ℝ) := by
    refine ae_restrict_of_forall_mem measurableSet_Icc fun y hy => ?_
    exact RealDecrTrialPMF₀_real_nonneg hy.1 (hy.2.trans hx.2) m
  simp only [RealDecrTrialPMF₀]
  rw [← ofReal_integral_eq_lintegral_ofReal (hcont.integrableOn_Icc) hnn,
      integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hx.1,
      RealDecrTrialPMF₀_real_integral]

end distribution

section creditExpectation

def RealDecrTrialCreditV (F : ℕ → ℝ≥0∞) (i : ℕ) (x : ℝ) : ℝ≥0∞ :=
  ∑' n : ℕ, RealDecrTrialPMF x i n * F n

theorem RealDecrTrialCreditV_nonneg (F : ℕ → ℝ≥0∞) (i : ℕ) (x : ℝ) :
    0 ≤ RealDecrTrialCreditV F i x := zero_le

theorem RealDecrTrialCreditV_reindex (F : ℕ → ℝ≥0∞) (i : ℕ) (x : ℝ) :
    RealDecrTrialCreditV F i x = ∑' m : ℕ, RealDecrTrialPMF₀ x m * F (i + m) := by
  unfold RealDecrTrialCreditV
  rw [← (add_right_injective i).tsum_eq (f := fun n => RealDecrTrialPMF x i n * F n) ?supp]
  · exact tsum_congr fun m => by
      rw [RealDecrTrialPMF_supp (Nat.le_add_right i m), Nat.add_sub_cancel_left]
  · intro n hn
    simp only [Function.mem_support, ne_eq] at hn
    have hin : i ≤ n := by
      by_contra h
      exact hn (by rw [RealDecrTrialPMF_not_supp (by omega), zero_mul])
    exact ⟨n - i, Nat.add_sub_cancel' hin⟩

theorem RealDecrTrialCreditV_parity (A B : ℝ≥0∞) {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    RealDecrTrialCreditV (fun n => if n % 2 = 0 then A else B) 0 x
      = ENNReal.ofReal (Real.exp (-x)) * A + ENNReal.ofReal (1 - Real.exp (-x)) * B := by
  obtain ⟨hpe, hpo⟩ := RealDecrTrialPMF₀_real_parity x
  have hCe := x.hasSum_cosh.summable
  have hCo := x.hasSum_sinh.summable
  have hinj3 : Function.Injective (fun k : ℕ => 2 * k + 2) := by
    intro i j h; dsimp only at h; omega
  have hC2_summ : Summable (fun k => x ^ (2 * k + 2) / ((2 * k + 2).factorial : ℝ)) :=
    (Real.summable_pow_div_factorial x).comp_injective hinj3

  have hEven : (∑' k, RealDecrTrialPMF₀ x (2 * k)) = ENNReal.ofReal (Real.exp (-x)) := by
    rw [← hpe, ENNReal.ofReal_tsum_of_nonneg (fun k => RealDecrTrialPMF₀_real_nonneg hx0 hx1 (2 * k))
        (hCe.sub hCo)]
    rfl
  have hOdd : (∑' k, RealDecrTrialPMF₀ x (2 * k + 1)) = ENNReal.ofReal (1 - Real.exp (-x)) := by
    rw [← hpo,
      ENNReal.ofReal_tsum_of_nonneg (fun k => RealDecrTrialPMF₀_real_nonneg hx0 hx1 (2 * k + 1))
        (hCo.sub hC2_summ)]
    rfl
  unfold RealDecrTrialCreditV
  simp only [RealDecrTrialPMF_base]
  rw [← tsum_even_add_odd (f := fun n => RealDecrTrialPMF₀ x n * if n % 2 = 0 then A else B)
      ENNReal.summable ENNReal.summable]
  congr 1
  · have heq : ∀ k, RealDecrTrialPMF₀ x (2 * k) * (if (2 * k) % 2 = 0 then A else B)
        = RealDecrTrialPMF₀ x (2 * k) * A := fun k => by rw [if_pos (by omega : (2 * k) % 2 = 0)]
    rw [tsum_congr heq, ENNReal.tsum_mul_right, hEven]
  · have heq : ∀ k, RealDecrTrialPMF₀ x (2 * k + 1) * (if (2 * k + 1) % 2 = 0 then A else B)
        = RealDecrTrialPMF₀ x (2 * k + 1) * B := fun k => by
      rw [if_neg (by omega : ¬ (2 * k + 1) % 2 = 0)]
    rw [tsum_congr heq, ENNReal.tsum_mul_right, hOdd]

end creditExpectation

section creditKernel

def RealDecrTrialCredit (F : ℕ → ℝ≥0∞) (i : ℕ) (x : ℝ) : ℝ → ℝ≥0∞ := fun y =>
  (if y ≤ x then RealDecrTrialCreditV F (i + 1) y else 0) +
  (if x ≤ y then F i else 0)

def RealDecrTrialCreditAmp (F : ℕ → ℝ≥0∞) (N : ℕ) (x : ℝ) (c : ℝ≥0∞) : ℝ → ℝ≥0∞ :=
  fun y => RealDecrTrialCredit F N x y + (if y < x then c else 0)

end creditKernel

section measurability

theorem measurable_realDecrTrialPMF₀ (n : ℕ) :
    Measurable (fun x : ℝ => RealDecrTrialPMF₀ x n) :=
  ENNReal.measurable_ofReal.comp (by fun_prop)

theorem measurable_realDecrTrialPMF (i n : ℕ) :
    Measurable (fun x : ℝ => RealDecrTrialPMF x i n) := by
  unfold RealDecrTrialPMF
  by_cases h : i ≤ n
  · simpa only [h, if_true] using measurable_realDecrTrialPMF₀ (n - i)
  · simpa only [h, if_false] using measurable_const

theorem measurable_realDecrTrialCreditV (F : ℕ → ℝ≥0∞) (i : ℕ) :
    Measurable (fun x : ℝ => RealDecrTrialCreditV F i x) :=
  Measurable.tsum fun n => (measurable_realDecrTrialPMF i n).mul_const (F n)

theorem measurable_realDecrTrialCredit (F : ℕ → ℝ≥0∞) (i : ℕ) (x : ℝ) :
    Measurable (RealDecrTrialCredit F i x) := by
  unfold RealDecrTrialCredit
  refine Measurable.add ?_ ?_
  · exact Measurable.ite measurableSet_Iic (measurable_realDecrTrialCreditV F (i + 1))
      measurable_const
  · exact Measurable.ite measurableSet_Ici measurable_const measurable_const

theorem measurable_realDecrTrialCreditAmp (F : ℕ → ℝ≥0∞) (N : ℕ) (x : ℝ) (c : ℝ≥0∞) :
    Measurable (RealDecrTrialCreditAmp F N x c) :=
  (measurable_realDecrTrialCredit F N x).add
    (Measurable.ite measurableSet_Iio measurable_const measurable_const)

open MeasureTheory in

theorem lintegral_ofReal_Icc {t : ℝ} (ht : 0 ≤ t) {g : ℝ → ℝ} (hg : Continuous g)
    (hgn : ∀ r ∈ Set.Icc (0 : ℝ) t, 0 ≤ g r) :
    ∫⁻ r in Set.Icc 0 t, ENNReal.ofReal (g r) ∂volume = ENNReal.ofReal (∫ r in (0 : ℝ)..t, g r) := by
  rw [← ofReal_integral_eq_lintegral_ofReal hg.integrableOn_Icc
        (ae_restrict_of_forall_mem measurableSet_Icc hgn),
      integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le ht]

open MeasureTheory in

@[simp]
theorem indicator_Iic_eq (x : ℝ) (f : ℝ → ℝ≥0∞) :
    (Set.Iic x).indicator f = fun y => if y ≤ x then f y else 0 := by
  ext y; simp only [Set.indicator_apply, Set.mem_Iic]

@[simp]
theorem indicator_Ici_eq (x : ℝ) (f : ℝ → ℝ≥0∞) :
    (Set.Ici x).indicator f = fun y => if x ≤ y then f y else 0 := by
  ext y; simp only [Set.indicator_apply, Set.mem_Ici]

@[simp]
theorem indicator_Iio_eq (x : ℝ) (f : ℝ → ℝ≥0∞) :
    (Set.Iio x).indicator f = fun y => if y < x then f y else 0 := by
  ext y; simp only [Set.indicator_apply, Set.mem_Iio]

end measurability

section conservation

open MeasureTheory in

theorem RealDecrTrialCredit_lintegral {F : ℕ → ℝ≥0∞} {M : ℝ≥0∞} {N : ℕ} {x : ℝ}
    (hx : 0 ≤ x ∧ x ≤ 1) (_hbound : ∀ n, F n ≤ M) :
    ∫⁻ y, RealDecrTrialCredit F N x y ∂(ProbLangℝ.unifUnit (T := ℝ)) =
      RealDecrTrialCreditV F N x := by
  obtain ⟨hx0, hx1⟩ := hx
  have hset2 : Set.Ici x ∩ Set.Icc (0 : ℝ) 1 = Set.Icc x 1 := by
    ext y; simp only [Set.mem_inter_iff, Set.mem_Ici, Set.mem_Icc]
    exact ⟨fun ⟨h1, _, h2⟩ => ⟨h1, h2⟩, fun ⟨h1, h2⟩ => ⟨h1, hx0.trans h1, h2⟩⟩
  have hset1 : Set.Iic x ∩ Set.Icc (0 : ℝ) 1 = Set.Icc 0 x := by
    ext y; simp only [Set.mem_inter_iff, Set.mem_Iic, Set.mem_Icc]
    exact ⟨fun ⟨h2, h1, _⟩ => ⟨h1, h2⟩, fun ⟨h1, h2⟩ => ⟨h2, h1, h2.trans hx1⟩⟩
  show ∫⁻ y, RealDecrTrialCredit F N x y ∂(volume.restrict (Set.Icc (0 : ℝ) 1)) = _
  simp only [RealDecrTrialCredit]
  rw [lintegral_add_left
      (Measurable.ite measurableSet_Iic (measurable_realDecrTrialCreditV F (N + 1)) measurable_const)]

  have hpart2 : (∫⁻ y, (if x ≤ y then F N else 0) ∂(volume.restrict (Set.Icc (0 : ℝ) 1)))
      = F N * RealDecrTrialPMF₀ x 0 := by
    rw [← indicator_Ici_eq, lintegral_indicator measurableSet_Ici, setLIntegral_const,
      Measure.restrict_apply measurableSet_Ici, hset2, Real.volume_Icc]
    rw [RealDecrTrialPMF₀]; norm_num

  have hpart1 : (∫⁻ y, (if y ≤ x then RealDecrTrialCreditV F (N + 1) y else 0)
        ∂(volume.restrict (Set.Icc (0 : ℝ) 1)))
      = ∑' m : ℕ, RealDecrTrialPMF₀ x (m + 1) * F (N + 1 + m) := by
    rw [← indicator_Iic_eq, lintegral_indicator measurableSet_Iic,
      Measure.restrict_restrict measurableSet_Iic, hset1]
    simp only [RealDecrTrialCreditV_reindex]
    rw [lintegral_tsum fun m =>
        ((measurable_realDecrTrialPMF₀ m).mul_const (F (N + 1 + m))).aemeasurable]
    exact tsum_congr fun m => by
      rw [lintegral_mul_const _ (measurable_realDecrTrialPMF₀ m),
        RealDecrTrialPMF₀_setLIntegral ⟨hx0, hx1⟩ m]
  rw [hpart1, hpart2, RealDecrTrialCreditV_reindex]
  have hsplit : (∑' m, RealDecrTrialPMF₀ x m * F (N + m))
      = RealDecrTrialPMF₀ x 0 * F N + ∑' m, RealDecrTrialPMF₀ x (m + 1) * F (N + (m + 1)) := by
    rw [tsum_eq_zero_add' ENNReal.summable, Nat.add_zero]
  rw [hsplit]
  have hkey : (∑' m, RealDecrTrialPMF₀ x (m + 1) * F (N + 1 + m))
      = ∑' m, RealDecrTrialPMF₀ x (m + 1) * F (N + (m + 1)) :=
    tsum_congr fun m => by rw [← Nat.add_assoc, Nat.add_right_comm]
  rw [hkey, add_comm (∑' m, RealDecrTrialPMF₀ x (m + 1) * F (N + (m + 1))) (F N * RealDecrTrialPMF₀ x 0),
      mul_comm (F N) (RealDecrTrialPMF₀ x 0)]

open MeasureTheory in

theorem RealDecrTrialCreditAmp_lintegral {F : ℕ → ℝ≥0∞} {M : ℝ≥0∞} {N : ℕ} {x : ℝ} {c : ℝ≥0∞}
    (hx : 0 ≤ x ∧ x ≤ 1) (hbound : ∀ n, F n ≤ M) :
    ∫⁻ y, RealDecrTrialCreditAmp F N x c y ∂(ProbLangℝ.unifUnit (T := ℝ)) =
      RealDecrTrialCreditV F N x + c * ENNReal.ofReal x := by
  obtain ⟨hx0, hx1⟩ := hx
  have hset : Set.Iio x ∩ Set.Icc (0 : ℝ) 1 = Set.Ico 0 x := by
    ext y; simp only [Set.mem_inter_iff, Set.mem_Iio, Set.mem_Icc, Set.mem_Ico]
    exact ⟨fun ⟨h2, h1, _⟩ => ⟨h1, h2⟩, fun ⟨h1, h2⟩ => ⟨h2, h1, h2.le.trans hx1⟩⟩
  show ∫⁻ y, RealDecrTrialCreditAmp F N x c y ∂(volume.restrict (Set.Icc (0 : ℝ) 1)) = _
  simp only [RealDecrTrialCreditAmp]
  rw [lintegral_add_left (measurable_realDecrTrialCredit F N x)]
  congr 1
  · exact RealDecrTrialCredit_lintegral ⟨hx0, hx1⟩ hbound
  · rw [← indicator_Iio_eq, lintegral_indicator measurableSet_Iio, setLIntegral_const,
        Measure.restrict_apply measurableSet_Iio, hset, Real.volume_Ico, sub_zero]

end conservation

section specification

theorem twp_DecrTrial_tail (E : CoPset) (F : ℕ → ℝ≥0∞) (M : ℝ≥0∞) (hnn : ∀ n, F n ≤ M)
    (B : ℝ) (hB0 : 0 < B) (hB1 : B < 1) :
    ⊢@{IProp GF} ∀ (N : ℕ) (x : ℝ), ⌜0 ≤ x⌝ -∗ ⌜x ≤ B⌝ -∗
      ↯ (RealDecrTrialCreditV F N x) -∗
      tglWp E pl(&DecrTrial #(.int (N : ℤ)) #(.real x))
        (fun v : Val ℝ => iprop(∃ n : ℕ, ⌜v.1 = .lit (.int (Int.ofNat n))⌝ ∗ ↯ (F n))) := by
  have hkpos : (0 : ℝ) ≤ 1 / B := by positivity
  set k : ℝ≥0 := ⟨1 / B, hkpos⟩ with hk_def
  have Hk1 : 1 < k := by
    have h : (1 : ℝ) < 1 / B := by rw [lt_div_iff₀ hB0]; linarith
    exact_mod_cast h
  iintro %N %x %Hx0 %HxB Hε_spec

  iapply twp_err_pos solve_not_red
  iintro %ε_term %Hε_pos Hε_term
  irevert Hε_spec
  irevert %HxB
  irevert %Hx0
  irevert %x
  irevert %N
  iapply ErrorCredit.Induction.simple (k := k) Hε_pos Hk1 $$ [] Hε_term
  imodintro
  iintro ⟨IH, Hε_term⟩ %N %x %Hx0 %HxB Hε_spec

  twp_pure
  twp_pure
  twp_pure
  twp_bind pl(urand)

  icombine Hε_spec Hε_term as Hε
  iapply (twp_urand_exp'
    (ε₂ := RealDecrTrialCreditAmp F N x ((k : ℝ≥0∞) * ε_term)) ?hmeas ?hint) $$ Hε
  case hmeas => exact measurable_realDecrTrialCreditAmp F N x _
  case hint =>
    rw [RealDecrTrialCreditAmp_lintegral ⟨Hx0, _root_.le_trans HxB hB1.le⟩ hnn]
    have hkx : (↑k : ℝ≥0∞) * ENNReal.ofReal x ≤ 1 := by
      have hkcast : (↑k : ℝ≥0∞) = ENNReal.ofReal (1 / B) := by
        rw [hk_def, ← ENNReal.ofReal_coe_nnreal]; rfl
      rw [hkcast, ← ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_le_one,
        div_mul_eq_mul_div, one_mul, div_le_one hB0]
      exact HxB
    gcongr
    calc (↑k * ε_term) * ENNReal.ofReal x
        = ε_term * ((↑k : ℝ≥0∞) * ENNReal.ofReal x) := by ring
      _ ≤ ε_term * 1 := mul_le_mul_right hkx ε_term
      _ = ε_term := mul_one _
  iintro %y ⟨%Hym, Hcy⟩
  have Hym01 : 0 < y ∧ y < 1 := mem_unifUnitSupport_real.mp Hym
  have Hyr : 0 ≤ y ∧ y ≤ 1 := ⟨Hym01.1.le, Hym01.2.le⟩

  twp_pures
  rcases hb : ProbLangℝ.realLt y x with _ | _
  ·
    twp_pures
    twp_value
    imodintro
    iexists N
    have hle : F N ≤ RealDecrTrialCreditAmp F N x ((k : ℝ≥0∞) * ε_term) y := by
      have hnlt : ¬ y < x := of_decide_eq_false hb
      have hxy : x ≤ y := _root_.not_lt.mp hnlt
      unfold RealDecrTrialCreditAmp RealDecrTrialCredit
      rw [if_pos hxy, if_neg hnlt, add_zero]
      exact le_add_self
    isplitr [Hcy]
    · ipureintro; rfl
    · iapply (ErrorCredit.weaken hle); iexact Hcy
  ·
    have hlt' : y < x := of_decide_eq_true hb
    twp_pure
    ihave Hcy' : iprop(↯ (RealDecrTrialCreditV F (N + 1) y + (k : ℝ≥0∞) * ε_term)) $$ [Hcy]
    ·
      have heq : RealDecrTrialCreditV F (N + 1) y + (k : ℝ≥0∞) * ε_term
          = RealDecrTrialCreditAmp F N x ((k : ℝ≥0∞) * ε_term) y := by
        unfold RealDecrTrialCreditAmp RealDecrTrialCredit
        rw [if_pos hlt'.le, if_neg (_root_.not_le.mpr hlt'), if_pos hlt', add_zero]
      rw [heq]; iexact Hcy
    ihave ⟨Hexp, Hterm⟩ := ErrorCredit.split (GF := GF) $$ Hcy'
    twp_pure
    rw [← Nat.cast_add_one]
    twp_bind pl(&DecrTrial #(.int ((N + 1 : ℕ) : ℤ)) #(.real y))
    iapply (tglWp_wand (Φ := fun v : Val ℝ => iprop(∃ n : ℕ,
      ⌜v.1 = .lit (.int (Int.ofNat n))⌝ ∗ ↯ (F n))))
    isplitl [Hexp Hterm IH]
    · iapply IH $$ Hterm
      · ipureintro; linarith [Hyr.1]
      · ipureintro; linarith [hlt'.le, HxB]
      · iexact Hexp
    iintro %w Hpost
    iapply tglWp_value
    iexact Hpost

theorem twp_DecrTrial (E : CoPset) (F : ℕ → ℝ≥0∞) (M : ℝ≥0∞) (Hnn : ∀ n, F n ≤ M)
    (N : ℕ) (x : ℝ) (Hx : 0 ≤ x ∧ x ≤ 1) :
    ⊢@{IProp GF} ↯ (RealDecrTrialCreditV F N x) -∗
      tglWp E pl(&DecrTrial #(.int (N : ℤ)) #(.real x))
        (fun v : Val ℝ => iprop(∃ n : ℕ, ⌜v.1 = .lit (.int (Int.ofNat n))⌝ ∗ ↯ (F n))) := by
  iintro Hε_spec

  twp_pure
  twp_pure
  twp_pure
  twp_bind pl(urand)
  iapply (twp_urand_exp' (ε₂ := RealDecrTrialCredit F N x) ?hmeas ?hint) $$ Hε_spec
  case hmeas => exact measurable_realDecrTrialCredit F N x
  case hint => exact _root_.le_of_eq (RealDecrTrialCredit_lintegral Hx Hnn)
  iintro %y ⟨%Hym, Hcy⟩
  have Hym01 : 0 < y ∧ y < 1 := mem_unifUnitSupport_real.mp Hym
  have Hyr : 0 ≤ y ∧ y ≤ 1 := ⟨Hym01.1.le, Hym01.2.le⟩
  twp_pures
  rcases hb : ProbLangℝ.realLt y x with _ | _
  ·
    twp_pures
    twp_value
    imodintro
    iexists N
    have hle : F N ≤ RealDecrTrialCredit F N x y := by
      have hxy : x ≤ y := _root_.not_lt.mp (of_decide_eq_false hb)
      unfold RealDecrTrialCredit
      rw [if_pos hxy]
      exact le_add_self
    isplitr [Hcy]
    · ipureintro; rfl
    · iapply (ErrorCredit.weaken hle); iexact Hcy
  ·

    have hlt' : y < x := of_decide_eq_true hb
    twp_pure
    ihave Hcy' : iprop(↯ (RealDecrTrialCreditV F (N + 1) y)) $$ [Hcy]
    ·
      have heq : RealDecrTrialCreditV F (N + 1) y = RealDecrTrialCredit F N x y := by
        unfold RealDecrTrialCredit
        rw [if_pos hlt'.le, if_neg (_root_.not_le.mpr hlt'), add_zero]
      rw [heq]; iexact Hcy
    have hy1 : y < 1 := _root_.lt_of_lt_of_le hlt' Hx.2
    have hy0 : 0 < y := Hym01.1
    twp_pure
    rw [← Nat.cast_add_one]
    twp_bind pl(&DecrTrial #(.int ((N + 1 : ℕ) : ℤ)) #(.real y))
    iapply (tglWp_wand (Φ := fun v : Val ℝ => iprop(∃ n : ℕ,
      ⌜v.1 = .lit (.int (Int.ofNat n))⌝ ∗ ↯ (F n))))
    isplitl [Hcy']
    · iapply (twp_DecrTrial_tail E F M Hnn y hy0 hy1)
      · ipureintro; exact Hyr.1
      · ipureintro; exact _root_.le_refl y
      · iexact Hcy'
    iintro %w Hpost
    iapply tglWp_value
    iexact Hpost

end specification

end
end Examples
end TotalEris
end ProbLang
