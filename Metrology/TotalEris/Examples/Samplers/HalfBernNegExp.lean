-- Bernoulli with base-½ negative-exponential bias
module

public import Metrology.TotalEris
public import Metrology.ProbLang.Reals
public import Metrology.TotalEris.Examples.Samplers.RealDecrTrial
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

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

def LeHalfSpec (r : ℝ) : Bool := decide (r ≤ 1 / 2)

@[pl_fold]
def LeHalf : Exp ℝ := pl% fun x, x <= #(.real (1 / 2 : ℝ))

@[pl_fold]
def BNEHalf : Exp ℝ := pl%
  fun _u,
    let x := urand;
    if &LeHalf x then
      let y := &DecrTrial #0 x;
      (y % #2 = #1)
    else #true

end program

section distribution

def BNEHalfPMF (b : Bool) : ℝ≥0∞ :=
  if b then .ofReal (Real.exp (-1 / 2)) else .ofReal (1 - Real.exp (-1 / 2))

end distribution

section creditExpectation

def BNEHalfCreditV (F : Bool → ℝ≥0∞) : ℝ≥0∞ :=
  F true * BNEHalfPMF true + F false * BNEHalfPMF false

end creditExpectation

section creditKernel

def LiftF (F : Bool → ℝ≥0∞) : ℕ → ℝ≥0∞ := fun n => F (n % 2 == 1)

def BNEHalfCredit (F : Bool → ℝ≥0∞) : ℝ → ℝ≥0∞ := fun r =>
  (if r ≤ 1 / 2 then RealDecrTrialCreditV (LiftF F) 0 r else 0) +
  (if ¬ r ≤ 1 / 2 then F true else 0)

end creditKernel

section measurability

theorem measurable_bneHalfCredit (F : Bool → ℝ≥0∞) : Measurable (BNEHalfCredit F) := by
  unfold BNEHalfCredit
  refine Measurable.add ?_ ?_
  · exact Measurable.ite measurableSet_Iic
      (measurable_realDecrTrialCreditV (LiftF F) 0) measurable_const
  · exact Measurable.ite measurableSet_Iic.compl measurable_const measurable_const

open MeasureTheory in

theorem lintegral_unifUnit_indicator {s : Set ℝ} (hs : MeasurableSet s) (f : ℝ → ℝ≥0∞) :
    ∫⁻ r, s.indicator f r ∂(volume.restrict (Set.Icc (0 : ℝ) 1))
      = ∫⁻ r in s ∩ Set.Icc 0 1, f r ∂volume := by
  rw [lintegral_indicator hs, Measure.restrict_restrict hs]

end measurability

section conservation

open MeasureTheory in

theorem BNEHalfCredit_lintegral {F : Bool → ℝ≥0∞} {M : ℝ≥0∞} (hbound : ∀ b, F b ≤ M) :
    ∫⁻ r, BNEHalfCredit F r ∂(ProbLangℝ.unifUnit (T := ℝ)) = BNEHalfCreditV F := by

  have hlift : LiftF F = fun n => if n % 2 = 0 then F false else F true := by
    funext n
    rcases Nat.mod_two_eq_zero_or_one n with h | h
    · simp [LiftF, h]
    · simp [LiftF, h]

  have hexphalf : ∫ r in (0 : ℝ)..(1 / 2), Real.exp (-r) = 1 - Real.exp (-1 / 2) := by
    rw [intervalIntegral.integral_comp_neg fun x => Real.exp x, neg_zero,
        integral_exp, Real.exp_zero]
    norm_num
  have hsetA : Set.Iic (1 / 2 : ℝ) ∩ Set.Icc (0 : ℝ) 1 = Set.Icc 0 (1 / 2) := by
    ext r; simp only [Set.mem_inter_iff, Set.mem_Iic, Set.mem_Icc]
    exact ⟨fun ⟨h2, h1, _⟩ => ⟨h1, h2⟩, fun ⟨h1, h2⟩ => ⟨h2, h1, by linarith⟩⟩
  have hsetB : Set.Ioi (1 / 2 : ℝ) ∩ Set.Icc (0 : ℝ) 1 = Set.Ioc (1 / 2) 1 := by
    ext r; simp only [Set.mem_inter_iff, Set.mem_Ioi, Set.mem_Icc, Set.mem_Ioc]
    exact ⟨fun ⟨h2, _, h1⟩ => ⟨h2, h1⟩, fun ⟨h2, h1⟩ => ⟨h2, by linarith, h1⟩⟩
  show ∫⁻ r, BNEHalfCredit F r ∂(volume.restrict (Set.Icc (0 : ℝ) 1)) = _
  simp only [BNEHalfCredit]
  rw [lintegral_add_left (Measurable.ite measurableSet_Iic
        (measurable_realDecrTrialCreditV (LiftF F) 0) measurable_const)]

  have hB : (∫⁻ r, (if ¬ r ≤ 1 / 2 then F true else 0) ∂(volume.restrict (Set.Icc (0 : ℝ) 1)))
      = ENNReal.ofReal (1 / 2) * F true := by
    have hind : (fun r => if ¬ r ≤ 1 / 2 then F true else 0)
        = (Set.Ioi (1 / 2 : ℝ)).indicator (fun _ => F true) := by
      ext r; simp only [Set.indicator_apply, Set.mem_Ioi, _root_.not_le]
    rw [hind, lintegral_unifUnit_indicator measurableSet_Ioi (fun _ => F true), hsetB,
        setLIntegral_const, Real.volume_Ioc, mul_comm]
    norm_num

  have hA : (∫⁻ r, (if r ≤ 1 / 2 then RealDecrTrialCreditV (LiftF F) 0 r else 0)
        ∂(volume.restrict (Set.Icc (0 : ℝ) 1)))
      = ENNReal.ofReal (1 - Real.exp (-1 / 2)) * F false
        + ENNReal.ofReal (Real.exp (-1 / 2) - 1 / 2) * F true := by
    have hind : (fun r => if r ≤ 1 / 2 then RealDecrTrialCreditV (LiftF F) 0 r else 0)
        = (Set.Iic (1 / 2 : ℝ)).indicator (RealDecrTrialCreditV (LiftF F) 0) := by
      ext r; simp only [Set.indicator_apply, Set.mem_Iic]
    rw [hind, lintegral_unifUnit_indicator measurableSet_Iic (RealDecrTrialCreditV (LiftF F) 0),
        hsetA, setLIntegral_congr_fun (g := fun x => ENNReal.ofReal (Real.exp (-x)) * F false
          + ENNReal.ofReal (1 - Real.exp (-x)) * F true) measurableSet_Icc fun r hr => by
        rw [hlift]
        exact RealDecrTrialCreditV_parity (F false) (F true) hr.1 (hr.2.trans (by norm_num))]
    have hmexp : Measurable (fun r : ℝ => ENNReal.ofReal (Real.exp (-r))) :=
      ENNReal.measurable_ofReal.comp (by fun_prop)
    have hmexp' : Measurable (fun r : ℝ => ENNReal.ofReal (1 - Real.exp (-r))) :=
      ENNReal.measurable_ofReal.comp (by fun_prop)
    have hintsub : ∫ r in (0 : ℝ)..(1 / 2), (1 - Real.exp (-r)) = Real.exp (-1 / 2) - 1 / 2 := by
      rw [intervalIntegral.integral_sub intervalIntegrable_const
            (Continuous.intervalIntegrable (by fun_prop) _ _),
          intervalIntegral.integral_const, hexphalf]
      simp only [smul_eq_mul, mul_one, sub_zero]
      ring
    rw [lintegral_add_left (hmexp.mul_const _), lintegral_mul_const _ hmexp,
        lintegral_mul_const _ hmexp',
        lintegral_ofReal_Icc (by norm_num) (by fun_prop) fun r _ => (Real.exp_pos _).le,
        hexphalf,
        lintegral_ofReal_Icc (by norm_num) (by fun_prop) fun r hr =>
          sub_nonneg.mpr (Real.exp_le_one_iff.mpr (neg_nonpos.mpr hr.1)),
        hintsub]
  rw [hA, hB]

  have hexp_ge : (0 : ℝ) ≤ Real.exp (-1 / 2) - 1 / 2 := by
    have := Real.add_one_le_exp (-1 / 2 : ℝ); linarith
  have ht : BNEHalfPMF true = ENNReal.ofReal (Real.exp (-1 / 2)) := rfl
  have hf : BNEHalfPMF false = ENNReal.ofReal (1 - Real.exp (-1 / 2)) := rfl
  rw [BNEHalfCreditV, ht, hf, add_assoc, ← add_mul,
      ← ENNReal.ofReal_add hexp_ge (by norm_num)]
  ring_nf

end conservation

section specification

theorem twp_LeHalf (E : CoPset) (r : ℝ) :
    ⊢@{IProp GF} tglWp E pl(&LeHalf #(.real r))
      (fun v : Val ℝ => iprop(⌜v.1 = .lit (.bool (LeHalfSpec r))⌝)) := by
  twp_pures
  twp_value
  imodintro
  ipureintro
  rfl

theorem twp_BNEHalf (E : CoPset) (F : Bool → ℝ≥0∞) (M : ℝ≥0∞) (Hnn : ∀ b, F b ≤ M) :
    ⊢@{IProp GF} ↯ (BNEHalfCreditV F) -∗
      tglWp E pl(&BNEHalf #.unit)
        (fun v : Val ℝ => iprop(∃ b : Bool, ⌜v.1 = .lit (.bool b)⌝ ∗ ↯ (F b))) := by
  iintro Hε

  twp_pure
  twp_bind pl(urand)

  iapply (twp_urand_exp' (ε₂ := BNEHalfCredit F) ?hmeas ?hint) $$ Hε
  case hmeas => exact measurable_bneHalfCredit F
  case hint => rw [BNEHalfCredit_lintegral (M := M) Hnn]
  iintro %r ⟨%Hrm, Hcr⟩

  have Hr01 : 0 < r ∧ r < 1 := mem_unifUnitSupport_real.mp Hrm
  have Hr : 0 ≤ r ∧ r ≤ 1 := ⟨Hr01.1.le, Hr01.2.le⟩

  twp_pure
  twp_bind pl(&LeHalf #(.real r))
  iapply (tglWp_wand (Φ := fun v : Val ℝ => iprop(⌜v.1 = .lit (.bool (LeHalfSpec r))⌝)))
  isplitl []
  · iapply twp_LeHalf
  iintro %v %hv
  rcases v with ⟨w, hwlc⟩
  simp only at hv

  generalize hbdef : LeHalfSpec r = b at hv
  subst hv
  rcases b with _ | _
  ·
    have hle : ¬ r ≤ 1 / 2 := of_decide_eq_false hbdef
    twp_pures
    twp_value
    imodintro
    iexists true
    have hcr : BNEHalfCredit F r = F true := by
      simp only [BNEHalfCredit, hle, if_false, if_true, not_false_iff, zero_add]

    rw [← hcr]
    iframe Hcr
    itrivial
  ·
    have hle : r ≤ 1 / 2 := of_decide_eq_true hbdef
    have hcr : BNEHalfCredit F r = RealDecrTrialCreditV (LiftF F) 0 r := by
      simp only [BNEHalfCredit, hle, if_true, not_true, if_false, add_zero]

    ihave Hcr' : iprop(↯ (RealDecrTrialCreditV (LiftF F) 0 r)) $$ [Hcr]
    · rw [← hcr]; iexact Hcr

    twp_pure
    twp_bind pl(&DecrTrial #(.int (0 : ℤ)) #(.real r))
    iapply (tglWp_wand (Φ := fun v : Val ℝ => iprop(∃ n : ℕ,
      ⌜v.1 = .lit (.int (Int.ofNat n))⌝ ∗ ↯ (LiftF F n))))
    isplitl [Hcr']
    · iapply (twp_DecrTrial E (LiftF F) M (fun n => Hnn _) 0 r Hr) $$ Hcr'
    iintro %w' ⟨%n, %hn, Hcrn⟩
    rcases w' with ⟨w', hwlc'⟩
    simp only at hn; subst hn

    twp_pures
    rcases Nat.mod_two_eq_zero_or_one n with hpar | hpar
    ·
      have hmod : (Int.ofNat n : ℤ) % 2 = 0 := by
        have h2 : ((n : ℤ)) % 2 = ((n % 2 : ℕ) : ℤ) := by push_cast [Int.natCast_mod]; ring
        simp [Int.ofNat_eq_natCast, h2, hpar]
      rw [hmod]
      twp_value
      imodintro
      iexists false
      have hlf : LiftF F n = F false := by simp only [LiftF, hpar]; rfl
      rw [← hlf]
      iframe Hcrn
      itrivial
    ·
      have hmod : (Int.ofNat n : ℤ) % 2 = 1 := by
        have h2 : ((n : ℤ)) % 2 = ((n % 2 : ℕ) : ℤ) := by push_cast [Int.natCast_mod]; ring
        simp [Int.ofNat_eq_natCast, h2, hpar]
      rw [hmod]
      twp_pures
      twp_value
      imodintro
      iexists true
      have hlf : LiftF F n = F true := by simp only [LiftF, hpar]; rfl
      rw [← hlf]
      iframe Hcrn
      itrivial

end specification

end
end Examples
end TotalEris
end ProbLang
