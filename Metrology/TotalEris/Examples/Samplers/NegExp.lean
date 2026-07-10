-- Negative-exponential sampler
module

public import Metrology.TotalEris
public import Metrology.ProbLang.Reals
public import Metrology.TotalEris.Examples.Samplers.RealDecrTrial

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
def NegExp : Exp ℝ := pl%
  rec trial L :=
    let x := urand;
    let y := &DecrTrial #0 x;
    if (y % #2 = #0) then (L, x) else trial (L + #1)

end program

section distribution

def NegExppdf₀ (k : ℕ) (x : ℝ) : ℝ≥0∞ :=
  if 0 ≤ x ∧ x ≤ 1 then .ofReal (Real.exp (-(x + k))) else 0

def NegExppdf (L k : ℕ) (x : ℝ) : ℝ≥0∞ :=
  if L ≤ k then NegExppdf₀ (k - L) x else 0

theorem NegExppdf₀_zero {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    NegExppdf₀ 0 x = ENNReal.ofReal (Real.exp (-x)) := by
  unfold NegExppdf₀
  rw [if_pos ⟨hx0, hx1⟩, Nat.cast_zero, add_zero]

theorem NegExppdf₀_succ {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (j : ℕ) :
    NegExppdf₀ (j + 1) x = ENNReal.ofReal (Real.exp (-1)) * NegExppdf₀ j x := by
  unfold NegExppdf₀
  rw [if_pos ⟨hx0, hx1⟩, if_pos ⟨hx0, hx1⟩, ← ENNReal.ofReal_mul (Real.exp_pos _).le,
    ← Real.exp_add]
  congr 2; push_cast; ring

def NegExpRejectProb : ℝ≥0∞ := .ofReal (Real.exp (-1))

def NegExpFactor : ℝ≥0 := ⟨Real.exp 1, (Real.exp_pos 1).le⟩

theorem one_lt_NegExpFactor : 1 < NegExpFactor := by
  rw [← NNReal.coe_lt_coe, NNReal.coe_one]
  show (1 : ℝ) < Real.exp 1
  linarith [Real.add_one_le_exp (1 : ℝ)]

theorem NegExpRejectProb_mul_NegExpFactor :
    NegExpRejectProb * (NegExpFactor : ℝ≥0∞) = 1 := by
  rw [NegExpRejectProb, ← ENNReal.ofReal_coe_nnreal (p := NegExpFactor),
      ← ENNReal.ofReal_mul (Real.exp_pos _).le]
  show ENNReal.ofReal (Real.exp (-1) * Real.exp 1) = 1
  rw [← Real.exp_add]
  norm_num

open MeasureTheory in

theorem NegExpReject_lintegral :
    ∫⁻ x, ENNReal.ofReal (1 - Real.exp (-x)) ∂(ProbLangℝ.unifUnit (T := ℝ))
      = ENNReal.ofReal (Real.exp (-1)) := by
  have h_exp : ∫ x in (0 : ℝ)..1, Real.exp (-x) = 1 - Real.exp (-1) := by
    rw [intervalIntegral.integral_comp_neg fun t => Real.exp t, integral_exp]
    simp only [neg_zero, Real.exp_zero]
  show ∫⁻ x in Set.Icc (0 : ℝ) 1, ENNReal.ofReal (1 - Real.exp (-x)) ∂volume = _
  rw [lintegral_ofReal_Icc (by norm_num) (by fun_prop) (fun x hx => by
        have : Real.exp (-x) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith [hx.1]); linarith)]
  congr 1
  rw [intervalIntegral.integral_sub intervalIntegrable_const
        (Continuous.intervalIntegrable (by fun_prop) _ _),
      intervalIntegral.integral_const, h_exp]
  simp only [smul_eq_mul, mul_one, sub_zero]
  ring

end distribution

section creditExpectation

open MeasureTheory in

def NegExpCreditV (F : ℕ → ℝ → ℝ≥0∞) (L : ℕ) : ℝ≥0∞ :=
  ∑' k : ℕ, ∫⁻ x, NegExppdf L k x * F k x ∂(ProbLangℝ.unifUnit (T := ℝ))

open MeasureTheory in

theorem NegExpCreditV_reindex (F : ℕ → ℝ → ℝ≥0∞) (L : ℕ) :
    NegExpCreditV F L = ∑' j : ℕ, ∫⁻ x, NegExppdf₀ j x * F (L + j) x ∂(ProbLangℝ.unifUnit (T := ℝ)) := by
  unfold NegExpCreditV
  rw [← (add_right_injective L).tsum_eq
        (f := fun k => ∫⁻ x, NegExppdf L k x * F k x ∂(ProbLangℝ.unifUnit (T := ℝ))) ?supp]
  · exact tsum_congr fun j => lintegral_congr fun x => by
      simp only [NegExppdf, if_pos (Nat.le_add_right L j), Nat.add_sub_cancel_left]
  · intro k hk
    simp only [Function.mem_support, ne_eq] at hk
    have hkL : L ≤ k := by
      by_contra h
      apply hk
      have hz : ∀ x, NegExppdf L k x * F k x = 0 := fun x => by
        simp only [NegExppdf, if_neg h, zero_mul]
      simp only [hz, lintegral_zero]
    exact ⟨k - L, Nat.add_sub_of_le hkL⟩

open MeasureTheory in

theorem NegExpCreditV_recurrence (F : ℕ → ℝ → ℝ≥0∞) (L : ℕ) :
    NegExpCreditV F L
      = (∫⁻ x, ENNReal.ofReal (Real.exp (-x)) * F L x ∂(ProbLangℝ.unifUnit (T := ℝ)))
        + ENNReal.ofReal (Real.exp (-1)) * NegExpCreditV F (L + 1) := by
  rw [NegExpCreditV_reindex F L,
    tsum_eq_zero_add' (f := fun j => ∫⁻ x, NegExppdf₀ j x * F (L + j) x ∂(ProbLangℝ.unifUnit (T := ℝ)))
      ENNReal.summable]
  congr 1
  · rw [Nat.add_zero]
    exact setLIntegral_congr_fun measurableSet_Icc
      (fun x hx => by rw [NegExppdf₀_zero hx.1 hx.2])
  · rw [NegExpCreditV_reindex F (L + 1), ← ENNReal.tsum_mul_left]
    refine tsum_congr fun j => ?_
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine setLIntegral_congr_fun measurableSet_Icc (fun x hx => ?_)
    have hidx : L + (j + 1) = L + 1 + j := by omega
    rw [NegExppdf₀_succ hx.1 hx.2, hidx, mul_assoc]

end creditExpectation

section creditKernel

def NegExpContAmp (F : ℕ → ℝ → ℝ≥0∞) (x : ℝ) (L : ℕ) (c : ℝ≥0∞) : ℕ → ℝ≥0∞ := fun z =>
  if z % 2 = 0 then F L x else NegExpCreditV F (L + 1) + c

end creditKernel

section measurability

open MeasureTheory in

theorem measurable_negExpContAmp (F : ℕ → ℝ → ℝ≥0∞) (hF : ∀ a, Measurable (F a))
    (L : ℕ) (c : ℝ≥0∞) :
    Measurable (fun x => RealDecrTrialCreditV (NegExpContAmp F x L c) 0 x) := by
  unfold RealDecrTrialCreditV
  refine Measurable.tsum fun n => (measurable_realDecrTrialPMF 0 n).mul ?_

  unfold NegExpContAmp
  by_cases h : n % 2 = 0
  · simpa only [h, if_true] using hF L
  · simpa only [h, if_false] using measurable_const

end measurability

section conservation

open MeasureTheory in

theorem NegExpCredit_recurrence (F : ℕ → ℝ → ℝ≥0∞) (L : ℕ) (c : ℝ≥0∞) :
    ∫⁻ x, RealDecrTrialCreditV (NegExpContAmp F x L c) 0 x ∂(ProbLangℝ.unifUnit (T := ℝ))
      = NegExpCreditV F L + NegExpRejectProb * c := by

  have key : ∫⁻ x, RealDecrTrialCreditV (NegExpContAmp F x L c) 0 x ∂(ProbLangℝ.unifUnit (T := ℝ))
      = ∫⁻ x, (ENNReal.ofReal (Real.exp (-x)) * F L x
          + ENNReal.ofReal (1 - Real.exp (-x)) * (NegExpCreditV F (L + 1) + c))
          ∂(ProbLangℝ.unifUnit (T := ℝ)) :=
    setLIntegral_congr_fun measurableSet_Icc (fun x hx => by
      exact RealDecrTrialCreditV_parity (F L x) (NegExpCreditV F (L + 1) + c) hx.1 hx.2)
  rw [key]

  have hmof : Measurable (fun x : ℝ => ENNReal.ofReal (1 - Real.exp (-x))) :=
    ENNReal.measurable_ofReal.comp (by fun_prop)
  have hmg : Measurable (fun x : ℝ =>
      ENNReal.ofReal (1 - Real.exp (-x)) * (NegExpCreditV F (L + 1) + c)) := hmof.mul_const _
  rw [lintegral_add_right _ hmg, lintegral_mul_const _ hmof,
      NegExpReject_lintegral, NegExpCreditV_recurrence F L]
  simp only [NegExpRejectProb]
  ring

end conservation

section specification

theorem twp_NegExp (E : CoPset) (F : ℕ → ℝ → ℝ≥0∞) (M : ℝ≥0∞)
    (hnn : ∀ a b, 0 ≤ b → b ≤ 1 → F a b ≤ M) (hFm : ∀ a, Measurable (F a)) (L : ℕ) :
    ⊢@{IProp GF} ↯ (NegExpCreditV F L) -∗
      tglWp E pl(&NegExp #(.int (L : ℤ)))
        (fun p : Val ℝ => iprop(∃ (vz : ℕ) (vr : ℝ),
          ⌜p.1 = .pair (.lit (.int (Int.ofNat vz))) (.lit (.real vr))⌝ ∗
          ⌜0 ≤ vr ∧ vr < 1⌝ ∗ ↯ (F vz vr))) := by
  iintro Hε_spec

  iapply twp_err_pos solve_not_red
  iintro %ε_term %Hε_term_pos Hε_term
  set k : ℝ≥0 := NegExpFactor
  have Hk1 : 1 < k := one_lt_NegExpFactor
  irevert Hε_spec
  irevert %L
  iapply ErrorCredit.Induction.simple (k := k) Hε_term_pos Hk1 $$ [] Hε_term
  imodintro
  iintro ⟨IH, Hε_term⟩ %L Hε_spec
  twp_pure
  twp_pure
  twp_bind pl(urand)

  icombine Hε_spec Hε_term as Hε
  iapply (twp_urand_exp'
    (ε₂ := fun x => RealDecrTrialCreditV (NegExpContAmp F x L ((k : ℝ≥0∞) * ε_term)) 0 x)
    (measurable_negExpContAmp F hFm L _) ?hint) $$ Hε
  case hint =>
    rw [NegExpCredit_recurrence, ← mul_assoc, NegExpRejectProb_mul_NegExpFactor, one_mul]
  iintro %x ⟨%Hxm, Hcx⟩
  have Hx01 : 0 < x ∧ x < 1 := mem_unifUnitSupport_real.mp Hxm
  have Hxr : 0 ≤ x ∧ x ≤ 1 := ⟨Hx01.1.le, Hx01.2.le⟩
  twp_pure
  twp_bind pl(&DecrTrial #(.int (0 : ℤ)) #(.real x))
  have HnnAmp : ∀ n, NegExpContAmp F x L ((k : ℝ≥0∞) * ε_term) n
      ≤ M + (NegExpCreditV F (L + 1) + (k : ℝ≥0∞) * ε_term) := by
    intro n
    unfold NegExpContAmp
    by_cases h : n % 2 = 0
    · rw [if_pos h]; exact _root_.le_trans (hnn L x Hxr.1 Hxr.2) le_self_add
    · rw [if_neg h]; exact le_add_self
  iapply (tglWp_wand (Φ := fun v : Val ℝ => iprop(∃ n : ℕ,
    ⌜v.1 = .lit (.int (Int.ofNat n))⌝ ∗ ↯ (NegExpContAmp F x L ((k : ℝ≥0∞) * ε_term) n))))
  isplitl [Hcx]
  · iapply (twp_DecrTrial E (NegExpContAmp F x L ((k : ℝ≥0∞) * ε_term))
      (M + (NegExpCreditV F (L + 1) + (k : ℝ≥0∞) * ε_term)) HnnAmp 0 x Hxr) $$ Hcx
  iintro %w ⟨%n, %hn, Hcn⟩
  rcases w with ⟨w, hwlc⟩
  simp only at hn; subst hn

  twp_pures
  rcases Nat.mod_two_eq_zero_or_one n with hpar | hpar
  ·
    have hmod : (Int.ofNat n % 2 : ℤ) = 0 := by
      simp only [Int.ofNat_eq_natCast]; omega
    rw [hmod]
    twp_pures
    twp_value
    imodintro
    iexists L, x
    have hcn : NegExpContAmp F x L ((k : ℝ≥0∞) * ε_term) n = F L x := by
      simp only [NegExpContAmp]; rw [if_pos hpar]
    rw [← hcn]
    isplitr [Hcn]
    · ipureintro; rfl
    · isplitr [Hcn]
      · ipureintro; exact ⟨Hx01.1.le, Hx01.2⟩
      · iexact Hcn
  ·
    have hmod : (Int.ofNat n % 2 : ℤ) = 1 := by
      simp only [Int.ofNat_eq_natCast]; omega
    rw [hmod]
    have hcn : NegExpContAmp F x L ((k : ℝ≥0∞) * ε_term) n
        = NegExpCreditV F (L + 1) + (k : ℝ≥0∞) * ε_term := by
      simp only [NegExpContAmp]; rw [if_neg (by omega)]
    ihave Hcn' : iprop(↯ (NegExpCreditV F (L + 1) + (k : ℝ≥0∞) * ε_term)) $$ [Hcn]
    · rw [← hcn]; iexact Hcn
    ihave ⟨Hexp, Hterm⟩ := ErrorCredit.split (GF := GF) $$ Hcn'
    twp_pure
    twp_pure
    have hL : ((L : ℤ) + 1) = ((L + 1 : ℕ) : ℤ) := by push_cast; ring
    rw [hL]
    twp_bind pl(&NegExp #(.int ((L + 1 : ℕ) : ℤ)))
    iapply (tglWp_wand (Φ := fun p : Val ℝ => iprop(∃ (vz : ℕ) (vr : ℝ),
      ⌜p.1 = .pair (.lit (.int (Int.ofNat vz))) (.lit (.real vr))⌝ ∗
      ⌜0 ≤ vr ∧ vr < 1⌝ ∗ ↯ (F vz vr))))
    isplitl [Hexp Hterm IH]
    · iapply IH $$ Hterm
      iexact Hexp
    iintro %w Hpost
    iapply tglWp_value
    iexact Hpost

end specification

end
end Examples
end TotalEris
end ProbLang
