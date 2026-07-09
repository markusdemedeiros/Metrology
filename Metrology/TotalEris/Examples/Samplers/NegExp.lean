module

public import Metrology.TotalEris
public import Metrology.ProbLang.Reals
public import Metrology.TotalEris.Examples.Samplers.RealDecrTrial

@[expose] public section

/-!
# Negative-exponential sampler

`NegExp L` samples a non-negative real from a (right-shifted) negative
exponential, returned split as an integer part `vz` and a fractional part
`vr ∈ [0,1)`: sample `x ← urand`, run a `DecrTrial` from `x` to get `y`; if `y`
is even return `(L, x)`, else recurse at `L+1`.

Fixed at `rT = ℝ`. Credit functions are `ℕ → ℝ → ℝ≥0∞` (integer + fractional).
-/

open Std Iris Iris.Std Iris.BI Iris.ProofMode OFE COFE ProbLang ProbLang.TotalEris
  ProbLang.TotalEris.ErisWpGS
open scoped AppGS ENNReal NNReal

namespace ProbLang
namespace TotalEris
namespace Examples

noncomputable section

variable {hlc : HasLC} {GF : BundledGFunctors.{0,0,0}} [ErisGS ℝ hlc GF]

/-! ## Program -/
@[pl_fold]
def NegExp : Exp ℝ := pl%
  rec trial L :=
    let x := urand;
    let y := &DecrTrial #0 x;
    if (y % #2 = #0) then (L, x) else trial (L + #1)

/-! ## Density and credits -/

/-- Negative-exponential density started at `0`:
`[0 ≤ x ≤ 1] · exp (-(x + k))`. -/
def NegExpρ0 (k : ℕ) (x : ℝ) : ℝ≥0∞ :=
  if 0 ≤ x ∧ x ≤ 1 then .ofReal (Real.exp (-(x + k))) else 0

/-- Negative-exponential density right-shifted by `L`:
`[L ≤ k] · NegExpρ0 (k - L) x`. -/
def NegExpρ (L k : ℕ) (x : ℝ) : ℝ≥0∞ :=
  if L ≤ k then NegExpρ0 (k - L) x else 0

/-- On `[0,1]`, `NegExpρ0 0 x` is `exp(-x)` (the `0 ≤ x ≤ 1` guard fires, `x + 0 = x`). -/
theorem NegExpρ0_zero {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    NegExpρ0 0 x = ENNReal.ofReal (Real.exp (-x)) := by
  unfold NegExpρ0; rw [if_pos ⟨hx0, hx1⟩]; congr 2; push_cast; ring

/-- On `[0,1]`, `NegExpρ0 (j+1)` factors an `exp(-1)` off `NegExpρ0 j`. -/
theorem NegExpρ0_succ {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (j : ℕ) :
    NegExpρ0 (j + 1) x = ENNReal.ofReal (Real.exp (-1)) * NegExpρ0 j x := by
  unfold NegExpρ0
  rw [if_pos ⟨hx0, hx1⟩, if_pos ⟨hx0, hx1⟩, ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
  congr 2; push_cast; ring

open MeasureTheory in
/-- Credit expectation `∑ₖ ∫₀¹ NegExpρ L k x · F k x dx`. -/
def NegExpCreditV (F : ℕ → ℝ → ℝ≥0∞) (L : ℕ) : ℝ≥0∞ :=
  ∑' k : ℕ, ∫⁻ x, NegExpρ L k x * F k x ∂(ProbLangℝ.unifUnit (T := ℝ))

open MeasureTheory in
/-- `NegExpCreditV` reindexed as a shift, dropping the `L ≤ k` guard. -/
theorem NegExpCreditV_reindex (F : ℕ → ℝ → ℝ≥0∞) (L : ℕ) :
    NegExpCreditV F L = ∑' j : ℕ, ∫⁻ x, NegExpρ0 j x * F (L + j) x ∂(ProbLangℝ.unifUnit (T := ℝ)) := by
  unfold NegExpCreditV
  rw [← (add_right_injective L).tsum_eq
        (f := fun k => ∫⁻ x, NegExpρ L k x * F k x ∂(ProbLangℝ.unifUnit (T := ℝ))) ?supp]
  · exact tsum_congr fun j => lintegral_congr fun x => by
      rw [show NegExpρ L (L + j) x = NegExpρ0 j x from by
        simp only [NegExpρ, if_pos (Nat.le_add_right L j), Nat.add_sub_cancel_left]]
  · intro k hk
    simp only [Function.mem_support, ne_eq] at hk
    have hkL : L ≤ k := by
      by_contra h
      apply hk
      have hz : ∀ x, NegExpρ L k x * F k x = 0 := fun x => by
        rw [show NegExpρ L k x = 0 from by simp only [NegExpρ, if_neg h], zero_mul]
      simp only [hz, lintegral_zero]
    exact ⟨k - L, by show L + (k - L) = k; omega⟩

open MeasureTheory in
/-- `NegExpCreditV` one-step recurrence: peel the `j = 0` answer term, factor `exp(-1)`
off the reject tail. -/
theorem NegExpCreditV_recurrence (F : ℕ → ℝ → ℝ≥0∞) (L : ℕ) :
    NegExpCreditV F L
      = (∫⁻ x, ENNReal.ofReal (Real.exp (-x)) * F L x ∂(ProbLangℝ.unifUnit (T := ℝ)))
        + ENNReal.ofReal (Real.exp (-1)) * NegExpCreditV F (L + 1) := by
  rw [NegExpCreditV_reindex F L,
    tsum_eq_zero_add' (f := fun j => ∫⁻ x, NegExpρ0 j x * F (L + j) x ∂(ProbLangℝ.unifUnit (T := ℝ)))
      ENNReal.summable]
  congr 1
  · rw [Nat.add_zero]
    exact setLIntegral_congr_fun measurableSet_Icc
      (fun x hx => by rw [NegExpρ0_zero hx.1 hx.2])
  · rw [NegExpCreditV_reindex F (L + 1), ← ENNReal.tsum_mul_left]
    refine tsum_congr fun j => ?_
    rw [show (∫⁻ x, NegExpρ0 (j + 1) x * F (L + (j + 1)) x ∂(ProbLangℝ.unifUnit (T := ℝ)))
          = ∫⁻ x, ENNReal.ofReal (Real.exp (-1)) * (NegExpρ0 j x * F (L + 1 + j) x)
              ∂(ProbLangℝ.unifUnit (T := ℝ)) from
        setLIntegral_congr_fun measurableSet_Icc (fun x hx => by
          rw [NegExpρ0_succ hx.1 hx.2, show L + (j + 1) = L + 1 + j from by omega, mul_assoc]),
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]

/-- Per-iteration **rejection** (odd-parity) probability `= exp (-1)`: the
closed form of the odd-indexed `DecrTrial` mass. -/
def NegExpRejectProb : ℝ≥0∞ := .ofReal (Real.exp (-1))

/-- Termination amplification factor `= exp 1 = 1 / exp (-1)`: recursion is
guarded behind the reject event (probability `exp (-1)`), so the remaining
credit may be amplified by its reciprocal. -/
def NegExpFactor : ℝ≥0 := ⟨Real.exp 1, (Real.exp_pos 1).le⟩

/-- `1 < NegExpFactor` (since `1 < exp 1`). -/
theorem one_lt_NegExpFactor : 1 < NegExpFactor := by
  rw [← NNReal.coe_lt_coe, NNReal.coe_one]
  show (1 : ℝ) < Real.exp 1
  have := Real.add_one_le_exp (1 : ℝ)
  linarith

/-- `exp (-1) · exp 1 = 1`: the reject probability times the amplification factor
collapses to one, exactly as `γ · (1/γ) = 1` does in `BernoulliGeometric`. -/
theorem NegExpRejectProb_mul_NegExpFactor :
    NegExpRejectProb * (NegExpFactor : ℝ≥0∞) = 1 := by
  unfold NegExpRejectProb
  rw [← ENNReal.ofReal_coe_nnreal (p := NegExpFactor), ← ENNReal.ofReal_mul (Real.exp_pos _).le]
  have h : Real.exp (-1) * (NegExpFactor : ℝ) = 1 := by
    show Real.exp (-1) * Real.exp 1 = 1
    rw [← Real.exp_add]; norm_num
  rw [h, ENNReal.ofReal_one]

/-- Amplified per-`DecrTrial`-result credit: on an **even** result (accept) the
answer cost `F L x`; on an **odd** result (reject/recurse) the continuation cost
`NegExpCreditV F (L+1)` topped up by a termination credit `c`. This is the
`Famp`-analogue of `BernoulliGeometric`, specialised to the parity event. -/
def NegExpAmp (F : ℕ → ℝ → ℝ≥0∞) (x : ℝ) (L : ℕ) (c : ℝ≥0∞) : ℕ → ℝ≥0∞ := fun z =>
  if z % 2 = 0 then F L x else NegExpCreditV F (L + 1) + c

open MeasureTheory in
/-- The per-iteration reject probability: `∫₀¹ (1 - exp(-x)) dx = exp(-1)`. -/
theorem NegExpReject_lintegral :
    ∫⁻ x, ENNReal.ofReal (1 - Real.exp (-x)) ∂(ProbLangℝ.unifUnit (T := ℝ))
      = ENNReal.ofReal (Real.exp (-1)) := by
  show ∫⁻ x in Set.Icc (0 : ℝ) 1, ENNReal.ofReal (1 - Real.exp (-x)) ∂volume = _
  rw [lintegral_ofReal_Icc (by norm_num) (by fun_prop) (fun x hx => by
        have : Real.exp (-x) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith [hx.1]); linarith),
    show (∫ x in (0 : ℝ)..1, (1 - Real.exp (-x))) = Real.exp (-1) from by
      rw [intervalIntegral.integral_sub intervalIntegrable_const
            (Continuous.intervalIntegrable (by fun_prop) _ _),
          intervalIntegral.integral_const,
          show (∫ x in (0 : ℝ)..1, Real.exp (-x)) = 1 - Real.exp (-1) from by
            rw [intervalIntegral.integral_comp_neg fun t => Real.exp t]
            simp only [neg_zero]; rw [integral_exp, Real.exp_zero]]
      simp only [smul_eq_mul, mul_one, sub_zero]; ring]

open MeasureTheory in
/-- The `NegExp` credit recurrence: integrating the amplified `DecrTrial` budget
over the fresh uniform sample `x` splits into the answer expectation
`NegExpCreditV F L` plus the reject-weighted continuation `exp(-1) · c`. -/
theorem NegExp_credit_recurrence (F : ℕ → ℝ → ℝ≥0∞) (L : ℕ) (c : ℝ≥0∞) :
    ∫⁻ x, RealDecrTrialCreditV (NegExpAmp F x L c) 0 x ∂(ProbLangℝ.unifUnit (T := ℝ))
      = NegExpCreditV F L + NegExpRejectProb * c := by
  -- Parity closed form of the integrand on `[0,1]`.
  rw [show (∫⁻ x, RealDecrTrialCreditV (NegExpAmp F x L c) 0 x ∂(ProbLangℝ.unifUnit (T := ℝ)))
        = ∫⁻ x, (ENNReal.ofReal (Real.exp (-x)) * F L x
            + ENNReal.ofReal (1 - Real.exp (-x)) * (NegExpCreditV F (L + 1) + c))
            ∂(ProbLangℝ.unifUnit (T := ℝ)) from
      setLIntegral_congr_fun measurableSet_Icc (fun x hx => by
        exact RealDecrTrialCreditV_parity (F L x) (NegExpCreditV F (L + 1) + c) hx.1 hx.2)]
  -- Split off the reject term (right summand is `x`-measurable).
  have hmof : Measurable (fun x : ℝ => ENNReal.ofReal (1 - Real.exp (-x))) :=
    ENNReal.measurable_ofReal.comp (by fun_prop)
  have hmg : Measurable (fun x : ℝ =>
      ENNReal.ofReal (1 - Real.exp (-x)) * (NegExpCreditV F (L + 1) + c)) := hmof.mul_const _
  rw [lintegral_add_right _ hmg, lintegral_mul_const _ hmof,
      NegExpReject_lintegral, NegExpCreditV_recurrence F L]
  unfold NegExpRejectProb
  ring

open MeasureTheory in
/-- Measurability of the amplified per-sample `DecrTrial` budget (consumed by
`twp_urand_exp'`). -/
theorem NegExpAmp_measurable (F : ℕ → ℝ → ℝ≥0∞) (hF : ∀ a, Measurable (F a))
    (L : ℕ) (c : ℝ≥0∞) :
    Measurable (fun x => RealDecrTrialCreditV (NegExpAmp F x L c) 0 x) := by
  unfold RealDecrTrialCreditV
  refine Measurable.ennreal_tsum fun n => (RealDecrTrialμ_measurable 0 n).mul ?_
  -- `NegExpAmp F x L c n` is `F L x` on even `n` (needs `hF`), else a constant.
  unfold NegExpAmp
  by_cases h : n % 2 = 0
  · simpa only [h, if_true] using hF L
  · simpa only [h, if_false] using measurable_const

/-! ## Specification -/

/-- Total weakest-precondition for `NegExp`: the result is a pair `(vz, vr)`
with `0 ≤ vr < 1`, carrying credit `F vz vr`. -/
theorem twp_NegExp (E : CoPset) (F : ℕ → ℝ → ℝ≥0∞) (M : ℝ≥0∞)
    (hnn : ∀ a b, 0 ≤ b → b ≤ 1 → F a b ≤ M) (hFm : ∀ a, Measurable (F a)) (L : ℕ) :
    ⊢@{IProp GF} ↯ (NegExpCreditV F L) -∗
      tglWp E pl(&NegExp #(.int (L : ℤ)))
        (fun p : Val ℝ => iprop(∃ (vz : ℕ) (vr : ℝ),
          ⌜p.1 = .pair (.lit (.int (Int.ofNat vz))) (.lit (.real vr))⌝ ∗
          ⌜0 ≤ vr ∧ vr < 1⌝ ∗ ↯ (F vz vr))) := by
  iintro Hε_spec
  -- Fresh thin-air termination credit. The reject loop is guarded by a fixed
  -- `exp (-1)` event, so amplify by `k = exp 1` and induct over `L`.
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
  -- Distribute `↯(NegExpCreditV F L) + ↯ε_term` across the sample via the amplified
  -- `DecrTrial` budget; the recurrence `∫ = NegExpCreditV F L + exp(-1)·(k·ε_term)`
  -- collapses (`exp(-1)·exp 1 = 1`) back to the combined credit.
  icombine Hε_spec Hε_term as Hε
  iapply (twp_urand_exp'
    (ε₂ := fun x => RealDecrTrialCreditV (NegExpAmp F x L ((k : ℝ≥0∞) * ε_term)) 0 x)
    (NegExpAmp_measurable F hFm L _) ?hint) $$ Hε
  case hint =>
    rw [NegExp_credit_recurrence, ← mul_assoc, NegExpRejectProb_mul_NegExpFactor, one_mul]
  iintro %x ⟨%Hxm, Hcx⟩
  have Hx01 : 0 < x ∧ x < 1 := mem_unifUnitSupport_real.mp Hxm
  have Hxr : 0 ≤ x ∧ x ≤ 1 := ⟨Hx01.1.le, Hx01.2.le⟩
  twp_pure
  twp_bind pl(&DecrTrial #(.int (0 : ℤ)) #(.real x))
  have HnnAmp : ∀ n, NegExpAmp F x L ((k : ℝ≥0∞) * ε_term) n
      ≤ M + (NegExpCreditV F (L + 1) + (k : ℝ≥0∞) * ε_term) := by
    intro n
    unfold NegExpAmp
    by_cases h : n % 2 = 0
    · rw [if_pos h]; exact _root_.le_trans (hnn L x Hxr.1 Hxr.2) le_self_add
    · rw [if_neg h]; exact le_add_self
  iapply (tglWp_wand (Φ := fun v : Val ℝ => iprop(∃ n : ℕ,
    ⌜v.1 = .lit (.int (Int.ofNat n))⌝ ∗ ↯ (NegExpAmp F x L ((k : ℝ≥0∞) * ε_term) n))))
  isplitl [Hcx]
  · iapply (twp_DecrTrial E (NegExpAmp F x L ((k : ℝ≥0∞) * ε_term))
      (M + (NegExpCreditV F (L + 1) + (k : ℝ≥0∞) * ε_term)) HnnAmp 0 x Hxr) $$ Hcx
  iintro %w ⟨%n, %hn, Hcn⟩
  rcases w with ⟨w, hwlc⟩
  simp only at hn; subst hn
  -- Test the parity of the `DecrTrial` result; `= #0` stays symbolic (`decide`
  -- stuck on `Int.ofNat n % 2`), so case on parity to make the operand concrete.
  twp_pures
  rcases Nat.mod_two_eq_zero_or_one n with hpar | hpar
  · -- `n` even (accept): `#0 = #0 → #true`, returns the pair `(L, x)`, credit `F L x`.
    rw [show (Int.ofNat n % 2 : ℤ) = 0 from by simp only [Int.ofNat_eq_natCast]; omega]
    twp_pures
    twp_value
    imodintro
    iexists L, x
    have hcn : NegExpAmp F x L ((k : ℝ≥0∞) * ε_term) n = F L x := by
      simp only [NegExpAmp]; rw [if_pos hpar]
    rw [← hcn]
    isplitr [Hcn]
    · ipureintro; rfl
    · isplitr [Hcn]
      · ipureintro; exact ⟨Hx01.1.le, Hx01.2⟩
      · iexact Hcn
  · -- `n` odd (reject): `#1 = #0 → #false`, recurse `trial (L+1)` via `IH`.
    rw [show (Int.ofNat n % 2 : ℤ) = 1 from by simp only [Int.ofNat_eq_natCast]; omega]
    have hcn : NegExpAmp F x L ((k : ℝ≥0∞) * ε_term) n
        = NegExpCreditV F (L + 1) + (k : ℝ≥0∞) * ε_term := by
      simp only [NegExpAmp]; rw [if_neg (by omega)]
    ihave Hcn' : iprop(↯ (NegExpCreditV F (L + 1) + (k : ℝ≥0∞) * ε_term)) $$ [Hcn]
    · rw [← hcn]; iexact Hcn
    ihave ⟨Hexp, Hterm⟩ := ErrorCredit.split (GF := GF) $$ Hcn'
    twp_pure
    twp_pure
    rw [show ((L : ℤ) + 1) = ((L + 1 : ℕ) : ℤ) from by push_cast; ring]
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

end
end Examples
end TotalEris
end ProbLang
