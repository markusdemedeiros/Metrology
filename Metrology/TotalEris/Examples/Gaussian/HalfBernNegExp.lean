module

public import Metrology.TotalEris
public import Metrology.ProbLang.Reals
public import Metrology.TotalEris.Examples.Gaussian.RealDecrTrial

@[expose] public section

/-!
# Bernoulli with base-½ negative-exponential bias — continuous-uniform port

Port of `clutch/theories/eris/examples/half_bern_neg_exp.v`, on `urand`
(see `RealDecrTrial.lean` for the redesign conventions).

`LeHalf x` tests whether a sampled real `x` is `≤ ½`. In the Rocq lazy-real
development this inspects the leading bit of the tape; under `urand` the value
*is* the real, so it is simply the comparison `x ≤ ½`.

`BNEHalf ()` is a Bernoulli whose `true`-probability is `exp (-½)`: sample
`x ← urand`; if `x ≤ ½` run a `DecrTrial` from `x` and return the parity of
its result, else return `true`.

**Status: stub.** Programs and specifications only; every proof is `sorry`.
Fixed at `rT = ℝ` (real analysis is irreducibly `ℝ`-based).
-/

open Std Iris Iris.Std Iris.BI Iris.ProofMode OFE COFE ProbLang ProbLang.TotalEris
  ProbLang.TotalEris.ErisWpGS
open scoped AppGS ENNReal NNReal

namespace ProbLang
namespace TotalEris
namespace Examples

noncomputable section

variable {hlc : HasLC} {GF : BundledGFunctors.{0,0,0}} [ErisGS ℝ hlc GF]

/-! ## PMF / credits -/

/-- Base-½ negative-exponential Bernoulli PMF. Rocq `BNEHalf_μ`:
`μ true = exp (-½)`, `μ false = 1 - exp (-½)`. -/
def BNEHalfμ (b : Bool) : ℝ≥0∞ :=
  if b then .ofReal (Real.exp (-1 / 2)) else .ofReal (1 - Real.exp (-1 / 2))

/-- Rocq `BNEHalf_CreditV`: `F true · μ true + F false · μ false`. -/
def BNEHalfCreditV (F : Bool → ℝ≥0∞) : ℝ≥0∞ :=
  F true * BNEHalfμ true + F false * BNEHalfμ false

/-- Lift a `Bool`-indexed credit function to a `ℕ`-indexed one by parity of the
argument. Rocq `LiftF`: `LiftF F n = F (n % 2 == 1)`. -/
def LiftF (F : Bool → ℝ≥0∞) : ℕ → ℝ≥0∞ := fun n => F (n % 2 == 1)

/-- Per-sample credit-distribution function. Rocq `g` (local):
`[r ≤ ½] · RealDecrTrialCreditV (LiftF F) 0 r  +  [¬ r ≤ ½] · F true`. -/
def HalfBerng (F : Bool → ℝ≥0∞) : ℝ → ℝ≥0∞ := fun r =>
  (if r ≤ 1 / 2 then RealDecrTrialCreditV (LiftF F) 0 r else 0) +
  (if ¬ r ≤ 1 / 2 then F true else 0)

section Wp

open MeasureTheory in
/-- Credit conservation (Rocq `g_expectation` composed with `RInt_poke`):
`∫ HalfBerng F = BNEHalfCreditV F` over the uniform-unit measure — consumed by
`twp_urand_exp` at the `x ← urand` step of `BNEHalf`. -/
theorem HalfBerng_lintegral {F : Bool → ℝ≥0∞} {M : ℝ≥0∞} (Hbound : ∀ b, F b ≤ M) :
    ∫⁻ r, HalfBerng F r ∂(ProbLangℝ.unifUnit (T := ℝ)) = BNEHalfCreditV F := by
  sorry

end Wp

/-! ## Programs

Rocq:
```
LeHalf  := λ "x", let "c1n" := get_chunk (Fst "x") (Snd "x") in
                  let "res" := cmpZ (Fst "c1n") #0 in "res" = #0.
BNEHalf := λ "_", let "x" := init #() in
             if: LeHalf "x" then let: "y" := lazyDecrR #0 "x" in ("y" `rem` #2 = #1)
                            else #true.
```
Under `urand`, `LeHalf "x"` is the real comparison `x ≤ ½` and `init ()`
is `urand`. -/

/-- Decidable spec of `LeHalf`. Rocq `LeHalf_spec r := bool_decide (r ≤ ½)`. -/
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

/-! ## Specifications -/

/-- Rocq `wp_LeHalf`: on a sampled real `r ≠ ½`, `LeHalf (.real r)` returns
`bool_decide (r ≤ ½)`. (The lazy-real `lazy_real v r` framing vanishes under
`urand`.) -/
theorem twp_LeHalf (E : CoPset) (r : ℝ) (Hhalf : r ≠ 1 / 2) :
    ⊢@{IProp GF} tglWp E pl(&LeHalf #(.real r))
      (fun v : Val ℝ => iprop(⌜v.1 = .lit (.bool (LeHalfSpec r))⌝)) := by
  sorry

/-- Rocq `wp_BNEHalf`: `BNEHalf ()` is a Bernoulli returning `b` with the
base-½ negative-exponential law, threading credit `F b`. -/
theorem twp_BNEHalf (E : CoPset) (F : Bool → ℝ≥0∞) (M : ℝ≥0∞) (Hnn : ∀ b, F b ≤ M) :
    ⊢@{IProp GF} ↯ (BNEHalfCreditV F) -∗
      tglWp E pl(&BNEHalf #.unit)
        (fun v : Val ℝ => iprop(∃ b : Bool, ⌜v.1 = .lit (.bool b)⌝ ∗ ↯ (F b))) := by
  sorry

end
end Examples
end TotalEris
end ProbLang
