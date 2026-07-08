module

public import Metrology.TotalEris
public import Metrology.ProbLang.Reals
public import Metrology.TotalEris.Examples.Samplers.RealDecrTrial

@[expose] public section

/-!
# Negative-exponential sampler — port of `neg_exp.v`

`NegExp L` samples a non-negative real from a (right-shifted) negative
exponential, returned split as an integer part `vz` and a fractional part
`vr ∈ [0,1)`: sample `x ← urand`, run a `DecrTrial` from `x` to get `y`; if `y`
is even return `(L, x)`, else recurse at `L+1`.

**Status: stub.** Programs and specifications only; every proof is `sorry`.
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

/-! ## PMF / credits -/

/-- Negative-exponential density started at `0`. Rocq `NegExp_ρ0`:
`[0 ≤ x ≤ 1] · exp (-(x + k))`. -/
def NegExpρ0 (k : ℕ) (x : ℝ) : ℝ≥0∞ :=
  if 0 ≤ x ∧ x ≤ 1 then .ofReal (Real.exp (-(x + k))) else 0

/-- Right-shifted by `L`. Rocq `NegExp_ρ`: `[L ≤ k] · NegExp_ρ0 (k - L) x`. -/
def NegExpρ (L k : ℕ) (x : ℝ) : ℝ≥0∞ :=
  if L ≤ k then NegExpρ0 (k - L) x else 0

open MeasureTheory in
/-- Rocq `NegExp_CreditV`: `∑ₖ ∫₀¹ NegExp_ρ L k x · F k x dx`. -/
def NegExpCreditV (F : ℕ → ℝ → ℝ≥0∞) (L : ℕ) : ℝ≥0∞ :=
  ∑' k : ℕ, ∫⁻ x, NegExpρ L k x * F k x ∂(ProbLangℝ.unifUnit (T := ℝ))

/-- Per-sample credit-distribution function. Rocq `hx`: the credit assigned to
`DecrTrial` result `z` — `Zeven z ↦ F L x`, else `↦ NegExpCreditV F (L+1)`. -/
def NegExphx (F : ℕ → ℝ → ℝ≥0∞) (x : ℝ) (L : ℕ) : ℕ → ℝ≥0∞ := fun z =>
  if z % 2 = 0 then F L x else NegExpCreditV F (L + 1)

/-! ## Program

Rocq:
```
NegExp := rec: "trial" "L" :=
  let: "x" := init #() in
  let: "y" := lazyDecrR #0 "x" in
  if: ("y" `rem` #2 = #0) then ("L", "x") else "trial" ("L" + #1).
```
-/
@[pl_fold]
def NegExp : Exp ℝ := pl%
  rec trial L :=
    let x := urand;
    let y := &DecrTrial #0 x;
    if (y % #2 = #0) then (L, x) else trial (L + #1)

/-! ## Specification -/

/-- Rocq `wp_NegExp_gen`. The lazy-real result `ℓ`/`lazy_real ℓ vr` becomes the
real value `.real vr` directly. -/
theorem twp_NegExp (E : CoPset) (F : ℕ → ℝ → ℝ≥0∞) (M : ℝ≥0∞)
    (Hnn : ∀ a b, 0 ≤ b → b ≤ 1 → F a b ≤ M) (L : ℕ) :
    ⊢@{IProp GF} ↯ (NegExpCreditV F L) -∗
      tglWp E pl(&NegExp #(.int (L : ℤ)))
        (fun p : Val ℝ => iprop(∃ (vz : ℕ) (vr : ℝ),
          ⌜p.1 = .pair (.lit (.int (Int.ofNat vz))) (.lit (.real vr))⌝ ∗
          ⌜0 ≤ vr ∧ vr < 1⌝ ∗ ↯ (F vz vr))) := by
  sorry

end
end Examples
end TotalEris
end ProbLang
