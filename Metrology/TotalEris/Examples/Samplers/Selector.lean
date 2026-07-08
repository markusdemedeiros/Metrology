module

public import Metrology.TotalEris
public import Metrology.ProbLang.Reals

@[expose] public section

/-!
# Index selector — port of `selector.v`

The combinators that pick the integer part of a Gaussian sample.

* `C m` chooses `0`, `1`, or `2` from a discrete `rand` (the only place a
  *discrete* sampler survives — the `{0,1,2}` selection is genuinely finite).
* `Bii k x`, `S`, `S0`, `B` are the continuous pieces: they compare the shared
  uniform `x` against fresh `urand` draws.

In the Rocq development the shared uniform is a lazy real `lazy_real xα x`
threaded through as `(xα, x)`; under `urand` it is the real value `.real x`, so
the `lazy_real` predicate drops out of every spec.

**Status: stub.** Programs and specifications only; every proof is `sorry`.
Fixed at `rT = ℝ`.
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

/-- Rocq `C_CreditV`: `1/(m+2) · F 0 + 1/(m+2) · F 1 + m/(m+2) · F 2`. -/
def C_CreditV (F : ℕ → ℝ≥0∞) (m : ℕ) : ℝ≥0∞ :=
  .ofReal (1 / ((m : ℝ) + 2)) * F 0 + .ofReal (1 / ((m : ℝ) + 2)) * F 1 +
  .ofReal ((m : ℝ) / ((m : ℝ) + 2)) * F 2

/-- Rocq `Bii_μ`: `μ true = 1 - (2k+x)/(2k+2)`, `μ false = (2k+x)/(2k+2)`. -/
def Biiμ (k : ℕ) (x : ℝ) : Bool → ℝ≥0∞
  | true => .ofReal (1 - (2 * (k : ℝ) + x) / (2 * k + 2))
  | false => .ofReal ((2 * (k : ℝ) + x) / (2 * k + 2))

/-- Rocq `Bii_CreditV`. -/
def Bii_CreditV (F : Bool → ℝ≥0∞) (k : ℕ) (x : ℝ) : ℝ≥0∞ :=
  Biiμ k x false * F false + Biiμ k x true * F true

/-- Rocq `S_μ0`. -/
def Sμ0 (k : ℕ) (x y : ℝ) (n : ℕ) : ℝ≥0∞ :=
  .ofReal ((y ^ n / n.factorial) * ((2 * (k : ℝ) + x) / (2 * k + 2)) ^ n -
    (y ^ (n + 1) / (n + 1).factorial) * ((2 * (k : ℝ) + x) / (2 * k + 2)) ^ (n + 1))

/-- Rocq `S_μ`: `[N ≤ n] · S_μ0 k x y (n - N)`. -/
def Sμ (k : ℕ) (x y : ℝ) (N n : ℕ) : ℝ≥0∞ :=
  if N ≤ n then Sμ0 k x y (n - N) else 0

/-- Rocq `S_CreditV`: `∑ₙ S_μ k x y N n · F n`. -/
def S_CreditV (F : ℕ → ℝ≥0∞) (k : ℕ) (x y : ℝ) (N : ℕ) : ℝ≥0∞ :=
  ∑' n : ℕ, Sμ k x y N n * F n

/-- Rocq `B_CreditV`:
`exp(-x(2k+x)/(2k+2)) · F true + (1 - exp(…)) · F false`. -/
def B_CreditV (F : Bool → ℝ≥0∞) (k : ℕ) (x : ℝ) : ℝ≥0∞ :=
  .ofReal (Real.exp (-x * (2 * k + x) / (2 * k + 2))) * F true +
  (1 - .ofReal (Real.exp (-x * (2 * k + x) / (2 * k + 2)))) * F false

/-! ## Programs

Rocq (`init` → `urand`, `cmp a b = #(-1)` → `a < b`):
```
C   := λ "m", let "v" := rand ("m"+1) in if "v"=#0 then #0 else if "v"=#1 then #1 else #2.
Bii := λ "k" "x", let "f" := C (#2*"k") in let "r" := init #() in
        ("f"=#0) || (("f"=#1) && (cmp "x" "r" = #(-1))).
S   := rec: "trial" "k" "x" "y" "N" := let "z" := init #() in
        if: (cmp "y" "z" = #(-1)) || (Bii "k" "x") then "N" else "trial" "k" "x" "z" ("N"+1).
S0  := λ "k" "x", let "z" := init #() in
        if: (cmp "x" "z" = #(-1)) || (Bii "k" "x") then #0 else S "k" "x" "z" #1.
B   := λ "k" "x", (S0 "k" "x") `rem` #2 = #0.
```
`rand ("m"+1)` (clutch: `m+2` outcomes) becomes ProbLang `rand (m+2)` (which
samples `{0,…,m+1}`). -/
@[pl_fold]
def C : Exp ℝ := pl%
  fun m, let v := rand(m + #2, #.unit); if v = #0 then #0 else if v = #1 then #1 else #2

@[pl_fold]
def Bii : Exp ℝ := pl%
  fun k, fun x,
    let f := &C (#2 * k);
    let r := urand;
    (f = #0) || ((f = #1) && (x < r))

@[pl_fold]
def S : Exp ℝ := pl%
  rec trial k x y N :=
    let z := urand;
    if (y < z) || (&Bii k x) then N else trial k x z (N + #1)

@[pl_fold]
def S0 : Exp ℝ := pl%
  fun k, fun x,
    let z := urand;
    if (x < z) || (&Bii k x) then #0 else &S k x z #1

@[pl_fold]
def B : Exp ℝ := pl%
  fun k, fun x, (&S0 k x % #2 = #0)

/-! ## Specifications -/

/-- Rocq `wp_C`. -/
theorem twp_C (E : CoPset) (F : ℕ → ℝ≥0∞) (m : ℕ) :
    ⊢@{IProp GF} ↯ (C_CreditV F m) -∗
      tglWp E pl(&C #(.int (m : ℤ)))
        (fun v : Val ℝ => iprop(∃ n : ℕ,
          ⌜v.1 = .lit (.int (Int.ofNat n))⌝ ∗ ⌜n = 0 ∨ n = 1 ∨ n = 2⌝ ∗ ↯ (F n))) := by
  sorry

/-- Rocq `wp_Bii`. -/
theorem twp_Bii (E : CoPset) (F : Bool → ℝ≥0∞) (k : ℕ) (x : ℝ) (Hx : 0 ≤ x ∧ x ≤ 1) :
    ⊢@{IProp GF} ↯ (Bii_CreditV F k x) -∗
      tglWp E pl(&Bii #(.int (k : ℤ)) #(.real x))
        (fun v : Val ℝ => iprop(∃ b : Bool, ⌜v.1 = .lit (.bool b)⌝ ∗ ↯ (F b))) := by
  sorry

/-- Rocq `wp_S`. -/
theorem twp_S (E : CoPset) (F : ℕ → ℝ≥0∞) (M : ℝ≥0∞) (Hnn : ∀ n, F n ≤ M)
    (k : ℕ) (x y : ℝ) (N : ℕ) (Hx : 0 ≤ x ∧ x ≤ 1) (Hy : 0 ≤ y ∧ y ≤ 1) :
    ⊢@{IProp GF} ↯ (S_CreditV F k x y N) -∗
      tglWp E pl(&S #(.int (k : ℤ)) #(.real x) #(.real y) #(.int (N : ℤ)))
        (fun v : Val ℝ => iprop(∃ n : ℕ, ⌜v.1 = .lit (.int (Int.ofNat n))⌝ ∗ ↯ (F n))) := by
  sorry

/-- Rocq `wp_S0`. -/
theorem twp_S0 (E : CoPset) (F : ℕ → ℝ≥0∞) (M : ℝ≥0∞) (Hnn : ∀ n, F n ≤ M)
    (k : ℕ) (x : ℝ) (Hx : 0 ≤ x ∧ x ≤ 1) :
    ⊢@{IProp GF} ↯ (S_CreditV F k x x 0) -∗
      tglWp E pl(&S0 #(.int (k : ℤ)) #(.real x))
        (fun v : Val ℝ => iprop(∃ n : ℕ, ⌜v.1 = .lit (.int (Int.ofNat n))⌝ ∗ ↯ (F n))) := by
  sorry

/-- Rocq `wp_B`. -/
theorem twp_B (E : CoPset) (F : Bool → ℝ≥0∞) (M : ℝ≥0∞) (Hnn : ∀ b, F b ≤ M)
    (k : ℕ) (x : ℝ) (Hx : 0 ≤ x ∧ x ≤ 1) :
    ⊢@{IProp GF} ↯ (B_CreditV F k x) -∗
      tglWp E pl(&B #(.int (k : ℤ)) #(.real x))
        (fun v : Val ℝ => iprop(∃ b : Bool, ⌜v.1 = .lit (.bool b)⌝ ∗ ↯ (F b))) := by
  sorry

end
end Examples
end TotalEris
end ProbLang
