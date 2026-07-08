module

public import Metrology.TotalEris
public import Metrology.ProbLang.Reals
public import Metrology.TotalEris.Examples.Samplers.HalfBernNegExp
public import Metrology.TotalEris.Examples.Samplers.BernoulliGeometric
public import Metrology.TotalEris.Examples.Samplers.BernIter
public import Metrology.TotalEris.Examples.Samplers.Selector

@[expose] public section

/-!
# Discrete/continuous Gaussian sampler — port of `gauss.v`

* `G1 ()` samples a non-negative integer `k` from the (half-)discrete Gaussian
  `G1_μ k = exp(-k²/2) / Norm1`, via a geometric trial (`GeometricTrial BNEHalf`)
  followed by an accept/reject iteration (`IterTrial BNEHalf`).
* `G2 ()` extends `G1` to a full continuous Gaussian on `[k, k+1)`, returning a
  pair `(x, k)` of fractional real `x ∈ [0,1)` and integer `k`, with density
  `G2_μ k x = exp(-(x+k)²/2) / Norm2`; the accept step uses the selector `B`.

This is the apex of the Gauss tower — it composes `BNEHalf`
(`HalfBernNegExp`), `GeometricTrial`/`IterTrial` (`BernoulliGeometric`/`BernIter`), and `B`
(`Selector`).

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

/-! ## PMF -/

/-- Normalising constant of the discrete Gaussian. Rocq `Norm1`. -/
def Norm1 : ℝ := ∑' k : ℕ, Real.exp (-(k : ℝ) ^ 2 / 2)

/-- Discrete-Gaussian PMF. Rocq `G1_μ`: `exp(-k²/2) / Norm1`. -/
def G1μ (k : ℕ) : ℝ≥0∞ := .ofReal (Real.exp (-(k : ℝ) ^ 2 / 2) / Norm1)

open MeasureTheory in
/-- Normalising constant of the continuous Gaussian on `[k, k+1)`. Rocq `Norm2`:
`∫₀¹ ∑ₖ exp(-(x+k)²/2) dx`. -/
def Norm2 : ℝ := ∫ x in (0 : ℝ)..1, ∑' k : ℕ, Real.exp (-((x + k) ^ 2) / 2)

/-- Continuous-Gaussian density. Rocq `G2_μ`: `exp(-(x+k)²/2) / Norm2`. -/
def G2μ (k : ℕ) (x : ℝ) : ℝ≥0∞ := .ofReal (Real.exp (-((x + k) ^ 2) / 2) / Norm2)

/-! ## Credits -/

/-- Rocq `G1_CreditV`: `∑ₖ G1_μ k · F k`. -/
def G1_CreditV (F : ℕ → ℝ≥0∞) : ℝ≥0∞ := ∑' k : ℕ, G1μ k * F k

open MeasureTheory in
/-- Rocq `G2_CreditV`: `∑ₖ ∫₀¹ G2_μ k x · F k x dx`. -/
def G2_CreditV (F : ℕ → ℝ → ℝ≥0∞) : ℝ≥0∞ :=
  ∑' k : ℕ, ∫⁻ x, G2μ k x * F k x ∂(ProbLangℝ.unifUnit (T := ℝ))

/-- Rocq `G1_h`: iteration continuation — `true ↦ F k`, `false ↦ G1_CreditV F`. -/
def G1_h (F : ℕ → ℝ≥0∞) (k : ℕ) : Bool → ℝ≥0∞
  | true => F k
  | false => G1_CreditV F

/-- Rocq `G1_f`: the geometric-trial credit function.
`exp(-(k(k-1))/2) · G1_h true + (1 - exp(…)) · G1_h false`. -/
def G1_f (F : ℕ → ℝ≥0∞) (k : ℕ) : ℝ≥0∞ :=
  .ofReal (Real.exp (-(↑(k * (k - 1)) : ℝ) / 2)) * G1_h F k true +
  (1 - .ofReal (Real.exp (-(↑(k * (k - 1)) : ℝ) / 2))) * G1_h F k false

/-- Rocq `G2_s`: `true ↦ F k x`, `false ↦ G2_CreditV F`. -/
def G2_s (F : ℕ → ℝ → ℝ≥0∞) (k : ℕ) (x : ℝ) : Bool → ℝ≥0∞
  | true => F k x
  | false => G2_CreditV F

/-- Rocq `G2_g`:
`exp(-x(2k+x)/2) · G2_s true + (1 - exp(…)) · G2_s false`. -/
def G2_g (F : ℕ → ℝ → ℝ≥0∞) (k : ℕ) (x : ℝ) : ℝ≥0∞ :=
  .ofReal (Real.exp (-x * (2 * k + x) / 2)) * G2_s F k x true +
  (1 - .ofReal (Real.exp (-x * (2 * k + x) / 2))) * G2_s F k x false

open MeasureTheory in
/-- Rocq `G2_f`: `∫₀¹ G2_g F k x dx`, the `G1`-level credit for `G2`. -/
def G2_f (F : ℕ → ℝ → ℝ≥0∞) (k : ℕ) : ℝ≥0∞ :=
  ∫⁻ x, G2_g F k x ∂(ProbLangℝ.unifUnit (T := ℝ))

/-! ## Programs

Rocq:
```
G1 := rec: "trial" "_" :=
  let: "k" := GeometricTrial BNEHalf #0 in
  if: IterTrial BNEHalf ("k" * ("k" - #1)) then "k" else "trial" #().
G2 := rec: "trial" "_" :=
  let: "k" := G1 #() in
  let: "x" := init #() in
  if: IterTrial (λ: "_", B "k" "x") ("k" + #1) then ("x", "k") else "trial" #().
```
-/
@[pl_fold]
def G1 : Exp ℝ := pl%
  rec trial u :=
    let k := &GeometricTrial &BNEHalf #0;
    if &IterTrial &BNEHalf (k * (k - #1)) then k else trial #.unit

@[pl_fold]
def G2 : Exp ℝ := pl%
  rec trial u :=
    let k := &G1 #.unit;
    let x := urand;
    if &IterTrial (fun _u, &B k x) (k + #1) then (x, k) else trial #.unit

/-! ## Specifications -/

/-- Rocq `wp_G1`: `G1 ()` samples `n` from the discrete Gaussian. -/
theorem twp_G1 (E : CoPset) (F : ℕ → ℝ≥0∞) (M : ℝ≥0∞) (Hnn : ∀ n, F n ≤ M) :
    ⊢@{IProp GF} ↯ (G1_CreditV F) -∗
      tglWp E pl(&G1 #.unit)
        (fun v : Val ℝ => iprop(∃ n : ℕ, ⌜v.1 = .lit (.int (Int.ofNat n))⌝ ∗ ↯ (F n))) := by
  sorry

/-- Rocq `wp_G2`: `G2 ()` returns `(x, k)` from the continuous Gaussian. The
lazy-real result `ℓ`/`lazy_real ℓ r` becomes the real value `.real r`. -/
theorem twp_G2 (E : CoPset) (F : ℕ → ℝ → ℝ≥0∞) (M : ℝ≥0∞)
    (Hnn : ∀ x k, 0 ≤ x → x ≤ 1 → F k x ≤ M) :
    ⊢@{IProp GF} ↯ (G2_CreditV F) -∗
      tglWp E pl(&G2 #.unit)
        (fun p : Val ℝ => iprop(∃ (k : ℕ) (r : ℝ),
          ⌜0 ≤ r ∧ r < 1⌝ ∗
          ⌜p.1 = .pair (.lit (.real r)) (.lit (.int (Int.ofNat k)))⌝ ∗ ↯ (F k r))) := by
  sorry

end
end Examples
end TotalEris
end ProbLang
