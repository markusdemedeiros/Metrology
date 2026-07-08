module

public import Metrology.TotalEris
public import Metrology.ProbLang.Reals

@[expose] public section

/-!
# Bounded Bernoulli iteration — port of `bern_iter.v`

`IterTrial b k` runs the Bernoulli `b` up to `k` times: it returns `true` iff
the first `k` trials all succeed, and short-circuits to `false` on the first
failure. The success probability is `γ^k`.

Unlike `bern_geo`, the Rocq `wp_Iter` threads a persistent invariant `I`
through the Bernoulli's spec (used by the Gaussian composition), so we use a
dedicated `AbstractBernoulliI` interface carrying `I`.

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

/-- A Bernoulli `v` with success bias `γ`, threading a persistent invariant
`I`. Rocq `wp_e` from `bern_iter.v`'s program section. -/
structure AbstractBernoulliI (v : Val ℝ) (γ : ↑unitInterval) (I : IProp GF) where
  spec {E} : iprop%
    ⊢@{IProp GF} ∀ (F : Bool → ℝ≥0∞),
      ↯ (.ofReal γ * F true + (1 - .ofReal γ) * F false) ∗ I -∗
      tglWp E pl(&v.1 #.unit)
        (fun w : Val ℝ => iprop% ∃ b : Bool, ⌜w.1 = .lit (.bool b)⌝ ∗ ↯ (F b) ∗ I)

/-! ## PMF / credits -/

/-- Iteration PMF. Rocq `Iter_μ`: `μ true = γ^N`, `μ false = 1 - γ^N`. -/
def Iterμ (γ : ↑unitInterval) (N : ℕ) : Bool → ℝ≥0∞
  | true => .ofReal ((γ : ℝ) ^ N)
  | false => 1 - .ofReal ((γ : ℝ) ^ N)

/-- Rocq `Iter_CreditV`: `γ^N · F true + (1 - γ^N) · F false`. -/
def IterCreditV (F : Bool → ℝ≥0∞) (γ : ↑unitInterval) (N : ℕ) : ℝ≥0∞ :=
  .ofReal ((γ : ℝ) ^ N) * F true + (1 - .ofReal ((γ : ℝ) ^ N)) * F false

/-- Rocq `g` (local) — per-trial split by Bernoulli outcome:
`true ↦ IterCreditV F γ N`, `false ↦ F false`. -/
def Iterg (F : Bool → ℝ≥0∞) (γ : ↑unitInterval) (N : ℕ) : Bool → ℝ≥0∞
  | true => IterCreditV F γ N
  | false => F false

/-- Rocq `g_expectation`: `IterCreditV F γ (N+1) = γ · g true + (1-γ) · g false`. -/
theorem Iter_expectation {F : Bool → ℝ≥0∞} {γ : ↑unitInterval} {N : ℕ} :
    IterCreditV F γ (N + 1) =
      .ofReal γ * Iterg F γ N true + (1 - .ofReal γ) * Iterg F γ N false := by
  sorry

/-! ## Program

Rocq:
```
IterTrial := rec: "trial" "e" "k" :=
  if: "k" = #0 then #true
  else if: "e" #() then "trial" "e" ("k" - #1) else #false.
```
-/
@[pl_fold]
def IterTrial : Exp ℝ := pl%
  rec iter b k :=
    if k = #0 then #true
    else if b #.unit then iter b (k - #1) else #false

/-! ## Specification -/

/-- Rocq `wp_Iter`. -/
theorem twp_IterTrial (E : CoPset) (v : Val ℝ) (γ : ↑unitInterval) (I : IProp GF)
    (Hspec : AbstractBernoulliI (hlc := hlc) (GF := GF) v γ I)
    (F : Bool → ℝ≥0∞) (N : ℕ) :
    ⊢@{IProp GF} ↯ (IterCreditV F γ N) ∗ I -∗
      tglWp E pl(&IterTrial &v.1 #(.int (N : ℤ)))
        (fun w : Val ℝ => iprop(∃ b : Bool, ⌜w.1 = .lit (.bool b)⌝ ∗ ↯ (F b) ∗ I)) := by
  sorry

end
end Examples
end TotalEris
end ProbLang
