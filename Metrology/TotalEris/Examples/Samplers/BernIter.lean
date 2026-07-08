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
  have hγ0 : (0:ℝ) ≤ (γ:ℝ) := γ.2.1
  have hγ1 : (γ:ℝ) ≤ 1 := γ.2.2
  have hpN : (0:ℝ) ≤ (γ:ℝ) ^ N := by positivity
  have hpN1 : (γ:ℝ) ^ N ≤ 1 := pow_le_one₀ hγ0 hγ1
  have hpSN : (0:ℝ) ≤ (γ:ℝ) ^ (N + 1) := by positivity
  -- Turn every truncated `1 - ofReal _` into `ofReal (1 - _)` so the goal becomes
  -- subtraction-free (a plain commutative-semiring identity).
  have e1 : (1 : ℝ≥0∞) - ENNReal.ofReal ((γ:ℝ) ^ N) = ENNReal.ofReal (1 - (γ:ℝ) ^ N) := by
    rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_sub _ hpN]
  have e2 : (1 : ℝ≥0∞) - ENNReal.ofReal (γ:ℝ) = ENNReal.ofReal (1 - (γ:ℝ)) := by
    rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_sub _ hγ0]
  have e3 : (1 : ℝ≥0∞) - ENNReal.ofReal ((γ:ℝ) ^ (N + 1)) = ENNReal.ofReal (1 - (γ:ℝ) ^ (N + 1)) := by
    rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_sub _ hpSN]
  have ct : ENNReal.ofReal ((γ:ℝ) ^ (N + 1))
      = ENNReal.ofReal (γ:ℝ) * ENNReal.ofReal ((γ:ℝ) ^ N) := by
    rw [← ENNReal.ofReal_mul hγ0]; congr 1; rw [pow_succ]; ring
  have cf : ENNReal.ofReal (γ:ℝ) * ENNReal.ofReal (1 - (γ:ℝ) ^ N) + ENNReal.ofReal (1 - (γ:ℝ))
      = ENNReal.ofReal (1 - (γ:ℝ) ^ (N + 1)) := by
    rw [← ENNReal.ofReal_mul hγ0,
        ← ENNReal.ofReal_add (mul_nonneg hγ0 (by linarith)) (by linarith)]
    congr 1; ring
  simp only [IterCreditV, Iterg]
  rw [e1, e2, e3, ct, ← cf]
  ring

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
  induction N generalizing F with
  | zero =>
    iintro ⟨Hcr, HI⟩
    -- `k = 0`: `if #0 = #0 then #true` → returns `true`; credit `IterCreditV F γ 0 = F true`.
    twp_pures
    twp_value
    imodintro
    iexists true
    have h0 : IterCreditV F γ 0 = F true := by
      simp only [IterCreditV, pow_zero, ENNReal.ofReal_one, one_mul, tsub_self, zero_mul, add_zero]
    rw [← h0]
    iframe Hcr HI
    itrivial
  | succ N IH =>
    iintro ⟨Hcr, HI⟩
    -- `k = N+1 ≠ 0`, so step to `if v () then iter v (k-1) else #false`.
    twp_pures
    -- Run the Bernoulli `v ()` via its spec, reshaping the credit through
    -- `Iter_expectation` into `γ · g true + (1-γ) · g false` with `g = Iterg F γ N`.
    twp_bind pl({v.fst} #.unit)
    iapply (tglWp_wand (Φ := fun w : Val ℝ => iprop(∃ b : Bool,
      ⌜w.1 = .lit (.bool b)⌝ ∗ ↯ (Iterg F γ N b) ∗ I)))
    isplitl [Hcr HI]
    · iapply (Hspec.spec (E := E)) $$ %(Iterg F γ N)
      isplitl [Hcr]
      · rw [← Iter_expectation]; iexact Hcr
      · iexact HI
    iintro %w' ⟨%b, %hret, Hcrb, HIb⟩
    rcases w' with ⟨w', hwlc'⟩
    simp only at hret; subst hret
    rcases b
    · -- `false`: short-circuit to `#false`, credit `Iterg F γ N false = F false`.
      twp_pures
      twp_value
      imodintro
      iexists false
      rw [show F false = Iterg F γ N false from rfl]
      iframe Hcrb HIb
      itrivial
    · -- `true`: recurse `iter v (k-1)` at `k-1 = N`, discharged by `IH`.
      twp_pure
      twp_pure
      rw [show ((N + 1 : ℕ) : ℤ) - 1 = (N : ℤ) from by push_cast; ring]
      twp_bind pl(&IterTrial {v.fst} #(.int (N : ℤ)))
      iapply (tglWp_wand (Φ := fun w : Val ℝ => iprop(∃ b : Bool,
        ⌜w.1 = .lit (.bool b)⌝ ∗ ↯ (F b) ∗ I)))
      isplitl [Hcrb HIb]
      · iapply IH
        isplitl [Hcrb]
        · rw [show IterCreditV F γ N = Iterg F γ N true from rfl]; iexact Hcrb
        · iexact HIb
      iintro %w Hpost
      iapply tglWp_value
      iexact Hpost

end
end Examples
end TotalEris
end ProbLang
