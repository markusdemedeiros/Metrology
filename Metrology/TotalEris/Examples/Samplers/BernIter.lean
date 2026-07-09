module

public import Metrology.ProbLang.Reals
public import Metrology.TotalEris

@[expose] public section

/-!
# Bounded Bernoulli iteration

`IterTrial b k` runs the Bernoulli `b` up to `k` times: it returns `true` iff
the first `k` trials all succeed, and short-circuits to `false` on the first
failure. The success probability is `γ^k`.

Unlike the geometric sampler, the specification threads a persistent invariant
`I` through the Bernoulli's spec (used by the Gaussian composition), so we use a
dedicated `AbstractBernoulliI` interface carrying `I`.

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

/-- A Bernoulli sampler `v` with success bias `γ`, whose specification threads a
persistent invariant `I` through the call (used by the Gaussian composition). -/
structure AbstractBernoulliI (v : Val ℝ) (γ : ↑unitInterval) (I : IProp GF) where
  spec {E} : iprop%
    ⊢@{IProp GF} ∀ (F : Bool → ℝ≥0∞),
      ↯ (.ofReal γ * F true + (1 - .ofReal γ) * F false) ∗ I -∗
      tglWp E pl(&v.1 #.unit)
        (fun w : Val ℝ => iprop% ∃ b : Bool, ⌜w.1 = .lit (.bool b)⌝ ∗ ↯ (F b) ∗ I)

/-! ## Program -/

/-- Bounded Bernoulli iteration: `IterTrial b k` returns `true` iff `k`
consecutive calls to `b` succeed, and `#false` on the first failure. -/
@[pl_fold]
def IterTrial : Exp ℝ := pl%
  rec iter b k :=
    if k = #0 then #true
    else if b #.unit then iter b (k - #1) else #false

/-! ## Iteration distribution and credits -/

/-- Iteration PMF: `μ true = γ^N` (all `N` trials succeed),
`μ false = 1 - γ^N`. -/
def Iterμ (γ : ↑unitInterval) (N : ℕ) : Bool → ℝ≥0∞
  | true => .ofReal ((γ : ℝ) ^ N)
  | false => 1 - .ofReal ((γ : ℝ) ^ N)

/-- Iteration credit: `γ^N · F true + (1 - γ^N) · F false`. -/
def IterCreditV (F : Bool → ℝ≥0∞) (γ : ↑unitInterval) (N : ℕ) : ℝ≥0∞ :=
  .ofReal ((γ : ℝ) ^ N) * F true + (1 - .ofReal ((γ : ℝ) ^ N)) * F false

/-- Per-trial continuation credit, split by the Bernoulli outcome: the `true`
branch carries the remaining iteration credit `IterCreditV F γ N`, the `false`
branch carries the terminal credit `F false`. -/
def Iterg (F : Bool → ℝ≥0∞) (γ : ↑unitInterval) (N : ℕ) : Bool → ℝ≥0∞
  | true => IterCreditV F γ N
  | false => F false

/-- One-step recurrence: `IterCreditV F γ (N+1)` splits across the next Bernoulli
trial into `γ · Iterg F γ N true + (1 - γ) · Iterg F γ N false`. -/
theorem IterCreditV_succ (F : Bool → ℝ≥0∞) (γ : ↑unitInterval) (N : ℕ) :
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
  have e3 : (1 : ℝ≥0∞) - ENNReal.ofReal ((γ:ℝ) ^ (N + 1))
      = ENNReal.ofReal (1 - (γ:ℝ) ^ (N + 1)) := by
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

/-! ## Specification -/

/-- Total weakest-precondition specification of `IterTrial`: from
`↯(IterCreditV F γ N) ∗ I`, the iteration delivers `↯(F b) ∗ I` for the
realised outcome `b`. -/
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
    -- `IterCreditV_succ` into `γ · g true + (1-γ) · g false` with `g = Iterg F γ N`.
    twp_bind pl({v.fst} #.unit)
    iapply (tglWp_wand (Φ := fun w : Val ℝ => iprop(∃ b : Bool,
      ⌜w.1 = .lit (.bool b)⌝ ∗ ↯ (Iterg F γ N b) ∗ I)))
    isplitl [Hcr HI]
    · iapply (Hspec.spec (E := E)) $$ %(Iterg F γ N)
      isplitl [Hcr]
      · rw [← IterCreditV_succ]; iexact Hcr
      · iexact HI
    iintro %w' ⟨%b, %hret, Hcrb, HIb⟩
    obtain ⟨w', hwlc'⟩ := w'
    simp only at hret
    subst hret
    cases b
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
        · rw [show IterCreditV F γ N = Iterg F γ N true from rfl]
          iexact Hcrb
        · iexact HIb
      iintro %w Hpost
      iapply tglWp_value
      iexact Hpost

end
end Examples
end TotalEris
end ProbLang
