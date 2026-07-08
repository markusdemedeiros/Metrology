module

public import Metrology.TotalEris
public import Metrology.ProbLang.Reals
public import Metrology.TotalEris.Examples.BernoulliGeometric

@[expose] public section

/-!
# Geometric trial over an abstract Bernoulli — port of `bern_geo.v`

`GeoTrial b N` repeatedly runs the Bernoulli `b`; while it returns `true` it
increments the counter, and returns the counter when `b` first returns
`false`. The number of successes is geometrically distributed.

This is a generic combinator over any Bernoulli satisfying
`AbstractBernoulli` (reused from `BernoulliGeometric.lean` — the seam the whole
tower hangs on). It is the clean `Geo_μ`/`Geo_CreditV` formulation of the
geometric spec; `BernoulliGeometric.twp_GeometricTrial` is the shifted variant
with an explicit termination factor.

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

/-- Geometric PMF started at `N`. Rocq `Geo_μ`:
`[N ≤ n] · γ^(n-N) · (1-γ)`. -/
def Geoμ (γ : ↑unitInterval) (N n : ℕ) : ℝ≥0∞ :=
  if N ≤ n then .ofReal ((γ : ℝ) ^ (n - N) * (1 - γ)) else 0

/-- Rocq `Geo_CreditV`: `∑ₙ F n · Geo_μ γ N n`. -/
def GeoCreditV (F : ℕ → ℝ≥0∞) (γ : ↑unitInterval) (N : ℕ) : ℝ≥0∞ :=
  ∑' n : ℕ, F n * Geoμ γ N n

/-- Rocq `g` (local) — the per-trial credit split by Bernoulli outcome:
`true ↦ GeoCreditV F γ (N+1)`, `false ↦ F N`. -/
def Geog (F : ℕ → ℝ≥0∞) (γ : ↑unitInterval) (N : ℕ) : Bool → ℝ≥0∞
  | true => GeoCreditV F γ (N + 1)
  | false => F N

/-- Rocq `g_expectation`: the credit recurrence
`GeoCreditV F γ N = γ · GeoCreditV F γ (N+1) + (1-γ) · F N`. -/
theorem Geo_expectation {F : ℕ → ℝ≥0∞} {γ : ↑unitInterval} {N : ℕ} {M : ℝ≥0∞}
    (Hnn : ∀ n, F n ≤ M) :
    GeoCreditV F γ N =
      .ofReal γ * GeoCreditV F γ (N + 1) + (1 - .ofReal γ) * F N := by
  sorry

/-! ## Program

Rocq `GeoTrial := rec: "trial" "N" := if: e #() then "trial" ("N"+1) else "N"`
(closing over the Bernoulli `e`). Here the Bernoulli is passed explicitly as
the first argument `b`, matching `BernoulliGeometric.GeometricTrial`. -/
@[pl_fold]
def GeoTrial : Exp ℝ := pl%
  rec geo b N := if b #.unit then geo b (N + #1) else N

/-! ## Specification -/

/-- Rocq `wp_Geo`. -/
theorem twp_GeoTrial (E : CoPset) (v : Val ℝ) (γ : ↑unitInterval)
    (Hspec : AbstractBernoulli (rT := ℝ) (hlc := hlc) (GF := GF) v γ)
    (F : ℕ → ℝ≥0∞) (M : ℝ≥0∞) (Hnn : ∀ n, F n ≤ M) (N : ℕ) :
    ⊢@{IProp GF} ↯ (GeoCreditV F γ N) -∗
      tglWp E pl(&GeoTrial &v.1 #(.int (N : ℤ)))
        (fun w : Val ℝ => iprop(∃ n : ℕ, ⌜w.1 = .lit (.int (Int.ofNat n))⌝ ∗ ↯ (F n))) := by
  sorry

end
end Examples
end TotalEris
end ProbLang
