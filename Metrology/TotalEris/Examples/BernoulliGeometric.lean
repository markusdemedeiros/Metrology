module

public import Metrology.TotalEris

@[expose] public section

/-! # Geometric sampler -/

open Std Iris Iris.Std Iris.BI Iris.ProofMode OFE COFE ProbLang ProbLang.TotalEris
  ProbLang.TotalEris.ErisWpGS
open scoped AppGS ENNReal NNReal

namespace ProbLang
namespace TotalEris
namespace Examples

variable {rT : Type _} [ProbLangℝ rT]
variable {hlc : HasLC} {GF : BundledGFunctors.{0,0,0}} [ErisGS rT hlc GF]

structure AbstractBernoulli (e : Val rT) (γ : ℝ≥0) where
  factor_le_1 : γ ≤ 1
  spec {E} : iprop%
    ⊢@{IProp GF}
      ∀ (F : Bool → ℝ≥0∞),
      ↯ (γ * F true + (1 - γ) * F false) -∗
      tglWp E pl(&e.1 #.unit) (fun (v : Val rT) => iprop%
        ∃ b : Bool, ⌜ v.1 = .lit (.bool b) ⌝ ∗ ↯ (F b))

@[pl_fold]
def GeometricTrial : Exp rT := pl%
  rec geo trial N := if trial #.unit then geo (N + #1) else N

theorem twp_GeometricTrial (v : Val rT)
    (Hspec : AbstractBernoulli (hlc := hlc) (GF := GF) v γ):
    ⊢@{IProp GF}
      ∀ (F : Bool → ℝ≥0∞),
      ↯ (γ * F true + (1 - γ) * F false) -∗
      tglWp E pl(&GeometricTrial &v.1 #0) (fun (v : Val rT) => iprop%
        ∃ b : Bool, ⌜ v.1 = .lit (.bool b) ⌝ ∗ ↯ (F b)) := by
  -- Each recursive call is guarded behind a probability γ event, therefore it terminates.
  iintro %F Hε_spec
  -- Use fresh thin-air credit for termination proof
  iapply twp_err_pos solve_not_red
  iintro %ε_term %Hε_term_pos Hε_term
  let k : ℝ≥0 := sorry
  have Hk1 : 1 < k := sorry
  irevert Hε_spec
  iapply ErrorCredit.Induction.simple (k := k) Hε_term_pos Hk1 $$ [] Hε_term
  imodintro
  iintro ⟨IH, Hε_term⟩ Hε_spec
  rw (occs := [2]) [GeometricTrial]
  twp_pures
  -- The substituted coin is the stuck `openRec 0 #0 v.fst`. Since `v` is a value it is
  -- locally closed (`v.lc`, the `Val.lc` field), so opening is a no-op (`open_lc`) and the
  -- coin folds back to `v.fst` — which is exactly what the spec `X` below is about.
  rw [← Exp.open_lc 0 (Exp.lit (.int 0)) v.fst v.lc]
  -- Instantiate the abstract Bernoulli spec at our `F`, consuming the available credit.
  ihave X := Hspec.spec (E := E) $$ %F [Hε_spec Hε_term]
  · sorry -- credit accounting: the provided `↯` must match the spec's precondition
          -- (depends on the `k`/`Hk1` design constants — still `sorry`).
  -- Apply the coin-flip spec `X` to the bound `v ()` via WP monotonicity.
  twp_bind (Exp.app v.fst (Exp.lit .unit))
  iapply (ErisWpGS.tglWp_wand (Φ := fun (w : Val rT) =>
    iprop(∃ b : Bool, ⌜w.1 = .lit (.bool b)⌝ ∗ ↯ F b)))
  isplitl [X]
  · iexact X
  -- Continuation: given the sampled boolean `b`, finish each branch — recurse via `IH`
  -- on `true`, return on `false`. (Still to do.)
  iintro %w Hpost
  all_goals sorry
