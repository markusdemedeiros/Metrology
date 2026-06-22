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
      tglWp E pl(&GeometricTrial v #0) (fun (v : Val rT) => iprop%
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
  have Hval : pl(v).isValue (rT := rT) := sorry
  twp_pures
  -- The value/expression thing rises again...
  -- Should I just make values a subtype of expressions?

  -- twp_bind pl(&v #.unit)
  -- New F, that includes the induction term, generic constructions
  ihave X := Hspec.spec (E := E) $$ %F [Hε_spec Hε_term]
  · sorry
  -- Apply the sampler spec `X` to the bound coin-flip via WP monotonicity.
  -- iapply tglWp_wand
  -- isplitl [X]
  -- · iexact X
  -- -- Continuation: case on the sampled boolean `b`, then finish each branch.
  -- iintro %w Hpost
  all_goals sorry
