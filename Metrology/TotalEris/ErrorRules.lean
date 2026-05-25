module

public import Metrology.TotalEris.ErisGS

@[expose] public section

/-!
# Selective port of Eris error rules

Port of the *subset* of `clutch/theories/eris/error_rules.v` needed by the
target examples. The error-credit ghost-state lemmas (`split`, `combine`,
`weaken`, `contradict`, `zero`, amplification family) are already in
`Metrology/Iris/ErrorCredits.lean` under the `ErrorCredit` namespace.

This file just re-exports the relevant ones under conventional Rocq-style
names (`ec_split`, `ec_combine`, …) so example proofs can stay close to the
Rocq text. -/

open Std Iris Iris.Std Iris.BI Iris.ProofMode OFE COFE ProbLang ProbLang.TotalEris
open scoped ENNReal

namespace ProbLang
namespace TotalEris

variable {GF : BundledGFunctors} [ECGS GF]

/-! ## Error-credit re-exports

These delegate to `Metrology.Iris.ErrorCredits` lemmas in the `ErrorCredit`
namespace. The chosen names mirror Rocq (`ec_split`, …). -/

/-- `↯(ε₁ + ε₂) ⊢ ↯ε₁ ∗ ↯ε₂`. Rocq: `ec_split`. -/
theorem ec_split {ε₁ ε₂ : ENNReal} :
    iprop(↯(ε₁ + ε₂)) ⊢@{IProp GF} iprop(↯ε₁ ∗ ↯ε₂) :=
  ErrorCredit.split

/-- `↯ε₁ ∗ ↯ε₂ ⊢ ↯(ε₁ + ε₂)`. Rocq: `ec_combine`. -/
theorem ec_combine {ε₁ ε₂ : ENNReal} :
    iprop(↯ε₁ ∗ ↯ε₂) ⊢@{IProp GF} iprop(↯(ε₁ + ε₂)) :=
  ErrorCredit.combine

/-- Definitional equality on credits. Rocq: `ec_eq`. -/
theorem ec_eq {ε₁ ε₂ : ENNReal} (h : ε₁ = ε₂) :
    iprop(↯ε₁) ⊢@{IProp GF} iprop(↯ε₂) :=
  ErrorCredit.ext h

/-- `1 ≤ ε → ↯ε ⊢ False`. Rocq: `ec_contradict`. -/
theorem ec_contradict {ε : ENNReal} (h : 1 ≤ ε) :
    iprop(↯ε) ⊢@{IProp GF} iprop(False : IProp GF) :=
  ErrorCredit.contradict h

/-- `ε₂ ≤ ε₁ → ↯ε₁ ⊢ ↯ε₂`. Rocq: `ec_weaken`. -/
theorem ec_weaken {ε₁ ε₂ : ENNReal} (h : ε₂ ≤ ε₁) :
    iprop(↯ε₁) ⊢@{IProp GF} iprop(↯ε₂) :=
  ErrorCredit.weaken h

/-- `⊢ |==> ↯0`. Rocq: `ec_zero`. -/
theorem ec_zero : ⊢@{IProp GF} iprop(|==> ↯0) :=
  ErrorCredit.zero

/-- Error credits are valid: `↯ε ⊢ ⌜ε < 1⌝`. -/
theorem ec_valid {ε : ENNReal} :
    iprop(↯ε) ⊢@{IProp GF} iprop(⌜ε < 1⌝) :=
  ErrorCredit.valid

/-! ## Error induction

These are re-exports from `Metrology/Iris/ErrorCredits.lean`'s
`ErrorCredit.Induction` namespace, named to match Rocq's `eris_rules.v`. -/

/-- Geometric-amplification induction: from a Lean-level rule that says
"given the wand `↯(k*ε) -∗ P` and `↯ε`, you can prove `P`", conclude
`↯ε ⊢ P`. Rocq: `ec_ind_simpl_external` (`error_credits.v:395`). -/
theorem ec_ind_simpl_external {ε : ENNReal} {k : NNReal} {P : IProp GF}
    (hε : 0 < ε) (hk : 1 < k)
    (hamp : iprop((↯((k : ENNReal) * ε) -∗ P) ∗ ↯ε) ⊢@{IProp GF} P) :
    iprop(↯ε) ⊢@{IProp GF} P :=
  ErrorCredit.Induction.external_simple hε hk hamp

/-- Linear-amplification induction: from "given the wand `↯ε' -∗ P` (where
`ε' > ε`) and `↯ε`, you can prove `P`", conclude `↯ε ⊢ P`. Rocq:
`ec_induction` (`eris_rules.v:173`). The Lean version requires `ε' : NNReal`
(finite) and currently expresses the hypothesis at the iris-wand level. -/
theorem ec_induction {ε : ENNReal} {ε' : NNReal} {P : IProp GF}
    (hε : 0 < ε) (hε' : ε < ε') :
    iprop(□ ((↯(ε' : ENNReal) -∗ P) ∗ ↯ε -∗ P)) ⊢@{IProp GF} iprop(↯ε -∗ P) :=
  ErrorCredit.Induction.increasing hε hε'

end TotalEris
end ProbLang
