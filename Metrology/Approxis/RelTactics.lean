import Metrology.Approxis.PrimitiveLaws
import Metrology.Approxis.Model
import Metrology.Approxis.AppRelRules
import Metrology.Approxis.Proofmode

/-!
# Relational Tactics — minimal kit for OTP-style examples

Macro wrappers around the existing `refines_*` lemmas in `AppRelRules.lean`
and `Compatibility.lean`. They paper over Lean-specific quirks (the
`Nat.repeat (▷·)` unfolding after `refines_pure_l/r`, the `Ectx.fill []`
identity rewrite, the `iintro !>` to strip the `▷`).

Naming convention: `rel_X_l`/`rel_X_r` mirror Rocq's `rel_X_l`/`rel_X_r`
from `rel_tactics.v`. -/

namespace ProbLang
open Iris Iris.BI Iris.ProofMode

/-! ### Pure-step tactics -/

/-- `rel_pure_l` — single pure step on the LHS. Caller provides the redex
shape via the `Hex` typeclass (auto-inferred for typical β-reduction,
`fst`/`snd`/etc. via existing `pureExec_*` instances). -/
syntax "rel_pure_l" : tactic
macro_rules
  | `(tactic| rel_pure_l) =>
    `(tactic| (iapply (refines_pure_l (K := []) (Hφ := by trivial));
               simp only [Nat.repeat]; iintro !>))

/-- `rel_pure_r` — single pure step on the RHS. -/
syntax "rel_pure_r" : tactic
macro_rules
  | `(tactic| rel_pure_r) =>
    `(tactic| iapply (refines_pure_r (K := []) (Hφ := by trivial)))

/-- `rel_pures_l` — iteratively apply `rel_pure_l` until no more pure
steps. Best-effort: stops when `rel_pure_l` fails. -/
syntax "rel_pures_l" : tactic
macro_rules
  | `(tactic| rel_pures_l) => `(tactic| (try repeat rel_pure_l))

/-- `rel_pures_r` — iterated `rel_pure_r`. -/
syntax "rel_pures_r" : tactic
macro_rules
  | `(tactic| rel_pures_r) => `(tactic| (try repeat rel_pure_r))

/-! ### Binding / structural -/

/-- `rel_apply lemma` — generic `iapply` for relational proofs. Equivalent
to plain `iapply` but provides a uniform tactic name for the rel_* family. -/
macro "rel_apply " L:term : tactic => `(tactic| iapply ($L : _))

/-- `rel_arrow_val` — finish a goal of the form `REL .lam _ << .lam _ : A → B`
via `refines_arrow_val`. -/
syntax "rel_arrow_val" : tactic
macro_rules
  | `(tactic| rel_arrow_val) => `(tactic| iapply refines_arrow_val)

/-- `rel_vals` — finish a value-relation goal via `refines_ret`. The caller
typically follows with `imodintro` and an `iexists`/`ipure_intro` proof of
the underlying `lrel_*` body. -/
syntax "rel_vals" : tactic
macro_rules
  | `(tactic| rel_vals) => `(tactic| iapply refines_ret)

/-! ### Heap operations -/

/-- `rel_alloc_l` — step a LHS `alloc v` to a fresh location. The
continuation receives `(l : Loc)` and `(l ↦ v)`. -/
syntax "rel_alloc_l" : tactic
macro_rules
  | `(tactic| rel_alloc_l) => `(tactic| iapply (refines_alloc_l (K := [])))

/-- `rel_alloc_r` — step a RHS `alloc v` to a fresh spec-side location. -/
syntax "rel_alloc_r" : tactic
macro_rules
  | `(tactic| rel_alloc_r) => `(tactic| iapply (refines_alloc_r (K := [])))

/-- `rel_load_l` — step a LHS `load #l`. -/
syntax "rel_load_l" : tactic
macro_rules
  | `(tactic| rel_load_l) => `(tactic| iapply (refines_load_l (K := [])))

/-- `rel_load_r` — step a RHS `load #l`. -/
syntax "rel_load_r" : tactic
macro_rules
  | `(tactic| rel_load_r) => `(tactic| iapply (refines_load_r (K := [])))

/-- `rel_store_l` — step a LHS `store #l v'`. -/
syntax "rel_store_l" : tactic
macro_rules
  | `(tactic| rel_store_l) => `(tactic| iapply (refines_store_l (K := [])))

/-- `rel_store_r` — step a RHS `store #l v'`. -/
syntax "rel_store_r" : tactic
macro_rules
  | `(tactic| rel_store_r) => `(tactic| iapply (refines_store_r (K := [])))

/-! ### Tape operations -/

/-- `rel_alloctape_l` — step a LHS `tape #z`. -/
syntax "rel_alloctape_l" : tactic
macro_rules
  | `(tactic| rel_alloctape_l) => `(tactic| iapply (refines_alloctape_l (K := [])))

/-- `rel_alloctape_r` — step a RHS `tape #z`. -/
syntax "rel_alloctape_r" : tactic
macro_rules
  | `(tactic| rel_alloctape_r) => `(tactic| iapply (refines_alloctape_r (K := [])))

/-! ### Rand operations -/

/-- `rel_randU_l Hz` — step a LHS `rand #z ()` with positivity proof `Hz`. -/
syntax "rel_randU_l" term : tactic
macro_rules
  | `(tactic| rel_randU_l $Hz) => `(tactic| iapply (refines_randU_l (K := []) $Hz))

/-- `rel_randU_r Hz` — step a RHS `rand #z ()`. -/
syntax "rel_randU_r" term : tactic
macro_rules
  | `(tactic| rel_randU_r $Hz) => `(tactic| iapply (refines_randU_r (K := []) $Hz))

/-- `rel_randT_l` — pop a LHS tape-rand. -/
syntax "rel_randT_l" : tactic
macro_rules
  | `(tactic| rel_randT_l) => `(tactic| iapply (refines_randT_l (K := [])))

/-- `rel_randT_r` — pop a RHS tape-rand. -/
syntax "rel_randT_r" : tactic
macro_rules
  | `(tactic| rel_randT_r) => `(tactic| iapply (refines_randT_r (K := [])))

end ProbLang
