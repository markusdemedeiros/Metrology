import Metrology.Approxis.PrimitiveLaws
import Metrology.Approxis.Model
import Metrology.Approxis.AppRelRules

/-! # Relational tactics: macro wrappers around `refines_*` lemmas, mirroring Rocq's `rel_*`. -/

namespace ProbLang
open Iris Iris.BI Iris.ProofMode

/-! ### Pure-step tactics -/

syntax "rel_pure_l" : tactic
macro_rules
  | `(tactic| rel_pure_l) =>
    `(tactic| (iapply (refines_pure_l (K := []) (Hφ := by trivial));
               simp only [Nat.repeat]; iintro !>))

syntax "rel_pure_r" : tactic
macro_rules
  | `(tactic| rel_pure_r) =>
    `(tactic| iapply (refines_pure_r (K := []) (Hφ := by trivial)))

syntax "rel_pures_l" : tactic
macro_rules
  | `(tactic| rel_pures_l) => `(tactic| (try repeat rel_pure_l))

syntax "rel_pures_r" : tactic
macro_rules
  | `(tactic| rel_pures_r) => `(tactic| (try repeat rel_pure_r))

/-! ### Binding / structural -/

macro "rel_apply " L:term : tactic => `(tactic| iapply ($L : _))

syntax "rel_arrow_val" : tactic
macro_rules
  | `(tactic| rel_arrow_val) => `(tactic| iapply refines_arrow_val)

syntax "rel_vals" : tactic
macro_rules
  | `(tactic| rel_vals) => `(tactic| iapply refines_ret)

/-! ### Heap operations -/

syntax "rel_alloc_l" : tactic
macro_rules
  | `(tactic| rel_alloc_l) => `(tactic| iapply (refines_alloc_l (K := [])))

syntax "rel_alloc_r" : tactic
macro_rules
  | `(tactic| rel_alloc_r) => `(tactic| iapply (refines_alloc_r (K := [])))

syntax "rel_load_l" : tactic
macro_rules
  | `(tactic| rel_load_l) => `(tactic| iapply (refines_load_l (K := [])))

syntax "rel_load_r" : tactic
macro_rules
  | `(tactic| rel_load_r) => `(tactic| iapply (refines_load_r (K := [])))

syntax "rel_store_l" : tactic
macro_rules
  | `(tactic| rel_store_l) => `(tactic| iapply (refines_store_l (K := [])))

syntax "rel_store_r" : tactic
macro_rules
  | `(tactic| rel_store_r) => `(tactic| iapply (refines_store_r (K := [])))

/-! ### Tape operations -/

syntax "rel_alloctape_l" : tactic
macro_rules
  | `(tactic| rel_alloctape_l) => `(tactic| iapply (refines_alloctape_l (K := [])))

syntax "rel_alloctape_r" : tactic
macro_rules
  | `(tactic| rel_alloctape_r) => `(tactic| iapply (refines_alloctape_r (K := [])))

/-! ### Rand operations -/

syntax "rel_randU_l" term : tactic
macro_rules
  | `(tactic| rel_randU_l $Hz) => `(tactic| iapply (refines_randU_l (K := []) $Hz))

syntax "rel_randU_r" term : tactic
macro_rules
  | `(tactic| rel_randU_r $Hz) => `(tactic| iapply (refines_randU_r (K := []) $Hz))

syntax "rel_randT_l" : tactic
macro_rules
  | `(tactic| rel_randT_l) => `(tactic| iapply (refines_randT_l (K := [])))

syntax "rel_randT_r" : tactic
macro_rules
  | `(tactic| rel_randT_r) => `(tactic| iapply (refines_randT_r (K := [])))

end ProbLang
