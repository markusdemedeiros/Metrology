module

public import Metrology.TotalEris.ErisGS
public import Metrology.TotalEris.TotalLifting
public import Metrology.Iris.SpecRules  -- for `ExtTreeMap.insert_eq_PartialMap_insert`

@[expose] public section

/-!
# Total-correctness primitive WP laws

Port of `clutch/theories/eris/total_primitive_laws.v`. Adapts the partial-WP
versions in `Metrology/Approxis/PrimitiveLaws.lean` to `tglWp` by:

* replacing `wp_lift_atomic_head_step` with `twp_lift_atomic_head_step`,
* dropping the `▷` (no `iintro !>` needed since `tglWp` has no later guard).

Notation `↦`, `↪ₐ`, `↯` comes from `Metrology/Iris/{AppProgram,ErrorCredits}`. -/

open Std Iris Iris.Std Iris.BI Iris.ProofMode OFE COFE ProbLang ProbLang.TotalEris
  ProbLang.TotalEris.ErisWpGS
open scoped AppGS

/-! ### `toVal?` simp lemmas for head-step successor expressions

Local re-statement so this file does not depend on Approxis's
`PrimitiveLaws.lean` (eris should not need Approxis at all). -/

@[simp] theorem ProbLang.Exp.toVal?_lit (b : BaseLit) :
    (Exp.lit b).toVal? = some ⟨.lit b, IsVal.lit⟩ := rfl

@[simp] theorem ProbLang.Exp.toVal?_lam (e : Exp) :
    (Exp.lam e).toVal? = some ⟨.lam e, IsVal.lam⟩ := rfl

@[simp] theorem ProbLang.Exp.toVal?_fix (e : Exp) :
    (Exp.fix e).toVal? = some ⟨.fix e, IsVal.fix⟩ := rfl

/-! ### `ExtTreeMap.insert` ↔ `PartialMap.insert` bridge -/

attribute [simp] ExtTreeMap.insert_eq_PartialMap_insert

namespace ProbLang
namespace TotalEris

section Lifting

variable {hlc : Bool} {GF : BundledGFunctors} [ErisGS hlc GF]

/-! ## Heap operations -/

/-- Allocation. Rocq: `twp_alloc`. -/
theorem twp_alloc {E : CoPset} {v : Val} {Φ : Val → IProp GF} :
    iprop(∀ (l : Loc), appHeapFrag l v -∗ Φ (⟨.lit (.loc l), IsVal.lit⟩ : Val))
      ⊢@{IProp GF} tglWp E (.alloc (.ofVal v)) Φ := by
  iintro HΦ
  have Hv : (Exp.alloc (Exp.ofVal v)).toVal? = none :=
    Exp.toVal?_eq_none.mpr fun ⟨w⟩ => nomatch w
  iapply (twp_lift_atomic_head_step Hv)
  iintro %σ₁ Hσ
  imodintro
  isplitr
  · ipure_intro
    exact ⟨_, HeadStepSupport.AllocS (Exp.toVal?_ofVal v) rfl rfl
      |> (headStep_support_iff _ _ _ _).mpr⟩
  iintro %e₂ %σ₂ %Hstep
  rw [headStep_support_iff] at Hstep
  cases Hstep with
  | AllocS hvd hl hσ =>
    rw [Exp.toVal?_ofVal] at hvd; cases hvd; subst hl; subst hσ
    ihave HAlloc := app_state_heap_alloc (GF := GF) (σ := σ₁) v $$ Hσ
    imod HAlloc with ⟨Hσ', Hl⟩
    imodintro
    simp only [erisWpGS_stateInterp_eq, ExtTreeMap.insert_eq_PartialMap_insert,
      Exp.toVal?_lit]
    isplitl [Hσ']; · iexact Hσ'
    iapply HΦ $$ %σ₁.heap.fresh
    iexact Hl

/-- Load. Rocq: `twp_load`. -/
theorem twp_load {E : CoPset} {l : Loc} {v : Val} {Φ : Val → IProp GF} :
    iprop(appHeapFrag l v ∗ (appHeapFrag l v -∗ Φ v))
      ⊢@{IProp GF} tglWp E (.load (.lit (.loc l))) Φ := by
  iintro ⟨Hl, HΦ⟩
  have Hv : (Exp.load (Exp.lit (.loc l))).toVal? = none :=
    Exp.toVal?_eq_none.mpr fun ⟨w⟩ => nomatch w
  iapply (twp_lift_atomic_head_step Hv)
  iintro %σ₁ Hσ
  ihave %hlook := app_state_lookup_heap (GF := GF) (σ := σ₁) $$ Hσ Hl
  imodintro
  isplitr
  · ipure_intro
    exact ⟨_, HeadStepSupport.LoadS hlook rfl
      |> (headStep_support_iff _ _ _ _).mpr⟩
  iintro %e₂ %σ₂ %Hstep
  rw [headStep_support_iff] at Hstep
  cases Hstep with
  | LoadS hlook' hofv =>
    rw [hlook] at hlook'; cases hlook'; subst hofv
    imodintro
    simp only [erisWpGS_stateInterp_eq, Exp.toVal?_ofVal]
    isplitl [Hσ]; · iexact Hσ
    iapply HΦ; iexact Hl

/-- Store. Rocq: `twp_store`. -/
theorem twp_store {E : CoPset} {l : Loc} {v v' : Val} {Φ : Val → IProp GF} :
    iprop(appHeapFrag l v' ∗
        (appHeapFrag l v -∗ Φ (⟨.lit .unit, IsVal.lit⟩ : Val)))
      ⊢@{IProp GF} tglWp E (.store (.lit (.loc l)) (.ofVal v)) Φ := by
  iintro ⟨Hl, HΦ⟩
  have Hv : (Exp.store (Exp.lit (.loc l)) (Exp.ofVal v)).toVal? = none :=
    Exp.toVal?_eq_none.mpr fun ⟨w⟩ => nomatch w
  iapply (twp_lift_atomic_head_step Hv)
  iintro %σ₁ Hσ
  ihave %hlook := app_state_lookup_heap (GF := GF) (σ := σ₁) $$ Hσ Hl
  imodintro
  isplitr
  · ipure_intro
    exact ⟨_, HeadStepSupport.StoreS (Exp.toVal?_ofVal v)
      (by rw [hlook]; exact Option.isSome_some) rfl
      |> (headStep_support_iff _ _ _ _).mpr⟩
  iintro %e₂ %σ₂ %Hstep
  rw [headStep_support_iff] at Hstep
  cases Hstep with
  | StoreS hvd _ hσ =>
    rw [Exp.toVal?_ofVal] at hvd; cases hvd; subst hσ
    ihave HUpd := app_state_update_heap (GF := GF) (σ := σ₁) (w := v) $$ Hσ Hl
    imod HUpd with ⟨Hσ', Hl'⟩
    imodintro
    simp only [erisWpGS_stateInterp_eq, ExtTreeMap.insert_eq_PartialMap_insert,
      Exp.toVal?_lit]
    isplitl [Hσ']; · iexact Hσ'
    iapply HΦ; iexact Hl'

/-! ## Tape operations -/

/-- Allocate a fresh tape. Rocq: `twp_alloc_tape`. -/
theorem twp_alloctape {E : CoPset} {z : Int} {Φ : Val → IProp GF} :
    iprop(∀ (l : Loc), appTapesFrag l (Tape.empty z) -∗
        Φ (⟨.lit (.lbl l), IsVal.lit⟩ : Val))
      ⊢@{IProp GF} tglWp E (.tape (.lit (.int z))) Φ := by
  iintro HΦ
  have Hv : (Exp.tape (Exp.lit (.int z))).toVal? = none :=
    Exp.toVal?_eq_none.mpr fun ⟨w⟩ => nomatch w
  iapply (twp_lift_atomic_head_step Hv)
  iintro %σ₁ Hσ
  imodintro
  isplitr
  · ipure_intro
    exact ⟨_, HeadStepSupport.TapeS (ℓ := σ₁.tapes.fresh) rfl rfl
      |> (headStep_support_iff _ _ _ _).mpr⟩
  iintro %e₂ %σ₂ %Hstep
  rw [headStep_support_iff] at Hstep
  cases Hstep with
  | TapeS hl hσ =>
    subst hl; subst hσ
    ihave HAlloc := app_state_tape_alloc (GF := GF) (σ := σ₁) (Tape.empty z) $$ Hσ
    imod HAlloc with ⟨Hσ', Hl⟩
    imodintro
    simp only [erisWpGS_stateInterp_eq, ExtTreeMap.insert_eq_PartialMap_insert,
      Exp.toVal?_lit]
    isplitl [Hσ']; · iexact Hσ'
    iapply HΦ $$ %σ₁.tapes.fresh
    iexact Hl

/-! ## Random sampling -/

/-- Uniform sample from `[0, z)`. Rocq: `twp_rand`. -/
theorem twp_rand {E : CoPset} {z : Int} {Φ : Val → IProp GF} (Hz : 0 < z) :
    iprop(∀ (n : Int), (⌜0 ≤ n ∧ n < z⌝) -∗
        Φ (⟨.lit (.int n), IsVal.lit⟩ : Val))
      ⊢@{IProp GF} tglWp E (.rand (.lit (.int z)) (.lit .unit)) Φ := by
  iintro HΦ
  have Hv : (Exp.rand (Exp.lit (.int z)) (Exp.lit .unit)).toVal? = none :=
    Exp.toVal?_eq_none.mpr fun ⟨w⟩ => nomatch w
  iapply (twp_lift_atomic_head_step Hv)
  iintro %σ₁ Hσ
  imodintro
  isplitr
  · ipure_intro
    refine ⟨⟨.lit (.int 0), σ₁⟩, ?_⟩
    rw [headStep_support_iff]
    exact .RandNoTapeS Hz (_root_.le_refl _) Hz
  iintro %e₂ %σ₂ %Hstep
  rw [headStep_support_iff] at Hstep
  cases Hstep with
  | RandNoTapeS _ Hv0 Hvz =>
    imodintro
    simp only [erisWpGS_stateInterp_eq, Exp.toVal?_lit]
    isplitl [Hσ]; · iexact Hσ
    iapply HΦ
    ipure_intro
    exact ⟨Hv0, Hvz⟩
  | RandNonposS hnz => exact absurd Hz hnz

/-- Read the head of a non-empty tape. Rocq: `twp_rand_tape`. -/
theorem twp_rand_tape {E : CoPset} {l : Loc} {z : Int}
    {n : { z' : Int // 0 ≤ z' ∧ z' < z }}
    {ns : List { z' : Int // 0 ≤ z' ∧ z' < z }}
    {Φ : Val → IProp GF} :
    iprop(l ↪ₐ ⟨z, n :: ns⟩ ∗
        (l ↪ₐ ⟨z, ns⟩ -∗ Φ (⟨.lit (.int n.val), IsVal.lit⟩ : Val)))
      ⊢@{IProp GF} tglWp E (.rand (.lit (.int z)) (.lit (.lbl l))) Φ := by
  iintro ⟨Hl, HΦ⟩
  have Hv : (Exp.rand (Exp.lit (.int z)) (Exp.lit (.lbl l))).toVal? = none :=
    Exp.toVal?_eq_none.mpr fun ⟨w⟩ => nomatch w
  iapply (twp_lift_atomic_head_step Hv)
  iintro %σ₁ Hσ
  ihave %hlook := app_state_lookup_tape (GF := GF) (σ := σ₁) $$ Hσ Hl
  have Hzpos : 0 < z := _root_.lt_of_le_of_lt n.2.1 n.2.2
  imodintro
  isplitr
  · ipure_intro
    exact ⟨_, HeadStepSupport.RandTapeS hlook rfl rfl rfl
      |> (headStep_support_iff _ _ _ _).mpr⟩
  iintro %e₂ %σ₂ %Hstep
  rw [headStep_support_iff] at Hstep
  cases Hstep with
  | RandTapeS hlook' _ hv hσ =>
    rw [hlook] at hlook'
    cases hlook'
    subst hσ; subst hv
    ihave HUpd := app_state_update_tape (GF := GF) (σ := σ₁) (s := ⟨z, ns⟩) $$ Hσ Hl
    imod HUpd with ⟨Hσ', Hl'⟩
    imodintro
    simp only [erisWpGS_stateInterp_eq, ExtTreeMap.insert_eq_PartialMap_insert,
      Exp.toVal?_lit]
    isplitl [Hσ']; · iexact Hσ'
    iapply HΦ; iexact Hl'
  | RandTapeEmptyS _ hlook' _ _ _ _ =>
    rw [hlook] at hlook'; cases hlook'
  | RandTapeOtherS _ hlook' hne _ _ _ =>
    rw [hlook] at hlook'; cases hlook'; exact absurd rfl hne
  | RandTapeNonposEmptyS hnz _ _ => exact absurd Hzpos hnz
  | RandTapeNonposOtherS hnz _ _ => exact absurd Hzpos hnz

/-- Read from an empty tape: falls through to uniform sampling.
Rocq: `twp_rand_tape_empty`. -/
theorem twp_rand_tape_empty {E : CoPset} {l : Loc} {z : Int}
    {Φ : Val → IProp GF} (Hz : 0 < z) :
    iprop(l ↪ₐ ⟨z, []⟩ ∗
        (∀ (n : Int), l ↪ₐ ⟨z, []⟩ -∗ (⌜0 ≤ n ∧ n < z⌝) -∗
          Φ (⟨.lit (.int n), IsVal.lit⟩ : Val)))
      ⊢@{IProp GF} tglWp E (.rand (.lit (.int z)) (.lit (.lbl l))) Φ := by
  iintro ⟨Hl, HΦ⟩
  have Hv : (Exp.rand (Exp.lit (.int z)) (Exp.lit (.lbl l))).toVal? = none :=
    Exp.toVal?_eq_none.mpr fun ⟨w⟩ => nomatch w
  iapply (twp_lift_atomic_head_step Hv)
  iintro %σ₁ Hσ
  ihave %hlook := app_state_lookup_tape (GF := GF) (σ := σ₁) $$ Hσ Hl
  imodintro
  isplitr
  · ipure_intro
    refine ⟨⟨.lit (.int 0), σ₁⟩, ?_⟩
    rw [headStep_support_iff]
    exact .RandTapeEmptyS Hz hlook rfl (_root_.le_refl _) Hz rfl
  iintro %e₂ %σ₂ %Hstep
  rw [headStep_support_iff] at Hstep
  cases Hstep with
  | RandTapeS hlook' _ _ _ =>
    rw [hlook] at hlook'; cases hlook'
  | RandTapeEmptyS _ _ _ Hv0 Hvz hσ =>
    subst hσ
    imodintro
    simp only [erisWpGS_stateInterp_eq, Exp.toVal?_lit]
    isplitl [Hσ]; · iexact Hσ
    iapply HΦ $$ Hl
    ipure_intro; exact ⟨Hv0, Hvz⟩
  | RandTapeOtherS _ hlook' hne _ _ _ =>
    rw [hlook] at hlook'; cases hlook'; exact absurd rfl hne
  | RandTapeNonposEmptyS hnz _ _ => exact absurd Hz hnz
  | RandTapeNonposOtherS hnz _ _ => exact absurd Hz hnz

end Lifting

end TotalEris
end ProbLang
