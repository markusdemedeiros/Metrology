module

public import Metrology.TotalEris.ErisGS
public import Metrology.TotalEris.TotalLifting
public import Metrology.Iris.SpecRules  -- for `ExtTreeMap.insert_eq_PartialMap_insert`

@[expose] public section

/-!
# Total-correctness primitive WP laws
-/

open Std Iris Iris.Std Iris.BI Iris.ProofMode OFE COFE ProbLang ProbLang.TotalEris ProbLang.TotalEris.ErisWpGS
open scoped AppGS

namespace ProbLang

variable {rT : Type _}

@[simp] theorem Exp.toVal?_lit (b : BaseLit rT) :
    (Exp.lit b).toVal? = some ⟨.lit b, IsVal.lit⟩ := rfl

@[simp] theorem Exp.toVal?_lam (e : Exp rT) :
    (Exp.lam e).toVal? = some ⟨.lam e, IsVal.lam⟩ := rfl

@[simp] theorem Exp.toVal?_fix (e : Exp rT) :
    (Exp.fix e).toVal? = some ⟨.fix e, IsVal.fix⟩ := rfl

/-! ### `ExtTreeMap.insert` ↔ `PartialMap.insert` bridge -/

attribute [simp] ExtTreeMap.insert_eq_PartialMap_insert

namespace TotalEris

section Lifting

variable {hlc : HasLC} {GF : BundledGFunctors} [ProbLangℝ rT] [ErisGS rT hlc GF]

/-! ## Heap operations -/

theorem twp_alloc {E : CoPset} {v : Val rT} {Φ : Val rT → IProp GF} : iprop%
    (∀ (l : Loc), appHeapFrag l v -∗ Φ ⟨.lit (.loc l), .lit⟩)
      ⊢@{IProp GF} tglWp E (.alloc (.ofVal v)) Φ := by
  iintro HΦ
  have Hv : (Exp.alloc (Exp.ofVal v) : Exp rT).toVal? = none :=
    Exp.toVal?_eq_none.mpr fun ⟨w⟩ => nomatch w
  iapply twp_lift_atomic_head_step Hv
  iintro %σ₁ Hσ
  imodintro
  isplitr
  · ipureintro
    exact (HeadStepSupport.AllocS (Exp.toVal?_ofVal v) rfl rfl).possible.ne_zero
  iintro %e₂ %σ₂ %Hstep
  rw [headStep_possible_iff] at Hstep
  cases Hstep with
  | AllocS hvd hl hσ =>
    rw [Exp.toVal?_ofVal] at hvd; cases hvd; subst hl; subst hσ
    imod app_state_heap_alloc v $$ Hσ with ⟨Hσ', Hl⟩
    imodintro
    simp only [erisWpGS_stateInterp_eq, ExtTreeMap.insert_eq_PartialMap_insert,
      Exp.toVal?_lit]
    iframe Hσ'
    iapply HΦ $$ %σ₁.heap.fresh Hl

/-- Load. Rocq: `twp_load`. -/
theorem twp_load {E : CoPset} {l : Loc} {v : Val rT} {Φ : Val rT → IProp GF} : iprop%
    (l ↦ v ∗ (l ↦ v -∗ Φ v)) ⊢@{IProp GF} tglWp E (.load (.lit (.loc l))) Φ := by
  iintro ⟨Hl, HΦ⟩
  have Hv : (Exp.load (Exp.lit (.loc l)) : Exp rT).toVal? = none :=
    Exp.toVal?_eq_none.mpr fun ⟨w⟩ => nomatch w
  iapply twp_lift_atomic_head_step Hv
  iintro %σ₁ Hσ
  ihave %hlook := app_state_lookup_heap $$ Hσ Hl
  imodintro
  isplitr
  · ipureintro
    exact (HeadStepSupport.LoadS hlook rfl).possible.ne_zero
  iintro %e₂ %σ₂ %Hstep
  rw [headStep_possible_iff] at Hstep
  cases Hstep with
  | LoadS hlook' hofv =>
    rw [hlook] at hlook'; cases hlook'; subst hofv
    imodintro
    simp only [erisWpGS_stateInterp_eq, Exp.toVal?_ofVal]
    iframe Hσ
    iapply HΦ $$ Hl

/-- Store. Rocq: `twp_store`. -/
theorem twp_store {E : CoPset} {l : Loc} {v v' : Val rT} {Φ : Val rT → IProp GF} : iprop%
    l ↦ v' ∗ (l ↦ v -∗ Φ ⟨.lit .unit, .lit⟩)
      ⊢@{IProp GF} tglWp E (.store (.lit (.loc l)) (.ofVal v)) Φ := by
  iintro ⟨Hl, HΦ⟩
  have Hv : (Exp.store (Exp.lit (.loc l)) (Exp.ofVal v) : Exp rT).toVal? = none :=
    Exp.toVal?_eq_none.mpr fun ⟨w⟩ => nomatch w
  iapply twp_lift_atomic_head_step Hv
  iintro %σ₁ Hσ
  ihave %hlook := app_state_lookup_heap (GF := GF) (σ := σ₁) $$ Hσ Hl
  imodintro
  isplitr
  · ipureintro
    exact (HeadStepSupport.StoreS (Exp.toVal?_ofVal v)
      (by rw [hlook]; exact Option.isSome_some) rfl).possible.ne_zero
  iintro %e₂ %σ₂ %Hstep
  rw [headStep_possible_iff] at Hstep
  cases Hstep with
  | StoreS hvd _ hσ =>
    rw [Exp.toVal?_ofVal] at hvd; cases hvd; subst hσ
    ihave HUpd := app_state_update_heap (GF := GF) (σ := σ₁) (w := v) $$ Hσ Hl
    imod HUpd with ⟨Hσ', Hl'⟩
    imodintro
    simp only [erisWpGS_stateInterp_eq, ExtTreeMap.insert_eq_PartialMap_insert, Exp.toVal?_lit]
    iframe Hσ'
    iapply HΦ $$ Hl'

/-! ## Tape operations -/

/-- Allocate a fresh tape. Rocq: `twp_alloc_tape`. -/
theorem twp_alloctape {E : CoPset} {z : Int} {Φ : Val rT → IProp GF} :
    (∀ (l : Loc), l ↪ₐ (Tape.empty z) -∗ Φ ⟨.lit (.lbl l), .lit⟩)
      ⊢@{IProp GF} tglWp E (.tape (.lit (.int z))) Φ := by
  iintro HΦ
  have Hv : (Exp.tape (Exp.lit (.int z)) : Exp rT).toVal? = none :=
    Exp.toVal?_eq_none.mpr fun ⟨w⟩ => nomatch w
  iapply twp_lift_atomic_head_step Hv
  iintro %σ₁ Hσ
  imodintro
  isplitr
  · ipureintro
    exact (HeadStepSupport.TapeS (ℓ := σ₁.tapes.fresh) rfl rfl).possible.ne_zero
  iintro %e₂ %σ₂ %Hstep
  rw [headStep_possible_iff] at Hstep
  cases Hstep with
  | TapeS hl hσ =>
    subst hl; subst hσ
    imod app_state_tape_alloc (Tape.empty z) $$ Hσ with ⟨Hσ', Hl⟩
    imodintro
    simp only [erisWpGS_stateInterp_eq, ExtTreeMap.insert_eq_PartialMap_insert, Exp.toVal?_lit]
    iframe Hσ'
    iapply HΦ $$ %σ₁.tapes.fresh
    iexact Hl

/-! ## Random sampling -/

theorem twp_rand {E : CoPset} {z : Int} {Φ : Val rT → IProp GF} (Hz : 0 < z) : iprop%
    (∀ (n : Int), (⌜0 ≤ n ∧ n < z⌝) -∗ Φ ⟨.lit (.int n), .lit⟩)
      ⊢@{IProp GF} tglWp E (.rand (.lit (.int z)) (.lit .unit)) Φ := by
  iintro HΦ
  have Hv : (Exp.rand (Exp.lit (.int z)) (Exp.lit .unit) : Exp rT).toVal? = none :=
    Exp.toVal?_eq_none.mpr fun ⟨w⟩ => nomatch w
  iapply twp_lift_atomic_head_step Hv
  iintro %σ₁ Hσ
  imodintro
  isplitr
  · ipureintro
    exact (HeadStepSupport.RandNoTapeS Hz (_root_.le_refl _) Hz).possible.ne_zero
  iintro %e₂ %σ₂ %Hstep
  rw [headStep_possible_iff] at Hstep
  cases Hstep with
  | RandNoTapeS _ Hv0 Hvz =>
    imodintro
    simp only [erisWpGS_stateInterp_eq, Exp.toVal?_lit]
    iframe Hσ
    iapply HΦ
    ipureintro
    exact ⟨Hv0, Hvz⟩
  | RandNonposS hnz => exact absurd Hz hnz

theorem twp_rand_tape {E : CoPset} {l : Loc} {z : Int} {n : { z' : Int // 0 ≤ z' ∧ z' < z }}
    {ns : List { z' : Int // 0 ≤ z' ∧ z' < z }} {Φ : Val rT → IProp GF} : iprop%
    (l ↪ₐ ⟨z, n :: ns⟩ ∗ (l ↪ₐ ⟨z, ns⟩ -∗ Φ ⟨.lit (.int n.val), .lit⟩))
      ⊢@{IProp GF} tglWp E (.rand (.lit (.int z)) (.lit (.lbl l))) Φ := by
  iintro ⟨Hl, HΦ⟩
  have Hv : (Exp.rand (Exp.lit (.int z)) (Exp.lit (.lbl l)) : Exp rT).toVal? = none :=
    Exp.toVal?_eq_none.mpr fun ⟨w⟩ => nomatch w
  iapply twp_lift_atomic_head_step Hv
  iintro %σ₁ Hσ
  ihave %hlook := app_state_lookup_tape (GF := GF) (σ := σ₁) $$ Hσ Hl
  have Hzpos : 0 < z := _root_.lt_of_le_of_lt n.2.1 n.2.2
  imodintro
  isplitr
  · ipureintro
    exact (HeadStepSupport.RandTapeS hlook rfl rfl rfl).possible.ne_zero
  iintro %e₂ %σ₂ %Hstep
  rw [headStep_possible_iff] at Hstep
  cases Hstep with
  | RandTapeS hlook' _ hv hσ =>
    rw [hlook] at hlook'
    cases hlook'
    subst hσ; subst hv
    imod app_state_update_tape (s := ⟨z, ns⟩) $$ Hσ Hl with ⟨Hσ', Hl'⟩
    imodintro
    simp only [erisWpGS_stateInterp_eq, ExtTreeMap.insert_eq_PartialMap_insert, Exp.toVal?_lit]
    iframe Hσ'
    iapply HΦ $$ Hl'
  | RandTapeEmptyS _ hlook' _ _ _ _ => rw [hlook] at hlook'; cases hlook'
  | RandTapeOtherS _ hlook' hne _ _ _ =>
    rw [hlook] at hlook'; cases hlook'; exact absurd rfl hne
  | RandTapeNonposEmptyS hnz _ _ => exact absurd Hzpos hnz
  | RandTapeNonposOtherS hnz _ _ => exact absurd Hzpos hnz

theorem twp_rand_tape_empty {E : CoPset} {l : Loc} {z : Int}
    {Φ : Val rT → IProp GF} (Hz : 0 < z) : iprop%
    (l ↪ₐ ⟨z, []⟩ ∗ (∀ (n : Int), l ↪ₐ ⟨z, []⟩ -∗ (⌜0 ≤ n ∧ n < z⌝) -∗ Φ ⟨.lit (.int n), .lit⟩))
      ⊢@{IProp GF} tglWp E (.rand (.lit (.int z)) (.lit (.lbl l))) Φ := by
  iintro ⟨Hl, HΦ⟩
  have Hv : (Exp.rand (Exp.lit (.int z)) (Exp.lit (.lbl l)) : Exp rT).toVal? = none :=
    Exp.toVal?_eq_none.mpr fun ⟨w⟩ => nomatch w
  iapply twp_lift_atomic_head_step Hv
  iintro %σ₁ Hσ
  ihave %hlook := app_state_lookup_tape (GF := GF) (σ := σ₁) $$ Hσ Hl
  imodintro
  isplitr
  · ipureintro
    exact (HeadStepSupport.RandTapeEmptyS Hz hlook rfl (_root_.le_refl _) Hz rfl).possible.ne_zero
  iintro %e₂ %σ₂ %Hstep
  rw [headStep_possible_iff] at Hstep
  cases Hstep with
  | RandTapeS hlook' _ _ _ => rw [hlook] at hlook'; cases hlook'
  | RandTapeEmptyS _ _ _ Hv0 Hvz hσ =>
    subst hσ
    imodintro
    simp only [erisWpGS_stateInterp_eq, Exp.toVal?_lit]
    iframe Hσ
    iapply HΦ $$ Hl
    ipureintro; exact ⟨Hv0, Hvz⟩
  | RandTapeOtherS _ hlook' hne _ _ _ =>
    rw [hlook] at hlook'; cases hlook'; exact absurd rfl hne
  | RandTapeNonposEmptyS hnz _ _ => exact absurd Hz hnz
  | RandTapeNonposOtherS hnz _ _ => exact absurd Hz hnz

end Lifting

end TotalEris
end ProbLang
