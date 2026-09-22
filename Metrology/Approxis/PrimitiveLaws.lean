module

public import Metrology.Approxis.AppWeakestpre
import Metrology.ProbLang.Syntax.Notation
public import Metrology.Iris.AppProgram
public import Metrology.Iris.SpecProgram
public import Metrology.Iris.SpecUpdate
public import Metrology.Iris.SpecRules
public import Metrology.Iris.ErrorCredits

@[expose] public section

set_option linter.discrete false


/-!
# Primitive Laws

Instantiates `ApproxisWpGS` at concrete ProbLang ghost state and proves
primitive WP rules for each language primitive.
-/

open Std Iris Iris.Std Iris.BI Iris.ProofMode OFE COFE ProbLang ProbLang.ApproxisWpGS
open scoped AppGS

namespace ProbLang

-- For the Approxis layer, carry the abstract real type `rT` as a section variable.


variable {rT : Type _} [ProbLang.ProbLangℝ rT] [MeasurableSingletonClass rT]

/-! ## Bundled ghost-state class -/
/-- Embeds `SpecGS` as a non-extends field to avoid Lean's diamond-inheritance
field collapse, which would force program and spec heaps to share γ-names. -/
class ApproxisGS (rT : Type _) [ProbLang.ProbLangℝ rT]
    [MeasurableSingletonClass rT]
    (hlc : outParam HasLC) (GF : BundledGFunctors) where
  appGS    : AppGS rT GF
  specGS   : SpecGS rT GF
  ecGS     : ECGS GF
  invGS    : InvGS_gen hlc GF

attribute [reducible, instance] ApproxisGS.appGS ApproxisGS.specGS
  ApproxisGS.ecGS ApproxisGS.invGS

/-! ## `ApproxisWpGS` instance synthesis -/

section ApproxisInstance

variable {hlc : HasLC} {GF : BundledGFunctors} [ApproxisGS rT hlc GF]

@[reducible]
noncomputable instance approxisWpGS_of_components : ApproxisWpGS (rT := rT) GF where
  hlc := hlc
  invGS := inferInstance
  stateInterp σ := appStateAuth σ
  errInterp ε := ecAuth ε

/-! ### `stateInterp` / `errInterp` unfolding lemmas -/

@[simp] theorem approxisWpGS_stateInterp_eq :
    (ApproxisWpGS.stateInterp : State rT → IProp GF) = appStateAuth := rfl

@[simp] theorem approxisWpGS_errInterp_eq :
    (ApproxisWpGS.errInterp (rT := rT) (GF := GF) : ENNReal → IProp GF) = ecAuth := rfl

@[simp] theorem approxisWpGS_specInterp_eq :
    (SpecUpdateGS.specInterp : Cfg rT → IProp GF) = Cfg.specAuth := rfl

end ApproxisInstance

/-! ### `toVal?` simp lemmas for head-step successor expressions -/

/-! ### `ExtTreeMap.insert` ↔ `PartialMap.insert` bridge -/

attribute [simp] ExtTreeMap.insert_eq_PartialMap_insert

/-! ## Primitive WP laws -/

section Lifting

variable {hlc : HasLC} {GF : BundledGFunctors} [ApproxisGS rT hlc GF]

theorem wp_alloc {E : CoPset} {v : Val rT} {Φ : Val rT → IProp GF} :
    iprop(∀ (l : Loc), appHeapFrag l v -∗ Φ (.loc l : Val rT))
      ⊢@{IProp GF} wp E (.alloc (.ofVal v)) Φ := by
  iintro HΦ
  have Hv : (Exp.alloc (Exp.ofVal v)).toVal? = none :=
    Exp.toVal?_eq_none.mpr fun ⟨w⟩ => nomatch w
  iapply (wp_lift_atomic_head_step Hv)
  iintro %σ₁ Hσ !>
  isplitr
  · ipureintro
    exact ⟨_, (HeadStepSupport.AllocS (Exp.toVal?_ofVal v) rfl rfl).pos⟩
  iintro !> %e₂ %σ₂ %Hstep
  replace Hstep := Possible.headStepSupport (possible_iff_pos.mpr Hstep)
  cases Hstep with
  | AllocS hvd hl hσ =>
    rw [Exp.toVal?_ofVal] at hvd; cases hvd; subst hl; subst hσ
    imod app_state_heap_alloc v $$ Hσ with ⟨Hσ', Hl⟩
    imodintro
    simp only [approxisWpGS_stateInterp_eq, ExtTreeMap.insert_eq_PartialMap_insert,
      Exp.toVal?_lit]
    iframe Hσ'
    iapply HΦ $$ %σ₁.heap.fresh
    iexact Hl

theorem wp_load {E : CoPset} {l : Loc} {v : Val rT} {Φ : Val rT → IProp GF} :
    iprop(appHeapFrag l v ∗ (appHeapFrag l v -∗ Φ v))
      ⊢@{IProp GF} wp E pl(!#(.loc l)) Φ := by
  iintro ⟨Hl, HΦ⟩
  have Hv : (pl(!#(.loc l)) : Exp rT).toVal? = none :=
    Exp.toVal?_eq_none.mpr fun ⟨w⟩ => nomatch w
  iapply (wp_lift_atomic_head_step Hv)
  iintro %σ₁ Hσ
  ihave %hlook := app_state_lookup_heap (GF := GF) (σ := σ₁) $$ Hσ Hl
  imodintro
  isplitr
  · ipureintro
    exact ⟨_, (HeadStepSupport.LoadS hlook rfl).pos⟩
  iintro !> %e₂ %σ₂ %Hstep
  replace Hstep := Possible.headStepSupport (possible_iff_pos.mpr Hstep)
  cases Hstep with
  | LoadS hlook' hofv =>
    rw [hlook] at hlook'; cases hlook'; subst hofv
    imodintro
    simp only [approxisWpGS_stateInterp_eq, Exp.toVal?_ofVal]
    iframe Hσ
    iapply HΦ $$ Hl


theorem wp_store {E : CoPset} {l : Loc} {v v' : Val rT} {Φ : Val rT → IProp GF} :
    iprop(appHeapFrag l v' ∗
        (appHeapFrag l v -∗ Φ (.unit : Val rT)))
      ⊢@{IProp GF} wp E (.store pl(#(.loc l)) (.ofVal v)) Φ := by
  iintro ⟨Hl, HΦ⟩
  have Hv : (Exp.store pl(#(.loc l)) (Exp.ofVal v)).toVal? = none :=
    Exp.toVal?_eq_none.mpr fun ⟨w⟩ => nomatch w
  iapply (wp_lift_atomic_head_step Hv)
  iintro %σ₁ Hσ
  ihave %hlook := app_state_lookup_heap (GF := GF) (σ := σ₁) $$ Hσ Hl
  imodintro
  isplitr
  · ipureintro
    exact ⟨_, (HeadStepSupport.StoreS (Exp.toVal?_ofVal v)
        (by rw [hlook]; exact Option.isSome_some) rfl).pos⟩
  iintro !> %e₂ %σ₂ %Hstep
  replace Hstep := Possible.headStepSupport (possible_iff_pos.mpr Hstep)
  cases Hstep with
  | StoreS hvd _ hσ =>
    rw [Exp.toVal?_ofVal] at hvd; cases hvd; subst hσ
    imod app_state_update_heap $$ Hσ Hl with ⟨Hσ', Hl'⟩
    imodintro
    simp only [approxisWpGS_stateInterp_eq, ExtTreeMap.insert_eq_PartialMap_insert,
      Exp.toVal?_lit]
    iframe Hσ'
    iapply HΦ $$ Hl'

theorem wp_alloctape {E : CoPset} {z : Int} {Φ : Val rT → IProp GF} :
    iprop(∀ (l : Loc), appTapesFrag l (Tape.empty z) -∗
        Φ (.lbl l : Val rT))
      ⊢@{IProp GF} wp E (pl(tape(#(.int z)))) Φ := by
  iintro HΦ
  have Hv : (pl(tape(#(.int z))) : Exp rT).toVal? = none :=
    Exp.toVal?_eq_none.mpr fun ⟨w⟩ => nomatch w
  iapply (wp_lift_atomic_head_step Hv)
  iintro %σ₁ Hσ !>
  isplitr
  · ipureintro
    exact ⟨_, (HeadStepSupport.TapeS rfl rfl).pos⟩
  iintro !> %e₂ %σ₂ %Hstep
  replace Hstep := Possible.headStepSupport (possible_iff_pos.mpr Hstep)
  cases Hstep with
  | TapeS hl hσ =>
    subst hl; subst hσ
    imod app_state_tape_alloc (Tape.empty z) $$ Hσ with ⟨Hσ', Hl⟩
    imodintro
    simp only [approxisWpGS_stateInterp_eq, ExtTreeMap.insert_eq_PartialMap_insert,
      Exp.toVal?_lit]
    iframe Hσ'
    iapply HΦ $$ %σ₁.tapes.fresh
    iexact Hl

theorem wp_rand {E : CoPset} {z : Int} {Φ : Val rT → IProp GF} (Hz : 0 < z) :
    iprop(∀ (n : Int), (⌜0 ≤ n ∧ n < z⌝) -∗
        Φ (.int n : Val rT))
      ⊢@{IProp GF} wp E (pl(rand(#(.int z), #(.unit)))) Φ := by
  iintro HΦ
  have Hv : (pl(rand(#(.int z), #(.unit))) : Exp rT).toVal? = none :=
    Exp.toVal?_eq_none.mpr fun ⟨w⟩ => nomatch w
  iapply (wp_lift_atomic_head_step Hv)
  iintro %σ₁ Hσ !>
  isplitr
  · ipureintro
    refine ⟨⟨pl(#(.int 0)), σ₁⟩, ?_⟩
    refine HeadStepSupport.pos ?_
    exact .RandNoTapeS Hz (_root_.le_refl _) Hz
  iintro !> %e₂ %σ₂ %Hstep
  replace Hstep := Possible.headStepSupport (possible_iff_pos.mpr Hstep)
  cases Hstep with
  | RandNoTapeS _ Hv0 Hvz =>
    imodintro
    simp only [approxisWpGS_stateInterp_eq, Exp.toVal?_lit]
    iframe Hσ
    iapply HΦ
    ipureintro
    exact ⟨Hv0, Hvz⟩
  | RandNonposS hnz => exact absurd Hz hnz

/-- `rand z ()` for `z ≤ 0` is deterministic, returning the sentinel `-1`. -/
theorem wp_rand_nonpos {E : CoPset} {z : Int} {Φ : Val rT → IProp GF} (Hz : ¬ 0 < z) :
    iprop(Φ (.int (-1) : Val rT))
      ⊢@{IProp GF} wp E (pl(rand(#(.int z), #(.unit)))) Φ := by
  iintro HΦ
  have Hv : (pl(rand(#(.int z), #(.unit))) : Exp rT).toVal? = none :=
    Exp.toVal?_eq_none.mpr fun ⟨w⟩ => nomatch w
  iapply (wp_lift_atomic_head_step Hv)
  iintro %σ₁ Hσ !>
  isplitr
  · ipureintro
    refine ⟨⟨pl(#(.int (-1))), σ₁⟩, ?_⟩
    refine HeadStepSupport.pos ?_
    exact .RandNonposS Hz
  iintro !> %e₂ %σ₂ %Hstep
  replace Hstep := Possible.headStepSupport (possible_iff_pos.mpr Hstep)
  cases Hstep with
  | RandNoTapeS hpos _ _ => exact absurd hpos Hz
  | RandNonposS _ =>
    imodintro
    simp only [approxisWpGS_stateInterp_eq, Exp.toVal?_lit]
    iframe Hσ
    iexact HΦ

theorem wp_rand_tape {E : CoPset} {l : Loc} {z : Int} {n : Int} {ns : List Int}
    {Φ : Val rT → IProp GF} :
    iprop(appNatTape l z (n :: ns) ∗
        (appNatTape l z ns -∗ (⌜0 ≤ n ∧ n < z⌝) -∗
          Φ (.int n : Val rT)))
      ⊢@{IProp GF} wp E (pl(rand(#(.int z), #(.lbl l)))) Φ := by
  iintro ⟨Hl, HΦ⟩
  have Hv : (pl(rand(#(.int z), #(.lbl l))) : Exp rT).toVal? = none :=
    Exp.toVal?_eq_none.mpr fun ⟨w⟩ => nomatch w
  iapply (wp_lift_atomic_head_step Hv)
  iintro %σ₁ Hσ
  ihave Hread := app_read_natTape_head
    (n := n) (ns := ns) $$ Hl
  icases Hread with ⟨%x, %xs, Hback, %hxv, HHandback⟩
  ihave %hlook := app_state_lookup_tape $$ Hσ Hback
  have Hzpos : 0 < z := by
    have := x.2
    omega
  imodintro
  isplitr
  · ipureintro
    exact ⟨_, (HeadStepSupport.RandTapeS hlook rfl rfl rfl).pos⟩
  iintro !> %e₂ %σ₂ %Hstep
  replace Hstep := Possible.headStepSupport (possible_iff_pos.mpr Hstep)
  cases Hstep with
  | RandTapeS hlook' _ hv hσ =>
    rw [hlook] at hlook'
    cases hlook'
    subst hσ; subst hv; subst hxv
    imod app_state_update_tape $$ Hσ Hback with ⟨Hσ', Hl'⟩
    imodintro
    simp only [approxisWpGS_stateInterp_eq, ExtTreeMap.insert_eq_PartialMap_insert,
      Exp.toVal?_lit]
    iframe Hσ'
    ihave HlNew := HHandback $$ Hl'
    iapply HΦ $$ HlNew
    ipureintro; exact x.2
  | RandTapeEmptyS _ hlook' _ _ _ _ =>
    rw [hlook] at hlook'; cases hlook'
  | RandTapeOtherS _ hlook' hne _ _ _ =>
    rw [hlook] at hlook'; cases hlook'; exact absurd rfl hne
  | RandTapeNonposEmptyS hnz _ _ => exact absurd Hzpos hnz
  | RandTapeNonposOtherS hnz _ _ => exact absurd Hzpos hnz

theorem wp_rand_tape_empty {E : CoPset} {l : Loc} {z : Int}
    {Φ : Val rT → IProp GF} (Hz : 0 < z) :
    iprop(appNatTape l z [] ∗
        (∀ (n : Int), appNatTape l z [] -∗ (⌜0 ≤ n ∧ n < z⌝) -∗
          Φ (.int n : Val rT)))
      ⊢@{IProp GF} wp E (pl(rand(#(.int z), #(.lbl l)))) Φ := by
  iintro ⟨Hl, HΦ⟩
  ihave HlBack := app_natTape_to_empty $$ Hl
  have Hv : (pl(rand(#(.int z), #(.lbl l))) : Exp rT).toVal? = none :=
    Exp.toVal?_eq_none.mpr fun ⟨w⟩ => nomatch w
  iapply (wp_lift_atomic_head_step Hv)
  iintro %σ₁ Hσ
  ihave %hlook := app_state_lookup_tape (GF := GF) (σ := σ₁) $$ Hσ HlBack
  imodintro
  isplitr
  · ipureintro
    refine ⟨⟨pl(#(.int 0)), σ₁⟩, ?_⟩
    refine HeadStepSupport.pos ?_
    exact .RandTapeEmptyS Hz hlook rfl (_root_.le_refl _) Hz rfl
  iintro !> %e₂ %σ₂ %Hstep
  replace Hstep := Possible.headStepSupport (possible_iff_pos.mpr Hstep)
  cases Hstep with
  | RandTapeS hlook' _ _ _ =>
    rw [hlook] at hlook'; cases hlook'
  | RandTapeEmptyS _ _ _ Hv0 Hvz hσ =>
    subst hσ
    imodintro
    simp only [approxisWpGS_stateInterp_eq, Exp.toVal?_lit]
    iframe Hσ
    ihave HlNat := app_empty_to_natTape $$ HlBack
    iapply HΦ $$ HlNat
    ipureintro; exact ⟨Hv0, Hvz⟩
  | RandTapeOtherS _ hlook' hne _ _ _ =>
    rw [hlook] at hlook'; cases hlook'; exact absurd rfl hne
  | RandTapeNonposEmptyS hnz _ _ => exact absurd Hz hnz
  | RandTapeNonposOtherS hnz _ _ => exact absurd Hz hnz

theorem wp_rand_tape_wrong_bound {E : CoPset} {l : Loc} {z M : Int}
    {ns : List Int} {Φ : Val rT → IProp GF}
    (Hz : 0 < z) (HneM : z ≠ M) :
    iprop(appNatTape l M ns ∗
        (∀ (n : Int), appNatTape l M ns -∗ (⌜0 ≤ n ∧ n < z⌝) -∗
          Φ (.int n : Val rT)))
      ⊢@{IProp GF} wp E (pl(rand(#(.int z), #(.lbl l)))) Φ := by
  iintro ⟨Hl, HΦ⟩
  ihave HlEx := show appNatTape l M ns ⊢@{IProp GF}
      ∃ fs : List { z' : Int // 0 ≤ z' ∧ z' < M },
        (⌜fs.map (fun x => x.val) = ns⌝) ∗ l ↪ₐ ⟨M, fs⟩ from
    BI.BIBase.Entails.rfl $$ Hl
  icases HlEx with ⟨%fs, %hmap, HlBack⟩
  have Hv : (pl(rand(#(.int z), #(.lbl l))) : Exp rT).toVal? = none :=
    Exp.toVal?_eq_none.mpr fun ⟨w⟩ => nomatch w
  iapply (wp_lift_atomic_head_step Hv)
  iintro %σ₁ Hσ
  ihave %hlook := app_state_lookup_tape (GF := GF) (σ := σ₁) $$ Hσ HlBack
  imodintro
  isplitr
  · ipureintro
    refine ⟨⟨pl(#(.int 0)), σ₁⟩, ?_⟩
    refine HeadStepSupport.pos ?_
    exact .RandTapeOtherS Hz hlook HneM (_root_.le_refl _) Hz rfl
  iintro !> %e₂ %σ₂ %Hstep
  replace Hstep := Possible.headStepSupport (possible_iff_pos.mpr Hstep)
  cases Hstep with
  | RandTapeS hlook' heq _ _ =>
    rw [hlook] at hlook'; cases hlook'; exact absurd heq HneM
  | RandTapeEmptyS _ hlook' heq _ _ _ =>
    rw [hlook] at hlook'; cases hlook'; exact absurd heq HneM
  | RandTapeNonposEmptyS hnz _ _ => exact absurd Hz hnz
  | RandTapeNonposOtherS hnz _ _ => exact absurd Hz hnz
  | RandTapeOtherS _ _ _ Hv0 Hvz hσ =>
    subst hσ
    imodintro
    simp only [approxisWpGS_stateInterp_eq, Exp.toVal?_lit]
    iframe Hσ
    ihave HlNat := show (l ↪ₐ ⟨M, fs⟩) ⊢@{IProp GF} appNatTape l M ns by
      iintro Hb
      unfold appNatTape
      iexists fs
      iframe %hmap
      iexact Hb
    ihave HlNat' := HlNat $$ HlBack
    iapply HΦ $$ HlNat'
    ipureintro; exact ⟨Hv0, Hvz⟩

/-! ### Spec-side `_r` WPs -/

theorem wp_rand_r {E : CoPset} (K : Ectx rT) {z : Int} {e : Exp rT}
    {Φ : Val rT → IProp GF} (Hz : 0 < z) :
    iprop((⤇ K.fill (pl(rand(#(.int z), #(.unit))))) ∗
        (∀ (n : Int), (⌜0 ≤ n ∧ n < z⌝) -∗
          (⤇ K.fill pl(#(.int n))) -∗ wp E e Φ))
      ⊢@{IProp GF} wp E e Φ := by
  iintro ⟨Hj, Hwp⟩
  iapply wp_lift_step_spec_couple
  iintro %σ₁ %e₁' %σ₁' %ε₁ ⟨Hσ, Hs, Hε⟩
  ihave %Heq := specAuth_specFrag_agree (GF := GF) (σ := σ₁') $$ Hs Hj
  subst Heq
  have Hhead_rand : 0 < headStep ⟨pl(rand(#(.int z), #(.unit))), σ₁'⟩
        {⟨pl(#(.int 0)), σ₁'⟩} :=
    HeadStepSupport.pos (.RandNoTapeS Hz (_root_.le_refl _) Hz)
  have Hhr_rand : HeadReducible (pl(rand(#(.int z), #(.unit)))) σ₁' :=
    fun hz => by rw [hz] at Hhead_rand; simp at Hhead_rand
  have Hred : Discrete.Reducible (K.fill (pl(rand(#(.int z), #(.unit))))) σ₁' :=
    Reducible.toDiscrete (by no_urand)
      ((reducible_of_headReducible (by is_lc) Hhr_rand).fill K)
  imod (BIFUpdate.subset (E1 := E) (E2 := ∅) Std.LawfulSet.empty_subset)
    with Hclose
  imodintro
  iapply (specCoupl_step (Hred := Hred))
  iintro %e₂' %σ₂' %Hstep
  have Hv_rand : ¬ (pl(rand(#(.int z), #(.unit))) : Exp rT).isValue := by
    intro ⟨w⟩; nomatch w
  obtain ⟨e', heq_e2', Hstep'⟩ := primStep_fill_inv Hv_rand Hstep
  subst heq_e2'
  have Hheq : primStep ⟨pl(rand(#(.int z), #(.unit))), σ₁'⟩ =
      headStep ⟨pl(rand(#(.int z), #(.unit))), σ₁'⟩ :=
    primStep_eq_headStep
      (Exp.decompItem_none_of_lc_headReducible (by is_lc) Hhr_rand)
  rw [Hheq] at Hstep'; replace Hstep' := Possible.headStepSupport (possible_iff_pos.mpr Hstep')
  cases Hstep' with
  | RandNoTapeS _ Hv0 Hvz =>
    imodintro
    iapply specCoupl_ret
    ihave HUpd := specProg_update (GF := GF)
      (e3 := K.fill pl(#(.int _))) $$ Hs Hj
    imod HUpd with ⟨Hs', Hj'⟩
    imod Hclose
    imodintro
    iframe Hσ
    iframe Hs'
    iframe Hε
    iapply Hwp
    · ipureintro; exact ⟨Hv0, Hvz⟩
    · iexact Hj'
  | RandNonposS hnz => exact absurd Hz hnz

/-- `rand z (lbl l)` for `z ≤ 0` is deterministic on `-1`, given that tape
`l` is empty. With a queued value, the rand pops it even when `z ≤ 0`, so
emptiness is required. -/
theorem wp_rand_lbl_nonpos {E : CoPset} {l : Loc} {z N : Int}
    {Φ : Val rT → IProp GF} (Hz : ¬ 0 < z) :
    iprop(appTapesFrag l ⟨N, []⟩ ∗
        (appTapesFrag l ⟨N, []⟩ -∗ Φ (.int (-1) : Val rT)))
      ⊢@{IProp GF} wp E (pl(rand(#(.int z), #(.lbl l)))) Φ := by
  iintro ⟨Hl, HΦ⟩
  have Hv : (pl(rand(#(.int z), #(.lbl l))) : Exp rT).toVal? = none :=
    Exp.toVal?_eq_none.mpr fun ⟨w⟩ => nomatch w
  iapply (wp_lift_atomic_head_step Hv)
  iintro %σ₁ Hσ
  ihave %hlook := app_state_lookup_tape (GF := GF) (σ := σ₁) $$ Hσ Hl
  imodintro
  isplitr
  · ipureintro
    refine ⟨⟨pl(#(.int (-1))), σ₁⟩, ?_⟩
    refine HeadStepSupport.pos ?_
    by_cases hN : N = z
    · subst hN; exact .RandTapeNonposEmptyS Hz hlook rfl
    · exact .RandTapeNonposOtherS Hz hlook (Ne.symm hN)
  iintro !> %e₂ %σ₂ %Hstep
  replace Hstep := Possible.headStepSupport (possible_iff_pos.mpr Hstep)
  cases Hstep with
  | RandTapeS hlook' _ _ _ =>
    rw [hlook] at hlook'
    exact absurd (Option.some.inj hlook') (by intro h; cases h)
  | RandTapeEmptyS hpos _ _ _ _ _ => exact absurd hpos Hz
  | RandTapeOtherS hpos _ _ _ _ _ => exact absurd hpos Hz
  | RandTapeNonposEmptyS _ _ _ =>
    imodintro
    simp only [approxisWpGS_stateInterp_eq, Exp.toVal?_lit]
    iframe Hσ
    iapply HΦ $$ Hl
  | RandTapeNonposOtherS _ _ _ =>
    imodintro
    simp only [approxisWpGS_stateInterp_eq, Exp.toVal?_lit]
    iframe Hσ
    iapply HΦ $$ Hl

/-- Spec-side: `rand z ()` for `z ≤ 0` deterministically returns `-1`. -/
theorem wp_rand_nonpos_r {E : CoPset} (K : Ectx rT) {z : Int} {e : Exp rT}
    {Φ : Val rT → IProp GF} (Hz : ¬ 0 < z) :
    iprop((⤇ K.fill (pl(rand(#(.int z), #(.unit))))) ∗
        ((⤇ K.fill (pl(#(.int (-1))))) -∗ wp E e Φ))
      ⊢@{IProp GF} wp E e Φ := by
  iintro ⟨Hj, Hwp⟩
  iapply wp_lift_step_spec_couple
  iintro %σ₁ %e₁' %σ₁' %ε₁ ⟨Hσ, Hs, Hε⟩
  ihave %Heq := specAuth_specFrag_agree (GF := GF) (σ := σ₁') $$ Hs Hj
  subst Heq
  have Hhead_rand : 0 < headStep ⟨pl(rand(#(.int z), #(.unit))), σ₁'⟩
        {⟨pl(#(.int (-1))), σ₁'⟩} :=
    HeadStepSupport.pos (.RandNonposS Hz)
  have Hhr_rand : HeadReducible (pl(rand(#(.int z), #(.unit)))) σ₁' :=
    fun hz => by rw [hz] at Hhead_rand; simp at Hhead_rand
  have Hred : Discrete.Reducible (K.fill (pl(rand(#(.int z), #(.unit))))) σ₁' :=
    Reducible.toDiscrete (by no_urand)
      ((reducible_of_headReducible (by is_lc) Hhr_rand).fill K)
  imod (BIFUpdate.subset (E1 := E) (E2 := ∅) Std.LawfulSet.empty_subset)
    with Hclose
  imodintro
  iapply (specCoupl_step (Hred := Hred))
  iintro %e₂' %σ₂' %Hstep
  have Hv_rand : ¬ (pl(rand(#(.int z), #(.unit))) : Exp rT).isValue := by
    intro ⟨w⟩; nomatch w
  obtain ⟨e', heq_e2', Hstep'⟩ := primStep_fill_inv Hv_rand Hstep
  subst heq_e2'
  have Hheq : primStep ⟨pl(rand(#(.int z), #(.unit))), σ₁'⟩ =
      headStep ⟨pl(rand(#(.int z), #(.unit))), σ₁'⟩ :=
    primStep_eq_headStep
      (Exp.decompItem_none_of_lc_headReducible (by is_lc) Hhr_rand)
  rw [Hheq] at Hstep'; replace Hstep' := Possible.headStepSupport (possible_iff_pos.mpr Hstep')
  cases Hstep' with
  | RandNoTapeS hpos _ _ => exact absurd hpos Hz
  | RandNonposS _ =>
    imodintro
    iapply specCoupl_ret
    ihave HUpd := specProg_update (GF := GF)
      (e3 := K.fill (pl(#(.int (-1))))) $$ Hs Hj
    imod HUpd with ⟨Hs', Hj'⟩
    imod Hclose
    imodintro
    iframe Hσ
    iframe Hs'
    iframe Hε
    iapply Hwp $$ Hj'

theorem wp_rand_tape_empty_r {E : CoPset} (K : Ectx rT) {l : Loc} {z : Int} {e : Exp rT}
    {Φ : Val rT → IProp GF} (Hz : 0 < z) :
    iprop((⤇ K.fill (pl(rand(#(.int z), #(.lbl l))))) ∗ specNatTape l z [] ∗
        (∀ (n : Int), specNatTape l z [] -∗
          (⤇ K.fill pl(#(.int n))) -∗ (⌜0 ≤ n ∧ n < z⌝) -∗ wp E e Φ))
      ⊢@{IProp GF} wp E e Φ := by
  iintro ⟨Hj, Hα, Hwp⟩
  ihave HαB := spec_natTape_to_empty $$ Hα
  iapply wp_lift_step_spec_couple
  iintro %σ₁ %e₁' %σ₁' %ε₁ ⟨Hσ, Hs, Hε⟩
  ihave %Heq := specAuth_specFrag_agree (GF := GF) (σ := σ₁') $$ Hs Hj
  subst Heq
  ihave %hlook := spec_auth_lookup_tape $$ Hs HαB
  have Hhead : 0 < headStep ⟨pl(rand(#(.int z), #(.lbl l))), σ₁'⟩
        {⟨pl(#(.int 0)), σ₁'⟩} :=
    HeadStepSupport.pos
      (.RandTapeEmptyS Hz hlook rfl (_root_.le_refl _) Hz rfl)
  have Hhr : HeadReducible (pl(rand(#(.int z), #(.lbl l)))) σ₁' :=
    fun hz => by rw [hz] at Hhead; simp at Hhead
  have Hred : Discrete.Reducible (K.fill (pl(rand(#(.int z), #(.lbl l))))) σ₁' :=
    Reducible.toDiscrete (by no_urand)
      ((reducible_of_headReducible (by is_lc) Hhr).fill K)
  imod (BIFUpdate.subset (E1 := E) (E2 := ∅) Std.LawfulSet.empty_subset)
    with Hclose
  imodintro
  iapply (specCoupl_step (Hred := Hred))
  iintro %e₂' %σ₂' %Hstep
  have Hv_rand : ¬ (pl(rand(#(.int z), #(.lbl l))) : Exp rT).isValue := by
    intro ⟨w⟩; nomatch w
  obtain ⟨e', heq_e2', Hstep'⟩ := primStep_fill_inv Hv_rand Hstep
  subst heq_e2'
  have Hheq : primStep ⟨pl(rand(#(.int z), #(.lbl l))), σ₁'⟩ =
      headStep ⟨pl(rand(#(.int z), #(.lbl l))), σ₁'⟩ :=
    primStep_eq_headStep
      (Exp.decompItem_none_of_lc_headReducible (by is_lc) Hhr)
  rw [Hheq] at Hstep'; replace Hstep' := Possible.headStepSupport (possible_iff_pos.mpr Hstep')
  cases Hstep' with
  | RandTapeS hlook' _ _ _ =>
    rw [hlook] at hlook'; cases hlook'
  | RandTapeEmptyS _ _ _ Hv0 Hvz hσ =>
    subst hσ
    imodintro
    iapply specCoupl_ret
    ihave HUpd := specProg_update (GF := GF)
      (e3 := K.fill pl(#(.int _))) $$ Hs Hj
    imod HUpd with ⟨Hs', Hj'⟩
    imod Hclose
    imodintro
    iframe Hσ
    iframe Hs'
    iframe Hε
    ihave HαNat := spec_empty_to_natTape $$ HαB
    iapply Hwp $$ HαNat Hj'
    ipureintro; exact ⟨Hv0, Hvz⟩
  | RandTapeOtherS _ hlook' hne _ _ _ =>
    rw [hlook] at hlook'; cases hlook'; exact absurd rfl hne
  | RandTapeNonposEmptyS hnz _ _ => exact absurd Hz hnz
  | RandTapeNonposOtherS hnz _ _ => exact absurd Hz hnz

/-- Spec-side: `rand z (lbl l)` for `z ≤ 0` with empty tape deterministically
returns `-1`. -/
theorem wp_rand_lbl_nonpos_r {E : CoPset} (K : Ectx rT) {l : Loc} {z N : Int} {e : Exp rT}
    {Φ : Val rT → IProp GF} (Hz : ¬ 0 < z) :
    iprop((⤇ K.fill (pl(rand(#(.int z), #(.lbl l))))) ∗ specTapesFrag l ⟨N, []⟩ ∗
        (specTapesFrag l ⟨N, []⟩ -∗ (⤇ K.fill (pl(#(.int (-1))))) -∗ wp E e Φ))
      ⊢@{IProp GF} wp E e Φ := by
  iintro ⟨Hj, Hl, Hwp⟩
  iapply wp_lift_step_spec_couple
  iintro %σ₁ %e₁' %σ₁' %ε₁ ⟨Hσ, Hs, Hε⟩
  ihave %Heq := specAuth_specFrag_agree (GF := GF) (σ := σ₁') $$ Hs Hj
  subst Heq
  ihave %hlook := spec_auth_lookup_tape $$ Hs Hl
  have Hhead : 0 < headStep ⟨pl(rand(#(.int z), #(.lbl l))), σ₁'⟩
        {⟨pl(#(.int (-1))), σ₁'⟩} := by
    refine HeadStepSupport.pos ?_
    by_cases hN : N = z
    · subst hN; exact .RandTapeNonposEmptyS Hz hlook rfl
    · exact .RandTapeNonposOtherS Hz hlook (Ne.symm hN)
  have Hhr : HeadReducible (pl(rand(#(.int z), #(.lbl l)))) σ₁' :=
    fun hz => by rw [hz] at Hhead; simp at Hhead
  have Hred : Discrete.Reducible (K.fill (pl(rand(#(.int z), #(.lbl l))))) σ₁' :=
    Reducible.toDiscrete (by no_urand)
      ((reducible_of_headReducible (by is_lc) Hhr).fill K)
  imod (BIFUpdate.subset (E1 := E) (E2 := ∅) Std.LawfulSet.empty_subset)
    with Hclose
  imodintro
  iapply (specCoupl_step (Hred := Hred))
  iintro %e₂' %σ₂' %Hstep
  have Hv_rand : ¬ (pl(rand(#(.int z), #(.lbl l))) : Exp rT).isValue := by
    intro ⟨w⟩; nomatch w
  obtain ⟨e', heq_e2', Hstep'⟩ := primStep_fill_inv Hv_rand Hstep
  subst heq_e2'
  have Hheq : primStep ⟨pl(rand(#(.int z), #(.lbl l))), σ₁'⟩ =
      headStep ⟨pl(rand(#(.int z), #(.lbl l))), σ₁'⟩ :=
    primStep_eq_headStep
      (Exp.decompItem_none_of_lc_headReducible (by is_lc) Hhr)
  rw [Hheq] at Hstep'; replace Hstep' := Possible.headStepSupport (possible_iff_pos.mpr Hstep')
  cases Hstep' with
  | RandTapeS hlook' _ _ _ =>
    rw [hlook] at hlook'
    exact absurd (Option.some.inj hlook') (by intro h; cases h)
  | RandTapeEmptyS hpos _ _ _ _ _ => exact absurd hpos Hz
  | RandTapeOtherS hpos _ _ _ _ _ => exact absurd hpos Hz
  | RandTapeNonposEmptyS _ _ _ =>
    imodintro
    iapply specCoupl_ret
    ihave HUpd := specProg_update (GF := GF)
      (e3 := K.fill (pl(#(.int (-1))))) $$ Hs Hj
    imod HUpd with ⟨Hs', Hj'⟩
    imod Hclose
    imodintro
    iframe Hσ
    iframe Hs'
    iframe Hε
    iapply Hwp $$ Hl Hj'
  | RandTapeNonposOtherS _ _ _ =>
    imodintro
    iapply specCoupl_ret
    ihave HUpd := specProg_update (GF := GF)
      (e3 := K.fill (pl(#(.int (-1))))) $$ Hs Hj
    imod HUpd with ⟨Hs', Hj'⟩
    imod Hclose
    imodintro
    iframe Hσ
    iframe Hs'
    iframe Hε
    iapply Hwp $$ Hl Hj'

theorem wp_alloc_tape_r {E : CoPset} (K : Ectx rT) {z : Int} {e : Exp rT}
    {Φ : Val rT → IProp GF} :
    iprop((⤇ K.fill (pl(tape(#(.int z))))) ∗
        (∀ (l : Loc), (⤇ K.fill pl(#(.lbl l))) -∗
          specNatTape l z [] -∗ wp E e Φ))
      ⊢@{IProp GF} wp E e Φ := by
  iintro ⟨Hj, Hwp⟩
  imod step_alloctape K z $$ Hj with ⟨%l, Hj', Hl⟩
  ihave Hl' := show (l ↪ₛ Tape.empty z) ⊢@{IProp GF}
      (l ↪ₛ ⟨z, ([] : List { z' : Int // 0 ≤ z' ∧ z' < z })⟩) from
    BI.BIBase.Entails.rfl $$ Hl
  ihave HlNat := spec_empty_to_natTape $$ Hl'
  iapply Hwp $$ %l Hj' HlNat

theorem wp_rand_tape_r {E : CoPset} (K : Ectx rT) {z : Int} {l : Loc}
    {n : Int} {ns : List Int} {e : Exp rT} {Φ : Val rT → IProp GF} :
    iprop((⤇ K.fill (pl(rand(#(.int z), #(.lbl l))))) ∗
        specNatTape l z (n :: ns) ∗
        ((⤇ K.fill pl(#(.int n))) -∗ specNatTape l z ns -∗
            (⌜0 ≤ n ∧ n < z⌝) -∗ wp E e Φ))
      ⊢@{IProp GF} wp E e Φ := by
  iintro ⟨Hj, Hl, Hwp⟩
  ihave Hread := spec_read_natTape_head
    (n := n) (ns := ns) $$ Hl
  icases Hread with ⟨%x, %xs, Hback, %hxv, HHandback⟩
  imod step_rand K l x xs $$ [$] with ⟨Hj', Hback'⟩
  subst hxv
  ihave HlNew := HHandback $$ Hback'
  iapply Hwp $$ Hj' HlNew
  ipureintro; exact x.2

theorem wp_rand_empty_r {E : CoPset} (K : Ectx rT) {z : Int} {l : Loc}
    {e : Exp rT} {Φ : Val rT → IProp GF} (Hz : 0 < z) :
    iprop((⤇ K.fill (pl(rand(#(.int z), #(.lbl l))))) ∗
        specNatTape l z [] ∗
        (∀ (n : Int), (specNatTape l z [] ∗ ⤇ K.fill pl(#(.int n))) -∗
          (⌜0 ≤ n ∧ n < z⌝) -∗ wp E e Φ))
      ⊢@{IProp GF} wp E e Φ := by
  iintro ⟨Hj, Hα, Hwp⟩
  ihave Hαb := spec_natTape_to_empty $$ Hα
  iapply wp_lift_step_spec_couple
  iintro %σ₁ %e₁' %σ₁' %ε₁ ⟨Hσ, Hs, Hε⟩
  ihave %Heq := specAuth_specFrag_agree (GF := GF) (σ := σ₁') $$ Hs Hj
  subst Heq
  ihave %Hlk := spec_auth_lookup_tape (GF := GF) (σ := σ₁') $$ Hs Hαb
  have Hhead : 0 < headStep ⟨pl(rand(#(.int z), #(.lbl l))), σ₁'⟩
        {⟨pl(#(.int 0)), σ₁'⟩} :=
    HeadStepSupport.pos
      (.RandTapeEmptyS Hz Hlk rfl (_root_.le_refl _) Hz rfl)
  have Hhr : HeadReducible (pl(rand(#(.int z), #(.lbl l)))) σ₁' :=
    fun hz => by rw [hz] at Hhead; simp at Hhead
  have Hred : Discrete.Reducible (K.fill (pl(rand(#(.int z), #(.lbl l))))) σ₁' :=
    Reducible.toDiscrete (by no_urand)
      ((reducible_of_headReducible (by is_lc) Hhr).fill K)
  imod (BIFUpdate.subset (E1 := E) (E2 := ∅) Std.LawfulSet.empty_subset)
    with Hclose
  imodintro
  iapply (specCoupl_step (Hred := Hred))
  iintro %e₂' %σ₂' %Hstep
  have Hv_rand : ¬ (pl(rand(#(.int z), #(.lbl l))) : Exp rT).isValue := by
    intro ⟨w⟩; nomatch w
  obtain ⟨e', heq_e2', Hstep'⟩ := primStep_fill_inv Hv_rand Hstep
  subst heq_e2'
  have Hheq : primStep ⟨pl(rand(#(.int z), #(.lbl l))), σ₁'⟩ =
      headStep ⟨pl(rand(#(.int z), #(.lbl l))), σ₁'⟩ :=
    primStep_eq_headStep
      (Exp.decompItem_none_of_lc_headReducible (by is_lc) Hhr)
  rw [Hheq] at Hstep'; replace Hstep' := Possible.headStepSupport (possible_iff_pos.mpr Hstep')
  cases Hstep' with
  | RandTapeS Hlk' _ _ _ =>
    rw [Hlk] at Hlk'; cases Hlk'
  | RandTapeEmptyS _ _ _ Hv0 Hvz hσ =>
    subst hσ
    imodintro
    iapply specCoupl_ret
    ihave HUpd := specProg_update (GF := GF)
      (e3 := K.fill pl(#(.int _))) $$ Hs Hj
    imod HUpd with ⟨Hs', Hj'⟩
    imod Hclose
    imodintro
    iframe Hσ
    iframe Hs'
    iframe Hε
    ihave HαNat := spec_empty_to_natTape $$ Hαb
    ihave HwpArg := show
        (specNatTape l z [] ∗ ⤇ K.fill pl(#(.int _))) ⊢@{IProp GF}
        (specNatTape l z [] ∗ ⤇ K.fill pl(#(.int _))) from
      BI.BIBase.Entails.rfl $$ [HαNat Hj']
    · isplitl [HαNat] <;> iassumption
    iapply Hwp $$ HwpArg
    ipureintro; exact ⟨Hv0, Hvz⟩
  | RandTapeOtherS _ Hlk' hne _ _ _ =>
    rw [Hlk] at Hlk'; cases Hlk'; exact absurd rfl hne
  | RandTapeNonposEmptyS hnz _ _ => exact absurd Hz hnz
  | RandTapeNonposOtherS hnz _ _ => exact absurd Hz hnz

theorem wp_rand_wrong_tape_r {E : CoPset} (K : Ectx rT) {z M : Int} {l : Loc}
    {ns : List Int} {e : Exp rT} {Φ : Val rT → IProp GF}
    (Hz : 0 < z) (HneM : z ≠ M) :
    iprop((⤇ K.fill (pl(rand(#(.int z), #(.lbl l))))) ∗
        specNatTape l M ns ∗
        (∀ (n : Int), (specNatTape l M ns ∗ ⤇ K.fill pl(#(.int n))) -∗
          (⌜0 ≤ n ∧ n < z⌝) -∗ wp E e Φ))
      ⊢@{IProp GF} wp E e Φ := by
  iintro ⟨Hj, Hα, Hwp⟩
  ihave HαEx := show specNatTape l M ns ⊢@{IProp GF}
      ∃ fs : List { z' : Int // 0 ≤ z' ∧ z' < M },
        (⌜fs.map (fun x => x.val) = ns⌝) ∗ l ↪ₛ ⟨M, fs⟩ from
    BI.BIBase.Entails.rfl $$ Hα
  icases HαEx with ⟨%fs, %hmap, Hαb⟩
  iapply wp_lift_step_spec_couple
  iintro %σ₁ %e₁' %σ₁' %ε₁ ⟨Hσ, Hs, Hε⟩
  ihave %Heq := specAuth_specFrag_agree (GF := GF) (σ := σ₁') $$ Hs Hj
  subst Heq
  ihave %Hlk := spec_auth_lookup_tape (GF := GF) (σ := σ₁') $$ Hs Hαb
  have Hhead : 0 < headStep ⟨pl(rand(#(.int z), #(.lbl l))), σ₁'⟩
        {⟨pl(#(.int 0)), σ₁'⟩} :=
    HeadStepSupport.pos
      (.RandTapeOtherS Hz Hlk HneM (_root_.le_refl _) Hz rfl)
  have Hhr : HeadReducible (pl(rand(#(.int z), #(.lbl l)))) σ₁' :=
    fun hz => by rw [hz] at Hhead; simp at Hhead
  have Hred : Discrete.Reducible (K.fill (pl(rand(#(.int z), #(.lbl l))))) σ₁' :=
    Reducible.toDiscrete (by no_urand)
      ((reducible_of_headReducible (by is_lc) Hhr).fill K)
  imod (BIFUpdate.subset (E1 := E) (E2 := ∅) Std.LawfulSet.empty_subset)
    with Hclose
  imodintro
  iapply (specCoupl_step (Hred := Hred))
  iintro %e₂' %σ₂' %Hstep
  have Hv_rand : ¬ (pl(rand(#(.int z), #(.lbl l))) : Exp rT).isValue := by
    intro ⟨w⟩; nomatch w
  obtain ⟨e', heq_e2', Hstep'⟩ := primStep_fill_inv Hv_rand Hstep
  subst heq_e2'
  have Hheq : primStep ⟨pl(rand(#(.int z), #(.lbl l))), σ₁'⟩ =
      headStep ⟨pl(rand(#(.int z), #(.lbl l))), σ₁'⟩ :=
    primStep_eq_headStep
      (Exp.decompItem_none_of_lc_headReducible (by is_lc) Hhr)
  rw [Hheq] at Hstep'; replace Hstep' := Possible.headStepSupport (possible_iff_pos.mpr Hstep')
  cases Hstep' with
  | RandTapeS Hlk' heq _ _ =>
    rw [Hlk] at Hlk'; cases Hlk'; exact absurd heq HneM
  | RandTapeEmptyS _ Hlk' heq _ _ _ =>
    rw [Hlk] at Hlk'; cases Hlk'; exact absurd heq HneM
  | RandTapeNonposEmptyS hnz _ _ => exact absurd Hz hnz
  | RandTapeNonposOtherS hnz _ _ => exact absurd Hz hnz
  | RandTapeOtherS _ _ _ Hv0 Hvz hσ =>
    subst hσ
    imodintro
    iapply specCoupl_ret
    ihave HUpd := specProg_update (GF := GF)
      (e3 := K.fill pl(#(.int _))) $$ Hs Hj
    imod HUpd with ⟨Hs', Hj'⟩
    imod Hclose
    imodintro
    iframe Hσ
    iframe Hs'
    iframe Hε
    ihave HαNat := show (l ↪ₛ ⟨M, fs⟩) ⊢@{IProp GF} specNatTape l M ns by
      iintro Hb
      unfold specNatTape
      iexists fs
      iframe %hmap
      iexact Hb
    ihave HαNat' := HαNat $$ Hαb
    ihave HwpArg := show
        (specNatTape l M ns ∗ ⤇ K.fill pl(#(.int _))) ⊢@{IProp GF}
        (specNatTape l M ns ∗ ⤇ K.fill pl(#(.int _))) from
      BI.BIBase.Entails.rfl $$ [HαNat' Hj']
    · isplitl [HαNat'] <;> iassumption
    iapply Hwp $$ HwpArg
    ipureintro; exact ⟨Hv0, Hvz⟩


end Lifting

end ProbLang
