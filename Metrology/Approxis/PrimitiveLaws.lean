import Metrology.Approxis.AppWeakestpre
import Metrology.Iris.AppProgram
import Metrology.Iris.SpecProgram
import Metrology.Iris.SpecUpdate
import Metrology.Iris.SpecRules
import Metrology.Iris.ErrorCredits

/-!
# Primitive Laws

Instantiates the abstract `ApproxisWpGS` at the concrete ProbLang ghost state
(program heap + tapes, spec heap + tapes, error credits) and proves the
primitive WP rules for each language primitive.

## Rocq source

`clutch/theories/approxis/primitive_laws.v`

## Concrete ghost-state instantiation

Rocq bundles program-side heap/tape ghost-maps + spec + error into a single
record `approxisGS` (primitive_laws.v:12–24), so all four γ-names are
allocated together and cannot alias. We reproduce the same guarantee by
bundling the three component GS classes into a single `ApproxisGS` class.

- `AppGS` (from `Metrology/Iris/AppProgram.lean`) — program heap + tapes γ's.
- `SpecGS` (from `Metrology/Iris/SpecProgram.lean`) — spec heap + tapes + prog γ's.
- `ECGS` (from `Metrology/Iris/ErrorCredits.lean`) — error-credit γ.

`ApproxisGS` extends all three (plus `InvGS_gen`). Downstream code should
depend on `[ApproxisGS GF]` alone; instances of `AppGS`/`SpecGS`/`ECGS` are
derived automatically. This (i) prevents γ-aliasing between program and spec
heaps (since any `ApproxisGS` instance instantiates all four γ-names at once)
and (ii) collapses the four-instance requirement at every call site to one.

**Status:** currently only the `ApproxisWpGS` instance is synthesized. The
actual primitive WP lemmas (`wp_alloc`, `wp_load`, ...) are the next
piece of work — see `clutch/theories/approxis/primitive_laws.v:162–505`.
-/

open Std Iris Iris.Std Iris.BI Iris.ProofMode OFE COFE ProbLang ProbLang.ApproxisWpGS
open scoped AppGS

namespace ProbLang

/-! ## Bundled ghost-state class

Mirrors Rocq's `approxisGS` record. Extending all four components in one
class ensures joint allocation of γ-names and prevents accidental aliasing
of program and spec heaps. -/
/-- **Structural port note.** We `extends AppGS, ECGS, InvGS_gen` but embed
`SpecGS` as a **non-extends** field `specGS`. Rocq's `approxisGS` uses
`approxisGS_spec :: specG_prob_lang Σ` (a nested instance field), giving the
spec-side heap/tape CMRAs and γ-names their own identities separate from the
program-side. If we instead used `extends SpecGS`, Lean's diamond-inheritance
field collapse would merge `AppPreGS.heap : ElemG GF (constOF SpecHeap)` with
`SpecPreGS.heap : ElemG GF (constOF SpecHeap)` (same type!), forcing program
and spec heaps to share γ-names — semantically wrong. -/
class ApproxisGS (hlc : outParam Bool) (GF : BundledGFunctors) where
  appGS    : AppGS GF
  specGS   : SpecGS GF
  ecGS     : ECGS GF
  invGS    : InvGS_gen hlc GF

-- Expose all nested component classes as instances so resources like `⤇ e`,
-- `appStateAuth`, `ecAuth`, etc. (which want `[SpecGS GF]` / `[AppGS GF]` /
-- `[ECGS GF]` / `[InvGS_gen hlc GF]`) resolve transparently under `[ApproxisGS hlc GF]`.
attribute [reducible, instance] ApproxisGS.appGS ApproxisGS.specGS
  ApproxisGS.ecGS ApproxisGS.invGS

/-! ## `ApproxisWpGS` instance synthesis

Given `[ApproxisGS hlc GF]`, package the concrete `stateInterp`/`errInterp`
as an `ApproxisWpGS` instance. Mirrors `approxisGS_irisGS` in
`primitive_laws.v:48–52`. -/

section ApproxisInstance

variable {hlc : Bool} {GF : BundledGFunctors} [ApproxisGS hlc GF]

@[reducible]
noncomputable instance approxisWpGS_of_components : ApproxisWpGS GF where
  hlc := hlc
  invGS := inferInstance
  stateInterp σ := appStateAuth σ
  errInterp ε := ecAuth ε

/-! ### `stateInterp` / `errInterp` unfolding lemmas

The `ApproxisWpGS` projections don't definitionally reduce through their
instance — `iexact` needs this bridge to use `appStateAuth`/`ecAuth`-framed
hypotheses. Marked `@[simp]` so `simp only` strips them automatically. -/

@[simp] theorem approxisWpGS_stateInterp_eq :
    (ApproxisWpGS.stateInterp : State → IProp GF) = appStateAuth := rfl

@[simp] theorem approxisWpGS_errInterp_eq :
    (ApproxisWpGS.errInterp : ENNReal → IProp GF) = ecAuth := rfl

@[simp] theorem approxisWpGS_specInterp_eq :
    (SpecUpdateGS.specInterp : Cfg → IProp GF) = Cfg.specAuth := rfl

end ApproxisInstance

/-! ### `toVal?` simp lemmas for head-step successor expressions

Every primitive WP needs to rewrite `(Exp.lit b).toVal? = some ⟨_, .lit⟩`,
`(Exp.lam e).toVal? = some ⟨_, .lam⟩`, etc., in the post-step continuation
where the match on `e₂.toVal?` is reduced. All are `rfl` because `IsVal.check?`
matches directly on the constructor. -/

@[simp] theorem Exp.toVal?_lit (b : BaseLit) :
    (Exp.lit b).toVal? = some ⟨.lit b, IsVal.lit⟩ := rfl

@[simp] theorem Exp.toVal?_lam (e : Exp) :
    (Exp.lam e).toVal? = some ⟨.lam e, IsVal.lam⟩ := rfl

@[simp] theorem Exp.toVal?_fix (e : Exp) :
    (Exp.fix e).toVal? = some ⟨.fix e, IsVal.fix⟩ := rfl

/-! ### `ExtTreeMap.insert` ↔ `PartialMap.insert` bridge

Promoted to `@[simp]` so heap/tape mutations unify automatically — the
`HeadStepSupport.AllocS`/`StoreS`/etc. cases produce `x.insert k v` forms
while our ghost-state update lemmas produce `PartialMap.insert x k v`. -/

attribute [simp] ExtTreeMap.insert_eq_PartialMap_insert

/-! ## Primitive WP laws -/

section Lifting

variable {hlc : Bool} {GF : BundledGFunctors} [ApproxisGS hlc GF]

/-- `wp_alloc` — allocate a fresh heap cell containing value `v`. The
continuation receives the fresh location `l` together with `l ↦ v`. -/
theorem wp_alloc {E : CoPset} {v : Val} {Φ : Val → IProp GF} :
    iprop(∀ (l : Loc), appHeapFrag l v -∗ Φ (⟨.lit (.loc l), IsVal.lit⟩ : Val))
      ⊢@{IProp GF} wp E (.alloc (.ofVal v)) Φ := by
  iintro HΦ
  have Hv : (Exp.alloc (Exp.ofVal v)).toVal? = none :=
    Exp.toVal?_eq_none.mpr fun ⟨w⟩ => nomatch w
  iapply (wp_lift_atomic_head_step Hv)
  iintro %σ₁ Hσ
  imodintro
  isplitr
  · ipure_intro
    exact ⟨_, HeadStepSupport.AllocS (Exp.toVal?_ofVal v) rfl rfl
      |> (headStep_support_iff _ _ _ _).mpr⟩
  iintro !> %e₂ %σ₂ %Hstep
  rw [headStep_support_iff] at Hstep
  cases Hstep with
  | AllocS hvd hl hσ =>
    rw [Exp.toVal?_ofVal] at hvd; cases hvd; subst hl; subst hσ
    ihave HAlloc := app_state_heap_alloc (GF := GF) (σ := σ₁) v $$ Hσ
    imod HAlloc with ⟨Hσ', Hl⟩
    imodintro
    simp only [approxisWpGS_stateInterp_eq, ExtTreeMap.insert_eq_PartialMap_insert,
      Exp.toVal?_lit]
    isplitl [Hσ']; · iexact Hσ'
    iapply HΦ $$ %σ₁.heap.fresh
    iexact Hl

/-- `wp_load` — read the value at heap location `l`. -/
theorem wp_load {E : CoPset} {l : Loc} {v : Val} {Φ : Val → IProp GF} :
    iprop(appHeapFrag l v ∗ (appHeapFrag l v -∗ Φ v))
      ⊢@{IProp GF} wp E (.load (.lit (.loc l))) Φ := by
  iintro ⟨Hl, HΦ⟩
  have Hv : (Exp.load (Exp.lit (.loc l))).toVal? = none :=
    Exp.toVal?_eq_none.mpr fun ⟨w⟩ => nomatch w
  iapply (wp_lift_atomic_head_step Hv)
  iintro %σ₁ Hσ
  ihave %hlook := app_state_lookup_heap (GF := GF) (σ := σ₁) $$ Hσ Hl
  imodintro
  isplitr
  · ipure_intro
    exact ⟨_, HeadStepSupport.LoadS hlook rfl
      |> (headStep_support_iff _ _ _ _).mpr⟩
  iintro !> %e₂ %σ₂ %Hstep
  rw [headStep_support_iff] at Hstep
  cases Hstep with
  | LoadS hlook' hofv =>
    rw [hlook] at hlook'; cases hlook'; subst hofv
    imodintro
    simp only [approxisWpGS_stateInterp_eq, Exp.toVal?_ofVal]
    isplitl [Hσ]; · iexact Hσ
    iapply HΦ; iexact Hl


/-- `wp_store` — overwrite the value at location `l` with `v`. -/
theorem wp_store {E : CoPset} {l : Loc} {v v' : Val} {Φ : Val → IProp GF} :
    iprop(appHeapFrag l v' ∗
        (appHeapFrag l v -∗ Φ (⟨.lit .unit, IsVal.lit⟩ : Val)))
      ⊢@{IProp GF} wp E (.store (.lit (.loc l)) (.ofVal v)) Φ := by
  iintro ⟨Hl, HΦ⟩
  have Hv : (Exp.store (Exp.lit (.loc l)) (Exp.ofVal v)).toVal? = none :=
    Exp.toVal?_eq_none.mpr fun ⟨w⟩ => nomatch w
  iapply (wp_lift_atomic_head_step Hv)
  iintro %σ₁ Hσ
  ihave %hlook := app_state_lookup_heap (GF := GF) (σ := σ₁) $$ Hσ Hl
  imodintro
  isplitr
  · ipure_intro
    exact ⟨_, HeadStepSupport.StoreS (Exp.toVal?_ofVal v)
      (by rw [hlook]; exact Option.isSome_some) rfl
      |> (headStep_support_iff _ _ _ _).mpr⟩
  iintro !> %e₂ %σ₂ %Hstep
  rw [headStep_support_iff] at Hstep
  cases Hstep with
  | StoreS hvd _ hσ =>
    rw [Exp.toVal?_ofVal] at hvd; cases hvd; subst hσ
    ihave HUpd := app_state_update_heap (GF := GF) (σ := σ₁) (w := v) $$ Hσ Hl
    imod HUpd with ⟨Hσ', Hl'⟩
    imodintro
    simp only [approxisWpGS_stateInterp_eq, ExtTreeMap.insert_eq_PartialMap_insert,
      Exp.toVal?_lit]
    isplitl [Hσ']; · iexact Hσ'
    iapply HΦ; iexact Hl'

/-- `wp_alloctape` — allocate a fresh tape with bound `z`. -/
theorem wp_alloctape {E : CoPset} {z : Int} {Φ : Val → IProp GF} :
    iprop(∀ (l : Loc), appTapesFrag l (Tape.empty z) -∗
        Φ (⟨.lit (.lbl l), IsVal.lit⟩ : Val))
      ⊢@{IProp GF} wp E (.tape (.lit (.int z))) Φ := by
  iintro HΦ
  have Hv : (Exp.tape (Exp.lit (.int z))).toVal? = none :=
    Exp.toVal?_eq_none.mpr fun ⟨w⟩ => nomatch w
  iapply (wp_lift_atomic_head_step Hv)
  iintro %σ₁ Hσ
  imodintro
  isplitr
  · ipure_intro
    exact ⟨_, HeadStepSupport.TapeS (ℓ := σ₁.tapes.fresh) rfl rfl
      |> (headStep_support_iff _ _ _ _).mpr⟩
  iintro !> %e₂ %σ₂ %Hstep
  rw [headStep_support_iff] at Hstep
  cases Hstep with
  | TapeS hl hσ =>
    subst hl; subst hσ
    ihave HAlloc := app_state_tape_alloc (GF := GF) (σ := σ₁) (Tape.empty z) $$ Hσ
    imod HAlloc with ⟨Hσ', Hl⟩
    imodintro
    simp only [approxisWpGS_stateInterp_eq, ExtTreeMap.insert_eq_PartialMap_insert,
      Exp.toVal?_lit]
    isplitl [Hσ']; · iexact Hσ'
    iapply HΦ $$ %σ₁.tapes.fresh
    iexact Hl

/-- `wp_rand` — sample a uniform random integer in `[0, z)` with no tape. -/
theorem wp_rand {E : CoPset} {z : Int} {Φ : Val → IProp GF} (Hz : 0 < z) :
    iprop(∀ (n : Int), (⌜0 ≤ n ∧ n < z⌝) -∗
        Φ (⟨.lit (.int n), IsVal.lit⟩ : Val))
      ⊢@{IProp GF} wp E (.rand (.lit (.int z)) (.lit .unit)) Φ := by
  iintro HΦ
  have Hv : (Exp.rand (Exp.lit (.int z)) (Exp.lit .unit)).toVal? = none :=
    Exp.toVal?_eq_none.mpr fun ⟨w⟩ => nomatch w
  iapply (wp_lift_atomic_head_step Hv)
  iintro %σ₁ Hσ
  imodintro
  isplitr
  · ipure_intro
    -- Pick v := 0; reducibility holds since 0 ≤ 0 < z.
    refine ⟨⟨.lit (.int 0), σ₁⟩, ?_⟩
    rw [headStep_support_iff]
    exact .RandNoTapeS Hz (_root_.le_refl _) Hz
  iintro !> %e₂ %σ₂ %Hstep
  rw [headStep_support_iff] at Hstep
  cases Hstep with
  | RandNoTapeS _ Hv0 Hvz =>
    imodintro
    simp only [approxisWpGS_stateInterp_eq, Exp.toVal?_lit]
    isplitl [Hσ]; · iexact Hσ
    iapply HΦ
    ipure_intro
    exact ⟨Hv0, Hvz⟩
  | RandNonposS hnz => exact absurd Hz hnz

/-- `wp_rand_nonpos` — `rand z ()` for `z ≤ 0` is deterministic, returning
the sentinel `-1`. Mirrors `wp_rand` but for the nonpositive branch. -/
theorem wp_rand_nonpos {E : CoPset} {z : Int} {Φ : Val → IProp GF} (Hz : ¬ 0 < z) :
    iprop(Φ (⟨.lit (.int (-1)), IsVal.lit⟩ : Val))
      ⊢@{IProp GF} wp E (.rand (.lit (.int z)) (.lit .unit)) Φ := by
  iintro HΦ
  have Hv : (Exp.rand (Exp.lit (.int z)) (Exp.lit .unit)).toVal? = none :=
    Exp.toVal?_eq_none.mpr fun ⟨w⟩ => nomatch w
  iapply (wp_lift_atomic_head_step Hv)
  iintro %σ₁ Hσ
  imodintro
  isplitr
  · ipure_intro
    refine ⟨⟨.lit (.int (-1)), σ₁⟩, ?_⟩
    rw [headStep_support_iff]
    exact .RandNonposS Hz
  iintro !> %e₂ %σ₂ %Hstep
  rw [headStep_support_iff] at Hstep
  cases Hstep with
  | RandNoTapeS hpos _ _ => exact absurd hpos Hz
  | RandNonposS _ =>
    imodintro
    simp only [approxisWpGS_stateInterp_eq, Exp.toVal?_lit]
    isplitl [Hσ]; · iexact Hσ
    iexact HΦ

/-- `wp_rand_tape` — read the head of a non-empty user-level tape,
obtaining an integer in `[0, z)`. -/
theorem wp_rand_tape {E : CoPset} {l : Loc} {z : Int} {n : Int} {ns : List Int}
    {Φ : Val → IProp GF} :
    iprop(appNatTape l z (n :: ns) ∗
        (appNatTape l z ns -∗ (⌜0 ≤ n ∧ n < z⌝) -∗
          Φ (⟨.lit (.int n), IsVal.lit⟩ : Val)))
      ⊢@{IProp GF} wp E (.rand (.lit (.int z)) (.lit (.lbl l))) Φ := by
  iintro ⟨Hl, HΦ⟩
  have Hv : (Exp.rand (Exp.lit (.int z)) (Exp.lit (.lbl l))).toVal? = none :=
    Exp.toVal?_eq_none.mpr fun ⟨w⟩ => nomatch w
  iapply (wp_lift_atomic_head_step Hv)
  iintro %σ₁ Hσ
  ihave Hread := app_read_natTape_head (GF := GF) (l := l) (z := z)
    (n := n) (ns := ns) $$ Hl
  icases Hread with ⟨%x, %xs, Hback, %hxv, HHandback⟩
  ihave %hlook := app_state_lookup_tape (GF := GF) (σ := σ₁) $$ Hσ Hback
  have Hzpos : 0 < z := by
    have := x.2
    omega
  imodintro
  isplitr
  · ipure_intro
    exact ⟨_, HeadStepSupport.RandTapeS hlook rfl rfl rfl
      |> (headStep_support_iff _ _ _ _).mpr⟩
  iintro !> %e₂ %σ₂ %Hstep
  rw [headStep_support_iff] at Hstep
  cases Hstep with
  | RandTapeS hlook' _ hv hσ =>
    rw [hlook] at hlook'
    cases hlook'
    subst hσ; subst hv; subst hxv
    ihave HUpd := app_state_update_tape (GF := GF) (σ := σ₁) (s := ⟨z, xs⟩) $$ Hσ Hback
    imod HUpd with ⟨Hσ', Hl'⟩
    imodintro
    simp only [approxisWpGS_stateInterp_eq, ExtTreeMap.insert_eq_PartialMap_insert,
      Exp.toVal?_lit]
    isplitl [Hσ']; · iexact Hσ'
    ihave HlNew := HHandback $$ Hl'
    iapply HΦ $$ HlNew
    ipure_intro; exact x.2
  | RandTapeEmptyS _ hlook' _ _ _ _ =>
    rw [hlook] at hlook'; cases hlook'
  | RandTapeOtherS _ hlook' hne _ _ _ =>
    rw [hlook] at hlook'; cases hlook'; exact absurd rfl hne
  | RandTapeNonposEmptyS hnz _ _ => exact absurd Hzpos hnz
  | RandTapeNonposOtherS hnz _ _ => exact absurd Hzpos hnz

/-- `wp_rand_tape_empty` — read from an *empty* user-level tape, falling back
to a uniform sample. The tape stays empty. -/
theorem wp_rand_tape_empty {E : CoPset} {l : Loc} {z : Int}
    {Φ : Val → IProp GF} (Hz : 0 < z) :
    iprop(appNatTape l z [] ∗
        (∀ (n : Int), appNatTape l z [] -∗ (⌜0 ≤ n ∧ n < z⌝) -∗
          Φ (⟨.lit (.int n), IsVal.lit⟩ : Val)))
      ⊢@{IProp GF} wp E (.rand (.lit (.int z)) (.lit (.lbl l))) Φ := by
  iintro ⟨Hl, HΦ⟩
  ihave HlBack := app_natTape_to_empty (GF := GF) (l := l) (z := z) $$ Hl
  have Hv : (Exp.rand (Exp.lit (.int z)) (Exp.lit (.lbl l))).toVal? = none :=
    Exp.toVal?_eq_none.mpr fun ⟨w⟩ => nomatch w
  iapply (wp_lift_atomic_head_step Hv)
  iintro %σ₁ Hσ
  ihave %hlook := app_state_lookup_tape (GF := GF) (σ := σ₁) $$ Hσ HlBack
  imodintro
  isplitr
  · ipure_intro
    refine ⟨⟨.lit (.int 0), σ₁⟩, ?_⟩
    rw [headStep_support_iff]
    exact .RandTapeEmptyS Hz hlook rfl (_root_.le_refl _) Hz rfl
  iintro !> %e₂ %σ₂ %Hstep
  rw [headStep_support_iff] at Hstep
  cases Hstep with
  | RandTapeS hlook' _ _ _ =>
    rw [hlook] at hlook'; cases hlook'
  | RandTapeEmptyS _ _ _ Hv0 Hvz hσ =>
    subst hσ
    imodintro
    simp only [approxisWpGS_stateInterp_eq, Exp.toVal?_lit]
    isplitl [Hσ]; · iexact Hσ
    ihave HlNat := app_empty_to_natTape (GF := GF) (l := l) (z := z) $$ HlBack
    iapply HΦ $$ HlNat
    ipure_intro; exact ⟨Hv0, Hvz⟩
  | RandTapeOtherS _ hlook' hne _ _ _ =>
    rw [hlook] at hlook'; cases hlook'; exact absurd rfl hne
  | RandTapeNonposEmptyS hnz _ _ => exact absurd Hz hnz
  | RandTapeNonposOtherS hnz _ _ => exact absurd Hz hnz

/-- `wp_rand_tape_wrong_bound` — read from a tape whose bound differs from
the `rand` argument; acts like the no-tape case. -/
theorem wp_rand_tape_wrong_bound {E : CoPset} {l : Loc} {z M : Int}
    {ns : List Int} {Φ : Val → IProp GF}
    (Hz : 0 < z) (HneM : z ≠ M) :
    iprop(appNatTape l M ns ∗
        (∀ (n : Int), appNatTape l M ns -∗ (⌜0 ≤ n ∧ n < z⌝) -∗
          Φ (⟨.lit (.int n), IsVal.lit⟩ : Val)))
      ⊢@{IProp GF} wp E (.rand (.lit (.int z)) (.lit (.lbl l))) Φ := by
  iintro ⟨Hl, HΦ⟩
  ihave HlEx := show appNatTape l M ns ⊢@{IProp GF}
      iprop(∃ fs : List { z' : Int // 0 ≤ z' ∧ z' < M },
        (⌜fs.map (fun x => x.val) = ns⌝) ∗ l ↪ₐ ⟨M, fs⟩) from
    BI.BIBase.Entails.rfl $$ Hl
  icases HlEx with ⟨%fs, %hmap, HlBack⟩
  have Hv : (Exp.rand (Exp.lit (.int z)) (Exp.lit (.lbl l))).toVal? = none :=
    Exp.toVal?_eq_none.mpr fun ⟨w⟩ => nomatch w
  iapply (wp_lift_atomic_head_step Hv)
  iintro %σ₁ Hσ
  ihave %hlook := app_state_lookup_tape (GF := GF) (σ := σ₁) $$ Hσ HlBack
  imodintro
  isplitr
  · ipure_intro
    refine ⟨⟨.lit (.int 0), σ₁⟩, ?_⟩
    rw [headStep_support_iff]
    exact .RandTapeOtherS Hz hlook HneM (_root_.le_refl _) Hz rfl
  iintro !> %e₂ %σ₂ %Hstep
  rw [headStep_support_iff] at Hstep
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
    isplitl [Hσ]; · iexact Hσ
    -- Repack the backend fragment + pure map equation into `appNatTape l M ns`.
    ihave HlNat := show (l ↪ₐ ⟨M, fs⟩) ⊢@{IProp GF} appNatTape l M ns by
      iintro Hb
      unfold appNatTape
      iexists fs
      isplitr; · ipure_intro; exact hmap
      iexact Hb
    ihave HlNat' := HlNat $$ HlBack
    iapply HΦ $$ HlNat'
    ipure_intro; exact ⟨Hv0, Hvz⟩

/-! ### Spec-side `_r` WPs

Lemmas that step the *spec* side (under a spec-program context `K`) while
the program side stays put. Each consumes a spec-fragment `⤇ K.fill (..)`
and feeds an updated fragment to the continuation. -/

/-- `wp_rand_r` — the spec side samples a uniform `n ∈ [0, z)`. -/
theorem wp_rand_r {E : CoPset} (K : Ectx) {z : Int} {e : Exp}
    {Φ : Val → IProp GF} (Hz : 0 < z) :
    iprop((⤇ K.fill (.rand (.lit (.int z)) (.lit .unit))) ∗
        (∀ (n : Int), (⌜0 ≤ n ∧ n < z⌝) -∗
          (⤇ K.fill (.lit (.int n))) -∗ wp E e Φ))
      ⊢@{IProp GF} wp E e Φ := by
  iintro ⟨Hj, Hwp⟩
  iapply wp_lift_step_spec_couple
  iintro %σ₁ %e₁' %σ₁' %ε₁ ⟨Hσ, Hs, Hε⟩
  -- Force `e₁' = K.fill (rand #z)` via frag/auth agreement.
  ihave %Heq := specAuth_specFrag_agree (GF := GF) (σ := σ₁') $$ Hs Hj
  subst Heq
  -- Reducibility of `K.fill (rand #z)` at state σ₁'.
  have Hhead_rand : 0 < headStep ⟨Exp.rand (.lit (.int z)) (.lit .unit), σ₁'⟩
        {⟨.lit (.int 0), σ₁'⟩} :=
    (headStep_support_iff _ _ _ _).mpr (.RandNoTapeS Hz (_root_.le_refl _) Hz)
  have Hred_rand : Reducible (Exp.rand (.lit (.int z)) (.lit .unit)) σ₁' :=
    Reducible.of_head ⟨_, Hhead_rand⟩
  have Hred : Reducible (K.fill (.rand (.lit (.int z)) (.lit .unit))) σ₁' :=
    Hred_rand.fill K
  -- Open mask E → ∅.
  imod (BIFUpdate.subset (E1 := E) (E2 := ∅) Std.LawfulSet.empty_subset)
    with Hclose
  imodintro
  iapply (specCoupl_step (Hred := Hred))
  iintro %e₂' %σ₂' %Hstep
  -- Invert: `primStep {K.fill (rand #z)} {(e₂', σ₂')}` — since `rand #z` is
  -- not a value, `e₂' = K.fill e'` for some `e'` with a positive headStep.
  have Hv_rand : ¬ (Exp.rand (Exp.lit (.int z)) (Exp.lit .unit)).isValue := by
    intro ⟨w⟩; nomatch w
  obtain ⟨e', heq_e2', Hstep'⟩ := primStep_fill_inv Hv_rand Hstep
  subst heq_e2'
  -- Invert `Hstep' : 0 < primStep {rand #z, σ₁'} {(e', σ₂')}`.
  -- Convert primStep → headStep via `primStep_eq_headStep` (rand is a redex).
  have Hheq : primStep ⟨Exp.rand (.lit (.int z)) (.lit .unit), σ₁'⟩ =
      headStep ⟨.rand (.lit (.int z)) (.lit .unit), σ₁'⟩ :=
    primStep_eq_headStep ⟨_, Hhead_rand⟩
  rw [Hheq, headStep_support_iff] at Hstep'
  cases Hstep' with
  | RandNoTapeS _ Hv0 Hvz =>
    imodintro
    iapply specCoupl_ret
    -- Update the spec program from `K.fill (rand #z)` to `K.fill #n`.
    ihave HUpd := specProg_update (GF := GF)
      (e3 := K.fill (.lit (.int _))) $$ Hs Hj
    imod HUpd with ⟨Hs', Hj'⟩
    imod Hclose
    imodintro
    -- Goal: stateInterp σ₁' ∗ specInterp ⟨K.fill #n, σ₁'⟩ ∗ errInterp ε₁ ∗ wp E e Φ
    isplitl [Hσ]; · iexact Hσ
    isplitl [Hs']; · iexact Hs'
    isplitl [Hε]; · iexact Hε
    iapply Hwp
    · ipure_intro; exact ⟨Hv0, Hvz⟩
    · iexact Hj'
  | RandNonposS hnz => exact absurd Hz hnz

/-- `wp_rand_lbl_nonpos` — `rand z (lbl l)` for `z ≤ 0` is deterministic on
`-1`, given that tape `l` is empty. (With a queued value, the rand pops it
even when `z ≤ 0`, so emptiness is required.) -/
theorem wp_rand_lbl_nonpos {E : CoPset} {l : Loc} {z N : Int}
    {Φ : Val → IProp GF} (Hz : ¬ 0 < z) :
    iprop(appTapesFrag l ⟨N, []⟩ ∗
        (appTapesFrag l ⟨N, []⟩ -∗ Φ (⟨.lit (.int (-1)), IsVal.lit⟩ : Val)))
      ⊢@{IProp GF} wp E (.rand (.lit (.int z)) (.lit (.lbl l))) Φ := by
  iintro ⟨Hl, HΦ⟩
  have Hv : (Exp.rand (Exp.lit (.int z)) (Exp.lit (.lbl l))).toVal? = none :=
    Exp.toVal?_eq_none.mpr fun ⟨w⟩ => nomatch w
  iapply (wp_lift_atomic_head_step Hv)
  iintro %σ₁ Hσ
  ihave %hlook := app_state_lookup_tape (GF := GF) (σ := σ₁) $$ Hσ Hl
  imodintro
  isplitr
  · ipure_intro
    refine ⟨⟨.lit (.int (-1)), σ₁⟩, ?_⟩
    rw [headStep_support_iff]
    by_cases hN : N = z
    · subst hN; exact .RandTapeNonposEmptyS Hz hlook rfl
    · exact .RandTapeNonposOtherS Hz hlook (Ne.symm hN)
  iintro !> %e₂ %σ₂ %Hstep
  rw [headStep_support_iff] at Hstep
  cases Hstep with
  | RandTapeS hlook' _ _ _ =>
    rw [hlook] at hlook'
    -- hlook' : some ⟨N, []⟩ = some ⟨_, _ :: _⟩ — list nil ≠ cons.
    exact absurd (Option.some.inj hlook') (by intro h; cases h)
  | RandTapeEmptyS hpos _ _ _ _ _ => exact absurd hpos Hz
  | RandTapeOtherS hpos _ _ _ _ _ => exact absurd hpos Hz
  | RandTapeNonposEmptyS _ _ _ =>
    imodintro
    simp only [approxisWpGS_stateInterp_eq, Exp.toVal?_lit]
    isplitl [Hσ]; · iexact Hσ
    iapply HΦ $$ Hl
  | RandTapeNonposOtherS _ _ _ =>
    imodintro
    simp only [approxisWpGS_stateInterp_eq, Exp.toVal?_lit]
    isplitl [Hσ]; · iexact Hσ
    iapply HΦ $$ Hl

/-- `wp_rand_nonpos_r` — spec-side: `rand z ()` for `z ≤ 0` deterministically
returns `-1`. Mirrors `wp_rand_r` for the nonpositive branch. -/
theorem wp_rand_nonpos_r {E : CoPset} (K : Ectx) {z : Int} {e : Exp}
    {Φ : Val → IProp GF} (Hz : ¬ 0 < z) :
    iprop((⤇ K.fill (.rand (.lit (.int z)) (.lit .unit))) ∗
        ((⤇ K.fill (.lit (.int (-1)))) -∗ wp E e Φ))
      ⊢@{IProp GF} wp E e Φ := by
  iintro ⟨Hj, Hwp⟩
  iapply wp_lift_step_spec_couple
  iintro %σ₁ %e₁' %σ₁' %ε₁ ⟨Hσ, Hs, Hε⟩
  ihave %Heq := specAuth_specFrag_agree (GF := GF) (σ := σ₁') $$ Hs Hj
  subst Heq
  have Hhead_rand : 0 < headStep ⟨Exp.rand (.lit (.int z)) (.lit .unit), σ₁'⟩
        {⟨.lit (.int (-1)), σ₁'⟩} :=
    (headStep_support_iff _ _ _ _).mpr (.RandNonposS Hz)
  have Hred_rand : Reducible (Exp.rand (.lit (.int z)) (.lit .unit)) σ₁' :=
    Reducible.of_head ⟨_, Hhead_rand⟩
  have Hred : Reducible (K.fill (.rand (.lit (.int z)) (.lit .unit))) σ₁' :=
    Hred_rand.fill K
  imod (BIFUpdate.subset (E1 := E) (E2 := ∅) Std.LawfulSet.empty_subset)
    with Hclose
  imodintro
  iapply (specCoupl_step (Hred := Hred))
  iintro %e₂' %σ₂' %Hstep
  have Hv_rand : ¬ (Exp.rand (Exp.lit (.int z)) (Exp.lit .unit)).isValue := by
    intro ⟨w⟩; nomatch w
  obtain ⟨e', heq_e2', Hstep'⟩ := primStep_fill_inv Hv_rand Hstep
  subst heq_e2'
  have Hheq : primStep ⟨Exp.rand (.lit (.int z)) (.lit .unit), σ₁'⟩ =
      headStep ⟨.rand (.lit (.int z)) (.lit .unit), σ₁'⟩ :=
    primStep_eq_headStep ⟨_, Hhead_rand⟩
  rw [Hheq, headStep_support_iff] at Hstep'
  cases Hstep' with
  | RandNoTapeS hpos _ _ => exact absurd hpos Hz
  | RandNonposS _ =>
    imodintro
    iapply specCoupl_ret
    ihave HUpd := specProg_update (GF := GF)
      (e3 := K.fill (.lit (.int (-1)))) $$ Hs Hj
    imod HUpd with ⟨Hs', Hj'⟩
    imod Hclose
    imodintro
    isplitl [Hσ]; · iexact Hσ
    isplitl [Hs']; · iexact Hs'
    isplitl [Hε]; · iexact Hε
    iapply Hwp $$ Hj'

/-- `wp_rand_tape_empty_r` — spec-side rand on an empty tape: samples a uniform
`n ∈ [0, z)`, leaving the tape empty. Mirrors `wp_rand_r` but the spec resource
is `specNatTape l z []` instead of `⤇ K.fill (rand z ())`. -/
theorem wp_rand_tape_empty_r {E : CoPset} (K : Ectx) {l : Loc} {z : Int} {e : Exp}
    {Φ : Val → IProp GF} (Hz : 0 < z) :
    iprop((⤇ K.fill (.rand (.lit (.int z)) (.lit (.lbl l)))) ∗ specNatTape l z [] ∗
        (∀ (n : Int), specNatTape l z [] -∗
          (⤇ K.fill (.lit (.int n))) -∗ (⌜0 ≤ n ∧ n < z⌝) -∗ wp E e Φ))
      ⊢@{IProp GF} wp E e Φ := by
  iintro ⟨Hj, Hα, Hwp⟩
  ihave HαB := spec_natTape_to_empty (GF := GF) (l := l) (z := z) $$ Hα
  iapply wp_lift_step_spec_couple
  iintro %σ₁ %e₁' %σ₁' %ε₁ ⟨Hσ, Hs, Hε⟩
  ihave %Heq := specAuth_specFrag_agree (GF := GF) (σ := σ₁') $$ Hs Hj
  subst Heq
  ihave %hlook := spec_auth_lookup_tape (GF := GF) (σ := σ₁') $$ Hs HαB
  -- Reducibility via RandTapeEmptyS.
  have Hhead : 0 < headStep ⟨Exp.rand (.lit (.int z)) (.lit (.lbl l)), σ₁'⟩
        {⟨.lit (.int 0), σ₁'⟩} :=
    (headStep_support_iff _ _ _ _).mpr
      (.RandTapeEmptyS Hz hlook rfl (_root_.le_refl _) Hz rfl)
  have Hred_rand : Reducible (Exp.rand (.lit (.int z)) (.lit (.lbl l))) σ₁' :=
    Reducible.of_head ⟨_, Hhead⟩
  have Hred : Reducible (K.fill (.rand (.lit (.int z)) (.lit (.lbl l)))) σ₁' :=
    Hred_rand.fill K
  imod (BIFUpdate.subset (E1 := E) (E2 := ∅) Std.LawfulSet.empty_subset)
    with Hclose
  imodintro
  iapply (specCoupl_step (Hred := Hred))
  iintro %e₂' %σ₂' %Hstep
  have Hv_rand : ¬ (Exp.rand (Exp.lit (.int z)) (Exp.lit (.lbl l))).isValue := by
    intro ⟨w⟩; nomatch w
  obtain ⟨e', heq_e2', Hstep'⟩ := primStep_fill_inv Hv_rand Hstep
  subst heq_e2'
  have Hheq : primStep ⟨Exp.rand (.lit (.int z)) (.lit (.lbl l)), σ₁'⟩ =
      headStep ⟨.rand (.lit (.int z)) (.lit (.lbl l)), σ₁'⟩ :=
    primStep_eq_headStep ⟨_, Hhead⟩
  rw [Hheq, headStep_support_iff] at Hstep'
  cases Hstep' with
  | RandTapeS hlook' _ _ _ =>
    rw [hlook] at hlook'; cases hlook'
  | RandTapeEmptyS _ _ _ Hv0 Hvz hσ =>
    subst hσ
    imodintro
    iapply specCoupl_ret
    ihave HUpd := specProg_update (GF := GF)
      (e3 := K.fill (.lit (.int _))) $$ Hs Hj
    imod HUpd with ⟨Hs', Hj'⟩
    imod Hclose
    imodintro
    isplitl [Hσ]; · iexact Hσ
    isplitl [Hs']; · iexact Hs'
    isplitl [Hε]; · iexact Hε
    -- Convert HαB back to specNatTape l z [].
    ihave HαNat := spec_empty_to_natTape (GF := GF) (l := l) (z := z) $$ HαB
    iapply Hwp $$ HαNat Hj'
    ipure_intro; exact ⟨Hv0, Hvz⟩
  | RandTapeOtherS _ hlook' hne _ _ _ =>
    rw [hlook] at hlook'; cases hlook'; exact absurd rfl hne
  | RandTapeNonposEmptyS hnz _ _ => exact absurd Hz hnz
  | RandTapeNonposOtherS hnz _ _ => exact absurd Hz hnz

/-- `wp_rand_lbl_nonpos_r` — spec-side: `rand z (lbl l)` for `z ≤ 0` with
empty tape deterministically returns `-1`. -/
theorem wp_rand_lbl_nonpos_r {E : CoPset} (K : Ectx) {l : Loc} {z N : Int} {e : Exp}
    {Φ : Val → IProp GF} (Hz : ¬ 0 < z) :
    iprop((⤇ K.fill (.rand (.lit (.int z)) (.lit (.lbl l)))) ∗ specTapesFrag l ⟨N, []⟩ ∗
        (specTapesFrag l ⟨N, []⟩ -∗ (⤇ K.fill (.lit (.int (-1)))) -∗ wp E e Φ))
      ⊢@{IProp GF} wp E e Φ := by
  iintro ⟨Hj, Hl, Hwp⟩
  iapply wp_lift_step_spec_couple
  iintro %σ₁ %e₁' %σ₁' %ε₁ ⟨Hσ, Hs, Hε⟩
  ihave %Heq := specAuth_specFrag_agree (GF := GF) (σ := σ₁') $$ Hs Hj
  subst Heq
  ihave %hlook := spec_auth_lookup_tape (GF := GF) (σ := σ₁') $$ Hs Hl
  -- Reducibility via NonposEmpty (when N=z) or NonposOther (when N≠z).
  have Hhead : 0 < headStep ⟨Exp.rand (.lit (.int z)) (.lit (.lbl l)), σ₁'⟩
        {⟨.lit (.int (-1)), σ₁'⟩} := by
    rw [headStep_support_iff]
    by_cases hN : N = z
    · subst hN; exact .RandTapeNonposEmptyS Hz hlook rfl
    · exact .RandTapeNonposOtherS Hz hlook (Ne.symm hN)
  have Hred_rand : Reducible (Exp.rand (.lit (.int z)) (.lit (.lbl l))) σ₁' :=
    Reducible.of_head ⟨_, Hhead⟩
  have Hred : Reducible (K.fill (.rand (.lit (.int z)) (.lit (.lbl l)))) σ₁' :=
    Hred_rand.fill K
  imod (BIFUpdate.subset (E1 := E) (E2 := ∅) Std.LawfulSet.empty_subset)
    with Hclose
  imodintro
  iapply (specCoupl_step (Hred := Hred))
  iintro %e₂' %σ₂' %Hstep
  have Hv_rand : ¬ (Exp.rand (Exp.lit (.int z)) (Exp.lit (.lbl l))).isValue := by
    intro ⟨w⟩; nomatch w
  obtain ⟨e', heq_e2', Hstep'⟩ := primStep_fill_inv Hv_rand Hstep
  subst heq_e2'
  have Hheq : primStep ⟨Exp.rand (.lit (.int z)) (.lit (.lbl l)), σ₁'⟩ =
      headStep ⟨.rand (.lit (.int z)) (.lit (.lbl l)), σ₁'⟩ :=
    primStep_eq_headStep ⟨_, Hhead⟩
  rw [Hheq, headStep_support_iff] at Hstep'
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
      (e3 := K.fill (.lit (.int (-1)))) $$ Hs Hj
    imod HUpd with ⟨Hs', Hj'⟩
    imod Hclose
    imodintro
    isplitl [Hσ]; · iexact Hσ
    isplitl [Hs']; · iexact Hs'
    isplitl [Hε]; · iexact Hε
    iapply Hwp $$ Hl Hj'
  | RandTapeNonposOtherS _ _ _ =>
    imodintro
    iapply specCoupl_ret
    ihave HUpd := specProg_update (GF := GF)
      (e3 := K.fill (.lit (.int (-1)))) $$ Hs Hj
    imod HUpd with ⟨Hs', Hj'⟩
    imod Hclose
    imodintro
    isplitl [Hσ]; · iexact Hσ
    isplitl [Hs']; · iexact Hs'
    isplitl [Hε]; · iexact Hε
    iapply Hwp $$ Hl Hj'

/-- `wp_alloc_tape_r` — the spec side allocates a fresh empty tape. -/
theorem wp_alloc_tape_r {E : CoPset} (K : Ectx) {z : Int} {e : Exp}
    {Φ : Val → IProp GF} :
    iprop((⤇ K.fill (.tape (.lit (.int z)))) ∗
        (∀ (l : Loc), (⤇ K.fill (.lit (.lbl l))) -∗
          specNatTape l z [] -∗ wp E e Φ))
      ⊢@{IProp GF} wp E e Φ := by
  iintro ⟨Hj, Hwp⟩
  ihave Hstep := step_alloctape (GF := GF) (E := E) K z $$ Hj
  imod Hstep with ⟨%l, Hj', Hl⟩
  -- `Tape.empty z = ⟨z, []⟩` definitionally; coerce via `show` at the entails level.
  ihave Hl' := show (l ↪ₛ Tape.empty z) ⊢@{IProp GF}
      (l ↪ₛ ⟨z, ([] : List { z' : Int // 0 ≤ z' ∧ z' < z })⟩) from
    BI.BIBase.Entails.rfl $$ Hl
  ihave HlNat := spec_empty_to_natTape (GF := GF) (l := l) (z := z) $$ Hl'
  iapply Hwp $$ %l Hj' HlNat

/-- `wp_rand_tape_r` — the spec side reads the head of a non-empty tape. -/
theorem wp_rand_tape_r {E : CoPset} (K : Ectx) {z : Int} {l : Loc}
    {n : Int} {ns : List Int} {e : Exp} {Φ : Val → IProp GF} :
    iprop((⤇ K.fill (.rand (.lit (.int z)) (.lit (.lbl l)))) ∗
        specNatTape l z (n :: ns) ∗
        ((⤇ K.fill (.lit (.int n))) -∗ specNatTape l z ns -∗
            (⌜0 ≤ n ∧ n < z⌝) -∗ wp E e Φ))
      ⊢@{IProp GF} wp E e Φ := by
  iintro ⟨Hj, Hl, Hwp⟩
  -- Read the head: get backend frag + handback wand.
  ihave Hread := spec_read_natTape_head (GF := GF) (l := l) (z := z)
    (n := n) (ns := ns) $$ Hl
  icases Hread with ⟨%x, %xs, Hback, %hxv, HHandback⟩
  -- Fire the backend spec step.
  ihave Hstep := step_rand (GF := GF) (E := E) K l x xs $$ [Hj Hback]
  · isplitl [Hj] <;> iassumption
  imod Hstep with ⟨Hj', Hback'⟩
  subst hxv
  -- Repack the new (backend) tape state into `specNatTape l z ns`.
  ihave HlNew := HHandback $$ Hback'
  iapply Hwp $$ Hj' HlNew
  ipure_intro; exact x.2

/-- `wp_rand_empty_r` — the spec side reads from an empty tape, falling back
to a uniform sample (tape stays empty). -/
theorem wp_rand_empty_r {E : CoPset} (K : Ectx) {z : Int} {l : Loc}
    {e : Exp} {Φ : Val → IProp GF} (Hz : 0 < z) :
    iprop((⤇ K.fill (.rand (.lit (.int z)) (.lit (.lbl l)))) ∗
        specNatTape l z [] ∗
        (∀ (n : Int), (specNatTape l z [] ∗ ⤇ K.fill (.lit (.int n))) -∗
          (⌜0 ≤ n ∧ n < z⌝) -∗ wp E e Φ))
      ⊢@{IProp GF} wp E e Φ := by
  iintro ⟨Hj, Hα, Hwp⟩
  ihave Hαb := spec_natTape_to_empty (GF := GF) (l := l) (z := z) $$ Hα
  iapply wp_lift_step_spec_couple
  iintro %σ₁ %e₁' %σ₁' %ε₁ ⟨Hσ, Hs, Hε⟩
  ihave %Heq := specAuth_specFrag_agree (GF := GF) (σ := σ₁') $$ Hs Hj
  subst Heq
  ihave %Hlk := spec_auth_lookup_tape (GF := GF) (σ := σ₁') $$ Hs Hαb
  -- Reducibility: `rand(lbl l) z` at σ₁' (empty tape → uniform sample).
  have Hhead : 0 < headStep ⟨Exp.rand (.lit (.int z)) (.lit (.lbl l)), σ₁'⟩
        {⟨.lit (.int 0), σ₁'⟩} :=
    (headStep_support_iff _ _ _ _).mpr
      (.RandTapeEmptyS Hz Hlk rfl (_root_.le_refl _) Hz rfl)
  have Hred_rand : Reducible (Exp.rand (.lit (.int z)) (.lit (.lbl l))) σ₁' :=
    Reducible.of_head ⟨_, Hhead⟩
  have Hred : Reducible (K.fill (.rand (.lit (.int z)) (.lit (.lbl l)))) σ₁' :=
    Hred_rand.fill K
  imod (BIFUpdate.subset (E1 := E) (E2 := ∅) Std.LawfulSet.empty_subset)
    with Hclose
  imodintro
  iapply (specCoupl_step (Hred := Hred))
  iintro %e₂' %σ₂' %Hstep
  have Hv_rand : ¬ (Exp.rand (Exp.lit (.int z)) (Exp.lit (.lbl l))).isValue := by
    intro ⟨w⟩; nomatch w
  obtain ⟨e', heq_e2', Hstep'⟩ := primStep_fill_inv Hv_rand Hstep
  subst heq_e2'
  have Hheq : primStep ⟨Exp.rand (.lit (.int z)) (.lit (.lbl l)), σ₁'⟩ =
      headStep ⟨.rand (.lit (.int z)) (.lit (.lbl l)), σ₁'⟩ :=
    primStep_eq_headStep ⟨_, Hhead⟩
  rw [Hheq, headStep_support_iff] at Hstep'
  cases Hstep' with
  | RandTapeS Hlk' _ _ _ =>
    rw [Hlk] at Hlk'; cases Hlk'
  | RandTapeEmptyS _ _ _ Hv0 Hvz hσ =>
    subst hσ
    imodintro
    iapply specCoupl_ret
    ihave HUpd := specProg_update (GF := GF)
      (e3 := K.fill (.lit (.int _))) $$ Hs Hj
    imod HUpd with ⟨Hs', Hj'⟩
    imod Hclose
    imodintro
    isplitl [Hσ]; · iexact Hσ
    isplitl [Hs']; · iexact Hs'
    isplitl [Hε]; · iexact Hε
    -- Repack `Hαb` as `specNatTape l z []` and bundle with `Hj'` to feed `Hwp`.
    ihave HαNat := spec_empty_to_natTape (GF := GF) (l := l) (z := z) $$ Hαb
    -- Build the ∗-bundle argument in one `ihave` via a constant-wand entailment.
    ihave HwpArg := show
        (specNatTape l z [] ∗ ⤇ K.fill (.lit (.int _))) ⊢@{IProp GF}
        (specNatTape l z [] ∗ ⤇ K.fill (.lit (.int _))) from
      BI.BIBase.Entails.rfl $$ [HαNat Hj']
    · isplitl [HαNat] <;> iassumption
    iapply Hwp $$ HwpArg
    ipure_intro; exact ⟨Hv0, Hvz⟩
  | RandTapeOtherS _ Hlk' hne _ _ _ =>
    rw [Hlk] at Hlk'; cases Hlk'; exact absurd rfl hne
  | RandTapeNonposEmptyS hnz _ _ => exact absurd Hz hnz
  | RandTapeNonposOtherS hnz _ _ => exact absurd Hz hnz

/-- `wp_rand_wrong_tape_r` — the spec side reads from a tape whose bound
differs from the `rand` argument (uniform fallback, tape unchanged). -/
theorem wp_rand_wrong_tape_r {E : CoPset} (K : Ectx) {z M : Int} {l : Loc}
    {ns : List Int} {e : Exp} {Φ : Val → IProp GF}
    (Hz : 0 < z) (HneM : z ≠ M) :
    iprop((⤇ K.fill (.rand (.lit (.int z)) (.lit (.lbl l)))) ∗
        specNatTape l M ns ∗
        (∀ (n : Int), (specNatTape l M ns ∗ ⤇ K.fill (.lit (.int n))) -∗
          (⌜0 ≤ n ∧ n < z⌝) -∗ wp E e Φ))
      ⊢@{IProp GF} wp E e Φ := by
  iintro ⟨Hj, Hα, Hwp⟩
  -- Unfold `specNatTape` to get the backend frag.
  ihave HαEx := show specNatTape l M ns ⊢@{IProp GF}
      iprop(∃ fs : List { z' : Int // 0 ≤ z' ∧ z' < M },
        (⌜fs.map (fun x => x.val) = ns⌝) ∗ l ↪ₛ ⟨M, fs⟩) from
    BI.BIBase.Entails.rfl $$ Hα
  icases HαEx with ⟨%fs, %hmap, Hαb⟩
  iapply wp_lift_step_spec_couple
  iintro %σ₁ %e₁' %σ₁' %ε₁ ⟨Hσ, Hs, Hε⟩
  ihave %Heq := specAuth_specFrag_agree (GF := GF) (σ := σ₁') $$ Hs Hj
  subst Heq
  ihave %Hlk := spec_auth_lookup_tape (GF := GF) (σ := σ₁') $$ Hs Hαb
  have Hhead : 0 < headStep ⟨Exp.rand (.lit (.int z)) (.lit (.lbl l)), σ₁'⟩
        {⟨.lit (.int 0), σ₁'⟩} :=
    (headStep_support_iff _ _ _ _).mpr
      (.RandTapeOtherS Hz Hlk HneM (_root_.le_refl _) Hz rfl)
  have Hred_rand : Reducible (Exp.rand (.lit (.int z)) (.lit (.lbl l))) σ₁' :=
    Reducible.of_head ⟨_, Hhead⟩
  have Hred : Reducible (K.fill (.rand (.lit (.int z)) (.lit (.lbl l)))) σ₁' :=
    Hred_rand.fill K
  imod (BIFUpdate.subset (E1 := E) (E2 := ∅) Std.LawfulSet.empty_subset)
    with Hclose
  imodintro
  iapply (specCoupl_step (Hred := Hred))
  iintro %e₂' %σ₂' %Hstep
  have Hv_rand : ¬ (Exp.rand (Exp.lit (.int z)) (Exp.lit (.lbl l))).isValue := by
    intro ⟨w⟩; nomatch w
  obtain ⟨e', heq_e2', Hstep'⟩ := primStep_fill_inv Hv_rand Hstep
  subst heq_e2'
  have Hheq : primStep ⟨Exp.rand (.lit (.int z)) (.lit (.lbl l)), σ₁'⟩ =
      headStep ⟨.rand (.lit (.int z)) (.lit (.lbl l)), σ₁'⟩ :=
    primStep_eq_headStep ⟨_, Hhead⟩
  rw [Hheq, headStep_support_iff] at Hstep'
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
      (e3 := K.fill (.lit (.int _))) $$ Hs Hj
    imod HUpd with ⟨Hs', Hj'⟩
    imod Hclose
    imodintro
    isplitl [Hσ]; · iexact Hσ
    isplitl [Hs']; · iexact Hs'
    isplitl [Hε]; · iexact Hε
    -- Repack `Hαb` back into `specNatTape l M ns`.
    ihave HαNat := show (l ↪ₛ ⟨M, fs⟩) ⊢@{IProp GF} specNatTape l M ns by
      iintro Hb
      unfold specNatTape
      iexists fs
      isplitr; · ipure_intro; exact hmap
      iexact Hb
    ihave HαNat' := HαNat $$ Hαb
    ihave HwpArg := show
        (specNatTape l M ns ∗ ⤇ K.fill (.lit (.int _))) ⊢@{IProp GF}
        (specNatTape l M ns ∗ ⤇ K.fill (.lit (.int _))) from
      BI.BIBase.Entails.rfl $$ [HαNat' Hj']
    · isplitl [HαNat'] <;> iassumption
    iapply Hwp $$ HwpArg
    ipure_intro; exact ⟨Hv0, Hvz⟩

end Lifting

end ProbLang
