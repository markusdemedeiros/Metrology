import Metrology.Approxis.PrimitiveLaws
import Metrology.Approxis.Proofmode
import Metrology.Approxis.Model
import Metrology.Approxis.RelTactics
import Metrology.Approxis.AppRelRules
import Metrology.ProbLang.Syntax.LocallyClosed

/-!
# Compatibility Lemmas

Port of `clutch/theories/approxis/compatibility.v` (192 lines, 10 lemmas).

Structural compatibility lemmas for the logical relation — one rule per language
construct. Used by `Fundamental.lean` to prove the fundamental theorem
one typing-rule case at a time.

## Lemmas ported

| Lemma | Rocq line | Uses |
|---|---|---|
| `refines_pair` | 19 | `refines_bind` (twice) + `lrel_prod` unfold |
| `refines_injl`, `refines_injr` | 31, 41 | `refines_bind` + `lrel_sum` unfold |
| `refines_app` | 51 | `refines_bind` (twice) + `lrel_arr` elimination |
| `refines_seq` | 62 | `refines_bind` + `refines_pure_{l,r}` |
| `refines_pack` | 73 | `refines_bind` + `lrel_exists` unfold |
| `refines_forall` | 83 | `refines_arrow_val` at `lrel_arr lrel_unit (C A)` |
| `refines_store` | 95 | `refines_atomic_l` + `wp_store` + `tp_store` under `lrel_ref` invariant |
| `refines_load` | 118 | `refines_atomic_l` + `wp_load` + `tp_load` under `lrel_ref` invariant |
| `refines_rand_tape` | 139 | `wp_couple_rand_lbl_rand_lbl{,_wrong}` under `lrel_tape` invariant |
| `refines_rand_unit` | 175 | `refines_couple_rands_lr` + `lrel_int` |

All proofs sorried pending completion of AppRelRules (which has sorries for
`refines_pure_l`, `refines_pure_r`, `refines_wp_l`, `refines_atomic_l`, and
the LHS/RHS heap ops). Once those are proved, the Compatibility proofs
should follow mechanically from their Rocq counterparts.
-/

open Std Iris Iris.Std Iris.BI Iris.ProofMode OFE COFE ProbLang ProbLang.ApproxisWpGS
open scoped AppGS

-- **Notation gotcha**: `refines E e e' (C A)` within `iprop(...)` clashes with
-- the `REL _ << _ @ _ : _` notation. The delaborator displays `refines` as
-- `REL ... : A`, and when `A` is actually `C A` (application), the parser/printer
-- get confused. Workaround: use `BI.intuitionistically`/`BI.forall` directly
-- rather than `iprop(□ (∀ ...))` for the few statements that need `C A`.

namespace ProbLang

section Compatibility
variable {hlc : Bool} {GF : BundledGFunctors} [IR : ApproxisRGS hlc GF]

/-- Helper: unfold `lrel_arr` application. Proves that `(lrel_arr A B).car v v'` is
definitionally the `□ (∀ w w', A w w' -∗ REL (v w) << (v' w') : B)` form, bridging the
`.car`/`lrel.mk` projection that iris tactics don't reduce. -/
theorem lrel_arr_unfold (A B : lrel GF) (v v' : Val) :
    (lrel_arr A B).car v v' ⊢@{IProp GF}
      iprop(□ (∀ (w1 w2 : Val), A w1 w2 -∗
        refines (⊤ : CoPset) (Exp.app v.1 w1.1) (Exp.app v'.1 w2.1) B)) :=
  -- The `.car` projection on `lrel_arr A B` is defeq to the body; this is `rfl` at
  -- Lean level and `BIBase.Entails.rfl` at iprop level.
  BIBase.Entails.rfl

/-- `refines_pair` (compatibility.v:19): pair compatibility.
`(REL e1 << e1' : A) ∗ (REL e2 << e2' : B) ⊢ REL (e1, e2) << (e1', e2') : A × B`.

Mirrors Rocq `rel_bind_ap e2 e2' "IH2" ...; rel_bind_ap e1 e1' "IH1" ...; value_case`
(compatibility.v:19–29). Right-to-left evaluation order on pairs.

**Port note**: we build the continuation as a first-class `ihave`-hypothesis
`Hcont` so that the inner `refines_bind` call has access to IH1 cleanly.
The `$$ [HYPS]` split in Lean Iris doesn't automatically retain unlisted
hypotheses past the tactic boundary when there are multiple wand args. -/
theorem refines_pair {e1 e2 e1' e2' : Exp} {A B : lrel GF} :
    iprop(refines ⊤ e1 e1' A) ⊢@{IProp GF}
      iprop(refines ⊤ e2 e2' B -∗
            refines ⊤ (Ectx.fill [EctxItem.pairR e1] e2)
                      (Ectx.fill [EctxItem.pairR e1'] e2') (lrel_prod A B)) := by
  -- Use an explicit rewrite to bridge [pairR e1].fill v2.1 = [pairL v2].fill e1.
  -- This is `rfl`, but `iapply`/`iexact` don't reduce it during unification.
  iintro IH1 IH2
  iapply (refines_bind [EctxItem.pairR e1] [EctxItem.pairR e1'] (A := B)) $$ [IH2]
  · iexact IH2
  iintro %v2 %v2' HB
  -- Goal shape: `refines ⊤ ([pairR e1].fill v2.1) ([pairR e1'].fill v2'.1) (A × B)`.
  -- Bridge via `refines_bind` on `e1/e1'` under `[pairL v2]/[pairL v2']` — defeq form.
  have hbridge_L : Ectx.fill [EctxItem.pairR e1] v2.1 = Ectx.fill [EctxItem.pairL v2] e1 := rfl
  have hbridge_R : Ectx.fill [EctxItem.pairR e1'] v2'.1 = Ectx.fill [EctxItem.pairL v2'] e1' := rfl
  rw [hbridge_L, hbridge_R]
  iapply (refines_bind [EctxItem.pairL v2] [EctxItem.pairL v2'] (A := A)) $$ [IH1]
  · iexact IH1
  iintro %v1 %v1' HA
  iapply refines_ret
    (e1 := Ectx.fill [EctxItem.pairL v2] v1.1)
    (e2 := Ectx.fill [EctxItem.pairL v2'] v1'.1)
    (v1 := ⟨.pair v1.1 v2.1, IsVal.pair v1.2 v2.2⟩)
    (v2 := ⟨.pair v1'.1 v2'.1, IsVal.pair v1'.2 v2'.2⟩)
    (hv1 := rfl) (hv2 := rfl)
  imodintro
  unfold lrel_prod
  iexists v1, v1', v2, v2'
  isplitr; · ipure_intro; rfl
  isplitr; · ipure_intro; rfl
  isplitl [HA]; · iexact HA
  iexact HB

/-- `refines_injl` (compatibility.v:31): left-injection compatibility. -/
theorem refines_injl {e e' : Exp} {A B : lrel GF} :
    iprop(refines ⊤ e e' A)
      ⊢@{IProp GF} refines ⊤ (.inl e) (.inl e') (lrel_sum A B) := by
  -- Reshape the goal from `.inl e` to `[inl].fill e` so `refines_bind` unifies.
  show _ ⊢@{IProp GF}
    refines ⊤ (Ectx.fill [EctxItem.inl] e) (Ectx.fill [EctxItem.inl] e') (lrel_sum A B)
  iintro IH
  iapply (refines_bind [EctxItem.inl] [EctxItem.inl] (A := A)) $$ [IH]
  · iexact IH
  iintro %v %v' HA
  -- Continuation goal: `REL [inl].fill v.1 << [inl].fill v'.1 : lrel_sum A B`.
  iapply refines_ret
    (e1 := Ectx.fill [EctxItem.inl] v.1)
    (e2 := Ectx.fill [EctxItem.inl] v'.1)
    (v1 := ⟨.inl v.1, IsVal.inl v.2⟩) (v2 := ⟨.inl v'.1, IsVal.inl v'.2⟩)
    (hv1 := rfl) (hv2 := rfl)
  imodintro
  unfold lrel_sum
  iexists v, v'
  iapply BI.or_intro_l
  isplitr; · ipure_intro; rfl
  isplitr; · ipure_intro; rfl
  iexact HA

/-- `refines_injr` (compatibility.v:41): right-injection compatibility. -/
theorem refines_injr {e e' : Exp} {A B : lrel GF} :
    iprop(refines ⊤ e e' B)
      ⊢@{IProp GF} refines ⊤ (.inr e) (.inr e') (lrel_sum A B) := by
  show _ ⊢@{IProp GF}
    refines ⊤ (Ectx.fill [EctxItem.inr] e) (Ectx.fill [EctxItem.inr] e') (lrel_sum A B)
  iintro IH
  iapply (refines_bind [EctxItem.inr] [EctxItem.inr] (A := B)) $$ [IH]
  · iexact IH
  iintro %v %v' HB
  iapply refines_ret
    (e1 := Ectx.fill [EctxItem.inr] v.1)
    (e2 := Ectx.fill [EctxItem.inr] v'.1)
    (v1 := ⟨.inr v.1, IsVal.inr v.2⟩) (v2 := ⟨.inr v'.1, IsVal.inr v'.2⟩)
    (hv1 := rfl) (hv2 := rfl)
  imodintro
  unfold lrel_sum
  iexists v, v'
  iapply BI.or_intro_r
  isplitr; · ipure_intro; rfl
  isplitr; · ipure_intro; rfl
  iexact HB

/-- `refines_app` (compatibility.v:51): function application compatibility. -/
theorem refines_app {e1 e2 e1' e2' : Exp} {A B : lrel GF} :
    iprop(refines ⊤ e1 e1' (lrel_arr A B)) ⊢@{IProp GF}
      iprop(refines ⊤ e2 e2' A -∗
            refines ⊤ (Ectx.fill [EctxItem.appR e1] e2)
                      (Ectx.fill [EctxItem.appR e1'] e2') B) := by
  iintro IH1 IH2
  iapply (refines_bind [EctxItem.appR e1] [EctxItem.appR e1'] (A := A)) $$ [IH2]
  · iexact IH2
  iintro %v2 %v2' HA
  have hbL : Ectx.fill [EctxItem.appR e1] v2.1 = Ectx.fill [EctxItem.appL v2] e1 := rfl
  have hbR : Ectx.fill [EctxItem.appR e1'] v2'.1 = Ectx.fill [EctxItem.appL v2'] e1' := rfl
  rw [hbL, hbR]
  iapply (refines_bind [EctxItem.appL v2] [EctxItem.appL v2'] (A := lrel_arr A B)) $$ [IH1]
  · iexact IH1
  iintro %v1 %v1' #Hff
  -- Goal: `REL [appL v2].fill v1.1 << [appL v2'].fill v1'.1 : B`, i.e. `.app v1.1 v2.1 << .app v1'.1 v2'.1`.
  -- Hff : (lrel_arr A B).car v1 v1' — unfold via lrel_arr_unfold helper.
  ihave Hff' := lrel_arr_unfold A B v1 v1' $$ Hff
  have hgL : Ectx.fill [EctxItem.appL v2] v1.1 = Exp.app v1.1 v2.1 := rfl
  have hgR : Ectx.fill [EctxItem.appL v2'] v1'.1 = Exp.app v1'.1 v2'.1 := rfl
  rw [hgL, hgR]
  iapply Hff' $$ %v2 %v2' HA

/-- `refines_seq` (compatibility.v:62): sequencing compatibility.
`(REL e1 << e1' : A) ∗ (REL e2 << e2' : B) ⊢ REL (e1; e2) << (e1'; e2') : B`.

**Port note**: Rocq's `e1 ;; e2 = (λ_. e2) e1` uses an anonymous binder, so
the body doesn't reference the bound variable. In Lean, `.lam e2`'s beta-step
gives `Exp.open' e2 v`, which equals `e2` only when e2 is locally closed.
We require `e2.IsLocallyClosed` and `e2'.IsLocallyClosed` as hypotheses. -/
theorem refines_seq (A : lrel GF) {e1 e2 e1' e2' : Exp} {B : lrel GF}
    (he2 : e2.IsLocallyClosed) (he2' : e2'.IsLocallyClosed) :
    iprop(refines ⊤ e1 e1' A) ⊢@{IProp GF}
      iprop(refines ⊤ e2 e2' B -∗
        refines ⊤ (.app (.lam e2) e1) (.app (.lam e2') e1') B) := by
  -- Reshape goal upfront to expose the bind contexts.
  show iprop(refines ⊤ e1 e1' A) ⊢@{IProp GF}
      iprop(refines ⊤ e2 e2' B -∗
        refines ⊤ (Ectx.fill [EctxItem.appR (.lam e2)] e1)
          (Ectx.fill [EctxItem.appR (.lam e2')] e1') B)
  iintro IH1 IH2
  iapply (refines_bind [EctxItem.appR (.lam e2)] [EctxItem.appR (.lam e2')]
    (A := A)) $$ [IH1]
  · iexact IH1
  iintro %v %v' _HA
  -- Goal: refines ⊤ ([appR (λe2)].fill v.1) ([appR (λe2')].fill v'.1) B
  --     = refines ⊤ (.app (λe2) v.1) (.app (λe2') v'.1) B.
  -- Wrap LHS in Ectx.fill [] for refines_pure_l; keep RHS bare.
  have hfv : Ectx.fill [EctxItem.appR (.lam e2)] v.1 =
    Ectx.fill [] (Exp.app (.lam e2) v.1) := rfl
  have hfv' : Ectx.fill [EctxItem.appR (.lam e2')] v'.1 =
    Exp.app (.lam e2') v'.1 := rfl
  rw [hfv, hfv']
  -- Now use refines_pure_l at [], with `pureExec_app_lam` (n = 1).
  have hv_iv : IsVal v.1 := v.2
  iapply (refines_pure_l (E := ⊤) (K := []) (t := .app (.lam e2') v'.1)
    (e := .app (.lam e2) v.1) (e' := Exp.open' e2 v.1) (A := B)
    (n := 1) (φ := v.1.isValue) (Hφ := ⟨hv_iv⟩))
  -- Goal: Nat.repeat (▷·) 1 (refines ⊤ ([].fill (open' e2 v.1)) (.app (λe2') v'.1) B)
  --     = ▷ refines ⊤ (open' e2 v.1) (.app (λe2') v'.1) B.
  simp only [Nat.repeat]
  -- Apply open_lc: open' e2 v.1 = e2 (since e2 is LC).
  have hopen : Exp.open' e2 v.1 = e2 := (Exp.open_lc 0 v.1 e2 he2).symm
  have hfill_empty : Ectx.fill [] (Exp.open' e2 v.1) = e2 := by
    show Exp.open' e2 v.1 = e2
    exact hopen
  rw [hfill_empty]
  -- Goal: ▷ refines ⊤ e2 (.app (λe2') v'.1) B.
  iintro !>
  -- Beta-step RHS similarly.
  have hrhs : Exp.app (.lam e2') v'.1 = Ectx.fill [] (.app (.lam e2') v'.1) := rfl
  rw [hrhs]
  have hv'_iv : IsVal v'.1 := v'.2
  iapply (refines_pure_r (E := ⊤) (K := []) (t := e2)
    (e := .app (.lam e2') v'.1) (e' := Exp.open' e2' v'.1) (A := B)
    (n := 1) (φ := v'.1.isValue) (Hφ := ⟨hv'_iv⟩))
  have hopen' : Exp.open' e2' v'.1 = e2' := (Exp.open_lc 0 v'.1 e2' he2').symm
  have hfillRHS : Ectx.fill [] (Exp.open' e2' v'.1) = e2' := hopen'
  rw [hfillRHS]
  iexact IH2

/-- Helper: `(lrel_exists C).car v v' = ∃ A, (C A).car v v'` (defeq via `lrel.mk` projection). -/
theorem lrel_exists_unfold (C : lrel GF → lrel GF) (v v' : Val) :
    iprop(∃ A : lrel GF, (C A).car v v') ⊢@{IProp GF} (lrel_exists C).car v v' :=
  BIBase.Entails.rfl

/-- Helper: `(lrel_nat).car v v' ⊢ ∃ n : Nat, v = #n ∧ v' = #n`. -/
theorem lrel_nat_unfold (v v' : Val) :
    (lrel_nat (GF := GF)).car v v'
      ⊢@{IProp GF} iprop(∃ n : Nat,
        ⌜v.1 = .lit (.int (n : Int)) ∧ v'.1 = .lit (.int (n : Int))⌝) :=
  BIBase.Entails.rfl

/-- Helper: `(lrel_pos_nat).car v v' ⊢ ∃ n : Nat, 0 < n ∧ v = #n ∧ v' = #n`. -/
theorem lrel_pos_nat_unfold (v v' : Val) :
    (lrel_pos_nat (GF := GF)).car v v'
      ⊢@{IProp GF} iprop(∃ n : Nat, ⌜0 < n ∧
        v.1 = .lit (.int (n : Int)) ∧ v'.1 = .lit (.int (n : Int))⌝) :=
  BIBase.Entails.rfl

/-- Helper: `(lrel_tape).car v v'` exposes the tape locations and bound. -/
theorem lrel_tape_unfold (v v' : Val) :
    (lrel_tape (GF := GF)).car v v' ⊢@{IProp GF}
      iprop(∃ (α1 α2 : Loc) (z : Int),
        (⌜ v.1 = .lit (.lbl α1) ⌝) ∗ (⌜ v'.1 = .lit (.lbl α2) ⌝) ∗
        Iris.inv (logN.@ ((α1, α2) : Loc × Loc))
          (iprop((appTapesFrag α1 ⟨z, []⟩) ∗ (specTapesFrag α2 ⟨z, []⟩)))) :=
  BIBase.Entails.rfl

/-- `refines_pack` (compatibility.v:73): existential-packing compatibility.
Given `REL e << e' : C A` for a specific `A`, conclude `REL e << e' : ∃ A, C A`. -/
theorem refines_pack (A : lrel GF) {e e' : Exp} {C : lrel GF → lrel GF}
    (_hC : OFE.NonExpansive C) :
    refines (⊤ : CoPset) e e' (C A)
      ⊢@{IProp GF} refines ⊤ e e' (lrel_exists C) := by
  show _ ⊢@{IProp GF}
    refines ⊤ (Ectx.fill Ectx.empty e) (Ectx.fill Ectx.empty e') (lrel_exists C)
  iintro IH
  iapply (refines_bind Ectx.empty Ectx.empty (A := C A)) $$ [IH]
  · iexact IH
  iintro %v %v' HCA
  -- Goal: `refines ⊤ ([].fill v.1) ([].fill v'.1) (lrel_exists C)`.
  iapply refines_ret
    (e1 := Ectx.fill Ectx.empty v.1) (e2 := Ectx.fill Ectx.empty v'.1)
    (v1 := v) (v2 := v') (hv1 := rfl) (hv2 := rfl)
  imodintro
  iapply lrel_exists_unfold
  iexists A
  iexact HCA

/-- `refines_forall` (compatibility.v:83): universal-typing compatibility.
If for all semantic types `A`, `REL e << e' : C A`, then `(λ_. e) << (λ_. e') : ∀A, C A`.

Two pure beta steps over the value-restricted forall encoding (via
`refines_pure_l`/`refines_pure_r`), then apply the persistent IH at the chosen
semantic type `A`.

**Port note**: same `IsLocallyClosed` requirement as `refines_seq`. -/
theorem refines_forall {e e' : Exp} {C : lrel GF → lrel GF}
    (he : e.IsLocallyClosed) (he' : e'.IsLocallyClosed) :
    BI.intuitionistically (BI.forall (fun A : lrel GF => refines (⊤ : CoPset) e e' (C A)))
      ⊢@{IProp GF} refines ⊤ (.lam e) (.lam e') (lrel_forall C) := by
  iintro #H
  iapply (refines_ret (e1 := Exp.lam e) (e2 := Exp.lam e')
    (v1 := ⟨.lam e, IsVal.lam⟩) (v2 := ⟨.lam e', IsVal.lam⟩) (hv1 := rfl) (hv2 := rfl))
  imodintro
  -- Goal: lrel_forall C ⟨.lam e, _⟩ ⟨.lam e', _⟩ = ∀ A, lrel_arr lrel_unit (C A) ...
  unfold lrel_forall
  iintro %A
  -- Goal: (lrel_arr lrel_unit (C A)).car ⟨.lam e, _⟩ ⟨.lam e', _⟩
  --     = □ ∀ u u', lrel_unit u u' -∗ refines ⊤ (.app (.lam e) u.1) (.app (.lam e') u'.1) (C A).
  unfold lrel_arr
  iintro !> %u %u' Hunit
  -- Hunit : lrel_unit u u' = ⌜u.1 = .lit .unit ∧ u'.1 = .lit .unit⌝.
  -- Goal: refines ⊤ (.app (.lam e) u.1) (.app (.lam e') u'.1) (C A).
  -- Beta-step LHS: reshape, apply refines_pure_l with n=1, use open_lc.
  have hfL : Exp.app (.lam e) u.1 = Ectx.fill [] (Exp.app (.lam e) u.1) := rfl
  rw [hfL]
  have hu_iv : IsVal u.1 := u.2
  iapply (refines_pure_l (E := ⊤) (K := []) (t := .app (.lam e') u'.1)
    (e := .app (.lam e) u.1) (e' := Exp.open' e u.1) (A := C A)
    (n := 1) (φ := u.1.isValue) (Hφ := ⟨hu_iv⟩))
  simp only [Nat.repeat]
  have hopenL : Exp.open' e u.1 = e := (Exp.open_lc 0 u.1 e he).symm
  have hfillL : Ectx.fill [] (Exp.open' e u.1) = e := hopenL
  rw [hfillL]
  iintro !>
  -- Goal: refines ⊤ e (.app (.lam e') u'.1) (C A).
  -- Beta-step RHS.
  have hfR : Exp.app (.lam e') u'.1 = Ectx.fill [] (Exp.app (.lam e') u'.1) := rfl
  rw [hfR]
  have hu'_iv : IsVal u'.1 := u'.2
  iapply (refines_pure_r (E := ⊤) (K := []) (t := e)
    (e := .app (.lam e') u'.1) (e' := Exp.open' e' u'.1) (A := C A)
    (n := 1) (φ := u'.1.isValue) (Hφ := ⟨hu'_iv⟩))
  have hopenR : Exp.open' e' u'.1 = e' := (Exp.open_lc 0 u'.1 e' he').symm
  have hfillR : Ectx.fill [] (Exp.open' e' u'.1) = e' := hopenR
  rw [hfillR]
  -- Goal: refines ⊤ e e' (C A). Apply IH (persistent H) at A.
  iapply H

/-- Helper: introduce a step-fupd from a `▷ P` with mask shift (E2 ⊆ E1).

Standard Iris `step_fupd_intro`. Construction:
- Use `fupd_mask_intro`: `((|={E2,E1}=> emp) -∗ Q) ⊢ |={E1, E2}=> Q`.
- Set Q := `▷ |={E2, E1}=> P`.
- Provide the wand: given `Hclose : |={E2,E1}=> emp`, produce `▷ |={E2,E1}=> P`.
  Lift Hclose under ▷ via `BI.later_intro`, combine with `▷ P`, mono fupd to drop emp. -/
theorem step_fupd_intro_later {E1 E2 : CoPset} {P : IProp GF} (HE : E2 ⊆ E1) :
    iprop(▷ P) ⊢@{IProp GF} iprop(|={E1, E2}=> ▷ |={E2, E1}=> P) := by
  iintro HP
  iapply Iris.fupd_mask_intro HE
  iintro Hclose
  iintro !>
  imod Hclose
  imodintro
  iexact HP

/-- Helper: `(lrel_ref A).car v v'` exposes the existence of related locations
plus the heap invariant. -/
theorem lrel_ref_unfold (A : lrel GF) (v v' : Val) :
    (lrel_ref A).car v v' ⊢@{IProp GF}
      iprop(∃ (l l' : Loc),
        (⌜ v.1 = .lit (.loc l) ⌝) ∗ (⌜ v'.1 = .lit (.loc l') ⌝) ∗
        Iris.inv (logN.@ ((l, l') : Loc × Loc))
          (iprop(∃ (w1 w2 : Val),
            (appHeapFrag l w1) ∗ (specHeapFrag l' w2) ∗ A w1 w2))) :=
  BIBase.Entails.rfl

/-- `refines_store` (compatibility.v:95): store compatibility.
Stores to related references preserve the refinement.

Same structure as `refines_load`: refines_bind on e2 then e1, destructure
`lrel_ref A` to get `(l, l', inv ...)`, refines_atomic_l, open inv,
step_store + wp_store, close inv with the NEW values. -/
theorem refines_store {e1 e2 e1' e2' : Exp} {A : lrel GF} :
    iprop(refines ⊤ e1 e1' (lrel_ref A)) ⊢@{IProp GF}
      iprop(refines ⊤ e2 e2' A -∗
        refines ⊤ (.store e1 e2) (.store e1' e2') lrel_unit) := by
  -- Reshape goal upfront to expose the bind contexts.
  show iprop(refines ⊤ e1 e1' (lrel_ref A)) ⊢@{IProp GF}
      iprop(refines ⊤ e2 e2' A -∗
        refines ⊤ (Ectx.fill [EctxItem.storeR e1] e2)
          (Ectx.fill [EctxItem.storeR e1'] e2') lrel_unit)
  iintro IH1 IH2
  iapply (refines_bind [EctxItem.storeR e1] [EctxItem.storeR e1'] (A := A)) $$ [IH2]
  · iexact IH2
  iintro %w %w' #HwA
  -- Goal: refines ⊤ ([storeR e1].fill w.1) ([storeR e1'].fill w'.1) lrel_unit
  -- which equals refines ⊤ (.store e1 w.1) (.store e1' w'.1) lrel_unit.
  -- Reshape via fill equalities: .store e1 w.1 = [storeL w].fill e1.
  have hfillR : Ectx.fill [EctxItem.storeR e1] w.1 = Ectx.fill [EctxItem.storeL w] e1 := rfl
  have hfillR' : Ectx.fill [EctxItem.storeR e1'] w'.1 = Ectx.fill [EctxItem.storeL w'] e1' := rfl
  rw [hfillR, hfillR']
  iapply (refines_bind [EctxItem.storeL w] [EctxItem.storeL w'] (A := lrel_ref A)) $$ [IH1]
  · iexact IH1
  iintro %v %v' HRef
  ihave HRef' := lrel_ref_unfold _ _ _ $$ HRef
  icases HRef' with ⟨%l, %l', %heq, %heq', #Hinv⟩
  have hfillv : Ectx.fill [EctxItem.storeL w] v.1 = Exp.store v.1 w.1 := rfl
  have hfillv' : Ectx.fill [EctxItem.storeL w'] v'.1 = Exp.store v'.1 w'.1 := rfl
  rw [hfillv, hfillv', heq, heq']
  -- Goal: refines ⊤ (.store #l w.1) (.store #l' w'.1) lrel_unit.
  have hfill_empty : Exp.store (.lit (.loc l)) w.1 =
    Ectx.fill [] (Exp.store (.lit (.loc l)) w.1) := rfl
  rw [hfill_empty]
  iapply (refines_atomic_l (E := ⊤) (E' := ⊤ \ ↑(logN.@ ((l, l') : Loc × Loc)))
    (K := []) (e1 := Exp.store (.lit (.loc l)) w.1)
    (t := Exp.store (.lit (.loc l')) w'.1)
    (A := lrel_unit) (OpenInv.of_atomic (Atomic.store l w)))
  iintro %K' Hr
  -- Open the invariant.
  have hsub : (↑(logN.@ ((l, l') : Loc × Loc)) : CoPset) ⊆ (⊤ : CoPset) :=
    fun _ _ => CoPset.mem_full
  imod Iris.inv_acc ⊤ _ _ hsub $$ Hinv with ⟨HInvBody, Hclose⟩
  ihave HInvBody1 := later_exists.mpr $$ HInvBody
  icases HInvBody1 with ⟨%v1, HInvBody2⟩
  ihave HInvBody3 := later_exists.mpr $$ HInvBody2
  icases HInvBody3 with ⟨%v2, HInvBody4⟩
  ihave HInvBody5 := later_sep.mp $$ HInvBody4
  icases HInvBody5 with ⟨Hv1L, HInvBody6⟩
  ihave HInvBody7 := later_sep.mp $$ HInvBody6
  icases HInvBody7 with ⟨Hv2L, _HwAL⟩
  imod Hv1L with Hv1
  imod Hv2L with Hv2
  imodintro
  -- RHS step: step_store on Hr.
  ihave HStep := step_store
    (E := ⊤ \ ↑(logN.@ ((l, l') : Loc × Loc))) K' (l := l') (v_old := v2) (v_new := w')
    (hv := w'.2) (hnew := Exp.toVal?_ofVal w') $$ [Hr Hv2]
  · isplitl [Hr]; · iexact Hr
    iexact Hv2
  iapply specUpdate_wp
  iapply (specUpdate_bind (E1 := ⊤ \ ↑(logN.@ ((l, l') : Loc × Loc)))
    (E2 := ⊤ \ ↑(logN.@ ((l, l') : Loc × Loc))) Std.LawfulSet.subset_refl)
  isplitl [HStep]; · iexact HStep
  iintro ⟨HKRes, Hv2'⟩
  iapply specUpdate_ret
  -- LHS step: wp_store. Use wp_step_fupd to thread close-inv through the step.
  -- Actually, there's no extra ▷ to absorb here (HwA is already persistent),
  -- so we don't need wp_step_fupd.
  have hstoreL : Exp.store (.lit (.loc l)) w.1 =
    Exp.store (.lit (.loc l)) (Exp.ofVal w) := rfl
  rw [hstoreL]
  iapply (wp_store (l := l) (v := w) (v' := v1))
  isplitl [Hv1]; · iexact Hv1
  iintro Hw1'
  -- Close the invariant with NEW values w, w'.
  ihave HCloseArg : iprop(▷ (∃ (w1 w2 : Val),
      (appHeapFrag l w1) ∗ (specHeapFrag l' w2) ∗ A w1 w2)) $$ [Hw1' Hv2' HwA]
  · iintro !>
    iexists w, w'
    isplitl [Hw1']; · iexact Hw1'
    isplitl [Hv2']; · iexact Hv2'
    iexact HwA
  ispecialize Hclose $$ HCloseArg
  imod Hclose with _
  imodintro
  iexists (Exp.lit .unit)
  isplitl [HKRes]; · iexact HKRes
  iapply (refines_ret (e1 := Ectx.fill [] (Exp.lit .unit)) (e2 := Exp.lit .unit)
    (v1 := ⟨.lit .unit, IsVal.lit⟩) (v2 := ⟨.lit .unit, IsVal.lit⟩)
    (hv1 := rfl) (hv2 := rfl))
  imodintro
  unfold lrel_unit
  ipure_intro
  exact ⟨rfl, rfl⟩

/-- `refines_load` (compatibility.v:118): dereference compatibility.
Loading through related references yields related values.

Mirrors Rocq's proof: `refines_bind` to focus on the values, destructure
`lrel_ref A` to get `(l, l', inv ...)`, apply `refines_atomic_l`, open the
invariant, RHS-step via `step_load`, LHS-step via `wp_load`, close the
invariant, produce the value post.

Uses `wp_step_fupd` (AppWeakestpre.lean:2048) to absorb the `▷ A.car w1 w2`
witness from the inv-open through `wp_load`'s atomic step. -/
theorem refines_load {e e' : Exp} {A : lrel GF} :
    iprop(refines ⊤ e e' (lrel_ref A))
      ⊢@{IProp GF} refines ⊤ (.load e) (.load e') A := by
  show _ ⊢@{IProp GF}
    refines ⊤ (Ectx.fill [EctxItem.load] e) (Ectx.fill [EctxItem.load] e') A
  iintro IH
  iapply (refines_bind [EctxItem.load] [EctxItem.load] (A := lrel_ref A)) $$ [IH]
  · iexact IH
  iintro %v %v' HRef
  ihave HRef' := lrel_ref_unfold _ _ _ $$ HRef
  icases HRef' with ⟨%l, %l', %heq, %heq', #Hinv⟩
  have hfillv : Ectx.fill [EctxItem.load] v.1 = Exp.load v.1 := rfl
  have hfillv' : Ectx.fill [EctxItem.load] v'.1 = Exp.load v'.1 := rfl
  rw [hfillv, hfillv', heq, heq']
  have hfill_empty : Exp.load (.lit (.loc l)) = Ectx.fill [] (Exp.load (.lit (.loc l))) := rfl
  rw [hfill_empty]
  iapply (refines_atomic_l (E := ⊤) (E' := ⊤ \ ↑(logN.@ ((l, l') : Loc × Loc)))
    (K := []) (e1 := Exp.load (.lit (.loc l))) (t := Exp.load (.lit (.loc l')))
    (A := A) (OpenInv.of_atomic (Atomic.load l)))
  iintro %K' Hr
  -- Open the invariant.
  have hsub : (↑(logN.@ ((l, l') : Loc × Loc)) : CoPset) ⊆ (⊤ : CoPset) :=
    fun _ _ => CoPset.mem_full
  imod Iris.inv_acc ⊤ _ _ hsub $$ Hinv with ⟨HInvBody, Hclose⟩
  -- HInvBody : ▷ (∃ w1 w2, l ↦ w1 ∗ l' ↦ₛ w2 ∗ A w1 w2).
  ihave HInvBody1 := later_exists.mpr $$ HInvBody
  icases HInvBody1 with ⟨%w1, HInvBody2⟩
  ihave HInvBody3 := later_exists.mpr $$ HInvBody2
  icases HInvBody3 with ⟨%w2, HInvBody4⟩
  ihave HInvBody5 := later_sep.mp $$ HInvBody4
  icases HInvBody5 with ⟨Hw1L, HInvBody6⟩
  ihave HInvBody7 := later_sep.mp $$ HInvBody6
  icases HInvBody7 with ⟨Hw2L, #HwAL⟩
  imod Hw1L with Hw1
  imod Hw2L with Hw2
  imodintro
  -- RHS step: step_load on Hr.
  ihave HStep := step_load (E := ⊤ \ ↑(logN.@ ((l, l') : Loc × Loc))) K' (l := l') (v := w2)
    $$ [Hr Hw2]
  · isplitl [Hr]; · iexact Hr
    iexact Hw2
  iapply specUpdate_wp
  iapply (specUpdate_bind (E1 := ⊤ \ ↑(logN.@ ((l, l') : Loc × Loc)))
    (E2 := ⊤ \ ↑(logN.@ ((l, l') : Loc × Loc))) Std.LawfulSet.subset_refl)
  isplitl [HStep]; · iexact HStep
  iintro ⟨HKRes, Hw2'⟩
  iapply specUpdate_ret
  -- LHS step: wp_load, but use wp_step_fupd to thread HwAL : ▷ A.car w1 w2
  -- through the step. The step absorbs the outer ▷, so inside the post we
  -- have access to A.car w1 w2 directly.
  have HE : (∅ : CoPset) ⊆ (⊤ \ ↑(logN.@ ((l, l') : Loc × Loc)) : CoPset) :=
    Std.LawfulSet.empty_subset
  have hv : (Exp.load (.lit (.loc l))).toVal? = none :=
    Exp.toVal?_eq_none.mpr fun ⟨w⟩ => nomatch w
  iapply (wp_step_fupd (P := A.car w1 w2)
    (E1 := ⊤ \ ↑(logN.@ ((l, l') : Loc × Loc))) (E2 := ∅) HE hv)
  isplitl [HwAL]
  · -- First sub-goal (with HwAL): |={E1, ∅}=> ▷ |={∅, E1}=> A.car w1 w2.
    ihave Hgoal := step_fupd_intro_later
      (E1 := ⊤ \ ↑(logN.@ ((l, l') : Loc × Loc))) (E2 := ∅)
      (P := A.car w1 w2) HE $$ HwAL
    iexact Hgoal
  -- Second sub-goal: wp ∅ (.load #l) (fun v => A.car w1 w2 -∗ ...).
  iapply (wp_load (l := l) (v := w1))
  isplitl [Hw1]; · iexact Hw1
  iintro Hw1'
  -- Now goal post: A.car w1 w2 -∗ ... (the wp_step_fupd post wand).
  iintro #HwA
  -- HwA : A.car w1 w2 (no ▷!). Now close inv and produce post.
  ihave HCloseArg : iprop(▷ (∃ (w1 w2 : Val),
      (appHeapFrag l w1) ∗ (specHeapFrag l' w2) ∗ A w1 w2)) $$ [Hw1' Hw2' HwA]
  · iintro !>
    iexists w1, w2
    isplitl [Hw1']; · iexact Hw1'
    isplitl [Hw2']; · iexact Hw2'
    iexact HwA
  ispecialize Hclose $$ HCloseArg
  imod Hclose with _
  imodintro
  iexists (Exp.ofVal w2)
  isplitl [HKRes]; · iexact HKRes
  iapply (refines_ret (e1 := Ectx.fill [] w1.1) (e2 := Exp.ofVal w2)
    (v1 := w1) (v2 := w2) (hv1 := rfl) (hv2 := rfl))
  imodintro
  iexact HwA

/-- `refines_rand_tape` (compatibility.v:139): labeled-rand compatibility.
Both sides sample from related tapes, at related bounds.

Mirrors Rocq's proof: bind e2/e2' (tape locations α, α', bound N with inv),
bind e1/e1' (nat value M), refines_atomic_l at `.rand #M (lbl α)`, open
the tape invariant, case-split `N = M` or `N ≠ M`, apply the corresponding
`wp_couple_rand_lbl_rand_lbl`{,_wrong} rule.

**Port note**: same `0 < M` hypothesis issue as `refines_rand_unit` in the
degenerate case — Rocq's auto discharge doesn't carry over. Requires
`0 < M` at the coupling step; when M = 0, LHS is stuck and lemma is false. -/
theorem refines_rand_tape {e1 e1' e2 e2' : Exp} :
    iprop(refines ⊤ e1 e1' lrel_pos_nat) ⊢@{IProp GF}
      iprop(refines ⊤ e2 e2' lrel_tape -∗
        refines ⊤ (.rand e1 e2) (.rand e1' e2') lrel_nat) := by
  show iprop(refines ⊤ e1 e1' lrel_pos_nat) ⊢@{IProp GF}
    iprop(refines ⊤ e2 e2' lrel_tape -∗
      refines ⊤ (Ectx.fill [EctxItem.randR e1] e2)
                (Ectx.fill [EctxItem.randR e1'] e2') lrel_nat)
  iintro IH1 IH2
  -- Bind e2/e2' to get tape locations α, α' and bound N under invariant.
  iapply (refines_bind [EctxItem.randR e1] [EctxItem.randR e1']
    (A := lrel_tape)) $$ [IH2]
  · iexact IH2
  iintro %w %w' HTapeRel
  ihave HTapeEx := lrel_tape_unfold _ _ $$ HTapeRel
  icases HTapeEx with ⟨%α, %α', %N, %Hw, %Hw', #Hinv⟩
  -- Reshape via defeq: [randR e1].fill w.1 = .rand e1 w.1 = [randL w].fill e1.
  have hfillR_to_L : Ectx.fill [EctxItem.randR e1] w.1 =
    Ectx.fill [EctxItem.randL w] e1 := rfl
  have hfillR_to_L' : Ectx.fill [EctxItem.randR e1'] w'.1 =
    Ectx.fill [EctxItem.randL w'] e1' := rfl
  rw [hfillR_to_L, hfillR_to_L']
  -- Now bind e1/e1' to get M : Nat (positive).
  iapply (refines_bind [EctxItem.randL w] [EctxItem.randL w']
    (A := lrel_pos_nat)) $$ [IH1]
  · iexact IH1
  iintro %v %v' HPosNat
  ihave HPosNatEx := lrel_pos_nat_unfold v v' $$ HPosNat
  icases HPosNatEx with ⟨%M, %hM_pos, %HvM, %Hv'M⟩
  have hfillv : Ectx.fill [EctxItem.randL w] v.1 = Exp.rand v.1 w.1 := rfl
  have hfillv' : Ectx.fill [EctxItem.randL w'] v'.1 = Exp.rand v'.1 w'.1 := rfl
  rw [hfillv, hfillv', HvM, Hv'M, Hw, Hw']
  -- Goal: refines ⊤ (.rand #M (lbl α)) (.rand #M (lbl α')) lrel_nat.
  -- Apply refines_atomic_l at K = [].
  have hfill_empty : Exp.rand (.lit (.int (M : Int))) (.lit (.lbl α)) =
    Ectx.fill [] (Exp.rand (.lit (.int (M : Int))) (.lit (.lbl α))) := rfl
  rw [hfill_empty]
  iapply (refines_atomic_l (E := ⊤) (E' := ⊤ \ ↑(logN.@ ((α, α') : Loc × Loc)))
    (K := []) (e1 := Exp.rand (.lit (.int (M : Int))) (.lit (.lbl α)))
    (t := Exp.rand (.lit (.int (M : Int))) (.lit (.lbl α')))
    (A := lrel_nat) (OpenInv.of_atomic (Atomic.rand_lbl (M : Int) α)))
  iintro %K' Hr
  -- Open the tape invariant.
  have hsub : (↑(logN.@ ((α, α') : Loc × Loc)) : CoPset) ⊆ (⊤ : CoPset) :=
    fun _ _ => CoPset.mem_full
  imod Iris.inv_acc ⊤ _ _ hsub $$ Hinv with ⟨HInvBody, Hclose⟩
  -- HInvBody : ▷ (α ↪ₐ ⟨N, []⟩ ∗ α' ↪ₛ ⟨N, []⟩). Push ▷ inside, strip via Timeless.
  ihave HInvBody1 := later_sep.mp $$ HInvBody
  icases HInvBody1 with ⟨HαL, Hα'L⟩
  imod HαL with Hα
  imod Hα'L with Hα'
  imodintro
  -- Convert backend-frags to user-level appNatTape/specNatTape.
  ihave HαN := app_empty_to_natTape (GF := GF) (l := α) (z := N) $$ Hα
  ihave Hα'N := spec_empty_to_natTape (GF := GF) (l := α') (z := N) $$ Hα'
  -- Case-split on N = M.
  by_cases hNM : N = (M : Int)
  · -- N = M case: use wp_couple_rand_lbl_rand_lbl.
    subst hNM
    -- M > 0 comes from lrel_pos_nat.
    have hMpos : (0 : Int) < (M : Int) := by exact_mod_cast hM_pos
    iapply (wp_couple_rand_lbl_rand_lbl (M : Int) id
      (hdom := fun _ h0 hlt => ⟨h0, hlt⟩)
      (hbij := fun m h0 hlt => ⟨m, ⟨⟨h0, hlt⟩, rfl⟩, fun n' ⟨_, heq⟩ => heq⟩)
      (Hz := hMpos) (K := K') (E := ⊤ \ ↑(logN.@ ((α, α') : Loc × Loc)))
      (α := α) (α' := α'))
    isplitl [HαN]
    · iintro !>; iexact HαN
    isplitl [Hα'N]
    · iintro !>; iexact Hα'N
    isplitl [Hr]; · iexact Hr
    iintro %n ⟨HαRet, Hα'Ret, HKRes, %Hnr⟩
    -- Close invariant.
    ihave HαBack := app_natTape_to_empty (GF := GF) (l := α) (z := M) $$ HαRet
    ihave Hα'Back := spec_natTape_to_empty (GF := GF) (l := α') (z := M) $$ Hα'Ret
    ihave HCloseArg : iprop(▷ (appTapesFrag α ⟨(M : Int), []⟩ ∗
        specTapesFrag α' ⟨(M : Int), []⟩)) $$ [HαBack Hα'Back]
    · iintro !>
      isplitl [HαBack]; · iexact HαBack
      iexact Hα'Back
    ispecialize Hclose $$ HCloseArg
    imod Hclose with _
    imodintro
    iexists (.lit (.int (id n)))
    isplitl [HKRes]; · iexact HKRes
    iapply (refines_ret (e1 := Ectx.fill [] (.lit (.int n)))
      (e2 := Exp.lit (.int (id n)))
      (v1 := ⟨.lit (.int n), IsVal.lit⟩) (v2 := ⟨.lit (.int (id n)), IsVal.lit⟩)
      (hv1 := rfl) (hv2 := rfl))
    imodintro
    unfold lrel_nat
    obtain ⟨Hn0, Hnm⟩ := Hnr
    iexists n.toNat
    ipure_intro
    have hk : (n.toNat : Int) = n := Int.toNat_of_nonneg Hn0
    refine ⟨?_, ?_⟩ <;> rw [hk]
    · rfl
  · -- N ≠ M case: use wp_couple_rand_lbl_rand_lbl_wrong (rand bound z = M, tape bound N).
    have hMpos : (0 : Int) < (M : Int) := by exact_mod_cast hM_pos
    iapply (wp_couple_rand_lbl_rand_lbl_wrong (M : Int) N id
      (hdom := fun _ h0 hlt => ⟨h0, hlt⟩)
      (hbij := fun m h0 hlt => ⟨m, ⟨⟨h0, hlt⟩, rfl⟩, fun n' ⟨_, heq⟩ => heq⟩)
      (Hz := hMpos) (HneM := fun heq => hNM heq.symm)
      (K := K') (E := ⊤ \ ↑(logN.@ ((α, α') : Loc × Loc)))
      (α := α) (α' := α') (xs := []) (ys := []))
    isplitl [HαN]
    · iintro !>; iexact HαN
    isplitl [Hα'N]
    · iintro !>; iexact Hα'N
    isplitl [Hr]; · iexact Hr
    iintro %n ⟨HαRet, Hα'Ret, HKRes, %Hnr⟩
    ihave HαBack := app_natTape_to_empty (GF := GF) (l := α) (z := N) $$ HαRet
    ihave Hα'Back := spec_natTape_to_empty (GF := GF) (l := α') (z := N) $$ Hα'Ret
    ihave HCloseArg : iprop(▷ (appTapesFrag α ⟨N, []⟩ ∗
        specTapesFrag α' ⟨N, []⟩)) $$ [HαBack Hα'Back]
    · iintro !>
      isplitl [HαBack]; · iexact HαBack
      iexact Hα'Back
    ispecialize Hclose $$ HCloseArg
    imod Hclose with _
    imodintro
    iexists (.lit (.int (id n)))
    isplitl [HKRes]; · iexact HKRes
    iapply (refines_ret (e1 := Ectx.fill [] (.lit (.int n)))
      (e2 := Exp.lit (.int (id n)))
      (v1 := ⟨.lit (.int n), IsVal.lit⟩) (v2 := ⟨.lit (.int (id n)), IsVal.lit⟩)
      (hv1 := rfl) (hv2 := rfl))
    imodintro
    unfold lrel_nat
    obtain ⟨Hn0, Hnm⟩ := Hnr
    iexists n.toNat
    ipure_intro
    have hk : (n.toNat : Int) = n := Int.toNat_of_nonneg Hn0
    refine ⟨?_, ?_⟩ <;> rw [hk]
    · rfl

/-- `refines_rand_unit` (compatibility.v:175): unlabeled-rand compatibility.
Couples unlabeled rand calls at related bounds using `refines_couple_rands_lr`.

**Port note**: Rocq's `rand n` accepts `n = 0` (returns 0), but our Lean
`RandNoTapeS` requires `0 < n`. We take the premise at `lrel_pos_nat`
(positivity-restricted), ruling out the stuck `rand 0` case. Conclusion
stays at `lrel_nat` since the result may be 0. -/
theorem refines_rand_unit {e e' : Exp} :
    iprop(refines ⊤ e e' lrel_pos_nat)
      ⊢@{IProp GF}
        refines ⊤ (Ectx.fill [EctxItem.randL ⟨.lit .unit, IsVal.lit⟩] e)
          (Ectx.fill [EctxItem.randL ⟨.lit .unit, IsVal.lit⟩] e')
          lrel_nat := by
  iintro IH
  iapply (refines_bind
    [EctxItem.randL ⟨.lit .unit, IsVal.lit⟩]
    [EctxItem.randL ⟨.lit .unit, IsVal.lit⟩]
    (A := lrel_pos_nat)) $$ [IH]
  · iexact IH
  iintro %v %v' HPosNat
  ihave HPosNatEx := lrel_pos_nat_unfold v v' $$ HPosNat
  icases HPosNatEx with ⟨%n, %hn_pos, %Hv, %Hv'⟩
  have hfillv : Ectx.fill [EctxItem.randL ⟨.lit .unit, IsVal.lit⟩] v.1 =
      Exp.rand v.1 (.lit .unit) := rfl
  have hfillv' : Ectx.fill [EctxItem.randL ⟨.lit .unit, IsVal.lit⟩] v'.1 =
      Exp.rand v'.1 (.lit .unit) := rfl
  rw [hfillv, hfillv', Hv, Hv']
  -- Goal: refines ⊤ (.rand #n ()) (.rand #n ()) lrel_nat. Apply couple_rands_lr.
  · have hnpos : (0 : Int) < (n : Int) := by exact_mod_cast hn_pos
    -- Reshape: .rand #n () = Ectx.fill [] (.rand #n ()).
    have hfill_emp : Exp.rand (.lit (.int (n : Int))) (.lit .unit) =
      Ectx.fill [] (Exp.rand (.lit (.int (n : Int))) (.lit .unit)) := rfl
    rw [hfill_emp]
    iapply (refines_couple_rands_lr (E := ⊤) (K := []) (K' := []) (A := lrel_nat)
      (z := (n : Int)) (f := id)
      (hdom := fun _ h0 hlt => ⟨h0, hlt⟩)
      (hbij := fun m h0 hlt => ⟨m, ⟨⟨h0, hlt⟩, rfl⟩, fun n' ⟨_, heq⟩ => heq⟩)
      (Hz := hnpos))
    iintro %m ⟨%Hm0, %Hmn⟩
    -- Goal: refines ⊤ ([].fill #m) ([].fill #(id m)) lrel_nat. id m = m.
    have hfill1 : Ectx.fill [] (Exp.lit (.int m)) = Exp.lit (.int m) := rfl
    have hfill2 : Ectx.fill [] (Exp.lit (.int (id m))) = Exp.lit (.int m) := rfl
    rw [hfill1, hfill2]
    -- Goal: refines ⊤ #m #m lrel_nat. Use refines_ret with v = ⟨#m, IsVal.lit⟩.
    -- But m : Int, and we need m = (some Nat : Int). We have 0 ≤ m, so m is Nat.
    iapply (refines_ret (e1 := Exp.lit (.int m)) (e2 := Exp.lit (.int m))
      (v1 := ⟨.lit (.int m), IsVal.lit⟩) (v2 := ⟨.lit (.int m), IsVal.lit⟩)
      (hv1 := rfl) (hv2 := rfl))
    imodintro
    -- Goal: lrel_nat.car ⟨#m, _⟩ ⟨#m, _⟩ = ∃ k : Nat, ⌜#m = #(k:Int) ∧ #m = #(k:Int)⌝.
    unfold lrel_nat
    iexists m.toNat
    ipure_intro
    have hk : (m.toNat : Int) = m := Int.toNat_of_nonneg Hm0
    refine ⟨?_, ?_⟩ <;> rw [hk]

end Compatibility

end ProbLang
