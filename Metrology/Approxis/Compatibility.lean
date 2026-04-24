import Metrology.Approxis.PrimitiveLaws
import Metrology.Approxis.Proofmode
import Metrology.Approxis.Model
import Metrology.Approxis.RelTactics
import Metrology.Approxis.AppRelRules

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
`(REL e1 << e1' : A) ∗ (REL e2 << e2' : B) ⊢ REL (e1; e2) << (e1'; e2') : B`. -/
theorem refines_seq (A : lrel GF) {e1 e2 e1' e2' : Exp} {B : lrel GF} :
    iprop(refines ⊤ e1 e1' A) ⊢@{IProp GF}
      iprop(refines ⊤ e2 e2' B -∗
        refines ⊤ (.app (.lam e2) e1) (.app (.lam e2') e1') B) := by
  sorry

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

**Blocker**: Rocq uses `rel_rec_l; rel_rec_r; iApply "H"` — two pure beta steps
over the value-restricted forall encoding. That requires `refines_pure_l` and
`refines_pure_r` (the former still sorry'd in AppRelRules). Once both are
proved, this reduces to a direct application of the persistent IH `H` at the
chosen semantic type `A`, after pure-stepping both sides past the `λ<>.·`. -/
theorem refines_forall {e e' : Exp} {C : lrel GF → lrel GF} :
    BI.intuitionistically (BI.forall (fun A : lrel GF => refines (⊤ : CoPset) e e' (C A)))
      ⊢@{IProp GF} refines ⊤ (.lam e) (.lam e') (lrel_forall C) := by
  sorry

/-- `refines_store` (compatibility.v:95): store compatibility.
Stores to related references preserve the refinement. -/
theorem refines_store {e1 e2 e1' e2' : Exp} {A : lrel GF} :
    iprop(refines ⊤ e1 e1' (lrel_ref A)) ⊢@{IProp GF}
      iprop(refines ⊤ e2 e2' A -∗
        refines ⊤ (.store e1 e2) (.store e1' e2') lrel_unit) := by
  sorry

/-- `refines_load` (compatibility.v:118): dereference compatibility.
Loading through related references yields related values. -/
theorem refines_load {e e' : Exp} {A : lrel GF} :
    iprop(refines ⊤ e e' (lrel_ref A))
      ⊢@{IProp GF} refines ⊤ (.load e) (.load e') A := by
  sorry

/-- `refines_rand_tape` (compatibility.v:139): labeled-rand compatibility.
Both sides sample from related tapes, at related bounds. -/
theorem refines_rand_tape {e1 e1' e2 e2' : Exp} :
    iprop(refines ⊤ e1 e1' lrel_nat) ⊢@{IProp GF}
      iprop(refines ⊤ e2 e2' lrel_tape -∗
        refines ⊤ (.rand e1 e2) (.rand e1' e2') lrel_nat) := by
  sorry

/-- `refines_rand_unit` (compatibility.v:175): unlabeled-rand compatibility.
Couples unlabeled rand calls at related bounds using `refines_couple_rands_lr`.

**Status**: partial — outer bind and value destructuring done; the inner
`refines_couple_rands_lr` application needs `0 < n` (which Rocq handles implicitly
via `fin (S N)`) and the final step. Deferred. -/
theorem refines_rand_unit {e e' : Exp} :
    iprop(refines ⊤ e e' lrel_nat)
      ⊢@{IProp GF}
        refines ⊤ (Ectx.fill [EctxItem.randL ⟨.lit .unit, IsVal.lit⟩] e)
          (Ectx.fill [EctxItem.randL ⟨.lit .unit, IsVal.lit⟩] e')
          lrel_nat := by
  iintro IH
  iapply (refines_bind
    [EctxItem.randL ⟨.lit .unit, IsVal.lit⟩]
    [EctxItem.randL ⟨.lit .unit, IsVal.lit⟩]
    (A := lrel_nat)) $$ [IH]
  · iexact IH
  iintro %v %v' HNat
  ihave HNatEx := lrel_nat_unfold v v' $$ HNat
  icases HNatEx with ⟨%n, %Hv, %Hv'⟩
  have hfillv : Ectx.fill [EctxItem.randL ⟨.lit .unit, IsVal.lit⟩] v.1 =
      Exp.rand v.1 (.lit .unit) := rfl
  have hfillv' : Ectx.fill [EctxItem.randL ⟨.lit .unit, IsVal.lit⟩] v'.1 =
      Exp.rand v'.1 (.lit .unit) := rfl
  rw [hfillv, hfillv', Hv, Hv']
  -- Goal: refines ⊤ (.rand #n ()) (.rand #n ()) lrel_nat.
  -- Apply refines_couple_rands_lr at z := n with f := id. Requires 0 < n.
  sorry

end Compatibility

end ProbLang
