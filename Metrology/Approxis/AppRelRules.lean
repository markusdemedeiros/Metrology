module

public import Metrology.Approxis.AppWeakestpre
public import Metrology.Approxis.Model
public import Metrology.Approxis.PrimitiveLaws
public import Metrology.Approxis.CouplingRules
public import Metrology.Approxis.OpenInv

@[expose] public section

set_option linter.discrete false

/-! # Relational Rules -/

open Std Iris Iris.Std Iris.BI Iris.ProofMode OFE COFE ProbLang ProbLang.ApproxisWpGS
open scoped AppGS

namespace ProbLang


variable {rT : Type _} [ProbLangℝ rT] [Countable rT] [MeasurableSingletonClass rT]

section AppRelRules
variable {hlc : HasLC} {GF : BundledGFunctors} [IR : ApproxisRGS rT hlc GF]

/-! ## Forward reductions on the LHS -/

theorem nat_repeat_later_eq_laterN (n : Nat) (P : IProp GF) :
    Nat.repeat (fun Q : IProp GF => iprop(▷ Q)) n P = iprop(▷^[n] P) := by
  induction n with
  | zero => rfl
  | succ m ih => simp only [Nat.repeat]; rw [ih]; rfl

/-- `refines_pure_l` (app_rel_rules.v:27): if `e` pure-steps to `e'` in `n` steps,
`▷^n (REL K[e'] << t : A) ⊢ REL K[e] << t : A`. -/
theorem refines_pure_l {E : CoPset} {K : Ectx rT} {e e' t : Exp rT} {A : lrel rT GF}
    {φ : Prop} {n : ℕ} [Hex : PureExec_discrete φ n e e'] (Hφ : φ) :
    Nat.repeat (fun Q : IProp GF => iprop(▷ Q)) n (refines E (K.fill e') t A)
      ⊢@{IProp GF} refines E (K.fill e) t A := by
  have HexK : PureExec_discrete φ n (K.fill e) (K.fill e') := PureExec_discrete.fill K
  unfold refines
  iintro H
  iintro %K' %ε HK Hna Herr Hpos
  iapply (wp_pure_step_later (Hex := HexK) Hφ)
  ihave H0 : iprop(▷^[n] (∀ (K₂ : Ectx rT) (ε₂ : ENNReal),
      (⤇ K₂.fill t) -∗ (naOwnP E) -∗ (↯ ε₂) -∗ (⌜(0 : ENNReal) < ε₂⌝) -∗
      wp ⊤ (K.fill e') (fun v => iprop(∃ v' ε',
        (⤇ K₂.fill v'.1) ∗ naOwnP ⊤ ∗ (↯ ε') ∗ (⌜(0 : ENNReal) < ε'⌝) ∗ A.car v v')))) $$ [H]
  · rw [← nat_repeat_later_eq_laterN]; iexact H
  rw [nat_repeat_later_eq_laterN]
  ihave H1 := (BI.laterN_forall n).mp $$ H0
  ispecialize H1 $$ %K'
  ihave H2 := (BI.laterN_forall n).mp $$ H1
  ispecialize H2 $$ %ε
  ihave H3 := BI.laterN_wand n $$ H2
  ihave HKLater : iprop(▷^[n] (⤇ K'.fill t)) $$ [HK]
  · iapply BI.laterN_intro n; iexact HK
  ispecialize H3 $$ HKLater
  ihave H4 := BI.laterN_wand n $$ H3
  ihave HnaLater : iprop(▷^[n] naOwnP E) $$ [Hna]
  · iapply BI.laterN_intro n; iexact Hna
  ispecialize H4 $$ HnaLater
  ihave H5 := BI.laterN_wand n $$ H4
  ihave HerrLater : iprop(▷^[n] (↯ ε)) $$ [Herr]
  · iapply BI.laterN_intro n; iexact Herr
  ispecialize H5 $$ HerrLater
  ihave H6 := BI.laterN_wand n $$ H5
  ihave HposLater : iprop(▷^[n] ⌜(0 : ENNReal) < ε⌝) $$ [Hpos]
  · iapply BI.laterN_intro n; iexact Hpos
  ispecialize H6 $$ HposLater
  iexact H6

/-- `refines_pure_r` (app_rel_rules.v:73): RHS pure step. -/
theorem refines_pure_r {E : CoPset} {K : Ectx rT} {e e' t : Exp rT} {A : lrel rT GF}
    {φ : Prop} {n : ℕ} [Hex : PureExec_discrete φ n e e'] (Hφ : φ) :
    refines E t (K.fill e') A ⊢@{IProp GF} refines E t (K.fill e) A := by
  unfold refines
  iintro H
  iintro %K' %ε Hj Hna Herr Hpos
  have hfc : K'.fill (K.fill e) = (K'.comp K).fill e := Ectx.fill_comp K' K e
  have hfc' : K'.fill (K.fill e') = (K'.comp K).fill e' := Ectx.fill_comp K' K e'
  rw [hfc]
  ihave HStep := step_pure (E := ⊤) (K'.comp K) (Hex := Hex) Hφ $$ Hj
  iapply specUpdate_wp
  iapply (specUpdate_bind (E1 := ⊤) (E2 := ⊤) Std.LawfulSet.subset_refl)
  isplitl [HStep]; · iexact HStep
  iintro HK'
  ihave HK'' : iprop(⤇ K'.fill (K.fill e')) $$ [HK']
  · rw [hfc']; iexact HK'
  iapply specUpdate_ret
  iapply H $$ %K' %ε HK'' Hna Herr Hpos

/-- `refines_step_r` (app_rel_rules.v): single-step RHS spec helper. The user
provides, for any outer context `K''`, a `specUpdate` from `⤇ K''.fill e₂` to
`∃ v, ⤇ K''.fill v ∗ refines E e₁ (K'.fill v) A`. -/
theorem refines_step_r {E : CoPset} {K' : Ectx rT} {e1 e2 : Exp rT} {A : lrel rT GF} :
    iprop(∀ (K : Ectx rT), (⤇ K.fill e2) -∗
            specUpdate rT ⊤ (∃ (v : Val rT), iprop((⤇ K.fill v.1) ∗
              refines E e1 (K'.fill v.1) A)))
      ⊢@{IProp GF} refines E e1 (K'.fill e2) A := by
  iintro He
  unfold refines
  iintro %K'' %ε Hj Hna Herr Hpos
  have hfc : K''.fill (K'.fill e2) = (K''.comp K').fill e2 := Ectx.fill_comp K'' K' e2
  ihave Hj' : iprop(⤇ (K''.comp K').fill e2) $$ [Hj]
  · rw [← hfc]; iexact Hj
  ihave HStep := He $$ %(K''.comp K') Hj'
  iapply specUpdate_wp
  iapply (specUpdate_bind (E1 := ⊤) (E2 := ⊤) Std.LawfulSet.subset_refl)
  isplitl [HStep]; · iexact HStep
  iintro ⟨%v, HK'', Hrefines⟩
  have hfcv : K''.fill (K'.fill v.1) = (K''.comp K').fill v.1 := Ectx.fill_comp K'' K' v.1
  ihave HK''' : iprop(⤇ K''.fill (K'.fill v.1)) $$ [HK'']
  · rw [hfcv]; iexact HK''
  iapply specUpdate_ret
  iapply Hrefines $$ %K'' %ε HK''' Hna Herr Hpos

/-- `refines_steps_r` (app_rel_rules.v): variant of `refines_step_r` where the
RHS reduct `e₂'` is known. Useful when the value isn't fresh. -/
theorem refines_steps_r {E : CoPset} {K' : Ectx rT} {e1 e2 e2' : Exp rT} {A : lrel rT GF} :
    iprop(∀ (K : Ectx rT), (⤇ K.fill e2) -∗ specUpdate rT ⊤ (⤇ K.fill e2'))
      ⊢@{IProp GF} (|={⊤}=> refines E e1 (K'.fill e2') A) -∗
        refines E e1 (K'.fill e2) A := by
  unfold refines
  iintro Hupd Hlog
  iintro %K'' %ε Hj Hna Herr Hpos
  imod Hlog
  have hfc : K''.fill (K'.fill e2) = (K''.comp K').fill e2 := Ectx.fill_comp K'' K' e2
  have hfc' : K''.fill (K'.fill e2') = (K''.comp K').fill e2' := Ectx.fill_comp K'' K' e2'
  ihave Hj' : iprop(⤇ (K''.comp K').fill e2) $$ [Hj]
  · rw [← hfc]; iexact Hj
  ihave HStep := Hupd $$ %(K''.comp K') Hj'
  iapply specUpdate_wp
  iapply (specUpdate_bind (E1 := ⊤) (E2 := ⊤) Std.LawfulSet.subset_refl)
  isplitl [HStep]; · iexact HStep
  iintro HKres
  ihave HKres' : iprop(⤇ K''.fill (K'.fill e2')) $$ [HKres]
  · rw [hfc']; iexact HKres
  iapply specUpdate_ret
  iapply Hlog $$ %K'' %ε HKres' Hna Herr Hpos

/-- `refines_wp_l` (app_rel_rules.v:41): embed a `wp` into a `refines` on the LHS.

Rocq: `iIntros "He" (K' ε) "Hs Hnais Herr Hpos"; wp_bind; iApply (wp_wand with "He")`.
In Lean Iris, `wp_wand` requires a persistent wand so we use `wp_frame_l` to thread
the spatial context through.

**Port notes**: `unfold refines` inside iris proofmode unfolds EVERYWHERE, including
the post of `He`. Strategy: (1) open the `refines` body at the top using `show` so
the Lean-level goal is `refines ... ⊢ refines ...`, (2) enter iris with `iintro He`
then `iintro %K' %ε ...` — `He`'s post still has `refines` since `unfold` happened
at the goal-shape level BEFORE any iintro. Key: do `show` with a `change`-like
entailment reshape that works outside iris proofmode. -/
theorem refines_wp_l {E : CoPset} {K : Ectx rT} {e1 t : Exp rT} {A : lrel rT GF} :
    iprop(wp ⊤ e1 (fun v => refines E (K.fill v.1) t A))
      ⊢@{IProp GF} refines E (K.fill e1) t A := by
  show iprop(wp ⊤ e1 (fun v => refines E (K.fill v.1) t A)) ⊢@{IProp GF}
    iprop(∀ (K' : Ectx rT) (ε : ENNReal),
      (⤇ (K'.fill t)) -∗
      (naOwnP E) -∗
      (↯ ε) -∗
      (⌜ (0 : ENNReal) < ε ⌝) -∗
      wp ⊤ (K.fill e1) (fun v => iprop(∃ (v' : Val rT) (ε' : ENNReal),
        (⤇ (K'.fill v'.1)) ∗ (naOwnP ⊤) ∗ (↯ ε') ∗ (⌜ (0 : ENNReal) < ε' ⌝) ∗ A v v')))
  iintro He %K' %ε HK Hna Herr Hpos
  iapply wp_bind (K := K)
  let R : IProp GF := iprop((⤇ K'.fill t) ∗ (naOwnP (rT := rT) (hlc := hlc) E) ∗ (↯ ε) ∗ (⌜(0 : ENNReal) < ε⌝))
  ihave HR : R $$ [HK Hna Herr Hpos]
  · isplitl [HK]; · iassumption
    isplitl [Hna]; · iassumption
    isplitl [Herr]; · iassumption
    iassumption
  ihave HFrame : iprop(wp ⊤ e1 (fun v => iprop(R ∗ refines E (K.fill v.1) t A)))
      $$ [HR He]
  · iapply (wp_frame_l (R := R) (e := e1) (E := ⊤)
      (Φ := fun v => refines E (K.fill v.1) t A))
    isplitl [HR]; · iexact HR
    iexact He
  iapply (wp_mono
    (Φ := fun v => iprop(R ∗ refines E (K.fill v.1) t A))
    (Ψ := fun v => wp ⊤ (K.fill (Exp.ofVal v))
      (fun v₀ => iprop(∃ v' ε', (⤇ K'.fill v'.1) ∗ naOwnP ⊤ ∗ (↯ ε') ∗
        (⌜(0 : ENNReal) < ε'⌝) ∗ A.car v₀ v'))))
  case HΦ =>
    intro v
    have hfill : Exp.ofVal v = v.1 := rfl
    rw [hfill]
    iintro ⟨⟨HK', Hna', Herr', %Hpos'⟩, HRefv⟩
    ihave HRefv' := refines_unfold $$ HRefv
    iapply HRefv' $$ %K' %ε HK' Hna' Herr'
    ipureintro; exact Hpos'
  iexact HFrame

/-- `refines_atomic_l` (app_rel_rules.v:54): atomic step on the LHS, opening the
continuation to allow spec-side steps + invariant opening.

Takes `OpenInv e1` (mirrors Rocq's `Atomic StronglyAtomic e1`) so that callers
can open invariants (mask-shift `⊤ → E'`) for the duration of the single step. -/
theorem refines_atomic_l {E E' : CoPset} {K : Ectx rT} {e1 t : Exp rT} {A : lrel rT GF}
    (Hopen : OpenInv e1) :
    iprop(∀ (K' : Ectx rT),
            (⤇ (K'.fill t)) -∗
            (|={⊤, E'}=> wp E' e1 (fun v => iprop(|={E', ⊤}=> ∃ (t' : Exp rT),
              (⤇ (K'.fill t')) ∗ refines E (K.fill v.1) t' A))))
      ⊢@{IProp GF} refines E (K.fill e1) t A := by
  show iprop(∀ (K' : Ectx rT),
            (⤇ (K'.fill t)) -∗
            (|={⊤, E'}=> wp E' e1 (fun v => iprop(|={E', ⊤}=> ∃ (t' : Exp rT),
              (⤇ (K'.fill t')) ∗ refines E (K.fill v.1) t' A)))) ⊢@{IProp GF}
    iprop(∀ (K' : Ectx rT) (ε : ENNReal),
      (⤇ (K'.fill t)) -∗
      (naOwnP E) -∗
      (↯ ε) -∗
      (⌜ (0 : ENNReal) < ε ⌝) -∗
      wp ⊤ (K.fill e1) (fun v => iprop(∃ (v' : Val rT) (ε' : ENNReal),
        (⤇ (K'.fill v'.1)) ∗ (naOwnP ⊤) ∗ (↯ ε') ∗ (⌜ (0 : ENNReal) < ε' ⌝) ∗ A v v')))
  iintro Hlog %K' %ε HK Hna Herr Hpos
  iapply wp_bind (K := K)
  iapply (wp_atomic Hopen (E1 := ⊤) (E2 := E')
    (Φ := fun v => wp ⊤ (K.fill (Exp.ofVal v)) (fun v₀ => iprop(∃ v' ε',
      (⤇ K'.fill v'.1) ∗ naOwnP ⊤ ∗ (↯ ε') ∗ (⌜(0 : ENNReal) < ε'⌝) ∗ A.car v₀ v'))))
  ispecialize Hlog $$ %K' HK
  imod Hlog with HW
  imodintro
  let R : IProp GF := iprop((naOwnP (rT := rT) (hlc := hlc) E) ∗ (↯ ε) ∗ (⌜(0 : ENNReal) < ε⌝))
  ihave HR : R $$ [Hna Herr Hpos]
  · isplitl [Hna]; · iassumption
    isplitl [Herr]; · iassumption
    iassumption
  ihave HFrame : iprop(wp E' e1 (fun v => iprop(R ∗
      (|={E', ⊤}=> ∃ t', ⤇ K'.fill t' ∗ refines E (K.fill v.1) t' A))))
      $$ [HR HW]
  · iapply (wp_frame_l (R := R) (e := e1) (E := E')
      (Φ := fun v => iprop(|={E',⊤}=> ∃ t', ⤇ K'.fill t' ∗ refines E (K.fill v.1) t' A)))
    isplitl [HR]; · iexact HR
    iexact HW
  iapply (wp_mono
    (Φ := fun v => iprop(R ∗
      (|={E',⊤}=> ∃ t', ⤇ K'.fill t' ∗ refines E (K.fill v.1) t' A)))
    (Ψ := fun v => iprop(|={E', ⊤}=> wp ⊤ (K.fill (Exp.ofVal v)) (fun v₀ => iprop(∃ v' ε',
      (⤇ K'.fill v'.1) ∗ naOwnP ⊤ ∗ (↯ ε') ∗ (⌜(0 : ENNReal) < ε'⌝) ∗ A.car v₀ v')))))
  case HΦ =>
    intro v
    have hfill : Exp.ofVal v = v.1 := rfl
    rw [hfill]
    iintro ⟨⟨Hna', Herr', %Hpos'⟩, HFup⟩
    imod HFup with ⟨%t', HKt', HRef⟩
    imodintro
    ihave HRef' := refines_unfold $$ HRef
    iapply HRef' $$ %K' %ε HKt' Hna' Herr'
    ipureintro; exact Hpos'
  iexact HFrame

/-! ## Stateful reductions on the LHS -/

/-- `refines_alloc_l` (app_rel_rules.v:244).

**Port note**: Rocq's statement uses `▷` (since Rocq's `wp_alloc` puts the new-location
ownership under later). The Lean `wp_alloc` returns the fragment directly without `▷`,
so we drop the `▷` in the port. Callers who have `▷` in their context can use
`iNext`-style stripping earlier. -/
theorem refines_alloc_l {E : CoPset} {K : Ectx rT} {v : Val rT} {t : Exp rT} {A : lrel rT GF} :
    iprop(∀ (l : Loc), (l ↦ v) -∗ refines E (K.fill (.lit (.loc l))) t A)
      ⊢@{IProp GF} refines E (K.fill (.alloc v.1)) t A := by
  iintro Hlog
  iapply (refines_wp_l (K := K) (e1 := .alloc v.1))
  have halloc : (Exp.alloc v.1) = (Exp.alloc (Exp.ofVal v)) := rfl
  rw [halloc]
  iapply wp_alloc
  iintro %l Hl
  iapply Hlog $$ %l Hl

/-- `refines_load_l` (app_rel_rules.v:255).

**Port note**: `▷`s dropped (Lean convention, same rationale as `refines_alloc_l`). -/
theorem refines_load_l {E : CoPset} {K : Ectx rT} {l : Loc} {t : Exp rT} {A : lrel rT GF} :
    iprop(∃ v : Val rT, (l ↦ v) ∗ ((l ↦ v) -∗ refines E (K.fill v.1) t A))
      ⊢@{IProp GF} refines E (K.fill (.load (.lit (.loc l)))) t A := by
  iintro ⟨%v, Hl, Hlog⟩
  iapply (refines_wp_l (K := K) (e1 := .load (.lit (.loc l))))
  iapply (wp_load (v := v))
  isplitl [Hl]; · iexact Hl
  iintro Hl
  iapply Hlog $$ Hl

/-- `refines_store_l` (app_rel_rules.v:266).

**Port note**: `▷`s dropped (Lean convention, same rationale as `refines_alloc_l`). -/
theorem refines_store_l {E : CoPset} {K : Ectx rT} {l : Loc} {v' : Val rT} {t : Exp rT}
    {A : lrel rT GF} :
    iprop(∃ v : Val rT, (l ↦ v) ∗ ((l ↦ v') -∗ refines E (K.fill (.lit .unit)) t A))
      ⊢@{IProp GF} refines E (K.fill (.store (.lit (.loc l)) v'.1)) t A := by
  iintro ⟨%v, Hl, Hlog⟩
  iapply (refines_wp_l (K := K) (e1 := .store (.lit (.loc l)) v'.1))
  have hstore : Exp.store (.lit (.loc l)) v'.1 =
      Exp.store (.lit (.loc l)) (Exp.ofVal v') := rfl
  rw [hstore]
  -- `wp_store`'s `v` is the NEW value, `v'` is the OLD; swapped here.
  iapply (wp_store (v := v') (v' := v))
  isplitl [Hl]; · iexact Hl
  iintro Hl
  iapply Hlog $$ Hl

/-! ## Stateful reductions on the RHS -/

/-- `refines_alloc_r` (app_rel_rules.v:119). -/
theorem refines_alloc_r {E : CoPset} {K : Ectx rT} {v : Val rT} {t : Exp rT} {A : lrel rT GF} :
    iprop(∀ (l : Loc), (l ↦ₛ v) -∗
            refines E t (K.fill (.lit (.loc l))) A)
      ⊢@{IProp GF} refines E t (K.fill (.alloc v.1)) A := by
  iintro Hlog
  unfold refines
  iintro %K' %ε Hj Hna Herr Hpos
  have hfc : K'.fill (K.fill (Exp.alloc v.1)) =
      (K'.comp K).fill (Exp.alloc v.1) := Ectx.fill_comp K' K _
  ihave Hj' : iprop(⤇ (K'.comp K).fill (Exp.alloc v.1)) $$ [Hj]
  · rw [← hfc]; iexact Hj
  ihave HStep := step_alloc (E := ⊤) (K'.comp K) (v := v.1) v.2 $$ Hj'
  iapply specUpdate_wp
  iapply (specUpdate_bind (E1 := ⊤) (E2 := ⊤) Std.LawfulSet.subset_refl)
  isplitl [HStep]; · iexact HStep
  iintro ⟨%l, HKRes, Hl⟩
  have hfcL : K'.fill (K.fill (Exp.lit (.loc l))) =
      (K'.comp K).fill (Exp.lit (.loc l)) := Ectx.fill_comp K' K _
  ihave HKRes' : iprop(⤇ K'.fill (K.fill (.lit (.loc l)))) $$ [HKRes]
  · rw [hfcL]; iexact HKRes
  iapply specUpdate_ret
  have hv_eq : (⟨v.1, v.2⟩ : Val rT) = v := rfl
  ihave Hl' : iprop(l ↦ₛ v) $$ [Hl]
  · rw [← hv_eq]; iexact Hl
  ispecialize Hlog $$ %l Hl'
  iapply Hlog $$ %K' %ε HKRes' Hna Herr Hpos

/-- `refines_load_r` (app_rel_rules.v:132): RHS heap load.

Note Rocq's `refines_load_r` takes `l ↦ₛ{q} v` with fractional permission; we port with
full ownership for simplicity (most callers have full permission). -/
theorem refines_load_r {E : CoPset} {K : Ectx rT} {l : Loc} {v : Val rT} {t : Exp rT}
    {A : lrel rT GF} :
    iprop((l ↦ₛ v) ∗ ((l ↦ₛ v) -∗ refines E t (K.fill v.1) A))
      ⊢@{IProp GF} refines E t (K.fill (.load (.lit (.loc l)))) A := by
  iintro ⟨Hl, Hlog⟩
  unfold refines
  iintro %K' %ε Hj Hna Herr Hpos
  have hfc : K'.fill (K.fill (Exp.load (.lit (.loc l)))) =
      (K'.comp K).fill (Exp.load (.lit (.loc l))) := Ectx.fill_comp K' K _
  have hfcv : (K'.comp K).fill (Exp.ofVal v) = K'.fill (K.fill v.1) := (Ectx.fill_comp K' K _).symm
  ihave Hj' : iprop(⤇ (K'.comp K).fill (Exp.load (.lit (.loc l)))) $$ [Hj]
  · rw [← hfc]; iexact Hj
  ihave HStep := step_load (E := ⊤) (K'.comp K) (l := l) (v := v) $$ [Hj' Hl]
  · isplitl [Hj']; · iexact Hj'
    iexact Hl
  iapply specUpdate_wp
  iapply (specUpdate_bind (E1 := ⊤) (E2 := ⊤) Std.LawfulSet.subset_refl)
  isplitl [HStep]; · iexact HStep
  iintro ⟨HKRes, HlRes⟩
  ihave HKRes' : iprop(⤇ K'.fill (K.fill v.1)) $$ [HKRes]
  · rw [← hfcv]; iexact HKRes
  iapply specUpdate_ret
  ispecialize Hlog $$ HlRes
  iapply Hlog $$ %K' %ε HKRes' Hna Herr Hpos

/-- `refines_store_r` (app_rel_rules.v:144). -/
theorem refines_store_r {E : CoPset} {K : Ectx rT} {l : Loc} {v v' : Val rT} {e : Exp rT}
    {A : lrel rT GF} :
    iprop((l ↦ₛ v) ∗ ((l ↦ₛ v') -∗ refines E e (K.fill (.lit .unit)) A))
      ⊢@{IProp GF} refines E e (K.fill (.store (.lit (.loc l)) v'.1)) A := by
  iintro ⟨Hl, Hlog⟩
  unfold refines
  iintro %K' %ε Hj Hna Herr Hpos
  have hfc : K'.fill (K.fill (Exp.store (.lit (.loc l)) v'.1)) =
      (K'.comp K).fill (Exp.store (.lit (.loc l)) v'.1) := Ectx.fill_comp K' K _
  ihave Hj' : iprop(⤇ (K'.comp K).fill (Exp.store (.lit (.loc l)) v'.1)) $$ [Hj]
  · rw [← hfc]; iexact Hj
  ihave HStep := step_store (E := ⊤) (K'.comp K) (l := l) (v_old := v) (v_new := v')
    (e := v'.1) v'.2 (Exp.toVal?_ofVal v') $$ [Hj' Hl]
  · isplitl [Hj']; · iexact Hj'
    iexact Hl
  iapply specUpdate_wp
  iapply (specUpdate_bind (E1 := ⊤) (E2 := ⊤) Std.LawfulSet.subset_refl)
  isplitl [HStep]; · iexact HStep
  iintro ⟨HKRes, Hl'⟩
  have hfcU : K'.fill (K.fill (Exp.lit .unit)) =
      (K'.comp K).fill (Exp.lit .unit) := Ectx.fill_comp K' K _
  ihave HKRes' : iprop(⤇ K'.fill (K.fill (.lit .unit))) $$ [HKRes]
  · rw [hfcU]; iexact HKRes
  iapply specUpdate_ret
  ispecialize Hlog $$ Hl'
  iapply Hlog $$ %K' %ε HKRes' Hna Herr Hpos

/-! ## Rand directional rules

LHS-only and RHS-only stepping rules for `rand z ()` and `rand z (lbl α)`.
These mirror Rocq's `refines_randT{,_empty}_l/r` and `refines_randU_l/r`.
Pure-Iris compositions of `refines_wp_l`/spec-side `step_*` updates with
the `wp_rand{,_lbl}*` lemmas from `PrimitiveLaws.lean`. -/

/-- `refines_randU_l`: LHS unit-rand step. Concludes the LHS at any
`n ∈ [0, z)` chosen by the continuation. -/
theorem refines_randU_l {E : CoPset} {K : Ectx rT} {z : Int} {t : Exp rT} {A : lrel rT GF}
    (Hz : 0 < z) :
    iprop(∀ (n : Int), (⌜0 ≤ n ∧ n < z⌝) -∗
            refines E (K.fill (.lit (.int n))) t A)
      ⊢@{IProp GF} refines E (K.fill (.rand (.lit (.int z)) (.lit .unit))) t A := by
  iintro Hlog
  iapply (refines_wp_l (K := K) (e1 := .rand (.lit (.int z)) (.lit .unit)))
  iapply (wp_rand Hz)
  iintro %n %Hbnds
  iapply Hlog $$ %n
  ipureintro; exact Hbnds

/-- `refines_randT_l`: LHS tape-rand pop. Consumes the head `n` of tape `α`. -/
theorem refines_randT_l {E : CoPset} {K : Ectx rT} {l : Loc} {z n : Int}
    {ns : List Int} {t : Exp rT} {A : lrel rT GF} :
    iprop(appNatTape l z (n :: ns) ∗
            (appNatTape l z ns -∗ (⌜0 ≤ n ∧ n < z⌝) -∗
              refines E (K.fill (.lit (.int n))) t A))
      ⊢@{IProp GF} refines E (K.fill (.rand (.lit (.int z)) (.lit (.lbl l)))) t A := by
  iintro ⟨Hl, Hlog⟩
  iapply (refines_wp_l (K := K) (e1 := .rand (.lit (.int z)) (.lit (.lbl l))))
  iapply wp_rand_tape
  isplitl [Hl]; · iexact Hl
  iintro Hl' %Hbnds
  iapply Hlog $$ Hl'
  ipureintro; exact Hbnds

/-- `refines_randT_empty_l`: LHS rand on an empty tape — uniform sample, tape stays empty. -/
theorem refines_randT_empty_l {E : CoPset} {K : Ectx rT} {l : Loc} {z : Int}
    {t : Exp rT} {A : lrel rT GF} (Hz : 0 < z) :
    iprop(appNatTape l z [] ∗
            (∀ (n : Int), appNatTape l z [] -∗ (⌜0 ≤ n ∧ n < z⌝) -∗
              refines E (K.fill (.lit (.int n))) t A))
      ⊢@{IProp GF} refines E (K.fill (.rand (.lit (.int z)) (.lit (.lbl l)))) t A := by
  iintro ⟨Hl, Hlog⟩
  iapply (refines_wp_l (K := K) (e1 := .rand (.lit (.int z)) (.lit (.lbl l))))
  iapply (wp_rand_tape_empty Hz)
  isplitl [Hl]; · iexact Hl
  iintro %n Hl' %Hbnds
  iapply Hlog $$ %n Hl'
  ipureintro; exact Hbnds

/-- `refines_randU_r`: RHS unit-rand step. -/
theorem refines_randU_r {E : CoPset} {K : Ectx rT} {z : Int} {e : Exp rT} {A : lrel rT GF}
    (Hz : 0 < z) :
    iprop(∀ (n : Int), (⌜0 ≤ n ∧ n < z⌝) -∗
            refines E e (K.fill (.lit (.int n))) A)
      ⊢@{IProp GF} refines E e (K.fill (.rand (.lit (.int z)) (.lit .unit))) A := by
  iintro Hlog
  unfold refines
  iintro %K' %ε Hj Hna Herr Hpos
  have hfc : K'.fill (K.fill (Exp.rand (.lit (.int z)) (.lit .unit))) =
      (K'.comp K).fill (Exp.rand (.lit (.int z)) (.lit .unit)) := Ectx.fill_comp K' K _
  ihave Hj' : iprop(⤇ (K'.comp K).fill (.rand (.lit (.int z)) (.lit .unit))) $$ [Hj]
  · rw [← hfc]; iexact Hj
  iapply (wp_rand_r (K'.comp K) Hz)
  isplitl [Hj']; · iexact Hj'
  iintro %n %Hbnds HKRes
  have hfcN : (K'.comp K).fill (Exp.lit (.int n)) = K'.fill (K.fill (.lit (.int n))) :=
    (Ectx.fill_comp K' K _).symm
  ihave HKRes' : iprop(⤇ K'.fill (K.fill (.lit (.int n)))) $$ [HKRes]
  · rw [← hfcN]; iexact HKRes
  ispecialize Hlog $$ %n
  ihave Hpure : iprop((⌜0 ≤ n ∧ n < z⌝ : IProp GF)) $$ []
  · ipureintro; exact Hbnds
  ispecialize Hlog $$ Hpure
  ispecialize Hlog $$ %K' %ε
  ispecialize Hlog $$ HKRes'
  ispecialize Hlog $$ Hna
  ispecialize Hlog $$ Herr
  iapply Hlog
  iexact Hpos

/-- `refines_randT_r`: RHS tape-rand pop. The continuation receives the popped
value and the tail tape. -/
theorem refines_randT_r {E : CoPset} {K : Ectx rT} {l : Loc} {z : Int}
    {n : Int} {ns : List Int} {e : Exp rT} {A : lrel rT GF} :
    iprop(specNatTape l z (n :: ns) ∗
            (specNatTape l z ns -∗ (⌜0 ≤ n ∧ n < z⌝) -∗
              refines E e (K.fill (.lit (.int n))) A))
      ⊢@{IProp GF} refines E e (K.fill (.rand (.lit (.int z)) (.lit (.lbl l)))) A := by
  iintro ⟨Hα, Hlog⟩
  unfold refines
  iintro %K' %ε Hj Hna Herr Hpos
  have hfc : K'.fill (K.fill (Exp.rand (.lit (.int z)) (.lit (.lbl l)))) =
      (K'.comp K).fill (Exp.rand (.lit (.int z)) (.lit (.lbl l))) := Ectx.fill_comp K' K _
  ihave Hjc : iprop(⤇ (K'.comp K).fill (Exp.rand (.lit (.int z)) (.lit (.lbl l)))) $$ [Hj]
  · rw [← hfc]; iexact Hj
  ihave HαEx := show specNatTape l z (n :: ns) ⊢@{IProp GF}
      iprop(∃ fs : List { z' : Int // 0 ≤ z' ∧ z' < z },
        (⌜fs.map (fun x => x.val) = (n :: ns)⌝) ∗ l ↪ₛ ⟨z, fs⟩) from
    BI.BIBase.Entails.rfl $$ Hα
  icases HαEx with ⟨%fs, %hmap, Hαb⟩
  cases fs with
  | nil => simp at hmap
  | cons w ws =>
    simp at hmap
    obtain ⟨hwn, hwsm⟩ := hmap
    ihave HStep := step_rand (E := ⊤) (K'.comp K) l w ws $$ [Hjc Hαb]
    · isplitl [Hjc]; · iexact Hjc
      iexact Hαb
    iapply specUpdate_wp
    iapply (specUpdate_bind (E1 := ⊤) (E2 := ⊤) Std.LawfulSet.subset_refl)
    isplitl [HStep]; · iexact HStep
    iintro ⟨HKRes, HαResNew⟩
    have hw_eq : w.val = n := hwn
    have hfcN : (K'.comp K).fill (Exp.lit (.int w.val)) =
        K'.fill (K.fill (.lit (.int w.val))) := (Ectx.fill_comp K' K _).symm
    ihave HKRes' : iprop(⤇ K'.fill (K.fill (.lit (.int n)))) $$ [HKRes]
    · rw [← hw_eq, ← hfcN]; iexact HKRes
    iapply specUpdate_ret
    ihave HαResNat : iprop(specNatTape l z ns) $$ [HαResNew]
    · unfold specNatTape
      iexists ws
      isplitr; · ipureintro; exact hwsm
      iexact HαResNew
    ispecialize Hlog $$ HαResNat
    ihave Hbnds : iprop((⌜0 ≤ n ∧ n < z⌝ : IProp GF)) $$ []
    · ipureintro; exact ⟨hw_eq ▸ w.2.1, hw_eq ▸ w.2.2⟩
    ispecialize Hlog $$ Hbnds
    ispecialize Hlog $$ %K' %ε
    ispecialize Hlog $$ HKRes'
    ispecialize Hlog $$ Hna
    ispecialize Hlog $$ Herr
    iapply Hlog
    iexact Hpos

/-- `refines_randT_empty_r`: RHS rand on an empty tape — uniform sample, tape empty. -/
theorem refines_randT_empty_r {E : CoPset} {K : Ectx rT} {l : Loc} {z : Int}
    {e : Exp rT} {A : lrel rT GF} (Hz : 0 < z) :
    iprop(specNatTape l z [] ∗
            (∀ (n : Int), specNatTape l z [] -∗ (⌜0 ≤ n ∧ n < z⌝) -∗
              refines E e (K.fill (.lit (.int n))) A))
      ⊢@{IProp GF} refines E e (K.fill (.rand (.lit (.int z)) (.lit (.lbl l)))) A := by
  iintro ⟨Hα, Hlog⟩
  unfold refines
  iintro %K' %ε Hj Hna Herr Hpos
  have hfc : K'.fill (K.fill (Exp.rand (.lit (.int z)) (.lit (.lbl l)))) =
      (K'.comp K).fill (Exp.rand (.lit (.int z)) (.lit (.lbl l))) := Ectx.fill_comp K' K _
  ihave Hjc : iprop(⤇ (K'.comp K).fill (.rand (.lit (.int z)) (.lit (.lbl l)))) $$ [Hj]
  · rw [← hfc]; iexact Hj
  iapply (wp_rand_tape_empty_r (K'.comp K) Hz)
  isplitl [Hjc]; · iexact Hjc
  isplitl [Hα]; · iexact Hα
  iintro %n HαNew HKRes %Hbnds
  have hfcN : (K'.comp K).fill (Exp.lit (.int n)) = K'.fill (K.fill (.lit (.int n))) :=
    (Ectx.fill_comp K' K _).symm
  ihave HKRes' : iprop(⤇ K'.fill (K.fill (.lit (.int n)))) $$ [HKRes]
  · rw [← hfcN]; iexact HKRes
  ispecialize Hlog $$ %n HαNew
  ihave Hbpure : iprop((⌜0 ≤ n ∧ n < z⌝ : IProp GF)) $$ []
  · ipureintro; exact Hbnds
  ispecialize Hlog $$ Hbpure
  ispecialize Hlog $$ %K' %ε
  ispecialize Hlog $$ HKRes'
  ispecialize Hlog $$ Hna
  ispecialize Hlog $$ Herr
  iapply Hlog
  iexact Hpos

/-- `refines_alloctape_l`: LHS tape allocation. -/
theorem refines_alloctape_l {E : CoPset} {K : Ectx rT} {z : Int} {t : Exp rT} {A : lrel rT GF} :
    iprop(∀ (l : Loc), appTapesFrag l (Tape.empty z) -∗
            refines E (K.fill (.lit (.lbl l))) t A)
      ⊢@{IProp GF} refines E (K.fill (.tape (.lit (.int z)))) t A := by
  iintro Hlog
  iapply (refines_wp_l (K := K) (e1 := .tape (.lit (.int z))))
  iapply wp_alloctape
  iintro %l Hl
  iapply Hlog $$ %l Hl

/-- `refines_alloctape_r`: RHS tape allocation. The fresh location's spec tape
fragment is delivered via the continuation. -/
theorem refines_alloctape_r {E : CoPset} {K : Ectx rT} {z : Int} {e : Exp rT} {A : lrel rT GF} :
    iprop(∀ (l : Loc), specNatTape l z [] -∗
            refines E e (K.fill (.lit (.lbl l))) A)
      ⊢@{IProp GF} refines E e (K.fill (.tape (.lit (.int z)))) A := by
  iintro Hlog
  unfold refines
  iintro %K' %ε Hj Hna Herr Hpos
  have hfc : K'.fill (K.fill (Exp.tape (.lit (.int z)))) =
      (K'.comp K).fill (Exp.tape (.lit (.int z))) := Ectx.fill_comp K' K _
  ihave Hjc : iprop(⤇ (K'.comp K).fill (Exp.tape (.lit (.int z)))) $$ [Hj]
  · rw [← hfc]; iexact Hj
  iapply (wp_alloc_tape_r (K'.comp K))
  isplitl [Hjc]; · iexact Hjc
  iintro %l HKRes Hl
  have hfcL : (K'.comp K).fill (Exp.lit (.lbl l)) = K'.fill (K.fill (.lit (.lbl l))) :=
    (Ectx.fill_comp K' K _).symm
  ihave HKRes' : iprop(⤇ K'.fill (K.fill (.lit (.lbl l)))) $$ [HKRes]
  · rw [← hfcL]; iexact HKRes
  ispecialize Hlog $$ %l Hl
  ispecialize Hlog $$ %K' %ε
  ispecialize Hlog $$ HKRes'
  ispecialize Hlog $$ Hna
  ispecialize Hlog $$ Herr
  iapply Hlog
  iexact Hpos

/-! ## Structural rules -/

/-- `refines_wand` (app_rel_rules.v:330): weakening the result relation. -/
theorem refines_wand {E : CoPset} {e1 e2 : Exp rT} {A A' : lrel rT GF} :
    iprop(refines E e1 e2 A) ⊢@{IProp GF}
      iprop((∀ (v1 v2 : Val rT), A v1 v2 ={⊤}=∗ A' v1 v2) -∗ refines E e1 e2 A') := by
  iintro He HAA
  have Hfill1 : e1 = Ectx.empty.fill e1 := rfl
  have Hfill2 : e2 = Ectx.empty.fill e2 := rfl
  rw [Hfill1, Hfill2]
  iapply (refines_bind (K := Ectx.empty) (K' := Ectx.empty)
    (A := A) (A' := A') (E := E) (e := e1) (e' := e2)) $$ [He]
  · rw [← Hfill1, ← Hfill2]; iexact He
  iintro %v %v' HA
  ihave HAA' := HAA $$ %v %v'
  have Hfillv1 : v.1 = Ectx.empty.fill v.1 := rfl
  have Hfillv2 : v'.1 = Ectx.empty.fill v'.1 := rfl
  rw [← Hfillv1, ← Hfillv2]
  iapply refines_ret (v1 := v) (v2 := v') (hv1 := rfl) (hv2 := rfl)
  iapply HAA' $$ HA

/-- `refines_arrow_val` (app_rel_rules.v:228). Requires the closedness
witness for `v, v'` (port-specific: `lrel_arr` carries closedness as a
conjunct because Lean's `Val` isn't intrinsically closed). -/
theorem refines_arrow_val {v v' : Val rT} {A A' : lrel rT GF}
    (hv : v.1.isClosedEmpty ∧ v'.1.isClosedEmpty) :
    iprop(□ (∀ (v1 v2 : Val rT), A v1 v2 -∗
            refines ⊤ (.app v.1 v1.1) (.app v'.1 v2.1) A'))
      ⊢@{IProp GF} refines (⊤ : CoPset) v.1 v'.1 (lrel_arr A A') := by
  iintro #H
  iapply refines_ret (v1 := v) (v2 := v') (hv1 := rfl) (hv2 := rfl)
  imodintro
  unfold lrel_arr
  isplitr
  · ipureintro; exact hv
  iintro !> %w1 %w2 HA
  iapply H $$ %w1 %w2 HA

/-- `refines_arrow` (app_rel_rules.v:341): function refinement built from value
refinement of argument. Reduces to `refines_arrow_val` via `refines_ret`
injection of `A v1 v2` into `□ REL v1 << v2 : A`. Requires closedness of
`v, v'` (port-specific: lrel_arr carries a closedness conjunct). -/
theorem refines_arrow {v v' : Val rT} {A A' : lrel rT GF}
    (hv : v.1.isClosedEmpty ∧ v'.1.isClosedEmpty) :
    iprop(□ (∀ (v1 v2 : Val rT),
            □ refines (⊤ : CoPset) v1.1 v2.1 A -∗
            refines ⊤ (.app v.1 v1.1) (.app v'.1 v2.1) A'))
      ⊢@{IProp GF} refines (⊤ : CoPset) v.1 v'.1 (lrel_arr A A') := by
  iintro #H
  iapply (refines_arrow_val (hv := hv))
  iintro !> %v1 %v2 #HA
  iapply H $$ %v1 %v2
  iintro !>
  iapply refines_ret (v1 := v1) (v2 := v2) (hv1 := rfl) (hv2 := rfl)
  imodintro
  iexact HA

/-! ## Error-credit rules -/

/-- `refines_get_ec` (app_rel_rules.v): introduces an error-credit `↯ε` into
the precondition. The user provides a refinement parametric in any positive ε,
having access to `↯ε`. -/
theorem refines_get_ec {E : CoPset} {e e' : Exp rT} {A : lrel rT GF} :
    iprop(∀ (ε : ENNReal), (↯ε) -∗ (⌜0 < ε⌝) -∗ refines E e e' A)
      ⊢@{IProp GF} refines E e e' A := by
  iintro Hcnt
  unfold refines
  iintro %K %ε Hj Hna HerrTot %HposTot
  have hsplit : ε = ε / 2 + ε / 2 := (ENNReal.add_halves _).symm
  ihave HerrEq : iprop(↯ (ε / 2 + ε / 2)) $$ [HerrTot]
  · rw [← hsplit]; iexact HerrTot
  ihave HerrSp : iprop((↯ (ε / 2)) ∗ (↯ (ε / 2))) $$ [HerrEq]
  · iapply ErrorCredit.split $$ HerrEq
  icases HerrSp with ⟨Herr1, Herr2⟩
  have hpos2 : (0 : ENNReal) < ε / 2 :=
    ENNReal.div_pos_iff.mpr ⟨ne_of_gt HposTot, by simp⟩
  ihave Hpos2I : iprop(⌜(0 : ENNReal) < ε / 2⌝) $$ []
  · ipureintro; exact hpos2
  ihave Hpos2I' : iprop(⌜(0 : ENNReal) < ε / 2⌝) $$ []
  · ipureintro; exact hpos2
  ihave HrefFolded := Hcnt $$ %(ε / 2) Herr1 Hpos2I
  iapply HrefFolded $$ %K %(ε / 2) Hj Hna Herr2 Hpos2I'


/-! ## Coupling-driven rule -/

/-- `refines_couple_rands_lr` (= `refines_couple_UU`, app_rel_rules.v:463):
couple two unlabeled rands via a bijection `f` on `[0, z)`. Uses
`wp_couple_rand_rand` from `CouplingRules.lean`.

**Port note**: `▷` dropped on the continuation (Lean convention; matches heap-op ports). -/
theorem refines_couple_rands_lr {E : CoPset} {K K' : Ectx rT} {A : lrel rT GF} {z : Int}
    (f : Int → Int)
    (hdom : ∀ n : Int, 0 ≤ n → n < z → 0 ≤ f n ∧ f n < z)
    (hbij : ∀ m : Int, 0 ≤ m → m < z → ∃! n : Int, (0 ≤ n ∧ n < z) ∧ f n = m)
    (Hz : 0 < z) :
    iprop(∀ (n : Int), (⌜0 ≤ n ∧ n < z⌝) -∗
            refines E (K.fill (.lit (.int n))) (K'.fill (.lit (.int (f n)))) A)
      ⊢@{IProp GF}
        refines E (K.fill (.rand (.lit (.int z)) (.lit .unit)))
          (K'.fill (.rand (.lit (.int z)) (.lit .unit))) A := by
  iintro Hcnt
  unfold refines
  iintro %K2 %ε Hj Hna Herr Hpos
  have hfc : K2.fill (K'.fill (Exp.rand (.lit (.int z)) (.lit .unit))) =
      (K2.comp K').fill (Exp.rand (.lit (.int z)) (.lit .unit)) := Ectx.fill_comp K2 K' _
  ihave Hj' : iprop(⤇ (K2.comp K').fill (Exp.rand (.lit (.int z)) (.lit .unit))) $$ [Hj]
  · rw [← hfc]; iexact Hj
  iapply wp_bind (K := K)
  iapply (wp_couple_rand_rand z f hdom hbij Hz (K2.comp K') ⊤
    (fun n => wp ⊤ (K.fill (Exp.ofVal n))
      (fun v => iprop(∃ v' ε',
        (⤇ K2.fill v'.1) ∗ naOwnP ⊤ ∗ (↯ ε') ∗ (⌜(0 : ENNReal) < ε'⌝) ∗ A.car v v'))))
  isplitl [Hj']; · iexact Hj'
  iintro %n %Hn HKres
  have hfcN : K2.fill (K'.fill (Exp.lit (.int (f n)))) =
      (K2.comp K').fill (Exp.lit (.int (f n))) := Ectx.fill_comp K2 K' _
  ihave HKres' : iprop(⤇ K2.fill (K'.fill (.lit (.int (f n))))) $$ [HKres]
  · rw [hfcN]; iexact HKres
  ispecialize Hcnt $$ %n
  ispecialize Hcnt $$ %Hn
  have hfillN : Exp.ofVal (⟨.lit (.int n), IsVal.lit⟩ : Val rT) =
      Exp.lit (.int n) := rfl
  rw [hfillN]
  iapply Hcnt $$ %K2 %ε HKres' Hna Herr Hpos

/-- `refines_couple_TU`: couple a LHS tape-rand (on empty tape α) with a RHS
unit-rand via bijection `f`. -/
theorem refines_couple_TU {E : CoPset} {K K' : Ectx rT} {A : lrel rT GF} {z : Int}
    (α : Loc) (f : Int → Int)
    (hdom : ∀ n : Int, 0 ≤ n → n < z → 0 ≤ f n ∧ f n < z)
    (hbij : ∀ m : Int, 0 ≤ m → m < z → ∃! n : Int, (0 ≤ n ∧ n < z) ∧ f n = m)
    (Hz : 0 < z) :
    iprop(▷ appNatTape α z [] ∗
        (∀ (n : Int), appNatTape α z [] -∗ (⌜0 ≤ n ∧ n < z⌝) -∗
            refines E (K.fill (.lit (.int n))) (K'.fill (.lit (.int (f n)))) A))
      ⊢@{IProp GF}
        refines E (K.fill (.rand (.lit (.int z)) (.lit (.lbl α))))
          (K'.fill (.rand (.lit (.int z)) (.lit .unit))) A := by
  iintro ⟨Hα, Hcnt⟩
  unfold refines
  iintro %K2 %ε Hj Hna Herr Hpos
  have hfc : K2.fill (K'.fill (Exp.rand (.lit (.int z)) (.lit .unit))) =
      (K2.comp K').fill (Exp.rand (.lit (.int z)) (.lit .unit)) := Ectx.fill_comp K2 K' _
  ihave Hj' : iprop(⤇ (K2.comp K').fill (Exp.rand (.lit (.int z)) (.lit .unit))) $$ [Hj]
  · rw [← hfc]; iexact Hj
  iapply wp_bind (K := K)
  iapply (wp_couple_tape_rand z f hdom hbij Hz (K2.comp K') ⊤ α
    (fun n => wp ⊤ (K.fill (Exp.ofVal n))
      (fun v => iprop(∃ v' ε',
        (⤇ K2.fill v'.1) ∗ naOwnP ⊤ ∗ (↯ ε') ∗ (⌜(0 : ENNReal) < ε'⌝) ∗ A.car v v'))))
  isplitl [Hα]; · iexact Hα
  isplitl [Hj']; · iexact Hj'
  iintro %n ⟨HαNew, HKres, %Hn⟩
  have hfcN : K2.fill (K'.fill (Exp.lit (.int (f n)))) =
      (K2.comp K').fill (Exp.lit (.int (f n))) := Ectx.fill_comp K2 K' _
  ihave HKres' : iprop(⤇ K2.fill (K'.fill (.lit (.int (f n))))) $$ [HKres]
  · rw [hfcN]; iexact HKres
  ispecialize Hcnt $$ %n HαNew
  ihave Hbnds : iprop((⌜0 ≤ n ∧ n < z⌝ : IProp GF)) $$ []
  · ipureintro; exact Hn
  ispecialize Hcnt $$ Hbnds
  have hfillN : Exp.ofVal (⟨.lit (.int n), IsVal.lit⟩ : Val rT) =
      Exp.lit (.int n) := rfl
  rw [hfillN]
  iapply Hcnt $$ %K2 %ε HKres' Hna Herr Hpos

/-- `refines_couple_UT`: symmetric — couple LHS unit-rand with RHS tape-rand on
empty tape α' via bijection `f`. -/
theorem refines_couple_UT {E : CoPset} {K K' : Ectx rT} {A : lrel rT GF} {z : Int}
    (α' : Loc) (f : Int → Int)
    (hdom : ∀ n : Int, 0 ≤ n → n < z → 0 ≤ f n ∧ f n < z)
    (hbij : ∀ m : Int, 0 ≤ m → m < z → ∃! n : Int, (0 ≤ n ∧ n < z) ∧ f n = m)
    (Hz : 0 < z) :
    iprop(▷ specNatTape α' z [] ∗
        (∀ (n : Int), specNatTape α' z [] -∗ (⌜0 ≤ n ∧ n < z⌝) -∗
            refines E (K.fill (.lit (.int n))) (K'.fill (.lit (.int (f n)))) A))
      ⊢@{IProp GF}
        refines E (K.fill (.rand (.lit (.int z)) (.lit .unit)))
          (K'.fill (.rand (.lit (.int z)) (.lit (.lbl α')))) A := by
  iintro ⟨Hα', Hcnt⟩
  unfold refines
  iintro %K2 %ε Hj Hna Herr Hpos
  have hfc : K2.fill (K'.fill (Exp.rand (.lit (.int z)) (.lit (.lbl α')))) =
      (K2.comp K').fill (Exp.rand (.lit (.int z)) (.lit (.lbl α'))) := Ectx.fill_comp K2 K' _
  ihave Hj' : iprop(⤇ (K2.comp K').fill (Exp.rand (.lit (.int z)) (.lit (.lbl α')))) $$ [Hj]
  · rw [← hfc]; iexact Hj
  iapply wp_bind (K := K)
  iapply (wp_couple_rand_tape z f hdom hbij Hz (K2.comp K') ⊤ α'
    (fun n => wp ⊤ (K.fill (Exp.ofVal n))
      (fun v => iprop(∃ v' ε',
        (⤇ K2.fill v'.1) ∗ naOwnP ⊤ ∗ (↯ ε') ∗ (⌜(0 : ENNReal) < ε'⌝) ∗ A.car v v'))))
  isplitl [Hα']; · iexact Hα'
  isplitl [Hj']; · iexact Hj'
  iintro %n ⟨Hα'New, HKres, %Hn⟩
  have hfcN : K2.fill (K'.fill (Exp.lit (.int (f n)))) =
      (K2.comp K').fill (Exp.lit (.int (f n))) := Ectx.fill_comp K2 K' _
  ihave HKres' : iprop(⤇ K2.fill (K'.fill (.lit (.int (f n))))) $$ [HKres]
  · rw [hfcN]; iexact HKres
  ispecialize Hcnt $$ %n Hα'New
  ihave Hbnds : iprop((⌜0 ≤ n ∧ n < z⌝ : IProp GF)) $$ []
  · ipureintro; exact Hn
  ispecialize Hcnt $$ Hbnds
  have hfillN : Exp.ofVal (⟨.lit (.int n), IsVal.lit⟩ : Val rT) =
      Exp.lit (.int n) := rfl
  rw [hfillN]
  iapply Hcnt $$ %K2 %ε HKres' Hna Herr Hpos

/-- `refines_couple_TT`: couple two empty tapes via a bijection. Uses the
existing `wp_couple_rand_lbl_rand_lbl`. -/
theorem refines_couple_TT {E : CoPset} {K K' : Ectx rT} {A : lrel rT GF} {z : Int}
    (α α' : Loc) (f : Int → Int)
    (hdom : ∀ n : Int, 0 ≤ n → n < z → 0 ≤ f n ∧ f n < z)
    (hbij : ∀ m : Int, 0 ≤ m → m < z → ∃! n : Int, (0 ≤ n ∧ n < z) ∧ f n = m)
    (Hz : 0 < z) :
    iprop(▷ appNatTape α z [] ∗ ▷ specNatTape α' z [] ∗
        (∀ (n : Int), appNatTape α z [] -∗ specNatTape α' z [] -∗ (⌜0 ≤ n ∧ n < z⌝) -∗
            refines E (K.fill (.lit (.int n))) (K'.fill (.lit (.int (f n)))) A))
      ⊢@{IProp GF}
        refines E (K.fill (.rand (.lit (.int z)) (.lit (.lbl α))))
          (K'.fill (.rand (.lit (.int z)) (.lit (.lbl α')))) A := by
  iintro ⟨Hα, Hα', Hcnt⟩
  unfold refines
  iintro %K2 %ε Hj Hna Herr Hpos
  have hfc : K2.fill (K'.fill (Exp.rand (.lit (.int z)) (.lit (.lbl α')))) =
      (K2.comp K').fill (Exp.rand (.lit (.int z)) (.lit (.lbl α'))) := Ectx.fill_comp K2 K' _
  ihave Hj' : iprop(⤇ (K2.comp K').fill (Exp.rand (.lit (.int z)) (.lit (.lbl α')))) $$ [Hj]
  · rw [← hfc]; iexact Hj
  iapply wp_bind (K := K)
  iapply (wp_couple_rand_lbl_rand_lbl z f hdom hbij Hz (K2.comp K') ⊤ α α'
    (fun n => wp ⊤ (K.fill (Exp.ofVal n))
      (fun v => iprop(∃ v' ε',
        (⤇ K2.fill v'.1) ∗ naOwnP ⊤ ∗ (↯ ε') ∗ (⌜(0 : ENNReal) < ε'⌝) ∗ A.car v v'))))
  isplitl [Hα]; · iexact Hα
  isplitl [Hα']; · iexact Hα'
  isplitl [Hj']; · iexact Hj'
  iintro %n ⟨HαNew, Hα'New, HKres, %Hn⟩
  have hfcN : K2.fill (K'.fill (Exp.lit (.int (f n)))) =
      (K2.comp K').fill (Exp.lit (.int (f n))) := Ectx.fill_comp K2 K' _
  ihave HKres' : iprop(⤇ K2.fill (K'.fill (.lit (.int (f n))))) $$ [HKres]
  · rw [hfcN]; iexact HKres
  ispecialize Hcnt $$ %n HαNew Hα'New
  ihave Hbnds : iprop((⌜0 ≤ n ∧ n < z⌝ : IProp GF)) $$ []
  · ipureintro; exact Hn
  ispecialize Hcnt $$ Hbnds
  have hfillN : Exp.ofVal (⟨.lit (.int n), IsVal.lit⟩ : Val rT) =
      Exp.lit (.int n) := rfl
  rw [hfillN]
  iapply Hcnt $$ %K2 %ε HKres' Hna Herr Hpos

end AppRelRules

end ProbLang
