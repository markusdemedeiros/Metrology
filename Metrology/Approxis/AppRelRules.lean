import Metrology.Approxis.EctxLifting
import Metrology.Approxis.AppWeakestpre
import Metrology.Approxis.Model
import Metrology.Approxis.Proofmode
import Metrology.Approxis.PrimitiveLaws
import Metrology.Approxis.CouplingRules
import Metrology.Approxis.OpenInv

/-!
# Relational Rules

Port of `clutch/theories/approxis/app_rel_rules.v`, narrowed to the lemmas
used by `Compatibility.lean` and downstream (Fundamental, Soundness).

## Scope (2026-04-24)

The full Rocq file has ~30 lemmas. This port covers the ~10 directly used by
`compatibility.v`:

| Lemma | Used by | Rocq line |
|---|---|---|
| `refines_pure_l`, `refines_pure_r` | pure-step compatibility | 27, 73 |
| `refines_wp_l` | LHS-step compatibility (load/store/rand) | 41 |
| `refines_atomic_l` | heap-op compatibility (store/load under invariant) | 54 |
| `refines_alloc_l`, `refines_load_l`, `refines_store_l` | heap ops | 244, 255, 266 |
| `refines_alloc_r`, `refines_load_r`, `refines_store_r` | spec heap ops | 119, 132, 144 |
| `refines_wand` | general weakening | 330 |
| `refines_arrow_val`, `refines_arrow` | function-refinement compatibility | 228, 341 |
| `refines_couple_rands_lr` (= `refines_couple_UU`) | rand-unit compatibility | 463 |

All statements ported as `sorry`'d for now — establishes the API surface that
`Compatibility.lean` can target. Proofs deferred: each requires careful
threading of the `refines` spatial context through WP/specCoupl primitives.

Omitted from port: adversarial-error variants (`refines_couple_TT_err`, …),
`refines_couple_TT_{frag,adv}`, `refines_get_ec`, `refines_ind_amp`,
`refines_arrow_val_err`, fragmented couplings (`refines_couple_exp*`),
`refines_couple_UU_err`/`_rev`/`_avoid`, LHS tape rules
(`refines_alloctape_l`, `refines_rand{T,U}_l`, `refines_rand_empty_l`),
RHS tape rules (`refines_alloctape_r`, `refines_rand{T,U}_r`,
`refines_rand_empty_r`), `refines_step_r`, `refines_steps_r`.
These depend on coupling-rules variants also omitted in `CouplingRules.lean`.
-/

open Std Iris Iris.Std Iris.BI Iris.ProofMode OFE COFE ProbLang ProbLang.ApproxisWpGS
open scoped AppGS

namespace ProbLang

section AppRelRules
variable {hlc : Bool} {GF : BundledGFunctors} [IR : ApproxisRGS hlc GF]

/-! ## Forward reductions on the LHS -/

/-- Helper: `Nat.repeat (▷·) n P = laterN n P = ▷^[n] P` (defeq). -/
theorem nat_repeat_later_eq_laterN (n : Nat) (P : IProp GF) :
    Nat.repeat (fun Q : IProp GF => iprop(▷ Q)) n P = iprop(▷^[n] P) := by
  induction n with
  | zero => rfl
  | succ m ih => simp only [Nat.repeat]; rw [ih]; rfl

/-- `refines_pure_l` (app_rel_rules.v:27): if `e` pure-steps to `e'` in `n` steps,
`▷^n (REL K[e'] << t : A) ⊢ REL K[e] << t : A`. -/
theorem refines_pure_l {E : CoPset} {K : Ectx} {e e' t : Exp} {A : lrel GF}
    {φ : Prop} {n : ℕ} [Hex : PureExec φ n e e'] (Hφ : φ) :
    Nat.repeat (fun Q : IProp GF => iprop(▷ Q)) n (refines E (K.fill e') t A)
      ⊢@{IProp GF} refines E (K.fill e) t A := by
  have HexK : PureExec φ n (K.fill e) (K.fill e') := PureExec.fill K
  unfold refines
  iintro H
  iintro %K' %ε HK Hna Herr Hpos
  iapply (wp_pure_step_later (Hex := HexK) Hφ)
  -- Transform H from `Nat.repeat (▷·) n ...` to `▷^[n] ...` at the iprop level FIRST
  -- (before touching the goal, to preserve iris context).
  ihave H0 : iprop(▷^[n] (∀ (K₂ : Ectx) (ε₂ : ENNReal),
      (⤇ K₂.fill t) -∗ (naOwnP E) -∗ (↯ ε₂) -∗ (⌜(0 : ENNReal) < ε₂⌝) -∗
      wp ⊤ (K.fill e') (fun v => iprop(∃ v' ε',
        (⤇ K₂.fill v'.1) ∗ naOwnP ⊤ ∗ (↯ ε') ∗ (⌜(0 : ENNReal) < ε'⌝) ∗ A.car v v')))) $$ [H]
  · rw [← nat_repeat_later_eq_laterN]; iexact H
  -- Now rewrite the goal to match laterN form.
  rw [nat_repeat_later_eq_laterN]
  ihave H1 := (BI.laterN_forall n).mp $$ H0
  -- H1 : ∀ K', ▷^[n] (∀ ε, ...).
  ispecialize H1 $$ %K'
  -- H1 : ▷^[n] (∀ ε, ...).
  ihave H2 := (BI.laterN_forall n).mp $$ H1
  ispecialize H2 $$ %ε
  -- H2 : ▷^[n] (⤇ K'.fill t -∗ naOwnP E -∗ ↯ε -∗ ⌜0<ε⌝ -∗ wp ⊤ (K.fill e') Φ).
  -- Apply laterN_wand 4 times to distribute through each -∗.
  ihave H3 := BI.laterN_wand n $$ H2
  -- H3 : ▷^[n] (⤇ K'.fill t) -∗ ▷^[n] (naOwnP E -∗ ↯ε -∗ ⌜0<ε⌝ -∗ wp).
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
  -- H6 : ▷^[n] (wp ⊤ (K.fill e') Φ). Matches goal.
  iexact H6

/-- `refines_pure_r` (app_rel_rules.v:73): RHS pure step. -/
theorem refines_pure_r {E : CoPset} {K : Ectx} {e e' t : Exp} {A : lrel GF}
    {φ : Prop} {n : ℕ} [Hex : PureExec φ n e e'] (Hφ : φ) :
    refines E t (K.fill e') A ⊢@{IProp GF} refines E t (K.fill e) A := by
  unfold refines
  iintro H
  iintro %K' %ε Hj Hna Herr Hpos
  have hfc : K'.fill (K.fill e) = (K'.comp K).fill e := Ectx.fill_comp K' K e
  have hfc' : K'.fill (K.fill e') = (K'.comp K).fill e' := Ectx.fill_comp K' K e'
  -- Rewrite goal to use the composed context shape.
  rw [hfc]
  -- Advance spec: ⤇ (K'.comp K).fill e → specUpdate ⊤ (⤇ (K'.comp K).fill e').
  ihave HStep := step_pure (E := ⊤) (K'.comp K) (Hex := Hex) Hφ $$ Hj
  iapply specUpdate_wp
  iapply (specUpdate_bind (E1 := ⊤) (E2 := ⊤) Std.LawfulSet.subset_refl)
  isplitl [HStep]; · iexact HStep
  iintro HK'
  -- HK' : ⤇ (K'.comp K).fill e'. Reshape via Ectx.fill_comp to ⤇ K'.fill (K.fill e').
  ihave HK'' : iprop(⤇ K'.fill (K.fill e')) $$ [HK']
  · rw [hfc']; iexact HK'
  iapply specUpdate_ret
  iapply H $$ %K' %ε HK'' Hna Herr Hpos

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
theorem refines_wp_l {E : CoPset} {K : Ectx} {e1 t : Exp} {A : lrel GF} :
    iprop(wp ⊤ e1 (fun v => refines E (K.fill v.1) t A))
      ⊢@{IProp GF} refines E (K.fill e1) t A := by
  -- Reshape goal's RHS: refines E (K.fill e1) t A = <unfolded body>.
  -- He's post stays as `refines E (K.fill v.1) t A` (folded).
  show iprop(wp ⊤ e1 (fun v => refines E (K.fill v.1) t A)) ⊢@{IProp GF}
    iprop(∀ (K' : Ectx) (ε : ENNReal),
      (⤇ (K'.fill t)) -∗
      (naOwnP E) -∗
      (↯ ε) -∗
      (⌜ (0 : ENNReal) < ε ⌝) -∗
      wp ⊤ (K.fill e1) (fun v => iprop(∃ (v' : Val) (ε' : ENNReal),
        (⤇ (K'.fill v'.1)) ∗ (naOwnP ⊤) ∗ (↯ ε') ∗ (⌜ (0 : ENNReal) < ε' ⌝) ∗ A v v')))
  iintro He %K' %ε HK Hna Herr Hpos
  iapply wp_bind (K := K)
  let R : IProp GF := iprop((⤇ K'.fill t) ∗ (naOwnP E) ∗ (↯ ε) ∗ (⌜(0 : ENNReal) < ε⌝))
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
    -- Unfold HRefv via the refines_unfold helper.
    ihave HRefv' := refines_unfold $$ HRefv
    iapply HRefv' $$ %K' %ε HK' Hna' Herr'
    ipure_intro; exact Hpos'
  iexact HFrame

/-- `refines_atomic_l` (app_rel_rules.v:54): atomic step on the LHS, opening the
continuation to allow spec-side steps + invariant opening.

Takes `OpenInv e1` (mirrors Rocq's `Atomic StronglyAtomic e1`) so that callers
can open invariants (mask-shift `⊤ → E'`) for the duration of the single step. -/
theorem refines_atomic_l {E E' : CoPset} {K : Ectx} {e1 t : Exp} {A : lrel GF}
    (Hopen : OpenInv e1) :
    iprop(∀ (K' : Ectx),
            (⤇ (K'.fill t)) -∗
            (|={⊤, E'}=> wp E' e1 (fun v => iprop(|={E', ⊤}=> ∃ (t' : Exp),
              (⤇ (K'.fill t')) ∗ refines E (K.fill v.1) t' A))))
      ⊢@{IProp GF} refines E (K.fill e1) t A := by
  show iprop(∀ (K' : Ectx),
            (⤇ (K'.fill t)) -∗
            (|={⊤, E'}=> wp E' e1 (fun v => iprop(|={E', ⊤}=> ∃ (t' : Exp),
              (⤇ (K'.fill t')) ∗ refines E (K.fill v.1) t' A)))) ⊢@{IProp GF}
    iprop(∀ (K' : Ectx) (ε : ENNReal),
      (⤇ (K'.fill t)) -∗
      (naOwnP E) -∗
      (↯ ε) -∗
      (⌜ (0 : ENNReal) < ε ⌝) -∗
      wp ⊤ (K.fill e1) (fun v => iprop(∃ (v' : Val) (ε' : ENNReal),
        (⤇ (K'.fill v'.1)) ∗ (naOwnP ⊤) ∗ (↯ ε') ∗ (⌜ (0 : ENNReal) < ε' ⌝) ∗ A v v')))
  iintro Hlog %K' %ε HK Hna Herr Hpos
  iapply wp_bind (K := K)
  -- Goal: wp ⊤ e1 (fun v => wp ⊤ (K.fill v.1) Φ).
  -- Apply wp_atomic Hopen: |={⊤,E'}=> wp E' e1 Ψ ⊢ wp ⊤ e1 Φ
  -- where Ψ v = |={E',⊤}=> Φ v.
  iapply (wp_atomic Hopen (E1 := ⊤) (E2 := E')
    (Φ := fun v => wp ⊤ (K.fill (Exp.ofVal v)) (fun v₀ => iprop(∃ v' ε',
      (⤇ K'.fill v'.1) ∗ naOwnP ⊤ ∗ (↯ ε') ∗ (⌜(0 : ENNReal) < ε'⌝) ∗ A.car v₀ v'))))
  -- Goal: |={⊤,E'}=> wp E' e1 (fun v => |={E',⊤}=> wp ⊤ (K.fill v.1) Φ).
  -- Specialize Hlog at K', feed HK to get the inner |={⊤,E'}=> wp E' e1 (...).
  ispecialize Hlog $$ %K' HK
  -- Hlog : |={⊤,E'}=> wp E' e1 (fun v => |={E',⊤}=> ∃ t', ⤇ K'.fill t' ∗ refines E (K.fill v.1) t' A)
  imod Hlog with HW
  imodintro
  -- Now thread (Hna, Herr, Hpos) into Hlog's wp via wp_frame_l + wp_mono.
  let R : IProp GF := iprop((naOwnP E) ∗ (↯ ε) ∗ (⌜(0 : ENNReal) < ε⌝))
  ihave HR : R $$ [Hna Herr Hpos]
  · isplitl [Hna]; · iassumption
    isplitl [Herr]; · iassumption
    iassumption
  -- Note: v.1 = Exp.ofVal v definitionally; iris doesn't reduce so we work
  -- with v.1 throughout this `have` and convert at wp_mono time.
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
    ipure_intro; exact Hpos'
  iexact HFrame

/-! ## Stateful reductions on the LHS -/

/-- `refines_alloc_l` (app_rel_rules.v:244).

**Port note**: Rocq's statement uses `▷` (since Rocq's `wp_alloc` puts the new-location
ownership under later). The Lean `wp_alloc` returns the fragment directly without `▷`,
so we drop the `▷` in the port. Callers who have `▷` in their context can use
`iNext`-style stripping earlier. -/
theorem refines_alloc_l {E : CoPset} {K : Ectx} {v : Val} {t : Exp} {A : lrel GF} :
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
theorem refines_load_l {E : CoPset} {K : Ectx} {l : Loc} {t : Exp} {A : lrel GF} :
    iprop(∃ v : Val, (l ↦ v) ∗ ((l ↦ v) -∗ refines E (K.fill v.1) t A))
      ⊢@{IProp GF} refines E (K.fill (.load (.lit (.loc l)))) t A := by
  iintro ⟨%v, Hl, Hlog⟩
  iapply (refines_wp_l (K := K) (e1 := .load (.lit (.loc l))))
  iapply (wp_load (v := v))
  isplitl [Hl]; · iexact Hl
  iintro Hl
  iapply Hlog $$ Hl

/-- `refines_store_l` (app_rel_rules.v:266).

**Port note**: `▷`s dropped (Lean convention, same rationale as `refines_alloc_l`). -/
theorem refines_store_l {E : CoPset} {K : Ectx} {l : Loc} {v' : Val} {t : Exp}
    {A : lrel GF} :
    iprop(∃ v : Val, (l ↦ v) ∗ ((l ↦ v') -∗ refines E (K.fill (.lit .unit)) t A))
      ⊢@{IProp GF} refines E (K.fill (.store (.lit (.loc l)) v'.1)) t A := by
  iintro ⟨%v, Hl, Hlog⟩
  iapply (refines_wp_l (K := K) (e1 := .store (.lit (.loc l)) v'.1))
  have hstore : Exp.store (.lit (.loc l)) v'.1 =
      Exp.store (.lit (.loc l)) (Exp.ofVal v') := rfl
  rw [hstore]
  -- wp_store arg names are confusing: `v` is the NEW value (being stored),
  -- `v'` is the OLD value (read via appHeapFrag l v'). Swap to match our spec.
  iapply (wp_store (v := v') (v' := v))
  isplitl [Hl]; · iexact Hl
  iintro Hl
  iapply Hlog $$ Hl

/-! ## Stateful reductions on the RHS -/

/-- `refines_alloc_r` (app_rel_rules.v:119). -/
theorem refines_alloc_r {E : CoPset} {K : Ectx} {v : Val} {t : Exp} {A : lrel GF} :
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
  -- step_alloc: ⤇ K.fill (alloc v) → specUpdate (∃ l, ⤇ K.fill #l ∗ l ↦ₛ v).
  ihave HStep := step_alloc (E := ⊤) (K'.comp K) (v := v.1) v.2 $$ Hj'
  iapply specUpdate_wp
  iapply (specUpdate_bind (E1 := ⊤) (E2 := ⊤) Std.LawfulSet.subset_refl)
  isplitl [HStep]; · iexact HStep
  iintro ⟨%l, HKRes, Hl⟩
  -- HKRes : ⤇ (K'.comp K).fill (.lit (.loc l)). Reshape.
  have hfcL : K'.fill (K.fill (Exp.lit (.loc l))) =
      (K'.comp K).fill (Exp.lit (.loc l)) := Ectx.fill_comp K' K _
  ihave HKRes' : iprop(⤇ K'.fill (K.fill (.lit (.loc l)))) $$ [HKRes]
  · rw [hfcL]; iexact HKRes
  iapply specUpdate_ret
  -- Hl has `l ↦ₛ ⟨v.1, v.2⟩`, Hlog wants `l ↦ₛ v`. Reshape at the iprop level.
  have hv_eq : (⟨v.1, v.2⟩ : Val) = v := rfl
  ihave Hl' : iprop(l ↦ₛ v) $$ [Hl]
  · rw [← hv_eq]; iexact Hl
  ispecialize Hlog $$ %l Hl'
  iapply Hlog $$ %K' %ε HKRes' Hna Herr Hpos

/-- `refines_load_r` (app_rel_rules.v:132): RHS heap load.

Note Rocq's `refines_load_r` takes `l ↦ₛ{q} v` with fractional permission; we port with
full ownership for simplicity (most callers have full permission). -/
theorem refines_load_r {E : CoPset} {K : Ectx} {l : Loc} {v : Val} {t : Exp}
    {A : lrel GF} :
    iprop((l ↦ₛ v) ∗ ((l ↦ₛ v) -∗ refines E t (K.fill v.1) A))
      ⊢@{IProp GF} refines E t (K.fill (.load (.lit (.loc l)))) A := by
  iintro ⟨Hl, Hlog⟩
  unfold refines
  iintro %K' %ε Hj Hna Herr Hpos
  -- Reshape Hj via iprop-level equality using Ectx.fill_comp.
  have hfc : K'.fill (K.fill (Exp.load (.lit (.loc l)))) =
      (K'.comp K).fill (Exp.load (.lit (.loc l))) := Ectx.fill_comp K' K _
  have hfcv : (K'.comp K).fill (Exp.ofVal v) = K'.fill (K.fill v.1) := (Ectx.fill_comp K' K _).symm
  ihave Hj' : iprop(⤇ (K'.comp K).fill (Exp.load (.lit (.loc l)))) $$ [Hj]
  · rw [← hfc]; iexact Hj
  -- step_load: ⤇ (K'.comp K).fill (load #l) ∗ l ↦ₛ v → specUpdate(⤇ ...(ofVal v) ∗ l ↦ₛ v).
  ihave HStep := step_load (E := ⊤) (K'.comp K) (l := l) (v := v) $$ [Hj' Hl]
  · isplitl [Hj']; · iexact Hj'
    iexact Hl
  iapply specUpdate_wp
  iapply (specUpdate_bind (E1 := ⊤) (E2 := ⊤) Std.LawfulSet.subset_refl)
  isplitl [HStep]; · iexact HStep
  iintro ⟨HKRes, HlRes⟩
  -- HKRes : ⤇ (K'.comp K).fill (Exp.ofVal v). Reshape to ⤇ K'.fill (K.fill v.1).
  -- Note: `Exp.ofVal v = v.1` definitionally.
  ihave HKRes' : iprop(⤇ K'.fill (K.fill v.1)) $$ [HKRes]
  · rw [← hfcv]; iexact HKRes
  iapply specUpdate_ret
  -- After ispecialize, Hlog is specialized via HlRes to refines E t (K.fill v.1) A.
  -- Apply with all 5 preconditions.
  ispecialize Hlog $$ HlRes
  iapply Hlog $$ %K' %ε HKRes' Hna Herr Hpos

/-- `refines_store_r` (app_rel_rules.v:144). -/
theorem refines_store_r {E : CoPset} {K : Ectx} {l : Loc} {v v' : Val} {e : Exp}
    {A : lrel GF} :
    iprop((l ↦ₛ v) ∗ ((l ↦ₛ v') -∗ refines E e (K.fill (.lit .unit)) A))
      ⊢@{IProp GF} refines E e (K.fill (.store (.lit (.loc l)) v'.1)) A := by
  iintro ⟨Hl, Hlog⟩
  unfold refines
  iintro %K' %ε Hj Hna Herr Hpos
  have hfc : K'.fill (K.fill (Exp.store (.lit (.loc l)) v'.1)) =
      (K'.comp K).fill (Exp.store (.lit (.loc l)) v'.1) := Ectx.fill_comp K' K _
  ihave Hj' : iprop(⤇ (K'.comp K).fill (Exp.store (.lit (.loc l)) v'.1)) $$ [Hj]
  · rw [← hfc]; iexact Hj
  -- step_store : ⤇ ... (store #l e) ∗ l ↦ₛ v_old → specUpdate (⤇ ... () ∗ l ↦ₛ v_new).
  ihave HStep := step_store (E := ⊤) (K'.comp K) (l := l) (v_old := v) (v_new := v')
    (e := v'.1) v'.2 (Exp.toVal?_ofVal v') $$ [Hj' Hl]
  · isplitl [Hj']; · iexact Hj'
    iexact Hl
  iapply specUpdate_wp
  iapply (specUpdate_bind (E1 := ⊤) (E2 := ⊤) Std.LawfulSet.subset_refl)
  isplitl [HStep]; · iexact HStep
  iintro ⟨HKRes, Hl'⟩
  -- HKRes : ⤇ (K'.comp K).fill (.lit .unit). Reshape.
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
theorem refines_randU_l {E : CoPset} {K : Ectx} {z : Int} {t : Exp} {A : lrel GF}
    (Hz : 0 < z) :
    iprop(∀ (n : Int), (⌜0 ≤ n ∧ n < z⌝) -∗
            refines E (K.fill (.lit (.int n))) t A)
      ⊢@{IProp GF} refines E (K.fill (.rand (.lit (.int z)) (.lit .unit))) t A := by
  iintro Hlog
  iapply (refines_wp_l (K := K) (e1 := .rand (.lit (.int z)) (.lit .unit)))
  iapply (wp_rand Hz)
  iintro %n %Hbnds
  iapply Hlog $$ %n
  ipure_intro; exact Hbnds

/-- `refines_randT_l`: LHS tape-rand pop. Consumes the head `n` of tape `α`. -/
theorem refines_randT_l {E : CoPset} {K : Ectx} {l : Loc} {z n : Int}
    {ns : List Int} {t : Exp} {A : lrel GF} :
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
  ipure_intro; exact Hbnds

/-- `refines_randT_empty_l`: LHS rand on an empty tape — uniform sample, tape stays empty. -/
theorem refines_randT_empty_l {E : CoPset} {K : Ectx} {l : Loc} {z : Int}
    {t : Exp} {A : lrel GF} (Hz : 0 < z) :
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
  ipure_intro; exact Hbnds

/-- `refines_randU_r`: RHS unit-rand step. -/
theorem refines_randU_r {E : CoPset} {K : Ectx} {z : Int} {e : Exp} {A : lrel GF}
    (Hz : 0 < z) :
    iprop(∀ (n : Int), (⌜0 ≤ n ∧ n < z⌝) -∗
            refines E e (K.fill (.lit (.int n))) A)
      ⊢@{IProp GF} refines E e (K.fill (.rand (.lit (.int z)) (.lit .unit))) A := by
  -- Pattern: build via wp_rand_nonpos isn't applicable (Hz : 0 < z); use wp_rand_r.
  -- In refines unfolded form we get `wp ⊤ e ...` as the goal; we need to step the
  -- SPEC side, which `wp_rand_r` does (inside the wp).
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
  -- Now goal is `wp ⊤ e Φ` where Φ is the original post.
  -- We need to use Hlog to fold back into refines, then unfold to get the wp.
  -- Specialize Hlog at n with the bounds proof.
  ispecialize Hlog $$ %n
  ihave Hpure : iprop((⌜0 ≤ n ∧ n < z⌝ : IProp GF)) $$ []
  · ipure_intro; exact Hbnds
  ispecialize Hlog $$ Hpure
  -- Hlog : refines E e (K.fill #n) A. Apply at K', ε via refines's def body.
  -- Since refines is defined as ∀ K ε, ... -∗ wp ..., we can directly specialize.
  ispecialize Hlog $$ %K' %ε
  ispecialize Hlog $$ HKRes'
  ispecialize Hlog $$ Hna
  ispecialize Hlog $$ Herr
  iapply Hlog
  iexact Hpos

/-- `refines_randT_r`: RHS tape-rand pop. The continuation receives the popped
value and the tail tape. -/
theorem refines_randT_r {E : CoPset} {K : Ectx} {l : Loc} {z : Int}
    {n : Int} {ns : List Int} {e : Exp} {A : lrel GF} :
    iprop(specNatTape l z (n :: ns) ∗
            (specNatTape l z ns -∗ (⌜0 ≤ n ∧ n < z⌝) -∗
              refines E e (K.fill (.lit (.int n))) A))
      ⊢@{IProp GF} refines E e (K.fill (.rand (.lit (.int z)) (.lit (.lbl l)))) A := by
  iintro ⟨Hα, Hlog⟩
  unfold refines
  iintro %K' %ε Hj Hna Herr Hpos
  -- Reshape Hj to (K'.comp K)-form.
  have hfc : K'.fill (K.fill (Exp.rand (.lit (.int z)) (.lit (.lbl l)))) =
      (K'.comp K).fill (Exp.rand (.lit (.int z)) (.lit (.lbl l))) := Ectx.fill_comp K' K _
  ihave Hjc : iprop(⤇ (K'.comp K).fill (Exp.rand (.lit (.int z)) (.lit (.lbl l)))) $$ [Hj]
  · rw [← hfc]; iexact Hj
  -- Convert specNatTape to backend frag form.
  ihave HαEx := show specNatTape l z (n :: ns) ⊢@{IProp GF}
      iprop(∃ fs : List { z' : Int // 0 ≤ z' ∧ z' < z },
        (⌜fs.map (fun x => x.val) = (n :: ns)⌝) ∗ l ↪ₛ ⟨z, fs⟩) from
    BI.BIBase.Entails.rfl $$ Hα
  icases HαEx with ⟨%fs, %hmap, Hαb⟩
  -- fs.map = n :: ns, so fs = (some witness for n) :: rest. Extract head.
  cases fs with
  | nil => simp at hmap
  | cons w ws =>
    simp at hmap
    obtain ⟨hwn, hwsm⟩ := hmap
    -- hwn : w.val = n, hwsm : ws.map (·.val) = ns.
    -- Use step_rand to step the spec.
    ihave HStep := step_rand (E := ⊤) (K'.comp K) l w ws $$ [Hjc Hαb]
    · isplitl [Hjc]; · iexact Hjc
      iexact Hαb
    iapply specUpdate_wp
    iapply (specUpdate_bind (E1 := ⊤) (E2 := ⊤) Std.LawfulSet.subset_refl)
    isplitl [HStep]; · iexact HStep
    iintro ⟨HKRes, HαResNew⟩
    -- HKRes : ⤇ (K'.comp K).fill #w.val = ⤇ (K'.comp K).fill #n.
    have hw_eq : w.val = n := hwn
    -- Reshape HKRes back to K'.fill (K.fill #n).
    have hfcN : (K'.comp K).fill (Exp.lit (.int w.val)) =
        K'.fill (K.fill (.lit (.int w.val))) := (Ectx.fill_comp K' K _).symm
    ihave HKRes' : iprop(⤇ K'.fill (K.fill (.lit (.int n)))) $$ [HKRes]
    · rw [← hw_eq, ← hfcN]; iexact HKRes
    iapply specUpdate_ret
    -- HαResNew : l ↪ₛ ⟨z, ws⟩. Convert to specNatTape.
    ihave HαResNat : iprop(specNatTape l z ns) $$ [HαResNew]
    · unfold specNatTape
      iexists ws
      isplitr; · ipure_intro; exact hwsm
      iexact HαResNew
    -- Apply Hlog at HαResNat with bounds proof and HKRes'.
    ispecialize Hlog $$ HαResNat
    ihave Hbnds : iprop((⌜0 ≤ n ∧ n < z⌝ : IProp GF)) $$ []
    · ipure_intro; exact ⟨hw_eq ▸ w.2.1, hw_eq ▸ w.2.2⟩
    ispecialize Hlog $$ Hbnds
    ispecialize Hlog $$ %K' %ε
    ispecialize Hlog $$ HKRes'
    ispecialize Hlog $$ Hna
    ispecialize Hlog $$ Herr
    iapply Hlog
    iexact Hpos

/-- `refines_randT_empty_r`: RHS rand on an empty tape — uniform sample, tape empty. -/
theorem refines_randT_empty_r {E : CoPset} {K : Ectx} {l : Loc} {z : Int}
    {e : Exp} {A : lrel GF} (Hz : 0 < z) :
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
  · ipure_intro; exact Hbnds
  ispecialize Hlog $$ Hbpure
  ispecialize Hlog $$ %K' %ε
  ispecialize Hlog $$ HKRes'
  ispecialize Hlog $$ Hna
  ispecialize Hlog $$ Herr
  iapply Hlog
  iexact Hpos

/-- `refines_alloctape_l`: LHS tape allocation. -/
theorem refines_alloctape_l {E : CoPset} {K : Ectx} {z : Int} {t : Exp} {A : lrel GF} :
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
theorem refines_alloctape_r {E : CoPset} {K : Ectx} {z : Int} {e : Exp} {A : lrel GF} :
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
theorem refines_wand {E : CoPset} {e1 e2 : Exp} {A A' : lrel GF} :
    iprop(refines E e1 e2 A) ⊢@{IProp GF}
      iprop((∀ (v1 v2 : Val), A v1 v2 ={⊤}=∗ A' v1 v2) -∗ refines E e1 e2 A') := by
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
theorem refines_arrow_val {v v' : Val} {A A' : lrel GF}
    (hv : v.1.isClosedEmpty ∧ v'.1.isClosedEmpty) :
    iprop(□ (∀ (v1 v2 : Val), A v1 v2 -∗
            refines ⊤ (.app v.1 v1.1) (.app v'.1 v2.1) A'))
      ⊢@{IProp GF} refines (⊤ : CoPset) v.1 v'.1 (lrel_arr A A') := by
  iintro #H
  iapply refines_ret (v1 := v) (v2 := v') (hv1 := rfl) (hv2 := rfl)
  imodintro
  unfold lrel_arr
  isplitr
  · ipure_intro; exact hv
  iintro !> %w1 %w2 HA
  iapply H $$ %w1 %w2 HA

/-- `refines_arrow` (app_rel_rules.v:341): function refinement built from value
refinement of argument. Reduces to `refines_arrow_val` via `refines_ret`
injection of `A v1 v2` into `□ REL v1 << v2 : A`. Requires closedness of
`v, v'` (port-specific: lrel_arr carries a closedness conjunct). -/
theorem refines_arrow {v v' : Val} {A A' : lrel GF}
    (hv : v.1.isClosedEmpty ∧ v'.1.isClosedEmpty) :
    iprop(□ (∀ (v1 v2 : Val),
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

/-! ## Coupling-driven rule -/

/-- `refines_couple_rands_lr` (= `refines_couple_UU`, app_rel_rules.v:463):
couple two unlabeled rands via a bijection `f` on `[0, z)`. Uses
`wp_couple_rand_rand` from `CouplingRules.lean`.

**Port note**: `▷` dropped on the continuation (Lean convention; matches heap-op ports). -/
theorem refines_couple_rands_lr {E : CoPset} {K K' : Ectx} {A : lrel GF} {z : Int}
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
  -- Reshape spec frag: ⤇ K2.fill (K'.fill (rand #z ())) = ⤇ (K2.comp K').fill (rand ...).
  have hfc : K2.fill (K'.fill (Exp.rand (.lit (.int z)) (.lit .unit))) =
      (K2.comp K').fill (Exp.rand (.lit (.int z)) (.lit .unit)) := Ectx.fill_comp K2 K' _
  ihave Hj' : iprop(⤇ (K2.comp K').fill (Exp.rand (.lit (.int z)) (.lit .unit))) $$ [Hj]
  · rw [← hfc]; iexact Hj
  -- Apply wp_bind to focus on the LHS rand inside K.
  iapply wp_bind (K := K)
  -- Apply wp_couple_rand_rand at the inner rand. Post: Φ n for n ∈ [0,z).
  -- The outer wp-bind then carries Φ through K.
  iapply (wp_couple_rand_rand z f hdom hbij Hz (K2.comp K') ⊤
    (fun n => wp ⊤ (K.fill (Exp.ofVal n))
      (fun v => iprop(∃ v' ε',
        (⤇ K2.fill v'.1) ∗ naOwnP ⊤ ∗ (↯ ε') ∗ (⌜(0 : ENNReal) < ε'⌝) ∗ A.car v v'))))
  isplitl [Hj']; · iexact Hj'
  iintro %n %Hn HKres
  -- HKres : ⤇ (K2.comp K').fill (.lit (.int (f n))). Reshape.
  have hfcN : K2.fill (K'.fill (Exp.lit (.int (f n)))) =
      (K2.comp K').fill (Exp.lit (.int (f n))) := Ectx.fill_comp K2 K' _
  ihave HKres' : iprop(⤇ K2.fill (K'.fill (.lit (.int (f n))))) $$ [HKres]
  · rw [hfcN]; iexact HKres
  -- Now specialize Hcnt at n; get refines E (K.fill #n) (K'.fill #(f n)) A.
  ispecialize Hcnt $$ %n
  ispecialize Hcnt $$ %Hn
  -- Hcnt : refines E (K.fill #n) (K'.fill #(f n)) A.
  -- Since ispecialize has already transformed Hcnt to its unfolded form, apply directly.
  -- Reshape K.fill (Exp.ofVal ⟨.lit (.int n), IsVal.lit⟩) = K.fill (.lit (.int n)).
  have hfillN : Exp.ofVal (⟨.lit (.int n), IsVal.lit⟩ : Val) =
      Exp.lit (.int n) := rfl
  rw [hfillN]
  iapply Hcnt $$ %K2 %ε HKres' Hna Herr Hpos

/-- `refines_couple_TU`: couple a LHS tape-rand (on empty tape α) with a RHS
unit-rand via bijection `f`. -/
theorem refines_couple_TU {E : CoPset} {K K' : Ectx} {A : lrel GF} {z : Int}
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
  · ipure_intro; exact Hn
  ispecialize Hcnt $$ Hbnds
  have hfillN : Exp.ofVal (⟨.lit (.int n), IsVal.lit⟩ : Val) =
      Exp.lit (.int n) := rfl
  rw [hfillN]
  iapply Hcnt $$ %K2 %ε HKres' Hna Herr Hpos

/-- `refines_couple_UT`: symmetric — couple LHS unit-rand with RHS tape-rand on
empty tape α' via bijection `f`. -/
theorem refines_couple_UT {E : CoPset} {K K' : Ectx} {A : lrel GF} {z : Int}
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
  · ipure_intro; exact Hn
  ispecialize Hcnt $$ Hbnds
  have hfillN : Exp.ofVal (⟨.lit (.int n), IsVal.lit⟩ : Val) =
      Exp.lit (.int n) := rfl
  rw [hfillN]
  iapply Hcnt $$ %K2 %ε HKres' Hna Herr Hpos

/-- `refines_couple_TT`: couple two empty tapes via a bijection. Uses the
existing `wp_couple_rand_lbl_rand_lbl`. -/
theorem refines_couple_TT {E : CoPset} {K K' : Ectx} {A : lrel GF} {z : Int}
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
  · ipure_intro; exact Hn
  ispecialize Hcnt $$ Hbnds
  have hfillN : Exp.ofVal (⟨.lit (.int n), IsVal.lit⟩ : Val) =
      Exp.lit (.int n) := rfl
  rw [hfillN]
  iapply Hcnt $$ %K2 %ε HKres' Hna Herr Hpos

end AppRelRules

end ProbLang
