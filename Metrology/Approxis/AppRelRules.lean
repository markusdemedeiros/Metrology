import Metrology.Approxis.EctxLifting
import Metrology.Approxis.AppWeakestpre
import Metrology.Approxis.Model
import Metrology.Approxis.Proofmode
import Metrology.Approxis.PrimitiveLaws
import Metrology.Approxis.CouplingRules

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

/-- `refines_pure_l` (app_rel_rules.v:27): if `e` pure-steps to `e'` in `n` steps,
`▷^n (REL K[e'] << t : A) ⊢ REL K[e] << t : A`.

**Port note**: Rocq's 3-line proof `wp_pures; iApply "IH" with "..."` relies on
`wp_pures`'s implicit `▷^n` stripping. The Lean analogue is `wp_pure_step_later`,
which gives us `Nat.repeat (▷·) n (wp ⊤ (K.fill e') Φ) ⊢ wp ⊤ (K.fill e) Φ`.

The proof requires threading spatial hyps (HK, Hna, Herr, Hpos) under a `laterN n`
layer. Inside iris proofmode, `iintro !>` strips ▷ from goal but only from
hypotheses flagged as timeless; our spatial hyps aren't. A direct `laterN`-distribution
proof (using `laterN_forall`, `laterN_wand`, `laterN_intro`) runs into the usual
defeq issues between `Nat.repeat (▷·)` and `laterN`. Left as a sorry. -/
theorem refines_pure_l {E : CoPset} {K : Ectx} {e e' t : Exp} {A : lrel GF}
    {φ : Prop} {n : ℕ} [Hex : PureExec φ n e e'] (Hφ : φ) :
    Nat.repeat (fun Q : IProp GF => iprop(▷ Q)) n (refines E (K.fill e') t A)
      ⊢@{IProp GF} refines E (K.fill e) t A := by
  sorry

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
continuation to allow spec-side steps + invariant opening. -/
theorem refines_atomic_l {E : CoPset} {K : Ectx} {e1 t : Exp} {A : lrel GF} :
    iprop(∀ (K' : Ectx),
            (⤇ (K'.fill t)) -∗
            wp ⊤ e1 (fun v => iprop(∃ (t' : Exp),
              (⤇ (K'.fill t')) ∗ refines E (K.fill v.1) t' A)))
      ⊢@{IProp GF} refines E (K.fill e1) t A := by
  sorry

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

/-- `refines_arrow_val` (app_rel_rules.v:228). -/
theorem refines_arrow_val {v v' : Val} {A A' : lrel GF} :
    iprop(□ (∀ (v1 v2 : Val), A v1 v2 -∗
            refines ⊤ (.app v.1 v1.1) (.app v'.1 v2.1) A'))
      ⊢@{IProp GF} refines (⊤ : CoPset) v.1 v'.1 (lrel_arr A A') := by
  iintro #H
  iapply refines_ret (v1 := v) (v2 := v') (hv1 := rfl) (hv2 := rfl)
  imodintro
  unfold lrel_arr
  iintro !> %w1 %w2 HA
  iapply H $$ %w1 %w2 HA

/-- `refines_arrow` (app_rel_rules.v:341): function refinement built from value
refinement of argument. Reduces to `refines_arrow_val` via `refines_ret`
injection of `A v1 v2` into `□ REL v1 << v2 : A`. -/
theorem refines_arrow {v v' : Val} {A A' : lrel GF} :
    iprop(□ (∀ (v1 v2 : Val),
            □ refines (⊤ : CoPset) v1.1 v2.1 A -∗
            refines ⊤ (.app v.1 v1.1) (.app v'.1 v2.1) A'))
      ⊢@{IProp GF} refines (⊤ : CoPset) v.1 v'.1 (lrel_arr A A') := by
  iintro #H
  iapply refines_arrow_val
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

end AppRelRules

end ProbLang
