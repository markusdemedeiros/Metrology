module

public import Metrology.Approxis.AppWeakestpre
import Metrology.ProbLang.Syntax.Notation
public import Metrology.Approxis.Model
public import Metrology.Approxis.PrimitiveLaws
public import Metrology.Approxis.CouplingRules
public import Metrology.Approxis.OpenInv

@[expose] public section


/-! # Relational Rules -/

open Std Iris Iris.Std Iris.BI Iris.ProofMode OFE COFE ProbLang ProbLang.ApproxisWpGS
open scoped AppGS

namespace ProbLang


variable {rT : Type _} [ProbLangℝ rT]

section AppRelRules
variable {hlc : HasLC} {GF : BundledGFunctors} [IR : ApproxisRGS rT hlc GF]
open ApproxisWpGS

/-! ## Forward reductions on the LHS -/

/-- If `e` pure-steps to `e'` in `n` steps, `▷^n (REL K[e'] << t : A) ⊢ REL K[e] << t : A`. -/
theorem refines_pure_l {E : CoPset} {K : Ectx rT} {e e' t : Exp rT} {A : lrel rT GF}
    {φ : Prop} {n : ℕ} [Hex : PureExec φ n e e'] (Hφ : φ) :
    iprop(▷^[n] refines E (K.fill e') t A) ⊢@{IProp GF} refines E (K.fill e) t A := by
  have HexK : PureExec φ n (K.fill e) (K.fill e') := PureExec.fill K
  iunfold refines
  iintro H %K' %ε HK Hna Herr Hpos
  iapply (ApproxisWpGS.wp_pure_step_later' (Hex := HexK) Hφ)
  inext
  iapply H $$ HK Hna Herr Hpos

/-- `refines_pure_r` (app_rel_rules.v:73): RHS pure step. -/
theorem refines_pure_r {E : CoPset} {K : Ectx rT} {e e' t : Exp rT} {A : lrel rT GF}
    {φ : Prop} {n : ℕ} [Hex : PureExec φ n e e'] (Hφ : φ) :
    refines E t (K.fill e') A ⊢@{IProp GF} refines E t (K.fill e) A := by
  iunfold refines
  iintro H %K' %ε Hj Hna Herr Hpos
  rw [Ectx.fill_comp]
  iapply specUpdate_wp
  iapply specUpdate_bind (E1 := ⊤) (E2 := ⊤) Std.LawfulSet.subset_refl
  ihave HStep := step_pure (K'.comp K) (Hex := Hex) Hφ $$ Hj
  iframe HStep
  iintro HK'
  iapply specUpdate_ret
  isimp only [← Ectx.fill_comp K' K e'] at HK'
  iapply H $$ %K' %ε HK' Hna Herr Hpos

/-- `refines_step_r` (app_rel_rules.v): single-step RHS spec helper. The user
provides, for any outer context `K''`, a `specUpdate` from `⤇ K''.fill e₂` to
`∃ v, ⤇ K''.fill v ∗ refines E e₁ (K'.fill v) A`. -/
theorem refines_step_r {E : CoPset} {K' : Ectx rT} {e1 e2 : Exp rT} {A : lrel rT GF} : iprop%
    (∀ (K : Ectx rT), (⤇ K.fill e2) -∗
      specUpdate rT ⊤ (∃ (v : Val rT), iprop((⤇ K.fill v.1) ∗ refines E e1 (K'.fill v.1) A)))
      ⊢@{IProp GF} refines E e1 (K'.fill e2) A := by
  iunfold refines
  iintro He %K'' %ε Hj Hna Herr Hpos
  iapply specUpdate_wp
  iapply specUpdate_bind Std.LawfulSet.subset_refl
  isimp only [Ectx.fill_comp K'' K' e2] at Hj
  ihave HStep := He $$ %(K''.comp K') Hj
  iframe HStep
  iintro ⟨%v, HK'', Hrefines⟩
  iapply specUpdate_ret
  isimp only [← Ectx.fill_comp K'' K' v.1] at HK''
  iapply Hrefines $$ %K'' %ε HK'' Hna Herr Hpos

/-- `refines_steps_r` (app_rel_rules.v): variant of `refines_step_r` where the
RHS reduct `e₂'` is known. Useful when the value isn't fresh. -/
theorem refines_steps_r {E : CoPset} {K' : Ectx rT} {e1 e2 e2' : Exp rT} {A : lrel rT GF} :
    iprop(∀ (K : Ectx rT), (⤇ K.fill e2) -∗ specUpdate rT ⊤ (⤇ K.fill e2'))
      ⊢@{IProp GF} (|={⊤}=> refines E e1 (K'.fill e2') A) -∗
        refines E e1 (K'.fill e2) A := by
  iunfold refines
  iintro Hupd Hlog
  iintro %K'' %ε Hj Hna Herr Hpos
  imod Hlog
  isimp only [Ectx.fill_comp K'' K'] at Hj
  ihave HStep := Hupd $$ %(K''.comp K') Hj
  iapply specUpdate_wp
  iapply (specUpdate_bind (E1 := ⊤) (E2 := ⊤) Std.LawfulSet.subset_refl)
  iframe HStep
  iintro HKres
  isimp only [← Ectx.fill_comp K'' K' e2'] at HKres
  iapply specUpdate_ret
  iapply Hlog $$ %K'' %ε HKres Hna Herr Hpos

/-- `refines_wp_l` (app_rel_rules.v:41): embed a `wp` into a `refines` on the LHS.

Rocq: `iIntros "He" (K' ε) "Hs Hnais Herr Hpos"; ApproxisWpGS.wp_bind; iApply (ApproxisWpGS.wp_wand
  with "He")`.
In Lean Iris, `ApproxisWpGS.wp_wand` requires a persistent wand, so we use
`ApproxisWpGS.wp_frame_l` to thread
the spatial context through.

**Port notes**: bare `unfold refines` unfolds EVERYWHERE, including the post of
`He`. `iunfold refines` (`ProofMode/Tactics/Eval.lean`) rewrites the proof-mode
*goal* only, so the strategy is: `iintro He` first, then `iunfold refines` to open
the `∀ K' ε, ... -∗ ...` body, then `iintro %K' %ε ...`. `He`'s post keeps its
folded `refines`. -/
theorem refines_wp_l {E : CoPset} {K : Ectx rT} {e1 t : Exp rT} {A : lrel rT GF} :
    iprop(wp ⊤ e1 (fun v => refines E (K.fill v.1) t A))
      ⊢@{IProp GF} refines E (K.fill e1) t A := by
  iintro He
  iunfold refines
  iintro %K' %ε HK Hna Herr Hpos
  iapply ApproxisWpGS.wp_bind (K := K)
  let R : IProp GF := iprop((⤇ K'.fill t) ∗ (naOwnP (rT := rT) (hlc := hlc) E) ∗ (↯ ε) ∗ (⌜(0 :
    ENNReal) < ε⌝))
  ihave HR : R $$ [HK Hna Herr Hpos]
  · isplitl [HK]; · iassumption
    iframe Hna Herr
    iassumption
  ihave HFrame : iprop(wp ⊤ e1 (fun v => iprop(R ∗ refines E (K.fill v.1) t A)))
      $$ [HR He]
  · iapply (ApproxisWpGS.wp_frame_l
      (Φ := fun v => refines E (K.fill v.1) t A))
    iframe HR
    iexact He
  iapply ApproxisWpGS.wp_mono $$ HFrame
  intro v
  rw [show Exp.ofVal v = v.1 from rfl]
  iintro ⟨⟨HK', Hna', Herr', %Hpos'⟩, HRefv⟩
  ihave HRefv' := refines_unfold $$ HRefv
  iapply HRefv' $$ %K' %ε HK' Hna' Herr' %Hpos'

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
  iintro Hlog
  iunfold refines
  iintro %K' %ε HK Hna Herr Hpos
  iapply ApproxisWpGS.wp_bind (K := K)
  iapply wp_atomic Hopen
  ispecialize Hlog $$ %K' HK
  imod Hlog with HW
  imodintro
  let R : IProp GF := iprop((naOwnP (rT := rT) (hlc := hlc) E) ∗ (↯ ε) ∗ (⌜(0 : ENNReal) < ε⌝))
  ihave HR : R $$ [Hna Herr Hpos]
  · isplitl [Hna]; · iassumption
    iframe Herr
    iassumption
  ihave HFrame : iprop(wp E' e1 (fun v => iprop(R ∗
      (|={E', ⊤}=> ∃ t', ⤇ K'.fill t' ∗ refines E (K.fill v.1) t' A))))
      $$ [HR HW]
  · iapply (ApproxisWpGS.wp_frame_l
      (Φ := fun v => iprop(|={E',⊤}=> ∃ t', ⤇ K'.fill t' ∗ refines E (K.fill v.1) t' A)))
    iframe HR
    iexact HW
  iapply ApproxisWpGS.wp_mono $$ HFrame
  intro v
  rw [show Exp.ofVal v = v.1 from rfl]
  iintro ⟨⟨Hna', Herr', %Hpos'⟩, HFup⟩
  imod HFup with ⟨%t', HKt', HRef⟩
  imodintro
  ihave HRef' := refines_unfold $$ HRef
  iapply HRef' $$ %K' %ε HKt' Hna' Herr' %Hpos'

/-! ## Stateful reductions on the LHS -/


/-- `refines_alloc_l` (app_rel_rules.v:244).

**Port note**: Rocq's statement uses `▷` (since Rocq's `wp_alloc` puts the new-location
ownership under later). The Lean `wp_alloc` returns the fragment directly without `▷`,
so we drop the `▷` in the port. Callers who have `▷` in their context can use
`iNext`-style stripping earlier. -/
theorem refines_alloc_l {E : CoPset} {K : Ectx rT} {v : Val rT} {t : Exp rT} {A : lrel rT GF} :
    iprop(∀ (l : Loc), (l ↦ v) -∗ refines E (K.fill pl(#(.loc l))) t A)
      ⊢@{IProp GF} refines E (K.fill (.alloc v.1)) t A := by
  iintro Hlog
  iapply refines_wp_l
  rw [show Exp.alloc v.1 = Exp.alloc (Exp.ofVal v) from rfl]
  iapply wp_alloc
  iintro %l Hl
  iapply Hlog $$ %l Hl

/-- `refines_load_l` (app_rel_rules.v:255).

**Port note**: `▷`s dropped (Lean convention, same rationale as `refines_alloc_l`). -/
theorem refines_load_l {E : CoPset} {K : Ectx rT} {l : Loc} {t : Exp rT} {A : lrel rT GF} :
    iprop(∃ v : Val rT, (l ↦ v) ∗ ((l ↦ v) -∗ refines E (K.fill v.1) t A))
      ⊢@{IProp GF} refines E (K.fill pl(!#(.loc l))) t A := by
  iintro ⟨%v, Hl, Hlog⟩
  iapply refines_wp_l
  iapply wp_load
  iframe Hl
  iintro Hl
  iapply Hlog $$ Hl

/-- `refines_store_l` (app_rel_rules.v:266).

**Port note**: `▷`s dropped (Lean convention, same rationale as `refines_alloc_l`). -/
theorem refines_store_l {E : CoPset} {K : Ectx rT} {l : Loc} {v' : Val rT} {t : Exp rT}
    {A : lrel rT GF} :
    iprop(∃ v : Val rT, (l ↦ v) ∗ ((l ↦ v') -∗ refines E (K.fill pl(#(.unit))) t A))
      ⊢@{IProp GF} refines E (K.fill (.store pl(#(.loc l)) v'.1)) t A := by
  iintro ⟨%v, Hl, Hlog⟩
  iapply refines_wp_l
  rw [show Exp.store pl(#(.loc l)) v'.1 =
        Exp.store pl(#(.loc l)) (Exp.ofVal v') from rfl]
  -- `wp_store`'s `v` is the NEW value, `v'` is the OLD; swapped here.
  iapply (wp_store (v' := v))
  iframe Hl
  iintro Hl
  iapply Hlog $$ Hl

/-! ## Stateful reductions on the RHS -/

/-- `refines_alloc_r` (app_rel_rules.v:119). -/
theorem refines_alloc_r {E : CoPset} {K : Ectx rT} {v : Val rT} {t : Exp rT} {A : lrel rT GF} :
    iprop(∀ (l : Loc), (l ↦ₛ v) -∗
            refines E t (K.fill pl(#(.loc l))) A)
      ⊢@{IProp GF} refines E t (K.fill (.alloc v.1)) A := by
  iintro Hlog
  unfold refines
  iintro %K' %ε Hj Hna Herr Hpos
  isimp only [Ectx.fill_comp K' K] at Hj
  ihave HStep := step_alloc (K'.comp K) v.2 $$ Hj
  iapply specUpdate_wp
  iapply (specUpdate_bind (E1 := ⊤) (E2 := ⊤) Std.LawfulSet.subset_refl)
  iframe HStep
  iintro ⟨%l, HKRes, Hl⟩
  isimp only [← Ectx.fill_comp K' K] at HKRes
  iapply specUpdate_ret
  iapply Hlog $$ %l Hl %K' %ε HKRes Hna Herr Hpos

/-- `refines_load_r` (app_rel_rules.v:132): RHS heap load.

Note Rocq's `refines_load_r` takes `l ↦ₛ{q} v` with fractional permission; we port with
full ownership for simplicity (most callers have full permission). -/
theorem refines_load_r {E : CoPset} {K : Ectx rT} {l : Loc} {v : Val rT} {t : Exp rT}
    {A : lrel rT GF} :
    iprop((l ↦ₛ v) ∗ ((l ↦ₛ v) -∗ refines E t (K.fill v.1) A))
      ⊢@{IProp GF} refines E t (K.fill pl(!#(.loc l))) A := by
  iintro ⟨Hl, Hlog⟩
  unfold refines
  iintro %K' %ε Hj Hna Herr Hpos
  have hfcv : (K'.comp K).fill (Exp.ofVal v) = K'.fill (K.fill v.1) := (Ectx.fill_comp K' K _).symm
  isimp only [Ectx.fill_comp K' K] at Hj
  ihave HStep := step_load (K'.comp K) (v := v) $$ [$]
  iapply specUpdate_wp
  iapply (specUpdate_bind (E1 := ⊤) (E2 := ⊤) Std.LawfulSet.subset_refl)
  iframe HStep
  iintro ⟨HKRes, HlRes⟩
  isimp only [hfcv] at HKRes
  iapply specUpdate_ret
  iapply Hlog $$ HlRes %K' %ε HKRes Hna Herr Hpos

/-- `refines_store_r` (app_rel_rules.v:144). -/
theorem refines_store_r {E : CoPset} {K : Ectx rT} {l : Loc} {v v' : Val rT} {e : Exp rT}
    {A : lrel rT GF} :
    iprop((l ↦ₛ v) ∗ ((l ↦ₛ v') -∗ refines E e (K.fill pl(#(.unit))) A))
      ⊢@{IProp GF} refines E e (K.fill (.store pl(#(.loc l)) v'.1)) A := by
  iintro ⟨Hl, Hlog⟩
  unfold refines
  iintro %K' %ε Hj Hna Herr Hpos
  isimp only [Ectx.fill_comp K' K] at Hj
  ihave HStep := step_store (K'.comp K) (v_old := v) (v_new := v')
    (e := v'.1) v'.2 (Exp.toVal?_ofVal v') $$ [$Hj $Hl]
  iapply specUpdate_wp
  iapply (specUpdate_bind (E1 := ⊤) (E2 := ⊤) Std.LawfulSet.subset_refl)
  iframe HStep
  iintro ⟨HKRes, Hl'⟩
  isimp only [← Ectx.fill_comp K' K] at HKRes
  iapply specUpdate_ret
  iapply Hlog $$ Hl' %K' %ε HKRes Hna Herr Hpos

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
            refines E (K.fill pl(#(.int n))) t A)
      ⊢@{IProp GF} refines E (K.fill (pl(rand(#(.int z), #(.unit))))) t A := by
  iintro Hlog
  iapply refines_wp_l
  iapply (wp_rand Hz)
  iintro %n %Hbnds
  iapply Hlog $$ %n %Hbnds

/-- `refines_randT_l`: LHS tape-rand pop. Consumes the head `n` of tape `α`. -/
theorem refines_randT_l {E : CoPset} {K : Ectx rT} {l : Loc} {z n : Int}
    {ns : List Int} {t : Exp rT} {A : lrel rT GF} :
    iprop(appNatTape l z (n :: ns) ∗
            (appNatTape l z ns -∗ (⌜0 ≤ n ∧ n < z⌝) -∗
              refines E (K.fill pl(#(.int n))) t A))
      ⊢@{IProp GF} refines E (K.fill (pl(rand(#(.int z), #(.lbl l))))) t A := by
  iintro ⟨Hl, Hlog⟩
  iapply (refines_wp_l (K := K) (e1 := pl(rand(#(.int z), #(.lbl l)))))
  iapply wp_rand_tape
  iframe Hl
  iintro Hl' %Hbnds
  iapply Hlog $$ Hl' %Hbnds

/-- `refines_randT_empty_l`: LHS rand on an empty tape — uniform sample, tape stays empty. -/
theorem refines_randT_empty_l {E : CoPset} {K : Ectx rT} {l : Loc} {z : Int}
    {t : Exp rT} {A : lrel rT GF} (Hz : 0 < z) :
    iprop(appNatTape l z [] ∗
            (∀ (n : Int), appNatTape l z [] -∗ (⌜0 ≤ n ∧ n < z⌝) -∗
              refines E (K.fill pl(#(.int n))) t A))
      ⊢@{IProp GF} refines E (K.fill (pl(rand(#(.int z), #(.lbl l))))) t A := by
  iintro ⟨Hl, Hlog⟩
  iapply (refines_wp_l (K := K) (e1 := pl(rand(#(.int z), #(.lbl l)))))
  iapply (wp_rand_tape_empty Hz)
  iframe Hl
  iintro %n Hl' %Hbnds
  iapply Hlog $$ %n Hl' %Hbnds

/-- `refines_randU_r`: RHS unit-rand step. -/
theorem refines_randU_r {E : CoPset} {K : Ectx rT} {z : Int} {e : Exp rT} {A : lrel rT GF}
    (Hz : 0 < z) :
    iprop(∀ (n : Int), (⌜0 ≤ n ∧ n < z⌝) -∗
            refines E e (K.fill pl(#(.int n))) A)
      ⊢@{IProp GF} refines E e (K.fill (pl(rand(#(.int z), #(.unit))))) A := by
  iintro Hlog
  unfold refines
  iintro %K' %ε Hj Hna Herr Hpos
  isimp only [Ectx.fill_comp K' K] at Hj
  iapply (wp_rand_r (K'.comp K) Hz)
  iframe Hj
  iintro %n %Hbnds HKRes
  isimp only [← Ectx.fill_comp K' K] at HKRes
  iapply Hlog $$ %n %Hbnds %K' %ε HKRes Hna Herr Hpos

/-- `refines_randT_r`: RHS tape-rand pop. The continuation receives the popped
value and the tail tape. -/
theorem refines_randT_r {E : CoPset} {K : Ectx rT} {l : Loc} {z : Int}
    {n : Int} {ns : List Int} {e : Exp rT} {A : lrel rT GF} :
    iprop(specNatTape l z (n :: ns) ∗
            (specNatTape l z ns -∗ (⌜0 ≤ n ∧ n < z⌝) -∗
              refines E e (K.fill pl(#(.int n))) A))
      ⊢@{IProp GF} refines E e (K.fill (pl(rand(#(.int z), #(.lbl l))))) A := by
  iintro ⟨Hα, Hlog⟩
  unfold refines
  iintro %K' %ε Hj Hna Herr Hpos
  isimp only [Ectx.fill_comp K' K] at Hj
  iunfold specNatTape at Hα
  icases Hα with ⟨%fs, %hmap, Hαb⟩
  cases fs with
  | nil => simp at hmap
  | cons w ws =>
    simp at hmap
    obtain ⟨hwn, hwsm⟩ := hmap
    ihave HStep := step_rand (K'.comp K) l w ws $$ [$]
    iapply specUpdate_wp
    iapply (specUpdate_bind Std.LawfulSet.subset_refl)
    iframe HStep
    iintro ⟨HKRes, HαResNew⟩
    isimp only [← Ectx.fill_comp K' K, hwn] at HKRes
    iapply specUpdate_ret
    ihave HαResNat : iprop(specNatTape l z ns) $$ [HαResNew]
    · unfold specNatTape
      iexists ws
      isplitr; · ipureintro; exact hwsm
      iexact HαResNew
    have hbnds : 0 ≤ n ∧ n < z := ⟨hwn ▸ w.2.1, hwn ▸ w.2.2⟩
    iapply Hlog $$ HαResNat %hbnds %K' %ε HKRes Hna Herr Hpos

/-- `refines_randT_empty_r`: RHS rand on an empty tape — uniform sample, tape empty. -/
theorem refines_randT_empty_r {E : CoPset} {K : Ectx rT} {l : Loc} {z : Int}
    {e : Exp rT} {A : lrel rT GF} (Hz : 0 < z) :
    iprop(specNatTape l z [] ∗
            (∀ (n : Int), specNatTape l z [] -∗ (⌜0 ≤ n ∧ n < z⌝) -∗
              refines E e (K.fill pl(#(.int n))) A))
      ⊢@{IProp GF} refines E e (K.fill (pl(rand(#(.int z), #(.lbl l))))) A := by
  iintro ⟨Hα, Hlog⟩
  unfold refines
  iintro %K' %ε Hj Hna Herr Hpos
  isimp only [Ectx.fill_comp K' K] at Hj
  iapply (wp_rand_tape_empty_r (K'.comp K) Hz)
  iframe Hj Hα
  iintro %n HαNew HKRes %Hbnds
  isimp only [← Ectx.fill_comp K' K] at HKRes
  iapply Hlog $$ %n HαNew %Hbnds %K' %ε HKRes Hna Herr Hpos

/-- `refines_alloctape_l`: LHS tape allocation. -/
theorem refines_alloctape_l {E : CoPset} {K : Ectx rT} {z : Int} {t : Exp rT} {A : lrel rT GF} :
    iprop(∀ (l : Loc), appTapesFrag l (Tape.empty z) -∗
            refines E (K.fill pl(#(.lbl l))) t A)
      ⊢@{IProp GF} refines E (K.fill (pl(tape(#(.int z))))) t A := by
  iintro Hlog
  iapply refines_wp_l
  iapply wp_alloctape
  iintro %l Hl
  iapply Hlog $$ %l Hl

/-- `refines_alloctape_r`: RHS tape allocation. The fresh location's spec tape
fragment is delivered via the continuation. -/
theorem refines_alloctape_r {E : CoPset} {K : Ectx rT} {z : Int} {e : Exp rT} {A : lrel rT GF} :
    iprop(∀ (l : Loc), specNatTape l z [] -∗
            refines E e (K.fill pl(#(.lbl l))) A)
      ⊢@{IProp GF} refines E e (K.fill (pl(tape(#(.int z))))) A := by
  iintro Hlog
  unfold refines
  iintro %K' %ε Hj Hna Herr Hpos
  isimp only [Ectx.fill_comp K' K] at Hj
  iapply (wp_alloc_tape_r (K'.comp K))
  iframe Hj
  iintro %l HKRes Hl
  isimp only [← Ectx.fill_comp K' K] at HKRes
  iapply Hlog $$ %l Hl %K' %ε HKRes Hna Herr Hpos

/-! ## Structural rules -/

/-- `refines_wand` (app_rel_rules.v:330): weakening the result relation. -/
theorem refines_wand {E : CoPset} {e1 e2 : Exp rT} {A A' : lrel rT GF} :
    iprop(refines E e1 e2 A) ⊢@{IProp GF}
      (∀ (v1 v2 : Val rT), A v1 v2 ={⊤}=∗ A' v1 v2) -∗ refines E e1 e2 A' := by
  iintro He HAA
  have Hfill1 : e1 = Ectx.empty.fill e1 := rfl
  have Hfill2 : e2 = Ectx.empty.fill e2 := rfl
  rw [Hfill1, Hfill2]
  iapply (refines_bind (K' := Ectx.empty)
    (A := A) (A' := A') (E := E) (e := e1) (e' := e2)) $$ [He]
  · rw [← Hfill1, ← Hfill2]; iexact He
  iintro %v %v' HA
  ihave HAA' := HAA $$ %v %v'
  rw [← (show v.1 = Ectx.empty.fill v.1 from rfl), ← (show v'.1 = Ectx.empty.fill v'.1 from rfl)]
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
  iapply refines_ret (hv1 := rfl) (hv2 := rfl)
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
  ihave HerrEq : iprop(↯ (ε / 2 + ε / 2)) $$ [HerrTot]
  · rw [ENNReal.add_halves]; iexact HerrTot
  ihave HerrSp : iprop((↯ (ε / 2)) ∗ (↯ (ε / 2))) $$ [HerrEq]
  · iapply ErrorCredit.split $$ HerrEq
  icases HerrSp with ⟨Herr1, Herr2⟩
  have hpos2 : (0 : ENNReal) < ε / 2 :=
    ENNReal.div_pos_iff.mpr ⟨ne_of_gt HposTot, by simp⟩
  ihave HrefFolded := Hcnt $$ %(ε / 2) Herr1 %hpos2
  iapply HrefFolded $$ %K %(ε / 2) Hj Hna Herr2 %hpos2


/-- `refines_ind_amp` (app_rel_rules.v): **error amplification**. To prove a
refinement outright it suffices to prove it from an arbitrary positive budget
`↯ ε`, given the same refinement at the amplified budget `↯ (k * ε)` for some
fixed `k > 1`. The initial budget comes from `refines_get_ec`; the induction is
`ErrorCredit.Induction.amplifying`, which terminates because `err_amp_power`
makes `ε * kⁿ ≥ 1` for some `n` and `↯ 1` is absurd. This is the mechanism for
unbounded rejection-sampling loops. -/
theorem refines_ind_amp {E : CoPset} {e e' : Exp rT} {A : lrel rT GF} {k : NNReal}
    (hk : 1 < k) :
    iprop(□ (∀ (ε : ENNReal), (⌜0 < ε⌝) -∗
            □ ((↯ ((k : ENNReal) * ε)) -∗ refines E e e' A) -∗
            (↯ ε) -∗ refines E e e' A))
      ⊢@{IProp GF} refines E e e' A := by
  iintro #Hamp
  iapply refines_get_ec
  iintro %ε Herr %hpos
  iapply (ErrorCredit.Induction.amplifying hpos hk) $$ [] Herr
  iintro !> %ε' %hε' #Hstep Hε'
  iapply Hamp $$ %ε' %hε' Hstep Hε'

/-- `refines_arrow_val_err` (app_rel_rules.v): `refines_ind_amp` at arrow type.
The amplification runs on the *quantified* body `∀ v1 v2, A v1 v2 -∗ REL …`, so
the budget is established once for the closure rather than per call. Requires
the closedness witness that `lrel_arr` carries. -/
theorem refines_arrow_val_err {v v' : Val rT} {A A' : lrel rT GF} {k : NNReal}
    (hk : 1 < k) (hv : v.1.isClosedEmpty ∧ v'.1.isClosedEmpty) :
    iprop(□ (∀ (ε : ENNReal), (⌜0 < ε⌝) -∗
            □ ((↯ ((k : ENNReal) * ε)) -∗ ∀ (v1 v2 : Val rT), A v1 v2 -∗
                refines (⊤ : CoPset) (.app v.1 v1.1) (.app v'.1 v2.1) A') -∗
            (↯ ε) -∗ ∀ (v1 v2 : Val rT), A v1 v2 -∗
              refines (⊤ : CoPset) (.app v.1 v1.1) (.app v'.1 v2.1) A'))
      ⊢@{IProp GF} refines (⊤ : CoPset) v.1 v'.1 (lrel_arr A A') := by
  iintro #Hamp
  iapply (refines_arrow_val (hv := hv))
  iintro !> %v1 %v2 HA
  iapply refines_get_ec
  iintro %ε Herr %hpos
  ihave Hall := (ErrorCredit.Induction.amplifying
      (P := iprop(∀ (w1 w2 : Val rT), A w1 w2 -∗
        refines (⊤ : CoPset) (.app v.1 w1.1) (.app v'.1 w2.1) A')) hpos hk) $$ [] Herr
  · imodintro
    iintro %ε' %hε' #Hstep Hε'
    iapply Hamp $$ %ε' %hε' Hstep Hε'
  iapply Hall $$ %v1 %v2 HA

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
            refines E (K.fill pl(#(.int n))) (K'.fill (pl(#(.int (f n))))) A)
      ⊢@{IProp GF}
        refines E (K.fill (pl(rand(#(.int z), #(.unit)))))
          (K'.fill (pl(rand(#(.int z), #(.unit))))) A := by
  iintro Hcnt
  unfold refines
  iintro %K2 %ε Hj Hna Herr Hpos
  isimp only [Ectx.fill_comp K2 K'] at Hj
  iapply ApproxisWpGS.wp_bind (K := K)
  iapply (wp_couple_rand_rand z f hdom hbij Hz (K2.comp K') ⊤
    (fun n => wp ⊤ (K.fill (Exp.ofVal n))
      (fun v => iprop(∃ v' ε',
        (⤇ K2.fill v'.1) ∗ naOwnP ⊤ ∗ (↯ ε') ∗ (⌜(0 : ENNReal) < ε'⌝) ∗ A.car v v'))))
  iframe Hj
  iintro %n %Hn HKres
  isimp only [← Ectx.fill_comp K2 K'] at HKres
  rw [show Exp.ofVal (.int n : Val rT) = pl(#(.int n)) from rfl]
  iapply Hcnt $$ %n %Hn %K2 %ε HKres Hna Herr Hpos

/-- Adversarial counterpart of `refines_couple_rands_lr`: the caller pays the
amortized credit `ε₁` and each branch is handed `↯ (ε₂ n)`. Lifts
`wp_couple_rand_rand_adv` through `refines`; the caller's `↯ ε₁` is independent
of the `↯ ε` slack that `refines` threads through its own definition. -/
theorem refines_couple_rands_lr_adv
    {E : CoPset} {K K' : Ectx rT} {A : lrel rT GF} {z : Int}
    (f : Int → Int) (ε₁ : ENNReal) (ε₂ : Int → ENNReal)
    (hdom : ∀ n : Int, 0 ≤ n → n < z → 0 ≤ f n ∧ f n < z)
    (hbij : ∀ m : Int, 0 ≤ m → m < z → ∃! n : Int, (0 ≤ n ∧ n < z) ∧ f n = m)
    (Hz : 0 < z)
    (hamort : (∑ n ∈ Finset.Ico (0 : Int) z, ε₂ n) / (z.toNat : ENNReal) ≤ ε₁) :
    iprop((↯ ε₁) ∗ ∀ (n : Int), (⌜0 ≤ n ∧ n < z⌝) -∗ (↯ (ε₂ n)) -∗
            refines E (K.fill pl(#(.int n))) (K'.fill (pl(#(.int (f n))))) A)
      ⊢@{IProp GF}
        refines E (K.fill (pl(rand(#(.int z), #(.unit)))))
          (K'.fill (pl(rand(#(.int z), #(.unit))))) A := by
  iintro ⟨Hε, Hcnt⟩
  unfold refines
  iintro %K2 %ε Hj Hna Herr Hpos
  isimp only [Ectx.fill_comp K2 K'] at Hj
  iapply ApproxisWpGS.wp_bind (K := K)
  iapply (wp_couple_rand_rand_adv z f ε₁ ε₂ hdom hbij Hz hamort (K2.comp K') ⊤
    (fun n => wp ⊤ (K.fill (Exp.ofVal n))
      (fun v => iprop(∃ v' ε',
        (⤇ K2.fill v'.1) ∗ naOwnP ⊤ ∗ (↯ ε') ∗ (⌜(0 : ENNReal) < ε'⌝) ∗ A.car v v'))))
  iframe Hj Hε
  iintro %n %Hn Hec HKres
  isimp only [← Ectx.fill_comp K2 K'] at HKres
  rw [show Exp.ofVal (.int n : Val rT) = pl(#(.int n)) from rfl]
  iapply Hcnt $$ %n %Hn Hec %K2 %ε HKres Hna Herr Hpos

/-- Avoidance at the relational level: paying `↯ (1/z)` buys `n ≠ bad` on both
sides of the coupling. -/
theorem refines_couple_rands_lr_avoid
    {E : CoPset} {K K' : Ectx rT} {A : lrel rT GF} {z : Int} (bad : Int) (Hz : 0 < z) :
    iprop((↯ ((z.toNat : ENNReal))⁻¹) ∗ ∀ (n : Int), (⌜(0 ≤ n ∧ n < z) ∧ n ≠ bad⌝) -∗
            refines E (K.fill pl(#(.int n))) (K'.fill (pl(#(.int n)))) A)
      ⊢@{IProp GF}
        refines E (K.fill (pl(rand(#(.int z), #(.unit)))))
          (K'.fill (pl(rand(#(.int z), #(.unit))))) A := by
  classical
  iintro ⟨Hε, Hcnt⟩
  have hamort : (∑ n ∈ Finset.Ico (0 : Int) z, if n = bad then (1 : ENNReal) else 0)
      / (z.toNat : ENNReal) ≤ ((z.toNat : ENNReal))⁻¹ := by
    rw [← one_div]
    gcongr
    rw [Finset.sum_ite_eq' (Finset.Ico (0 : Int) z) bad (fun _ => (1 : ENNReal))]
    split <;> simp
  iapply (refines_couple_rands_lr_adv (K' := K') id
    ((z.toNat : ENNReal))⁻¹ (fun n => if n = bad then 1 else 0)
    (fun _ h1 h2 => ⟨h1, h2⟩) (fun m h1 h2 => ⟨m, ⟨⟨h1, h2⟩, rfl⟩, fun _ hn' => hn'.2⟩)
    Hz hamort)
  iframe Hε
  iintro %n %hn Hec
  by_cases hb : n = bad
  · rw [if_pos hb]
    iexfalso
    iapply ErrorCredit.contradict (_root_.le_refl 1) $$ Hec
  · simp only [id_eq]
    iapply Hcnt
    ipureintro
    exact ⟨hn, hb⟩

/-- `refines_couple_tapes` (app_rel_rules.v): presample both tapes in lockstep
along a bijection `f` on `[0, z)`, without stepping either program. -/
theorem refines_couple_tapes_bij {E : CoPset} {e e' : Exp rT} {A : lrel rT GF}
    {z : Int} {α αₛ : Loc} {ns nsₛ : List Int} (f : Int → Int)
    (hdom : ∀ n : Int, 0 ≤ n → n < z → 0 ≤ f n ∧ f n < z)
    (hbij : ∀ m : Int, 0 ≤ m → m < z → ∃! n : Int, (0 ≤ n ∧ n < z) ∧ f n = m)
    (Hz : 0 < z) :
    iprop(appNatTape α z ns ∗ specNatTape αₛ z nsₛ ∗
        (∀ (n : Int), (⌜0 ≤ n ∧ n < z⌝) -∗ appNatTape α z (ns ++ [n]) -∗
          specNatTape αₛ z (nsₛ ++ [f n]) -∗ refines E e e' A))
      ⊢@{IProp GF} refines E e e' A := by
  iintro ⟨Hα, Hαₛ, Hcnt⟩
  unfold refines
  iintro %K %ε Hj Hna Herr Hpos
  iapply (wp_couple_tapes_bij (αₛ := αₛ) (ns := ns) (nsₛ := nsₛ)
    f hdom hbij Hz)
  iframe Hα Hαₛ
  iintro %n %hn HA HS
  iapply Hcnt $$ %n %hn HA HS %K %ε Hj Hna Herr Hpos

/-- `refines_couple_TU`: couple a LHS tape-rand (on empty tape α) with a RHS
unit-rand via bijection `f`. -/
theorem refines_couple_TU {E : CoPset} {K K' : Ectx rT} {A : lrel rT GF} {z : Int}
    (α : Loc) (f : Int → Int)
    (hdom : ∀ n : Int, 0 ≤ n → n < z → 0 ≤ f n ∧ f n < z)
    (hbij : ∀ m : Int, 0 ≤ m → m < z → ∃! n : Int, (0 ≤ n ∧ n < z) ∧ f n = m)
    (Hz : 0 < z) :
    iprop(▷ appNatTape α z [] ∗
        (∀ (n : Int), appNatTape α z [] -∗ (⌜0 ≤ n ∧ n < z⌝) -∗
            refines E (K.fill pl(#(.int n))) (K'.fill (pl(#(.int (f n))))) A))
      ⊢@{IProp GF}
        refines E (K.fill (pl(rand(#(.int z), #(.lbl α)))))
          (K'.fill (pl(rand(#(.int z), #(.unit))))) A := by
  iintro ⟨Hα, Hcnt⟩
  unfold refines
  iintro %K2 %ε Hj Hna Herr Hpos
  isimp only [Ectx.fill_comp K2 K'] at Hj
  iapply ApproxisWpGS.wp_bind (K := K)
  iapply (wp_couple_tape_rand z f hdom hbij Hz (K2.comp K') ⊤ α
    (fun n => wp ⊤ (K.fill (Exp.ofVal n))
      (fun v => iprop(∃ v' ε',
        (⤇ K2.fill v'.1) ∗ naOwnP ⊤ ∗ (↯ ε') ∗ (⌜(0 : ENNReal) < ε'⌝) ∗ A.car v v'))))
  iframe Hα Hj
  iintro %n ⟨HαNew, HKres, %Hn⟩
  isimp only [← Ectx.fill_comp K2 K'] at HKres
  rw [show Exp.ofVal (.int n : Val rT) = pl(#(.int n)) from rfl]
  iapply Hcnt $$ %n HαNew %Hn %K2 %ε HKres Hna Herr Hpos

/-- `refines_couple_UT`: symmetric — couple LHS unit-rand with RHS tape-rand on
empty tape α' via bijection `f`. -/
theorem refines_couple_UT {E : CoPset} {K K' : Ectx rT} {A : lrel rT GF} {z : Int}
    (α' : Loc) (f : Int → Int)
    (hdom : ∀ n : Int, 0 ≤ n → n < z → 0 ≤ f n ∧ f n < z)
    (hbij : ∀ m : Int, 0 ≤ m → m < z → ∃! n : Int, (0 ≤ n ∧ n < z) ∧ f n = m)
    (Hz : 0 < z) :
    iprop(▷ specNatTape α' z [] ∗
        (∀ (n : Int), specNatTape α' z [] -∗ (⌜0 ≤ n ∧ n < z⌝) -∗
            refines E (K.fill pl(#(.int n))) (K'.fill (pl(#(.int (f n))))) A))
      ⊢@{IProp GF}
        refines E (K.fill (pl(rand(#(.int z), #(.unit)))))
          (K'.fill (pl(rand(#(.int z), #(.lbl α'))))) A := by
  iintro ⟨Hα', Hcnt⟩
  unfold refines
  iintro %K2 %ε Hj Hna Herr Hpos
  isimp only [Ectx.fill_comp K2 K'] at Hj
  iapply ApproxisWpGS.wp_bind (K := K)
  iapply (wp_couple_rand_tape z f hdom hbij Hz (K2.comp K') ⊤ α'
    (fun n => wp ⊤ (K.fill (Exp.ofVal n))
      (fun v => iprop(∃ v' ε',
        (⤇ K2.fill v'.1) ∗ naOwnP ⊤ ∗ (↯ ε') ∗ (⌜(0 : ENNReal) < ε'⌝) ∗ A.car v v'))))
  iframe Hα' Hj
  iintro %n ⟨Hα'New, HKres, %Hn⟩
  isimp only [← Ectx.fill_comp K2 K'] at HKres
  rw [show Exp.ofVal (.int n : Val rT) = pl(#(.int n)) from rfl]
  iapply Hcnt $$ %n Hα'New %Hn %K2 %ε HKres Hna Herr Hpos

/-- `refines_couple_TT`: couple two empty tapes via a bijection. Uses the
existing `wp_couple_rand_lbl_rand_lbl`. -/
theorem refines_couple_TT {E : CoPset} {K K' : Ectx rT} {A : lrel rT GF} {z : Int}
    (α α' : Loc) (f : Int → Int)
    (hdom : ∀ n : Int, 0 ≤ n → n < z → 0 ≤ f n ∧ f n < z)
    (hbij : ∀ m : Int, 0 ≤ m → m < z → ∃! n : Int, (0 ≤ n ∧ n < z) ∧ f n = m)
    (Hz : 0 < z) :
    iprop(▷ appNatTape α z [] ∗ ▷ specNatTape α' z [] ∗
        (∀ (n : Int), appNatTape α z [] -∗ specNatTape α' z [] -∗ (⌜0 ≤ n ∧ n < z⌝) -∗
            refines E (K.fill pl(#(.int n))) (K'.fill (pl(#(.int (f n))))) A))
      ⊢@{IProp GF}
        refines E (K.fill (pl(rand(#(.int z), #(.lbl α)))))
          (K'.fill (pl(rand(#(.int z), #(.lbl α'))))) A := by
  iintro ⟨Hα, Hα', Hcnt⟩
  unfold refines
  iintro %K2 %ε Hj Hna Herr Hpos
  isimp only [Ectx.fill_comp K2 K'] at Hj
  iapply ApproxisWpGS.wp_bind (K := K)
  iapply (wp_couple_rand_lbl_rand_lbl z f hdom hbij Hz (K2.comp K') ⊤ α α'
    (fun n => wp ⊤ (K.fill (Exp.ofVal n))
      (fun v => iprop(∃ v' ε',
        (⤇ K2.fill v'.1) ∗ naOwnP ⊤ ∗ (↯ ε') ∗ (⌜(0 : ENNReal) < ε'⌝) ∗ A.car v v'))))
  iframe Hα Hα' Hj
  iintro %n ⟨HαNew, Hα'New, HKres, %Hn⟩
  isimp only [← Ectx.fill_comp K2 K'] at HKres
  rw [show Exp.ofVal (.int n : Val rT) = pl(#(.int n)) from rfl]
  iapply Hcnt $$ %n HαNew Hα'New %Hn %K2 %ε HKres Hna Herr Hpos

end AppRelRules

end ProbLang
