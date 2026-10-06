module

public import Metrology.LiveEris.Lifting
import Metrology.ProbLang.Syntax.Notation
public import Metrology.Iris.SpecRules

@[expose] public section

/-! # LiveEris primitive laws -/

open Iris Iris.Std Iris.BI Iris.ProofMode ProbLang ProbLang.LiveEris.LiveWpGS
open scoped AppGS ENNReal

namespace ProbLang
namespace LiveEris

variable {rT : Type _} {hlc : HasLC} {GF : BundledGFunctors} [LawfulProbLangℝ rT]
  [LiveGS rT hlc GF]
variable {Q : State rT → State rT → Prop}

/-! ## Heap operations -/

theorem lwp_alloc {E : CoPset} {v : Val rT} {Φ : Val rT → IProp GF} :
    iprop(∀ l, appHeapFrag l v -∗ Φ (.loc l)) ⊢@{IProp GF} lwp Q E (.alloc (.ofVal v)) Φ := by
  iintro HΦ
  iapply lwp_lift_atomic_head_step (Exp.toVal?_eq_none.mpr fun ⟨w⟩ => nomatch w) (by is_lc)
  iintro %σ₁ %c ⟨Hσ, Hc⟩ !>
  have hred : HeadReducible (.alloc (.ofVal v)) σ₁ :=
    (HeadStepSupport.AllocS (Exp.toVal?_ofVal v) rfl rfl).ne_zero
  iframe %hred
  iintro %e₂ %σ₂ %Hstep
  cases Possible.headStepSupport Hstep with
  | AllocS hvd hl hσ =>
    rw [Exp.toVal?_ofVal] at hvd; cases hvd; subst hl hσ
    isimp only [Exp.toVal?_lit]
    ileft
    imod app_state_heap_alloc v $$ Hσ with ⟨Hσ', Hl⟩
    imodintro
    isimp only [liveWpGS_stateInterp_eq, ExtTreeMap.insert_eq_PartialMap_insert]
    iframe Hσ' Hc
    iapply HΦ $$ %σ₁.heap.fresh Hl

theorem lwp_load {E : CoPset} {l : Loc} {v : Val rT} {Φ : Val rT → IProp GF} :
    iprop(l ↦ v ∗ (l ↦ v -∗ Φ v)) ⊢@{IProp GF} lwp Q E pl(!#(.loc l)) Φ := by
  iintro ⟨Hl, HΦ⟩
  iapply lwp_lift_atomic_head_step (Exp.toVal?_eq_none.mpr fun ⟨w⟩ => nomatch w) (by is_lc)
  iintro %σ₁ %c ⟨Hσ, Hc⟩
  ihave %hlook := app_state_lookup_heap $$ Hσ Hl
  have hred : HeadReducible pl(!#(.loc l)) σ₁ := (HeadStepSupport.LoadS hlook rfl).ne_zero
  imodintro
  iframe %hred
  iintro %e₂ %σ₂ %Hstep
  cases Possible.headStepSupport Hstep with
  | LoadS hlook' hofv =>
    rw [hlook] at hlook'; cases hlook'; subst hofv
    isimp only [Exp.toVal?_ofVal]
    ileft
    imodintro
    iframe Hσ Hc
    iapply HΦ $$ Hl

theorem lwp_store {E : CoPset} {l : Loc} {v v' : Val rT} {Φ : Val rT → IProp GF} :
    iprop(l ↦ v' ∗ (l ↦ v -∗ Φ .unit)) ⊢@{IProp GF} lwp Q E (.store pl(#(.loc l)) (.ofVal v)) Φ := by
  iintro ⟨Hl, HΦ⟩
  iapply lwp_lift_atomic_head_step (Exp.toVal?_eq_none.mpr fun ⟨w⟩ => nomatch w) (by is_lc)
  iintro %σ₁ %c ⟨Hσ, Hc⟩
  ihave %hlook := app_state_lookup_heap $$ Hσ Hl
  have hred : HeadReducible (.store pl(#(.loc l)) (.ofVal v)) σ₁ :=
    (HeadStepSupport.StoreS (Exp.toVal?_ofVal v)
      (by rw [hlook]; exact Option.isSome_some) rfl).ne_zero
  imodintro
  iframe %hred
  iintro %e₂ %σ₂ %Hstep
  cases Possible.headStepSupport Hstep with
  | StoreS hvd _ hσ =>
    rw [Exp.toVal?_ofVal] at hvd; cases hvd; subst hσ
    isimp only [Exp.toVal?_lit]
    ileft
    imod app_state_update_heap $$ Hσ Hl with ⟨Hσ', Hl'⟩
    imodintro
    isimp only [liveWpGS_stateInterp_eq, ExtTreeMap.insert_eq_PartialMap_insert]
    iframe Hσ' Hc
    iapply HΦ $$ Hl'

/-- A store that makes progress is a free checkpoint. -/
theorem lwp_store_progress {E : CoPset} {l : Loc} {v v' : Val rT} {Φ : Val rT → IProp GF}
    (HQ : ∀ σ : State rT, σ.heap[l]? = some v' → Q σ (σ.update_heap (·.insert l v))) :
    iprop(l ↦ v' ∗ ▷ (l ↦ v -∗ Φ .unit))
      ⊢@{IProp GF} lwp Q E (.store pl(#(.loc l)) (.ofVal v)) Φ := by
  iintro ⟨Hl, HΦ⟩
  iapply lwp_lift_atomic_head_step (Exp.toVal?_eq_none.mpr fun ⟨w⟩ => nomatch w) (by is_lc)
  iintro %σ₁ %c ⟨Hσ, Hc⟩
  ihave %hlook := app_state_lookup_heap $$ Hσ Hl
  have hred : HeadReducible (.store pl(#(.loc l)) (.ofVal v)) σ₁ :=
    (HeadStepSupport.StoreS (Exp.toVal?_ofVal v)
      (by rw [hlook]; exact Option.isSome_some) rfl).ne_zero
  imodintro
  iframe %hred
  iintro %e₂ %σ₂ %Hstep
  cases Possible.headStepSupport Hstep with
  | StoreS hvd _ hσ =>
    rw [Exp.toVal?_ofVal] at hvd; cases hvd; subst hσ
    isimp only [Exp.toVal?_lit]
    iright
    isplitr; · ipureintro; exact Or.inl (HQ σ₁ hlook)
    inext
    imod app_state_update_heap $$ Hσ Hl with ⟨Hσ', Hl'⟩
    imodintro
    isimp only [liveWpGS_stateInterp_eq, ExtTreeMap.insert_eq_PartialMap_insert]
    iframe Hσ' Hc
    iapply HΦ $$ Hl'

/-! ## Random sampling -/

theorem lwp_rand {E : CoPset} {z : Int} {Φ : Val rT → IProp GF} (Hz : 0 < z) :
    iprop(∀ n, ⌜0 ≤ n ∧ n < z⌝ -∗ Φ (.int n))
      ⊢@{IProp GF} lwp Q E (pl(rand(#(.int z), #(.unit)))) Φ := by
  iintro HΦ
  iapply lwp_lift_atomic_head_step (Exp.toVal?_eq_none.mpr fun ⟨w⟩ => nomatch w) (by is_lc)
  iintro %σ₁ %c ⟨Hσ, Hc⟩ !>
  have hred : HeadReducible (pl(rand(#(.int z), #(.unit)))) σ₁ :=
    (HeadStepSupport.RandNoTapeS Hz (le_refl _) Hz).ne_zero
  iframe %hred
  iintro %e₂ %σ₂ %Hstep
  cases Possible.headStepSupport Hstep with
  | RandNoTapeS _ Hv0 Hvz =>
    isimp only [Exp.toVal?_lit]
    ileft
    imodintro
    iframe Hσ Hc
    iapply HΦ
    ipureintro; exact ⟨Hv0, Hvz⟩
  | RandNonposS hnz => exact absurd Hz hnz

/-! ## Excused checkpoints -/

/-- A pure step may cross a checkpoint while the branch holds a full divergence credit. -/
theorem lwp_pure_step_excused {E : CoPset} {Φ : Val rT → IProp GF} {e₁ e₂ : Exp rT}
    (h : PureStep e₁ e₂) :
    iprop(↻1 ∗ ▷ (↻1 -∗ lwp Q E e₂ Φ)) ⊢@{IProp GF} lwp Q E e₁ Φ := by
  iintro ⟨Hd, HW⟩
  iapply lwp_lift_pure_det_step_of_pureStep h
  iintro %σ %c ⟨Hσ, Hc⟩
  isimp only [liveWpGS_creditInterp_eq] at Hc
  icases Hc with ⟨%δ, %Hδ, Ha⟩
  ihave %h1 := Credit.div_bound $$ Ha Hd
  imodintro
  iright
  isplitr
  · ipureintro
    exact Or.inr (by rw [Hδ]; exact h1.trans le_add_self)
  inext
  imodintro
  iframe Hσ
  isplitl [Ha]
  · isimp only [liveWpGS_creditInterp_eq]
    iexists δ
    iframe Ha
    ipureintro; exact Hδ
  · iapply HW $$ Hd

theorem lwp_pure_steps_excused {E : CoPset} {Φ : Val rT → IProp GF} {n : ℕ} {e₁ e₂ : Exp rT}
    (φ : Prop) [HEx : PureExec φ (n + 1) e₁ e₂] (Hφ : φ := by is_value) :
    iprop(↻1 ∗ ▷ (↻1 -∗ lwp Q E e₂ Φ)) ⊢@{IProp GF} lwp Q E e₁ Φ := by
  obtain ⟨e', hstep, hrest⟩ := HEx.pure_exec Hφ
  iintro ⟨Hd, HW⟩
  iapply lwp_pure_step_excused hstep
  iframe Hd
  inext
  iintro Hd
  iapply lwp_pure_nsteps hrest
  iapply HW $$ Hd

end LiveEris
end ProbLang
