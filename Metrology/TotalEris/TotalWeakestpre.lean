module

public import Metrology.TotalEris.Glm
public import Iris.BI.Lib.Fixpoint
public import Iris.ProofMode.Classes
public import Iris.ProofMode.InstancesUpdates

@[expose] public section

open Std Iris Iris.Std Iris.BI Iris.ProofMode OFE COFE ProbLang
open scoped ENNReal

namespace ProbLang


variable {rT : Type _} [ProbLang.ProbLangℝ rT]

namespace TotalEris
namespace ErisWpGS

variable {GF : BundledGFunctors} [ErisWpGS (rT := rT) GF]

instance : COFE (Exp rT) := COFE.ofDiscrete _
instance : OFE.Discrete (Exp rT) := ⟨id⟩

abbrev TglWpState (rT : Type _) : Type _ := CoPset × Exp rT

instance : COFE (TglWpState rT) := COFE.ofDiscrete _
instance : OFE.Discrete (TglWpState rT) := ⟨id⟩

abbrev tglWpPre -- [Countable rT] [MeasurableSingletonClass rT]
    (wp : CoPset → Exp rT → (Val rT → IProp GF) → IProp GF)
    (E : CoPset) (e₁ : Exp rT) (Φ : Val rT → IProp GF) : IProp GF :=
  iprop(∀ (σ₁ : State rT) (ε₁ : ENNReal),
    (stateInterp σ₁ ∗ errInterp (rT := rT) ε₁) -∗
      match e₁.toVal? with
      | some v => iprop(|={E}=>
          stateInterp σ₁ ∗ errInterp (rT := rT) ε₁ ∗ Φ v)
      | none => iprop(|={E, ∅}=>
          glm' e₁ σ₁ ε₁ (fun ρ ε₂ =>
            iprop(|={∅, E}=>
              stateInterp ρ.state ∗ errInterp (rT := rT) ε₂ ∗ wp E ρ.expr Φ))))

abbrev tglWpPreFixed (Φ : Val rT → IProp GF)
    (wp : TglWpState rT → IProp GF) : TglWpState rT → IProp GF :=
  fun ⟨E, e⟩ => tglWpPre (fun E' e' _ => wp ⟨E', e'⟩) E e Φ

instance tglWpPreFixed_mono {Φ : Val rT → IProp GF} :
    BIMonoPred (tglWpPreFixed (rT := rT) (GF := GF) Φ) where
  mono_pred {wp1 wp2 _ _} := by
    iintro #Hwand %s Hs
    rcases s with ⟨E, e⟩
    unfold tglWpPreFixed tglWpPre
    iintro %σ %ε ⟨Hσ, Hε⟩
    ispecialize Hs $$ %σ %ε [Hσ Hε]
    · isplitl [Hσ]; · iexact Hσ
      iexact Hε
    cases htv : e.toVal? with
    | some v =>
      iexact Hs
    | none =>
      imod Hs with HG
      imodintro
      iapply glm'_mono_pred
      isplitr [HG]
      swap
      · iexact HG
      iintro !> %ρ %ε' HC
      imod HC with ⟨Hσ', Hε', HW⟩
      imodintro
      isplitl [Hσ']; · iexact Hσ'
      isplitl [Hε']; · iexact Hε'
      iapply Hwand
      iexact HW
  mono_pred_ne.ne {_ s s'} hd := by
    have := eq_of_dist_discrete_leibniz hd; subst this; exact .of_eq rfl

@[reducible]
noncomputable def tglWp (E : CoPset) (e : Exp rT) (Φ : Val rT → IProp GF) : IProp GF :=
  bi_least_fixpoint (tglWpPreFixed (rT := rT) (GF := GF) Φ) ⟨E, e⟩

/-- Fixpoint unfolding for `tglWp`. -/
theorem tglWp_unfold {E : CoPset} {e : Exp rT} {Φ : Val rT → IProp GF} :
    tglWp (rT := rT) (GF := GF) E e Φ = tglWpPre (tglWp (rT := rT) (GF := GF)) E e Φ :=
  least_fixpoint_unfold (F := tglWpPreFixed (rT := rT) (GF := GF) Φ) (x := ⟨E, e⟩)

theorem tglWp_unfold_value {E : CoPset} {v : Val rT} {Φ : Val rT → IProp GF} :
    tglWp E (Exp.ofVal v) Φ =
      iprop(∀ (σ : State rT) (ε : ENNReal),
        (stateInterp σ ∗ errInterp (rT := rT) ε) -∗
          |={E}=> stateInterp σ ∗ errInterp (rT := rT) ε ∗ Φ v) := by
  refine .trans tglWp_unfold ?_
  unfold tglWpPre
  rw [Exp.toVal?_ofVal]

theorem tglWp_unfold_step {E : CoPset} {e : Exp rT} {Φ : Val rT → IProp GF}
    (Hv : e.toVal? = none) :
    tglWp E e Φ =
      iprop(∀ (σ : State rT) (ε : ENNReal),
        (stateInterp σ ∗ errInterp (rT := rT) ε) -∗
          |={E, ∅}=> glm' e σ ε (fun ρ ε₂ =>
            iprop(|={∅, E}=>
              stateInterp ρ.state ∗ errInterp (rT := rT) ε₂ ∗ tglWp E ρ.expr Φ))) := by
  refine .trans tglWp_unfold ?_
  unfold tglWpPre
  rw [Hv]

theorem tglWpPre_eq_value {wp : CoPset → Exp rT → (Val rT → IProp GF) → IProp GF}
    {E : CoPset} {v : Val rT} {Φ : Val rT → IProp GF} :
    tglWpPre wp E (Exp.ofVal v) Φ =
      iprop(∀ (σ : State rT) (ε : ENNReal),
        (stateInterp σ ∗ errInterp (rT := rT) ε) -∗
          |={E}=> stateInterp σ ∗ errInterp (rT := rT) ε ∗ Φ v) := by
  unfold tglWpPre; rw [Exp.toVal?_ofVal]

theorem tglWpPre_eq_step {wp : CoPset → Exp rT → (Val rT → IProp GF) → IProp GF}
    {E : CoPset} {e : Exp rT} {Φ : Val rT → IProp GF} (Hv : e.toVal? = none) :
    tglWpPre wp E e Φ =
      iprop(∀ (σ : State rT) (ε : ENNReal),
        (stateInterp σ ∗ errInterp (rT := rT) ε) -∗
          |={E, ∅}=> glm' e σ ε (fun ρ ε₂ =>
            iprop(|={∅, E}=>
              stateInterp ρ.state ∗ errInterp (rT := rT) ε₂ ∗ wp E ρ.expr Φ))) := by
  unfold tglWpPre; rw [Hv]

/-! ## Value rules -/

theorem tglWp_value_fupd {E : CoPset} {v : Val rT} {Φ : Val rT → IProp GF} :
    iprop(|={E}=> Φ v) ⊢@{IProp GF} tglWp E (Exp.ofVal v) Φ := by
  iintro HΦ
  iapply tglWp_unfold
  unfold tglWpPre
  iintro %σ %ε ⟨Hσ, Hε⟩
  rw [Exp.toVal?_ofVal]
  imod HΦ with HΦ'
  imodintro
  isplitl [Hσ]; · iexact Hσ
  isplitl [Hε]; · iexact Hε
  iexact HΦ'

theorem tglWp_value {E : CoPset} {v : Val rT} {Φ : Val rT → IProp GF} :
    Φ v ⊢@{IProp GF} tglWp E (Exp.ofVal v) Φ := by
  iintro HΦ
  iapply tglWp_value_fupd
  imodintro
  iexact HΦ

theorem tglWp_value_of_toVal {E : CoPset} {e : Exp rT} {v : Val rT}
    {Φ : Val rT → IProp GF} (h : e.toVal? = some v) :
    Φ v ⊢@{IProp GF} tglWp E e Φ := by
  rw [← Exp.ofVal_of_toVal_some h]
  exact tglWp_value

theorem tglWp_value_fupd_of_toVal {E : CoPset} {e : Exp rT} {v : Val rT}
    {Φ : Val rT → IProp GF} (h : e.toVal? = some v) :
    iprop(|={E}=> Φ v) ⊢@{IProp GF} tglWp E e Φ := by
  rw [← Exp.ofVal_of_toVal_some h]
  exact tglWp_value_fupd

theorem tglWp_value_inv_with_state {E : CoPset} {v : Val rT} {σ : State rT}
    {ε : ENNReal} {Φ : Val rT → IProp GF} :
    iprop(tglWp E (Exp.ofVal v) Φ ∗ stateInterp σ ∗ errInterp (rT := rT) ε) ⊢@{IProp GF}
      iprop(|={E}=> stateInterp σ ∗ errInterp (rT := rT) ε ∗ Φ v) := by
  iintro ⟨HW, Hσ, Hε⟩
  ihave HW' := (BI.equiv_iff.mp tglWp_unfold_value).1 $$ HW
  iapply HW' $$ %σ %ε
  isplitl [Hσ]; · iexact Hσ
  iexact Hε

/-- `tglWp` absorbs a state-frame-preserving fupd: if from every `(σ, ε)` one can `|={E}=>`-return
the state/error interpretation together with `tglWp E e Φ`, then `tglWp E e Φ` holds. -/
theorem tglWp_of_frame_fupd {E : CoPset} {e : Exp rT} {Φ : Val rT → IProp GF} :
    iprop(∀ (σ : State rT) (ε : ENNReal),
        stateInterp σ ∗ errInterp (rT := rT) ε -∗
          |={E}=> stateInterp σ ∗ errInterp (rT := rT) ε ∗ tglWp E e Φ)
      ⊢@{IProp GF} tglWp E e Φ := by
  iintro HF
  cases htv : e.toVal? with
  | some v =>
    obtain rfl : e = Exp.ofVal v := (Exp.ofVal_of_toVal_some htv).symm
    iapply (BI.equiv_iff.mp tglWp_unfold_value).2
    iintro %σ %ε ⟨Hσ, Hε⟩
    ispecialize HF $$ %σ %ε [Hσ Hε]
    · isplitl [Hσ]; · iexact Hσ
      iexact Hε
    imod HF with ⟨Hσ', Hε', HW⟩
    iapply tglWp_value_inv_with_state
    iframe HW Hσ' Hε'
  | none =>
    iapply (BI.equiv_iff.mp (tglWp_unfold_step htv)).2
    iintro %σ %ε ⟨Hσ, Hε⟩
    ispecialize HF $$ %σ %ε [Hσ Hε]
    · isplitl [Hσ]; · iexact Hσ
      iexact Hε
    imod HF with ⟨Hσ', Hε', HW⟩
    ihave HW' := (BI.equiv_iff.mp (tglWp_unfold_step htv)).1 $$ HW
    iapply HW' $$ %σ %ε
    isplitl [Hσ']; · iexact Hσ'
    iexact Hε'

/-! ## Induction principle -/

theorem tglWp_ind_simple {E : CoPset} {e : Exp rT} {Φ : Val rT → IProp GF}
    (Q : Exp rT → IProp GF) [NonExpansive Q] :
    iprop(□ (∀ e',
      tglWpPre (fun _ e'' _ => Q e'') E e' Φ -∗ Q e')) ⊢@{IProp GF}
        (tglWp E e Φ -∗ Q e) := by
  iintro #HInd HW
  letI Q' : TglWpState rT → IProp GF := fun s => iprop(⌜s.1 = E⌝ -∗ Q s.2)
  letI : NonExpansive Q' := nonExpansive_of_discrete_leibniz Q'
  ihave HQ' : iprop(Q' ⟨E, e⟩) $$ [HW]
  ·
    iapply least_fixpoint_iter (F := tglWpPreFixed Φ) (Φ := Q')
    swap
    · iexact HW
    iintro !> %s HF
    rcases s with ⟨E', e'⟩
    iintro %hEeq
    subst hEeq
    iapply HInd
    iintro %σ %ε ⟨Hσ, Hε⟩
    ispecialize HF $$ %σ %ε [Hσ Hε]
    · isplitl [Hσ]; · iexact Hσ
      iexact Hε
    cases htv : e'.toVal? with
    | some v => iexact HF
    | none =>
      imod HF with HG
      imodintro
      iapply glm'_mono_pred
      isplitr [HG]
      swap
      · iexact HG
      iintro !> %ρ %ε' HC
      imod HC with ⟨Hσ', Hε', HW⟩
      imodintro
      isplitl [Hσ']; · iexact Hσ'
      isplitl [Hε']; · iexact Hε'
      -- HW : Q' ⟨E, ρ.expr⟩ = ⌜E = E⌝ -∗ Q ρ.expr. Discharge with rfl.
      iapply HW; ipureintro; rfl
  iapply HQ'; ipureintro; rfl

/-! ## Derived structural rules -/

theorem tglWp_strong_mono {E : CoPset} {e : Exp rT} {Φ Ψ : Val rT → IProp GF} :
    iprop(tglWp E e Φ ∗ (∀ v, Φ v ={E}=∗ Ψ v)) ⊢@{IProp GF} tglWp E e Ψ := by
  iintro ⟨HW, Hwand⟩
  letI Q : Exp rT → IProp GF := fun e' => iprop(
    ∀ (Ψ' : Val rT → IProp GF), (∀ v, Φ v ={E}=∗ Ψ' v) -∗ tglWp E e' Ψ')
  letI : NonExpansive Q := nonExpansive_of_discrete_leibniz Q
  ihave HQe : iprop(Q e) $$ [HW]
  · iapply (tglWp_ind_simple (E := E) (Φ := Φ) (Q := Q))
    swap; · iexact HW
    iintro !> %e' HF
    iintro %Ψ' Hwand'
    iapply tglWp_unfold
    iintro %σ %ε ⟨Hσ, Hε⟩
    ispecialize HF $$ %σ %ε [Hσ Hε]
    · isplitl [Hσ]; · iexact Hσ
      iexact Hε
    cases htv : e'.toVal? with
    | some v =>
      imod HF with ⟨Hσ', Hε', HΦv⟩
      ihave HwandΨ := Hwand' $$ %v HΦv
      imod HwandΨ with HΨv
      imodintro
      isplitl [Hσ']; · iexact Hσ'
      isplitl [Hε']; · iexact Hε'
      iexact HΨv
    | none =>
      imod HF with HG
      imodintro
      iapply glm'_strong_mono
      isplitr [HG]
      swap
      · iexact HG
      iintro %ρ %ε₂ HC
      imod HC with ⟨Hσ', Hε', HQρ⟩
      imodintro
      isplitl [Hσ']; · iexact Hσ'
      isplitl [Hε']; · iexact Hε'
      iapply HQρ $$ %Ψ' Hwand'
  iapply HQe $$ %Ψ Hwand

theorem tglWp_wand {E : CoPset} {e : Exp rT} {Φ Ψ : Val rT → IProp GF} :
    iprop(tglWp E e Φ ∗ (∀ v, Φ v -∗ Ψ v)) ⊢@{IProp GF} tglWp E e Ψ := by
  iintro ⟨HW, HΦΨ⟩
  iapply tglWp_strong_mono
  isplitl [HW]; · iexact HW
  iintro %v HΦv
  imodintro
  iapply HΦΨ; iexact HΦv

theorem tglWp_wand_l {E : CoPset} {e : Exp rT} {Φ Ψ : Val rT → IProp GF} :
    iprop((∀ v, Φ v -∗ Ψ v) ∗ tglWp E e Φ) ⊢@{IProp GF} tglWp E e Ψ := by
  iintro ⟨HΦΨ, HW⟩
  iapply tglWp_wand
  isplitl [HW]; · iexact HW
  iexact HΦΨ

theorem fupd_tglWp {E : CoPset} {e : Exp rT} {Φ : Val rT → IProp GF} :
    iprop(|={E}=> tglWp E e Φ) ⊢@{IProp GF} tglWp E e Φ := by
  iintro HW
  iapply tglWp_unfold
  iintro %σ %ε ⟨Hσ, Hε⟩
  cases htv : e.toVal? with
  | some v =>
    have heq : e = Exp.ofVal v := (Exp.ofVal_of_toVal_some htv).symm
    subst heq
    imod HW
    ihave HW' := (BI.equiv_iff.mp tglWp_unfold_value).1 $$ HW
    iapply HW' $$ %σ %ε
    isplitl [Hσ]; · iexact Hσ
    iexact Hε
  | none =>
    imod HW
    ihave HW' := (BI.equiv_iff.mp (tglWp_unfold_step htv)).1 $$ HW
    iapply HW' $$ %σ %ε
    isplitl [Hσ]; · iexact Hσ
    iexact Hε

theorem tglWp_fupd {E : CoPset} {e : Exp rT} {Φ : Val rT → IProp GF} :
    tglWp E e (fun v => iprop(|={E}=> Φ v)) ⊢@{IProp GF} tglWp E e Φ := by
  iintro HW
  iapply tglWp_strong_mono
    (Φ := fun v => iprop(|={E}=> Φ v)) (Ψ := Φ)
  isplitl [HW]; · iexact HW
  iintro %v HΦfupd
  imod HΦfupd
  imodintro
  iexact HΦfupd

theorem tglWp_frame_l {E : CoPset} {e : Exp rT} {R : IProp GF}
    {Φ : Val rT → IProp GF} :
    iprop(R ∗ tglWp E e Φ) ⊢@{IProp GF} tglWp E e (fun v => iprop(R ∗ Φ v)) := by
  iintro ⟨HR, HW⟩
  iapply tglWp_wand
  isplitl [HW]; · iexact HW
  iintro %v HΦv
  isplitr [HΦv]; swap
  · iexact HΦv
  iexact HR

theorem tglWp_frame_r {E : CoPset} {e : Exp rT} {R : IProp GF}
    {Φ : Val rT → IProp GF} :
    iprop(tglWp E e Φ ∗ R) ⊢@{IProp GF} tglWp E e (fun v => iprop(Φ v ∗ R)) := by
  iintro ⟨HW, HR⟩
  iapply tglWp_wand
  isplitl [HW]; · iexact HW
  iintro %v HΦv
  isplitl [HΦv]
  · iexact HΦv
  iexact HR

theorem tglWp_frame_wand {E : CoPset} {e : Exp rT} {R : IProp GF}
    {Φ : Val rT → IProp GF} :
    iprop(R ∗ tglWp E e (fun v => iprop(R -∗ Φ v))) ⊢@{IProp GF} tglWp E e Φ := by
  iintro ⟨HR, HW⟩
  iapply (tglWp_wand (Φ := fun v => iprop(R ∗ (R -∗ Φ v))) (Ψ := Φ))
  isplitl [HR HW]
  · iapply (tglWp_frame_l (R := R) (Φ := fun v => iprop(R -∗ Φ v)))
    isplitl [HR]; · iassumption
    iexact HW
  iintro %v ⟨HRv, HW'⟩
  iapply HW' $$ HRv

theorem tglWp_mono {E : CoPset} {e : Exp rT} {Φ Ψ : Val rT → IProp GF}
    (HΦ : ∀ v, Φ v ⊢@{IProp GF} Ψ v) :
    tglWp E e Φ ⊢@{IProp GF} tglWp E e Ψ := by
  iintro HW
  letI : NonExpansive (fun e' => tglWp E e' Ψ) :=
    nonExpansive_of_discrete_leibniz _
  iapply (tglWp_ind_simple (E := E) (Φ := Φ) (Q := fun e' => tglWp E e' Ψ))
  swap
  · iexact HW
  iintro !> %e' HF
  iapply tglWp_unfold
  iintro %σ %ε ⟨Hσ, Hε⟩
  ispecialize HF $$ %σ %ε [Hσ Hε]
  · isplitl [Hσ]; · iexact Hσ
    iexact Hε
  cases htv : e'.toVal? with
  | some v =>
    imod HF with ⟨Hσ', Hε', HΦv⟩
    imodintro
    isplitl [Hσ']; · iexact Hσ'
    isplitl [Hε']; · iexact Hε'
    iapply HΦ
    iexact HΦv
  | none =>
    iexact HF

/-! ## Bind -/

theorem tglWp_bind {K : Ectx rT} {E : CoPset} {e : Exp rT} {Φ : Val rT → IProp GF} :
    tglWp E e (fun v => tglWp E (K.fill (Exp.ofVal v)) Φ) ⊢@{IProp GF}
      tglWp E (K.fill e) Φ := by
  iintro HW
  letI : NonExpansive (fun e' => tglWp E (K.fill e') Φ) :=
    nonExpansive_of_discrete_leibniz _
  iapply (tglWp_ind_simple (E := E)
    (Φ := fun v => tglWp E (K.fill (Exp.ofVal v)) Φ)
    (Q := fun e' => tglWp E (K.fill e') Φ))
  swap; · iexact HW
  iintro !> %e' HF
  cases htv : e'.toVal? with
  | some v =>
    have heq : e' = Exp.ofVal v := (Exp.ofVal_of_toVal_some htv).symm
    subst heq
    -- Bridge HF to its reduced form via iassert + the Lean-level equality.
    have heqV := tglWpPre_eq_value (wp := fun _ e'' _ => tglWp E (K.fill e'') Φ)
                  (E := E) (v := v)
                  (Φ := fun w => tglWp E (K.fill (Exp.ofVal w)) Φ)
    ihave HF_red : iprop(∀ (σ : State rT) (ε : ENNReal),
        (stateInterp σ ∗ errInterp (rT := rT) ε) -∗
          |={E}=> stateInterp σ ∗ errInterp (rT := rT) ε ∗ tglWp E (K.fill (Exp.ofVal v)) Φ)
      $$ [HF]
    · rw [← heqV]; iexact HF
    iapply tglWp_of_frame_fupd
    iexact HF_red
  | none =>
    have hKtv : (K.fill e').toVal? = none :=
      Exp.toVal?_eq_none.mpr fun hKv =>
        (Exp.toVal?_eq_none.mp htv) (Ectx.fill_isValue hKv)
    have heqS := tglWpPre_eq_step (wp := fun _ e'' _ => tglWp E (K.fill e'') Φ)
                  (E := E) (e := e')
                  (Φ := fun w => tglWp E (K.fill (Exp.ofVal w)) Φ) htv
    ihave HF_red : iprop(∀ (σ : State rT) (ε : ENNReal),
        (stateInterp σ ∗ errInterp (rT := rT) ε) -∗
          |={E, ∅}=> glm' e' σ ε (fun ρ ε₂ =>
            iprop(|={∅, E}=>
              stateInterp ρ.state ∗ errInterp (rT := rT) ε₂ ∗ tglWp E (K.fill ρ.expr) Φ)))
      $$ [HF]
    · rw [← heqS]; iexact HF
    have key : tglWp E (K.fill e') Φ =
               iprop(∀ (σ' : State rT) (ε' : ENNReal),
                 (stateInterp σ' ∗ errInterp (rT := rT) ε') -∗
                   |={E, ∅}=> glm' (K.fill e') σ' ε' (fun ρ ε₂ =>
                     iprop(|={∅, E}=>
                       stateInterp ρ.state ∗ errInterp (rT := rT) ε₂ ∗ tglWp E ρ.expr Φ))) :=
      tglWp_unfold_step hKtv
    iapply (BI.equiv_iff.mp key).2
    iintro %σ %ε ⟨Hσ, Hε⟩
    ispecialize HF_red $$ %σ %ε [Hσ Hε]
    · isplitl [Hσ]; · iexact Hσ
      iexact Hε
    imod HF_red
    imodintro
    iapply (glm'_bind (K := K) (e := e') (σ := σ) (ε := ε)
            (Z := fun ρ ε₂ => iprop(|={∅, E}=>
              stateInterp ρ.state ∗ errInterp (rT := rT) ε₂ ∗ tglWp E ρ.expr Φ)))
    iexact HF_red

theorem tglWp_bind_value {K : Ectx rT} {E : CoPset} {v : Val rT} {Φ : Val rT → IProp GF} :
    tglWp E (Exp.ofVal v) (fun v' => tglWp E (K.fill (Exp.ofVal v')) Φ) ⊢@{IProp GF}
      tglWp E (K.fill (Exp.ofVal v)) Φ := by
  iintro HW
  iapply tglWp_unfold
  iintro %σ %ε ⟨Hσ, Hε⟩
  ihave HW' := (BI.equiv_iff.mp tglWp_unfold_value).1 $$ HW
  ispecialize HW' $$ %σ %ε [Hσ Hε]
  · isplitl [Hσ]; · iexact Hσ
    iexact Hε
  cases htv : (K.fill (Exp.ofVal v)).toVal? with
  | some v' =>
    have heq : K.fill (Exp.ofVal v) = Exp.ofVal v' := (Exp.ofVal_of_toVal_some htv).symm
    have key : tglWp E (K.fill (Exp.ofVal v)) Φ =
               iprop(∀ (σ' : State rT) (ε' : ENNReal),
                 (stateInterp σ' ∗ errInterp (rT := rT) ε') -∗
                   |={E}=> stateInterp σ' ∗ errInterp (rT := rT) ε' ∗ Φ v') := by
      rw [heq]; exact tglWp_unfold_value
    imod HW' with ⟨Hσ', Hε', HInner⟩
    ihave HInner' := (BI.equiv_iff.mp key).1 $$ HInner
    iapply HInner' $$ %σ %ε
    isplitl [Hσ']; · iexact Hσ'
    iexact Hε'
  | none =>
    imod HW' with ⟨Hσ', Hε', HInner⟩
    ihave HInner' := (BI.equiv_iff.mp (tglWp_unfold_step htv)).1 $$ HInner
    iapply HInner' $$ %σ %ε
    isplitl [Hσ']; · iexact Hσ'
    iexact Hε'

end ErisWpGS
end TotalEris
end ProbLang
