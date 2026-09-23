module

public import Metrology.Approxis.AppWeakestpre
public import Metrology.ProbLang.Atomic
import Metrology.ProbLang.Syntax.Notation

@[expose] public section


/-! # `OpenInv e`: the logical-atomicity predicate enabling mask-shift around evaluating `e`. -/

open Std Iris Iris.Std Iris.BI Iris.ProofMode OFE COFE ProbLang ProbLang.ApproxisWpGS

namespace ProbLang

-- For the Approxis layer, carry the abstract real type `rT` as a section variable.


variable {rT : Type _} [ProbLang.ProbLangℝ rT]

/-- `OpenInv e`: `e` can be evaluated inside a `|={E1, E2}=>` mask-shift, with
the mask closed back in the post. -/
def OpenInv (e : Exp rT) : Prop :=
  ∀ {GF : BundledGFunctors} [ApproxisWpGS (rT := rT) GF] {E1 E2 : CoPset} {Φ : Val rT → IProp
    GF}, iprop%
    (|={E1, E2}=> wp E2 e (fun v => iprop% |={E2, E1}=> Φ v)) ⊢ wp E1 e Φ

namespace OpenInv

theorem fupd_open_cont {GF : BundledGFunctors} [ApproxisWpGS (rT := rT) GF] {E1 E2 E3 : CoPset}
    {P Q : IProp GF}
    (h : P ⊢ |={E2, E3}=> Q) : iprop(|={E1, E2}=> P) ⊢ |={E1, E3}=> Q := fupd_elim h

theorem fupd_open_frame_cont {GF : BundledGFunctors} [ApproxisWpGS (rT := rT) GF]
    {E1 E2 E3 : CoPset}
    {P R Q : IProp GF} (h : P ∗ R ⊢ |={E2, E3}=> Q) : (|={E1, E2}=> P) ∗ R ⊢ |={E1, E3}=> Q :=
  fupd_frame_right.trans (fupd_elim h)

theorem specCoupl_atomic_bridge_some {hlc : HasLC} {GF : BundledGFunctors}
    [ApproxisWpGS (rT := rT) GF] [InvGS_gen hlc GF]
    {E1 E2 : CoPset}
    {σ₁ : State rT} {e₁' : Exp rT} {σ₁' : State rT} {ε₁ : ENNReal}
    {Φ : Val rT → IProp GF} {v : Val rT} :
    iprop% specCoupl ∅ σ₁ e₁' σ₁' ε₁ (fun σ₂ ρ' ε₂ => iprop%
        |={∅, E2}=> stateInterp (rT := rT) σ₂ ∗ SpecUpdateGS.specInterp (rT :=
          rT) ρ' ∗ errInterp (rT := rT) ε₂ ∗ (|={E2, E1}=> Φ v))
      ⊢ specCoupl ∅ σ₁ e₁' σ₁' ε₁ (fun σ₂ ρ' ε₂ => iprop%
        |={∅, E1}=> stateInterp (rT := rT) σ₂ ∗ SpecUpdateGS.specInterp (rT :=
          rT) ρ' ∗ errInterp (rT := rT) ε₂ ∗ Φ v) := by
  iintro HSC
  iapply specCoupl_mono_spatial
  iframe
  iintro %σ₂ %ρ' %ε₂ HBody
  imod HBody with ⟨Hσ, Hs, Hε, HΦc⟩
  imod HΦc with HΦ
  iframe

theorem specCoupl_atomic_bridge_none {GF : BundledGFunctors} [ApproxisWpGS (rT := rT) GF]
    {e : Exp rT} (h : Atomic' e) {E1 E2 : CoPset}
    {σ₁ : State rT} {e₁' : Exp rT} {σ₁' : State rT} {ε₁ : ENNReal}
    {Φ : Val rT → IProp GF} :
    specCoupl ∅ σ₁ e₁' σ₁' ε₁ (fun σ₂ ρ' ε₂ =>
        progCoupl e σ₂ ρ'.expr ρ'.state ε₂
          (fun e₃ σ₃ e₃' σ₃' ε₃ => iprop%
            ▷ specCoupl ∅ σ₃ e₃' σ₃' ε₃ (fun σ₄ ρ'' ε₄ => iprop%
              |={∅, E2}=>
                stateInterp (rT := rT) σ₄ ∗ SpecUpdateGS.specInterp (rT := rT) ρ'' ∗ errInterp (rT
                  := rT) ε₄ ∗
                  wp E2 e₃ (fun v => iprop(|={E2, E1}=> Φ v)))))
      ⊢@{IProp GF}
    specCoupl ∅ σ₁ e₁' σ₁' ε₁ (fun σ₂ ρ' ε₂ =>
        progCoupl e σ₂ ρ'.expr ρ'.state ε₂
          (fun e₃ σ₃ e₃' σ₃' ε₃ =>
            iprop(▷ specCoupl ∅ σ₃ e₃' σ₃' ε₃ (fun σ₄ ρ'' ε₄ =>
              iprop(|={∅, E1}=>
                stateInterp (rT := rT) σ₄ ∗ SpecUpdateGS.specInterp (rT := rT) ρ'' ∗ errInterp (rT
                  := rT) ε₄ ∗
                  wp E1 e₃ Φ))))) := by
  iintro _
  iapply specCoupl_mono_spatial
  iframe
  iintro %σ₂ %ρ' %ε₂ HBody
  iapply (progCoupl_mono (σ₁ := σ₂) (e₁' := ρ'.expr) (σ₁' := ρ'.state) (ε := ε₂))
  isplitr
  swap
  · iapply (progCoupl_strengthen
      (e₁ := e) (σ₁ := σ₂) (e₁' := ρ'.expr) (σ₁' := ρ'.state) (ε := ε₂)
      (S := {ρ : Cfg rT | ρ.1.isValue}) Cfg.isValue_measurableSet (h σ₂))
    isplitr
    swap
    · iexact HBody
    iintro !> %_ %_ %_ %_ !>
    iapply specCoupl_err_ge_1
    exact _root_.le_refl _
  iintro %e₃ %σ₃ %e₃' %σ₃' %ε₃ ⟨%Hreach, HInner⟩
  rcases Hreach with he₃val | Hε1
  · -- `⟨e₃, σ₃⟩` lies in the value set, which *is* the fact we wanted.
    iintro !>
    iapply (specCoupl_bind (E2 := ∅) Std.LawfulSet.subset_refl)
    isplitr [HInner]
    swap
    · iexact HInner
    iintro %σ₄ %ρ'' %ε₄ HBody4
    iapply fupd_specCoupl
    have Hbody : iprop(stateInterp (rT := rT) σ₄ ∗ SpecUpdateGS.specInterp (rT := rT) ρ'' ∗
      errInterp (rT := rT) ε₄ ∗
        wp E2 e₃ (fun v => iprop(|={E2, E1}=> Φ v)))
        ⊢@{IProp GF}
        iprop(|={E2, ∅}=> specCoupl ∅ σ₄ ρ''.expr ρ''.state ε₄
          (fun σ₄' ρ''' ε₄' =>
            iprop(|={∅, E1}=>
              stateInterp (rT := rT) σ₄' ∗ SpecUpdateGS.specInterp (rT := rT) ρ''' ∗ errInterp (rT
                := rT) ε₄' ∗
                wp E1 e₃ Φ))) := by
      iintro ⟨Hσ4, Hs4, Hε4, HW4⟩
      ihave HW4' := (BI.equiv_iff.mp ApproxisWpGS.wp_unfold).1 $$ HW4
      ispecialize HW4' $$ %σ₄ %ρ''.expr %ρ''.state %ε₄ [$]
      irevert HW4'
      refine BI.entails_wand ?_
      refine fupd_open_cont (E1 := E2) (E2 := ∅) (E3 := ∅) ?_
      iintro HSC
      iapply fupd_intro
      iapply specCoupl_mono_spatial
      iframe
      iintro %σ₅ %ρ''' %ε₅ HInnerBody
      cases htv : e₃.toVal? with
      | none => exact absurd ((Exp.toVal?_eq_none).mp htv) (fun nv => nv he₃val)
      | some v' =>
        imod HInnerBody with ⟨Hσ5, Hs5, Hε5, HΦc⟩
        imod HΦc with HΦv
        imodintro
        iframe
        iapply wp_value_of_toVal htv $$ HΦv
    irevert HBody4
    refine BI.entails_wand ?_
    exact fupd_open_cont (E2 := E2) (E3 := ∅) Hbody
  · iintro !>
    iapply specCoupl_err_ge_1
    exact Hε1

/-- Every syntactically atomic expression satisfies `OpenInv`. -/
theorem of_atomic {e : Exp rT} (h : Atomic' e) : OpenInv e := by
  intro GF _ E1 E2 Φ
  iintro HF
  iapply ApproxisWpGS.wp_unfold
  unfold wpPre
  iintro %σ₁ %e₁' %σ₁' %ε₁ Hres
  ihave HFR : iprop(
      (|={E1, E2}=> wp E2 e (fun v => iprop(|={E2, E1}=> Φ v))) ∗
        (stateInterp (rT := rT) σ₁ ∗ SpecUpdateGS.specInterp (rT := rT) ⟨e₁', σ₁'⟩ ∗ errInterp (rT
          := rT) ε₁))
    $$ [HF Hres]
  · isplitl [HF]
    · iexact HF
    iexact Hres
  have Hbody : iprop(
      (wp E2 e (fun v => iprop(|={E2, E1}=> Φ v))) ∗
        (stateInterp (rT := rT) σ₁ ∗ SpecUpdateGS.specInterp (rT := rT) ⟨e₁', σ₁'⟩ ∗ errInterp (rT
          := rT) ε₁))
      ⊢@{IProp GF}
    iprop(|={E2, ∅}=> specCoupl ∅ σ₁ e₁' σ₁' ε₁ (fun σ₂ ρ' ε₂ =>
        match e.toVal? with
        | some v => iprop(|={∅, E1}=>
            stateInterp (rT := rT) σ₂ ∗ SpecUpdateGS.specInterp (rT := rT) ρ' ∗ errInterp (rT :=
              rT) ε₂ ∗ Φ v)
        | none => progCoupl e σ₂ ρ'.expr ρ'.state ε₂
            (fun e₃ σ₃ e₃' σ₃' ε₃ =>
              iprop(▷ specCoupl ∅ σ₃ e₃' σ₃' ε₃ (fun σ₄ ρ'' ε₄ =>
                iprop(|={∅, E1}=>
                  stateInterp (rT := rT) σ₄ ∗ SpecUpdateGS.specInterp (rT := rT) ρ'' ∗ errInterp (rT
                    := rT) ε₄ ∗
                    wp E1 e₃ Φ)))))) := by
    iintro ⟨HW, HresInner⟩
    ihave HW' := (BI.equiv_iff.mp ApproxisWpGS.wp_unfold).1 $$ HW
    ispecialize HW' $$ %σ₁ %e₁' %σ₁' %ε₁ HresInner
    cases htv : e.toVal? with
    | some v =>
      irevert HW'
      refine BI.entails_wand ?_
      refine fupd_open_cont (E1 := E2) (E2 := ∅) (E3 := ∅) ?_
      exact (specCoupl_atomic_bridge_some (v := v)).trans Iris.fupd_intro
    | none =>
      irevert HW'
      refine BI.entails_wand ?_
      refine fupd_open_cont (E1 := E2) (E2 := ∅) (E3 := ∅) ?_
      exact (specCoupl_atomic_bridge_none h).trans Iris.fupd_intro
  irevert HFR
  refine BI.entails_wand ?_
  exact fupd_open_frame_cont (E2 := E2) (E3 := ∅) Hbody

end OpenInv

/-- User-facing WP rule for atomic (or logically-atomic) expressions:
mask-shift around a single step. -/
theorem wp_atomic {GF : BundledGFunctors} [ApproxisWpGS (rT := rT) GF]
    {e : Exp rT} (h : OpenInv e) {E1 E2 : CoPset} {Φ : Val rT → IProp GF} :
    iprop((|={E1, E2}=> wp E2 e (fun v => iprop(|={E2, E1}=> Φ v)))) ⊢@{IProp GF}
      wp E1 e Φ :=
  h

/-! ## Proof-mode support

`wp_atomic` is the theorem; these make the proof mode *find* it. Without the
`ElimModal` instance below, `imod`/`iinv` will not fire on an atomic `wp` and the
lemma has to be applied by hand. `OpenInv` is a plain `Prop`, so it is wrapped in
a class that the concrete redexes register into. -/

/-- Typeclass form of `OpenInv`, so proof-mode instances can discover logical
atomicity by synthesis. -/
class IsOpenInv (e : Exp rT) : Prop where
  out : OpenInv e

section Instances
variable [MeasurableSingletonClass rT]

instance : IsOpenInv (rT := rT) .urand := ⟨OpenInv.of_atomic Atomic.urand'⟩

instance (l : Loc) : IsOpenInv (rT := rT) pl(!#(.loc l)) :=
  ⟨OpenInv.of_atomic (Atomic.load' l)⟩

instance (l : Loc) (v : Val rT) : IsOpenInv (Exp.store pl(#(.loc l)) v.1) :=
  ⟨OpenInv.of_atomic (Atomic.store' l v)⟩

instance (v : Val rT) : IsOpenInv (Exp.alloc v.1) :=
  ⟨OpenInv.of_atomic (Atomic.alloc' v)⟩

instance (z : Int) : IsOpenInv (rT := rT) pl(rand(#(.int z), #(.unit))) :=
  ⟨OpenInv.of_atomic (Atomic.rand_unit' z)⟩

instance (z : Int) (l : Loc) : IsOpenInv (rT := rT) pl(rand(#(.int z), #(.lbl l))) :=
  ⟨OpenInv.of_atomic (Atomic.rand_lbl' z l)⟩

end Instances

/-- `imod`/`iinv` on a mask-shifting update in front of an *atomic* `wp`: the
mask reopens in the post-condition. Rocq's `elim_modal_fupd_wp_atomic`. -/
instance (priority := low) elimModal_fupd_wp_atomic {p : Bool} {io : InOut} {E1 E2 : CoPset} {e :
  Exp rT}
    [h : IsOpenInv e] {GF : BundledGFunctors} [ApproxisWpGS (rT := rT) GF]
    {P : IProp GF} {Φ : Val rT → IProp GF} :
    ElimModal True p io false iprop(|={E1, E2}=> P) P
      (wp E1 e Φ) (wp E2 e (fun v => iprop(|={E2, E1}=> Φ v))) where
  elim_modal _ := (sep_mono_left intuitionisticallyIf_elim).trans <|
    fupd_frame_right.trans <| (BIFUpdate.mono wand_elim_right).trans (wp_atomic h.out)

/-- `iinv` on an *atomic* `wp`: open the invariant, take the step, close it in
the post-condition. iris-lean's `elimAcc_wp_atomic` with `IsOpenInv` in place of
`Language.Atomic`. The closing wand is spatial, so it is carried through the
`wp` by `wp_frame_wand` rather than `wp_wand` (whose continuation here is
persistent). -/
instance (priority := low) elimAcc_wp_atomic {X : Type} {e : Exp rT} [h : IsOpenInv e]
    {GF : BundledGFunctors} [ApproxisWpGS (rT := rT) GF] {Φ : Val rT → IProp GF}
    (E₁ E₂ : CoPset) (α β : X → IProp GF) (γ : X → Option (IProp GF)) :
    ElimAcc True (fupd E₁ E₂) (fupd E₂ E₁) α β γ (wp E₁ e Φ)
      (fun x => wp E₂ e (fun v => iprop(|={E₂}=> β x ∗ (γ x -∗? Φ v)))) where
  elim_acc := by
    dsimp only [accessor]
    iintro %_ Hinner Hacc
    iapply (wp_atomic h.out)
    imod Hacc with ⟨%x, Hα, Hclose⟩
    imodintro
    ispecialize Hinner $$ %x Hα
    iapply ApproxisWpGS.wp_frame_wand
    iframe Hclose
    iapply (ApproxisWpGS.wp_mono (Φ := fun v => iprop(|={E₂}=> β x ∗ (γ x -∗? Φ v))))
    case HΦ =>
      intro v
      iintro Hpost Hcl
      imod Hpost with ⟨Hβ, HΦ⟩
      ispecialize Hcl $$ Hβ
      imod Hcl
      imodintro
      cases γ x with
      | none =>
        dsimp only [BIBase.wandM]
        iexact HΦ
      | some P => iapply HΦ $$ Hcl
    iexact Hinner

/-- `iinv` on a non-atomic `wp` at a fixed mask. -/
instance elimAcc_wp_nonatomic {X : Type} {e : Exp rT}
    {GF : BundledGFunctors} [ApproxisWpGS (rT := rT) GF] {Φ : Val rT → IProp GF}
    (E : CoPset) (α β : X → IProp GF) (γ : X → Option (IProp GF)) :
    ElimAcc True (fupd E E) (fupd E E) α β γ (wp E e Φ)
      (fun x => wp E e (fun v => iprop(|={E}=> β x ∗ (γ x -∗? Φ v)))) where
  elim_acc := by
    dsimp only [accessor]
    iintro %_ Hinner Hacc
    iapply ApproxisWpGS.fupd_wp
    imod Hacc with ⟨%x, Hα, Hclose⟩
    imodintro
    ispecialize Hinner $$ %x Hα
    iapply ApproxisWpGS.wp_fupd
    iapply ApproxisWpGS.wp_frame_wand
    iframe Hclose
    iapply (ApproxisWpGS.wp_mono (Φ := fun v => iprop(|={E}=> β x ∗ (γ x -∗? Φ v))))
    case HΦ =>
      intro v
      iintro Hpost Hcl
      imod Hpost with ⟨Hβ, HΦ⟩
      ispecialize Hcl $$ Hβ
      imod Hcl
      imodintro
      cases γ x with
      | none =>
        dsimp only [BIBase.wandM]
        iexact HΦ
      | some P => iapply HΦ $$ Hcl
    iexact Hinner

end ProbLang
