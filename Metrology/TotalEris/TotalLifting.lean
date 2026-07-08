module

public import Metrology.TotalEris.TotalWeakestpre

@[expose] public section

open Std Iris Iris.Std Iris.BI Iris.ProofMode OFE COFE ProbLang
open scoped ENNReal

namespace ProbLang
namespace TotalEris
namespace ErisWpGS

variable {rT : Type _} [ProbLangℝ rT]
variable {GF : BundledGFunctors} [ErisWpGS (rT := rT) GF]

/-! # Total-WP lifting lemmas -/

theorem twp_lift_step_fupd_glm {E : CoPset} {Φ : Val rT → IProp GF} {e₁ : Exp rT}
    (hv : e₁.toVal? = none) : iprop%
    (∀ σ₁ ε₁, stateInterp σ₁ ∗ errInterp (rT := rT) ε₁ -∗
        |={E, ∅}=> glm' e₁ σ₁ ε₁ (fun ρ ε₂ => iprop%
          |={∅, E}=> stateInterp ρ.state ∗ errInterp (rT := rT) ε₂ ∗ tglWp E ρ.expr Φ))
    ⊢@{IProp GF} tglWp E e₁ Φ := by
  iintro HG
  iapply tglWp_unfold
  unfold tglWpPre
  iintro %σ %ε ⟨Hσ, Hε⟩
  simp only [hv]
  iapply HG $$ %σ %ε
  iframe

theorem twp_lift_step_fupd_gen {E : CoPset} {Φ : Val rT → IProp GF} {e₁ : Exp rT}
    (hv : e₁.toVal? = none) (R : State rT → Cfg rT → Prop) (hRmeas : ∀ σ₁, MeasurableSet {ρ | R σ₁ ρ})
    (hconc : ∀ σ₁, Concentrated (primStep ⟨e₁, σ₁⟩) {ρ | R σ₁ ρ}) : iprop%
    (∀ σ₁, stateInterp σ₁ -∗ |={E, ∅}=>
      ⌜Reducible e₁ σ₁⌝ ∗
      ∀ e₂ σ₂, ⌜R σ₁ ⟨e₂, σ₂⟩⌝ -∗ |={∅}=> |={∅, E}=> stateInterp σ₂ ∗ tglWp E e₂ Φ)
    ⊢@{IProp GF} tglWp E e₁ Φ := by
  iintro H
  iapply twp_lift_step_fupd_glm hv
  iintro %σ₁ %ε₁ ⟨Hσ, Hε⟩
  imod H $$ %σ₁ Hσ with ⟨%Hred, HCont⟩
  imodintro
  iapply glm'_prim_step
  iexists (R σ₁), 0, (fun _ => ε₁), ε₁
  have hfr (ρ : Cfg rT) : (fun x ↦ ε₁) ρ ≤ ε₁ := _root_.le_refl _
  specialize hRmeas σ₁
  have hfr' : Pgl 0 (R σ₁) (primStep ⟨e₁, σ₁⟩) := Pgl.of_concentrated (hconc σ₁)
  iframe %Hred %hRmeas %hfr %hfr'
  isplitr
  · ipureintro
    calc  0 + ∫⁻ ρ, (fun _ ↦ ε₁) ρ ∂primStep ⟨e₁, σ₁⟩
        = ∫⁻ ρ, (fun _ ↦ ε₁) ρ ∂primStep ⟨e₁, σ₁⟩ := by grind
      _ = ε₁ * primStep ⟨e₁, σ₁⟩ .univ := by rw [MeasureTheory.lintegral_const]
      _ ≤ ε₁ * 1 := by gcongr; exact primStep_univ_le_one _
      _ = ε₁ := mul_one ε₁
  iintro %ρ %HR
  ispecialize HCont $$ %ρ.expr %ρ.state %HR
  imod HCont with HC
  imodintro
  iright
  imod HC with ⟨Hσ', HW⟩
  iframe

theorem twp_lift_step_fupd {E : CoPset} {Φ : Val rT → IProp GF} {e₁ : Exp rT}
    (hv : e₁.toVal? = none)
    (hatom : ∀ σ₁, IsAtomicSupport (primStep ⟨e₁, σ₁⟩)) : iprop%
    (∀ σ₁, stateInterp σ₁ -∗ |={E, ∅}=>
      ⌜Reducible e₁ σ₁⌝ ∗
      ∀ e₂ σ₂, ⌜Possible ⟨e₂, σ₂⟩ (primStep ⟨e₁, σ₁⟩)⌝ -∗
        |={∅}=> |={∅, E}=> stateInterp σ₂ ∗ tglWp E e₂ Φ)
    ⊢@{IProp GF} tglWp E e₁ Φ :=
  twp_lift_step_fupd_gen hv
    (fun σ₁ ρ => Possible ρ (primStep ⟨e₁, σ₁⟩))
    (fun σ₁ => measurableSet_possible_support)
    (fun σ₁ => by
      have hset : {ρ : Cfg rT | Possible ρ (primStep ⟨e₁, σ₁⟩)}
          = {ρ | 0 < primStep ⟨e₁, σ₁⟩ {ρ}} := Set.ext fun ρ => possible_iff_pos
      rw [hset]; exact (hatom σ₁).concentrated_atoms)

theorem twp_lift_atomic_step_fupd {E₁ : CoPset} {Φ : Val rT → IProp GF} {e₁ : Exp rT}
    (hv : e₁.toVal? = none)
    (hatom : ∀ σ₁, IsAtomicSupport (primStep ⟨e₁, σ₁⟩)) : iprop%
    (∀ σ₁, stateInterp σ₁ -∗ |={E₁}=>
      ⌜Reducible e₁ σ₁⌝ ∗
      ∀ e₂ σ₂, ⌜Possible ⟨e₂, σ₂⟩ (primStep ⟨e₁, σ₁⟩)⌝ -∗ |={E₁}=>
          stateInterp σ₂ ∗ match e₂.toVal? with | some v => Φ v | none => iprop% False)
      ⊢@{IProp GF} tglWp E₁ e₁ Φ := by
  iintro H
  iapply twp_lift_step_fupd hv hatom
  iintro %σ₁ Hσ
  imod H $$ %σ₁ Hσ with ⟨%Hred, HCont⟩
  imod BIFUpdate.subset Std.LawfulSet.empty_subset with Hclose
  imodintro
  iframe %Hred
  iintro %e₂ %σ₂ %Hstep
  imodintro
  imod Hclose with -
  imod HCont $$ %e₂ %σ₂ %Hstep with ⟨Hσ', HΦv⟩
  imodintro
  iframe Hσ'
  cases htv : e₂.toVal? with
  | some v => iapply tglWp_value_of_toVal htv $$ [$]
  | none => iexfalso; iexact HΦv

theorem twp_lift_pure_step {E : CoPset} {Φ : Val rT → IProp GF} {e₁ : Exp rT}
    (hv : e₁.toVal? = none)
    (hatom : ∀ σ₁, IsAtomicSupport (primStep ⟨e₁, σ₁⟩))
    (Hsafe : ∀ σ₁, Reducible e₁ σ₁)
    (Hstep : ∀ σ₁ e₂ σ₂, Possible (⟨e₂, σ₂⟩ : Cfg rT) (primStep ⟨e₁, σ₁⟩) → σ₂ = σ₁) : iprop%
    (|={E}=> ∀ e₂ σ, ⌜Possible ⟨e₂, σ⟩ (primStep ⟨e₁, σ⟩)⌝ -∗ tglWp E e₂ Φ)
    ⊢@{IProp GF} tglWp E e₁ Φ := by
  iintro H
  iapply twp_lift_step_fupd hv hatom
  iintro %σ₁ Hσ
  imod H
  imod BIFUpdate.subset Std.LawfulSet.empty_subset with Hclose
  imodintro
  specialize Hsafe σ₁
  iframe %Hsafe
  iintro %e₂ %σ₂ %Hstep'
  imodintro
  imod Hclose
  imodintro
  cases Hstep _ _ _ Hstep'
  iframe Hσ
  iapply H $$ %_ %_ %Hstep'

theorem twp_lift_pure_det_step {E : CoPset} {Φ : Val rT → IProp GF} {e₁ e₂ : Exp rT}
    (hv : e₁.toVal? = none)
    (hatom : ∀ σ₁, IsAtomicSupport (primStep ⟨e₁, σ₁⟩))
    (Hsafe : ∀ σ₁, Reducible e₁ σ₁)
    (Hpuredet : ∀ σ₁ e₂' σ₂, Possible ⟨e₂', σ₂⟩ (primStep ⟨e₁, σ₁⟩) → σ₂ = σ₁ ∧ e₂' = e₂) : iprop%
    (|={E}=> tglWp E e₂ Φ) ⊢@{IProp GF} tglWp E e₁ Φ := by
  iintro H
  iapply twp_lift_pure_step hv hatom Hsafe (fun σ e₂' σ₂ hstep => (Hpuredet σ e₂' σ₂ hstep).1)
  imod H
  imodintro
  iintro %e₂' %σ %Hstep
  obtain ⟨_, rfl⟩ := Hpuredet σ e₂' σ Hstep
  iexact H

theorem twp_lift_atomic_head_step {E : CoPset} {Φ : Val rT → IProp GF} {e₁ : Exp rT}
    (hv : e₁.toVal? = none) (hlc : e₁.IsLocallyClosed)
    (hd : e₁.decompItem = none := by simp [Exp.decompItem, Exp.toVal?_lit, Exp.toVal?_ofVal])
    (hne : e₁ ≠ .urand := by nofun) : iprop%
    (∀ σ₁, stateInterp σ₁ -∗ |={E}=>
      ⌜HeadReducible e₁ σ₁⌝ ∗
      ∀ e₂ σ₂, ⌜Possible ⟨e₂, σ₂⟩ (headStep ⟨e₁, σ₁⟩)⌝ -∗ |={E}=>
          stateInterp σ₂ ∗ match e₂.toVal? with | some v => Φ v | none => iprop% False)
      ⊢@{IProp GF} tglWp E e₁ Φ := by
  iintro H
  iapply twp_lift_atomic_step_fupd hv
    (fun σ => by rw [primStep_eq_headStep hd]; exact headStep_atomic e₁ σ hne)
  iintro %σ₁ Hσ
  ispecialize H $$ %σ₁ Hσ
  imod H with ⟨%Hhred, HCont⟩
  rw [← primStep_eq_headStep hd]
  replace Hhred := reducible_of_headReducible hlc Hhred
  imodintro
  iframe %Hhred
  iintro %e₂ %σ₂ %Hpstep
  iapply HCont $$ %e₂ %σ₂ %_
  exact Hpstep

theorem twp_lift_pure_det_head_step {E : CoPset} {Φ : Val rT → IProp GF} {e₁ e₂ : Exp rT}
    (hlc : e₁.IsLocallyClosed) (hv : e₁.toVal? = none)
    (Hsafe : ∀ σ₁, ∃ ρ : Cfg rT, Possible ρ (headStep ⟨e₁, σ₁⟩))
    (Hdet : ∀ σ₁ e₂' σ₂, Possible (⟨e₂', σ₂⟩ : Cfg rT) (headStep ⟨e₁, σ₁⟩) → σ₂ = σ₁ ∧ e₂' = e₂)
    (hne : e₁ ≠ .urand := by nofun) :
    iprop(|={E}=> tglWp E e₂ Φ) ⊢@{IProp GF} tglWp E e₁ Φ := by
  have hd : e₁.decompItem = none :=
    Exp.decompItem_none_of_lc_headReducible hlc ((Hsafe default).elim fun _ hρ => hρ.ne_zero)
  iapply twp_lift_pure_det_step hv
    (hatom := fun σ => by rw [primStep_eq_headStep hd]; exact headStep_atomic e₁ σ hne)
    (Hsafe := fun σ => .of_head hlc ((Hsafe σ).elim fun _ hρ => hρ.ne_zero))
  refine fun σ e₂' σ₂ hp => Hdet σ e₂' σ₂ ?_
  rw [← primStep_eq_headStep
    (Exp.decompItem_none_of_lc_headReducible hlc ((Hsafe σ).elim fun _ hρ => hρ.ne_zero))]
  exact hp

/-! ## `PureExec_discrete` integration -/

theorem twp_lift_pure_det_step_of_pureStep {E : CoPset} {Φ : Val rT → IProp GF} {e₁ e₂ : Exp rT}
    (h : PureStep e₁ e₂) : iprop(|={E}=> tglWp E e₂ Φ) ⊢@{IProp GF} tglWp E e₁ Φ := by
  have hv : e₁.toVal? = none := Exp.toVal?_eq_none.mpr <| val_stuck <| h.safe default
  iapply twp_lift_pure_det_step hv
    (hatom := fun σ => by rw [h.det σ]; exact isAtomicSupport_dirac _) (Hsafe := h.safe)
  intros σ e₂' σ₂ hp
  by_contra hne
  rw [h.det σ, possible_iff_pos, dirac_singleton_pos'] at hp
  have hother : (⟨e₂', σ₂⟩ : Cfg rT) ≠ ⟨e₂, σ⟩ := by
    rintro ⟨⟩; exact hne ⟨rfl, rfl⟩
  exact hother hp.symm

/-- `is_lc` discharges `Exp.IsLocallyClosed e` goals. Runtime values and program
fragments are locally closed; the proof is either a kernel computation of the decidable
checker (`Exp.lcb_imp_lc (by rfl)`, for fully concrete closed subterms such as source
`lam`/`fix` bodies), or a structural decomposition bottoming out at an abstract value's
`Val.lc` field (`exact Val.lc _`) or a closedness hypothesis already in context. -/
syntax "is_lc" : tactic
macro_rules
  | `(tactic| is_lc) =>
    `(tactic| first
        | assumption
        | exact Exp.lcb_imp_lc (by rfl)
        | repeat' (first
            | assumption
            | exact Exp.lcb_imp_lc (by rfl)
            | exact Val.lc _
            | exact Exp.IsLocallyClosed.fvar _
            | exact Exp.IsLocallyClosed.lit _
            | exact Exp.IsLocallyClosed.fail
            | exact Exp.IsLocallyClosed.urand
            -- Binders: introduce a fresh opening variable (cofinite, `L := ∅`) and
            -- reduce the `open'` so the body's constructors are exposed to the descent.
            -- `openRec`/`open'` are `@[simp]`, so `simp only` distributes them and
            -- decides the `bvar`→`fvar` substitution; it leaves an `openRec _ _ e₀`
            -- stuck on each opaque leaf `e₀` (a `Val` projection or a closed constant),
            -- cleared below by `← Exp.open_lc`.
            | (refine Exp.IsLocallyClosed.lam ∅ _ ?_ <;> intro _ _ <;>
                 simp only [Exp.open', Exp.openRec])
            | (refine Exp.IsLocallyClosed.fix ∅ _ ?_ <;> intro _ _ <;>
                 simp only [Exp.open', Exp.openRec])
            -- Clear an `openRec k t e₀` stuck on a closed leaf `e₀`: rewrite it back to
            -- `e₀` (the side goal `e₀.IsLocallyClosed` is then closed by the recursion —
            -- `Val.lc` for a value, `lcb_imp_lc (by rfl)` for a closed constant).
            | rw [← Exp.open_lc]
            | apply Exp.IsLocallyClosed.app | apply Exp.IsLocallyClosed.unop
            | apply Exp.IsLocallyClosed.binop | apply Exp.IsLocallyClosed.cond
            | apply Exp.IsLocallyClosed.pair | apply Exp.IsLocallyClosed.fst
            | apply Exp.IsLocallyClosed.snd | apply Exp.IsLocallyClosed.inl
            | apply Exp.IsLocallyClosed.inr | apply Exp.IsLocallyClosed.case
            | apply Exp.IsLocallyClosed.alloc | apply Exp.IsLocallyClosed.load
            | apply Exp.IsLocallyClosed.store | apply Exp.IsLocallyClosed.tape
            | apply Exp.IsLocallyClosed.rand | apply Exp.IsLocallyClosed.scrut))

syntax "is_value" : tactic
macro_rules
  | `(tactic| is_value) =>
    `(tactic| first
        | trivial
        | repeat' (first
            | rfl
            | assumption       -- a value-hood fact already in context (e.g. an abstract
                               -- `Val`'s `v.isValue`), matched up to defeq
            | exact Val.snd _                -- `IsVal v.fst` for an abstract `Val v`
            | exact Val.isValue _            -- `v.fst.isValue` (`Nonempty (IsVal v.fst)`)
            | exact Exp.lcb_imp_lc (by rfl)  -- a closed `(lam/fix …).IsLocallyClosed` subterm
            | exact Val.lc _                 -- a value's closedness, from its `Val.lc` field
            | exact ProbLang.IsVal.lit
            | refine ProbLang.IsVal.lam ?_ | refine ProbLang.IsVal.fix ?_
            | apply ProbLang.IsVal.inl | apply ProbLang.IsVal.inr | apply ProbLang.IsVal.pair
            -- A `(lam/fix …).IsLocallyClosed` side condition whose body is *not* closed
            -- (e.g. it mentions an abstract `Val` projection): introduce the cofinite
            -- opening variable, reduce `open'`, and let the descent below finish — see
            -- `is_lc` for the full rationale (`← Exp.open_lc` clears the `openRec`
            -- stuck on each opaque leaf).
            | (refine Exp.IsLocallyClosed.lam ∅ _ ?_ <;> intro _ _ <;>
                 simp only [Exp.open', Exp.openRec])
            | (refine Exp.IsLocallyClosed.fix ∅ _ ?_ <;> intro _ _ <;>
                 simp only [Exp.open', Exp.openRec])
            | rw [← Exp.open_lc]
            | apply Exp.IsLocallyClosed.fvar
            | apply Exp.IsLocallyClosed.lit | apply Exp.IsLocallyClosed.app
            | apply Exp.IsLocallyClosed.unop | apply Exp.IsLocallyClosed.binop
            | apply Exp.IsLocallyClosed.cond | apply Exp.IsLocallyClosed.pair
            | apply Exp.IsLocallyClosed.fst | apply Exp.IsLocallyClosed.snd
            | apply Exp.IsLocallyClosed.inl | apply Exp.IsLocallyClosed.inr
            | apply Exp.IsLocallyClosed.case | apply Exp.IsLocallyClosed.alloc
            | apply Exp.IsLocallyClosed.load | apply Exp.IsLocallyClosed.store
            | apply Exp.IsLocallyClosed.tape | apply Exp.IsLocallyClosed.rand
            | apply Exp.IsLocallyClosed.scrut
            | refine ⟨?_, ?_⟩    -- split `∧` (binop/unop/scrut side condition)
            | refine ⟨?_⟩))      -- enter `Nonempty (IsVal …)`

theorem twp_pure_step_fupd {E : CoPset} {Φ : Val rT → IProp GF} {n : ℕ} {e₁ e₂ : Exp rT}
    (φ : Prop) [HEx : PureExec φ n e₁ e₂] (Hφ : φ := by is_value) :
    tglWp E e₂ Φ ⊢@{IProp GF} tglWp E e₁ Φ := by
  have Hex := HEx.pure_exec Hφ
  clear HEx
  induction n generalizing e₁ with
  | zero =>
    simp only [nsteps] at Hex
    subst Hex
    iintro H; iexact H
  | succ n ih =>
    obtain ⟨c, hstep, hrest⟩ := Hex
    iintro H
    iapply twp_lift_pure_det_step_of_pureStep hstep
    imodintro
    iapply ih hrest $$ [$]

end ErisWpGS
end TotalEris
end ProbLang
