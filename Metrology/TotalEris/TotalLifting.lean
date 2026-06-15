module

public import Metrology.TotalEris.TotalWeakestpre

@[expose] public section

open Std Iris Iris.Std Iris.BI Iris.ProofMode OFE COFE ProbLang
open scoped ENNReal

namespace ProbLang


variable {rT : Type _} [ProbLang.ProbLangℝ rT]

namespace TotalEris
namespace ErisWpGS

variable {GF : BundledGFunctors} [ErisWpGS (rT := rT) GF]

/-! # Total-WP lifting lemmas

Port of `clutch/theories/eris/total_lifting.v`. These let us prove
`tgl_wp` triples by exhibiting an appropriate `glm` coupling. Mirrors
the partial-WP lifting in `Metrology/TotalEris/Lifting.lean`. -/

-- omit [Countable rT] in
/-- Lift a `glm`-shaped predicate into `tgl_wp`. Rocq:
`twp_lift_step_fupd_glm`. -/
theorem twp_lift_step_fupd_glm {E : CoPset} {Φ : Val rT → IProp GF} {e₁ : Exp rT}
    (hv : e₁.toVal? = none) :
    iprop(∀ (σ₁ : State rT) (ε₁ : ENNReal),
      (stateInterp σ₁ ∗ errInterp (rT := rT) ε₁) -∗
        |={E, ∅}=> glm' e₁ σ₁ ε₁ (fun ρ ε₂ =>
          iprop(|={∅, E}=>
            stateInterp ρ.state ∗ errInterp (rT := rT) ε₂ ∗ tglWp E ρ.expr Φ))) ⊢@{IProp GF}
      tglWp E e₁ Φ := by
  iintro HG
  iapply tglWp_unfold
  unfold tglWpPre
  iintro %σ %ε ⟨Hσ, Hε⟩
  rw [hv]
  iapply HG $$ %σ %ε
  isplitl [Hσ]; · iexact Hσ
  iexact Hε

/-- **Generic single-step lifting**, parametrised by an arbitrary support family
`R σ₁ : Cfg rT → Prop`. The prover supplies (i) measurability of each support
`{ρ | R σ₁ ρ}` and (ii) a **`Concentrated`** certificate — `primStep ⟨e₁,σ₁⟩` lives
on that support. The continuation is then quantified over `R σ₁`, error-free.

This replaces the atomicity dependency in the critical path with the more general
"concentrated on a measurable operational support" — the unary-lifting view. The
atomic case (`twp_lift_step_fupd`) is the instance `R := Possible`; a future
continuous sampler is the instance `R := reach`, with the `Concentrated` certificate
from `concentratedOn_map`. -/
theorem twp_lift_step_fupd_gen {E : CoPset} {Φ : Val rT → IProp GF} {e₁ : Exp rT}
    (hv : e₁.toVal? = none)
    (R : State rT → Cfg rT → Prop)
    (hRmeas : ∀ σ₁, MeasurableSet {ρ | R σ₁ ρ})
    (hconc : ∀ σ₁, Concentrated (primStep ⟨e₁, σ₁⟩) {ρ | R σ₁ ρ}) :
    iprop(∀ (σ₁ : State rT), stateInterp σ₁ -∗ |={E, ∅}=>
      (⌜Reducible e₁ σ₁⌝) ∗
      ∀ (e₂ : Exp rT) (σ₂ : State rT),
        (⌜R σ₁ (⟨e₂, σ₂⟩ : Cfg rT)⌝) -∗
        |={∅}=> |={∅, E}=>
          stateInterp σ₂ ∗ tglWp E e₂ Φ) ⊢@{IProp GF}
      tglWp E e₁ Φ := by
  iintro H
  iapply twp_lift_step_fupd_glm hv
  iintro %σ₁ %ε₁ ⟨Hσ, Hε⟩
  imod H $$ %σ₁ Hσ with ⟨%Hred, HCont⟩
  imodintro
  iapply glm'_prim_step
  iexists (R σ₁), 0, (fun _ => ε₁), ε₁
  isplitr; · ipureintro; exact Hred
  isplitr; · ipureintro; exact hRmeas σ₁
  isplitr; · ipureintro; intro _; exact _root_.le_refl _
  isplitr
  · ipureintro
    -- `ε₁ * primStep(univ) ≤ ε₁ * 1 = ε₁` for the sub-probability measure `primStep`.
    rw [zero_add, MeasureTheory.lintegral_const]
    calc ε₁ * primStep ⟨e₁, σ₁⟩ Set.univ
        ≤ ε₁ * 1 := by gcongr; exact primStep_univ_le_one _
      _ = ε₁ := mul_one ε₁
  -- `Pgl 0 R primStep`: the support `{R σ₁}` is co-null — exactly the
  -- `Concentrated` certificate, bridged via `Pgl.of_concentrated`.
  isplitr
  · ipureintro
    exact Pgl.of_concentrated (hconc σ₁)
  iintro %ρ %HR
  ispecialize HCont $$ %ρ.expr %ρ.state %HR
  imod HCont with HC
  imodintro
  iright
  imod HC with ⟨Hσ', HW⟩
  imodintro
  isplitl [Hσ']
  · iexact Hσ'
  isplitl [Hε]
  · iexact Hε
  iexact HW

/-- Lift a step rule that doesn't need an `err_interp` change. The **atomic
driver**: instantiates the generic `twp_lift_step_fupd_gen` with the atom support
`R := Possible · (primStep …)`, discharging measurability via the countable-atoms
proof (`measurableSet_primStep_support`) and concentration via `primStep_atomic`.

Rocq: `twp_lift_step_fupd`. -/
theorem twp_lift_step_fupd {E : CoPset} {Φ : Val rT → IProp GF} {e₁ : Exp rT}
    (hv : e₁.toVal? = none) :
    iprop(∀ (σ₁ : State rT), stateInterp σ₁ -∗ |={E, ∅}=>
      (⌜Reducible e₁ σ₁⌝) ∗
      ∀ (e₂ : Exp rT) (σ₂ : State rT),
        (⌜Possible (⟨e₂, σ₂⟩ : Cfg rT) (primStep ⟨e₁, σ₁⟩)⌝) -∗
        |={∅}=> |={∅, E}=>
          stateInterp σ₂ ∗ tglWp E e₂ Φ) ⊢@{IProp GF}
      tglWp E e₁ Φ :=
  twp_lift_step_fupd_gen hv
    (fun σ₁ ρ => Possible ρ (primStep ⟨e₁, σ₁⟩))
    (fun σ₁ => by
      have hset : {ρ : Cfg rT | Possible ρ (primStep ⟨e₁, σ₁⟩)}
          = {ρ | 0 < primStep ⟨e₁, σ₁⟩ {ρ}} := Set.ext fun ρ => possible_iff_pos
      rw [hset]; exact measurableSet_primStep_support e₁ σ₁)
    (fun σ₁ => by
      have hset : {ρ : Cfg rT | Possible ρ (primStep ⟨e₁, σ₁⟩)}
          = {ρ | 0 < primStep ⟨e₁, σ₁⟩ {ρ}} := Set.ext fun ρ => possible_iff_pos
      rw [hset]; exact (primStep_atomic e₁ σ₁).concentrated_atoms)

/-- Lift an atomic-step (post-condition delivered on the value
of the stepped expression). Rocq: `twp_lift_atomic_step_fupd`. -/
theorem twp_lift_atomic_step_fupd {E₁ : CoPset} {Φ : Val rT → IProp GF} {e₁ : Exp rT}
    (hv : e₁.toVal? = none) :
    iprop(∀ (σ₁ : State rT), stateInterp σ₁ -∗ |={E₁}=>
      (⌜Reducible e₁ σ₁⌝) ∗
      ∀ (e₂ : Exp rT) (σ₂ : State rT),
        (⌜Possible (⟨e₂, σ₂⟩ : Cfg rT) (primStep ⟨e₁, σ₁⟩)⌝) -∗ |={E₁}=>
          stateInterp σ₂ ∗
          iprop(match e₂.toVal? with
                | some v => Φ v
                | none => iprop(False : IProp GF)))
      ⊢@{IProp GF} tglWp E₁ e₁ Φ := by
  iintro H
  iapply (twp_lift_step_fupd hv)
  iintro %σ₁ Hσ
  imod H $$ %σ₁ Hσ with ⟨%Hred, HCont⟩
  imod (BIFUpdate.subset (E1 := E₁) (E2 := ∅) Std.LawfulSet.empty_subset)
    with Hclose
  imodintro
  isplitr; · ipureintro; exact Hred
  iintro %e₂ %σ₂ %Hstep
  imodintro
  imod Hclose
  ispecialize HCont $$ %e₂ %σ₂ %Hstep
  imod HCont with ⟨Hσ', HΦv⟩
  imodintro
  isplitl [Hσ']; · iexact Hσ'
  cases htv : e₂.toVal? with
  | some v =>
    iapply (tglWp_value_of_toVal htv)
    iexact HΦv
  | none =>
    iexfalso
    iexact HΦv

/-- Lift a pure (state-preserving, possibly-nondeterministic) reduction.
Rocq: `twp_lift_pure_step`. -/
theorem twp_lift_pure_step {E : CoPset} {Φ : Val rT → IProp GF} {e₁ : Exp rT}
    (hv : e₁.toVal? = none)
    (Hsafe : ∀ σ₁, Reducible e₁ σ₁)
    (Hstep : ∀ σ₁ e₂ σ₂, Possible (⟨e₂, σ₂⟩ : Cfg rT) (primStep ⟨e₁, σ₁⟩) → σ₂ = σ₁) :
    iprop(|={E}=>
      ∀ (e₂ : Exp rT) (σ : State rT),
        (⌜Possible (⟨e₂, σ⟩ : Cfg rT) (primStep ⟨e₁, σ⟩)⌝) -∗
        tglWp E e₂ Φ) ⊢@{IProp GF}
      tglWp E e₁ Φ := by
  iintro H
  iapply (twp_lift_step_fupd hv)
  iintro %σ₁ Hσ
  imod H with H
  imod (BIFUpdate.subset (E1 := E) (E2 := ∅) Std.LawfulSet.empty_subset)
    with Hclose
  imodintro
  isplitr; · ipureintro; exact Hsafe σ₁
  iintro %e₂ %σ₂ %Hstep'
  imodintro
  imod Hclose
  imodintro
  cases Hstep _ _ _ Hstep'
  isplitl [Hσ]; · iexact Hσ
  iapply H; ipureintro; exact Hstep'

/-- Single deterministic pure step. Rocq: `twp_lift_pure_det_step`. -/
theorem twp_lift_pure_det_step {E : CoPset} {Φ : Val rT → IProp GF} {e₁ e₂ : Exp rT}
    (hv : e₁.toVal? = none)
    (Hsafe : ∀ σ₁, Reducible e₁ σ₁)
    (Hpuredet : ∀ σ₁ e₂' σ₂, Possible (⟨e₂', σ₂⟩ : Cfg rT) (primStep ⟨e₁, σ₁⟩) →
      σ₂ = σ₁ ∧ e₂' = e₂) :
    iprop(|={E}=> tglWp E e₂ Φ) ⊢@{IProp GF} tglWp E e₁ Φ := by
  iintro H
  iapply (twp_lift_pure_step hv Hsafe
    (fun σ e₂' σ₂ hstep => (Hpuredet σ e₂' σ₂ hstep).1))
  imod H with H
  imodintro
  iintro %e₂' %σ %Hstep
  obtain ⟨_, heq⟩ := Hpuredet σ e₂' σ Hstep
  subst heq
  iexact H

/-! ## Head-step bridges

The primitive WP laws prefer `headStep` over `primStep` because head steps
are easier to discriminate (no ambient context). The bridges below convert
between the two views. -/

/-- Atomic-step lifting via `headStep`. Rocq: `twp_lift_atomic_head_step`. -/
theorem twp_lift_atomic_head_step {E : CoPset} {Φ : Val rT → IProp GF} {e₁ : Exp rT}
    (hv : e₁.toVal? = none) :
    iprop(∀ (σ₁ : State rT), stateInterp σ₁ -∗ |={E}=>
      (⌜HeadReducible e₁ σ₁⌝) ∗
      ∀ (e₂ : Exp rT) (σ₂ : State rT),
        (⌜Possible (⟨e₂, σ₂⟩ : Cfg rT) (headStep ⟨e₁, σ₁⟩)⌝) -∗ |={E}=>
          stateInterp σ₂ ∗
          iprop(match e₂.toVal? with
                | some v => Φ v
                | none => iprop(False : IProp GF)))
      ⊢@{IProp GF} tglWp E e₁ Φ := by
  iintro H
  iapply (twp_lift_atomic_step_fupd hv)
  iintro %σ₁ Hσ
  ispecialize H $$ %σ₁ Hσ
  imod H with ⟨%Hhred, HCont⟩
  imodintro
  isplitr
  · ipureintro
    exact reducible_of_headReducible Hhred
  iintro %e₂ %σ₂ %Hpstep
  have heq : primStep ⟨e₁, σ₁⟩ = headStep ⟨e₁, σ₁⟩ := by
    exact primStep_eq_headStep Hhred
  have hpos : Possible (⟨e₂, σ₂⟩ : Cfg rT) (headStep ⟨e₁, σ₁⟩) := heq ▸ Hpstep
  iapply HCont $$ %e₂ %σ₂ %hpos

/-- Pure-deterministic head-step lifting. Rocq: `twp_lift_pure_det_head_step`. -/
theorem twp_lift_pure_det_head_step {E : CoPset} {Φ : Val rT → IProp GF} {e₁ e₂ : Exp rT}
    (hv : e₁.toVal? = none)
    (Hsafe : ∀ σ₁, ∃ ρ : Cfg rT, Possible ρ (headStep ⟨e₁, σ₁⟩))
    -- How is this used? Can it be changed to be the Dirac critereon?
    (Hdet : ∀ σ₁ e₂' σ₂, Possible (⟨e₂', σ₂⟩ : Cfg rT) (headStep ⟨e₁, σ₁⟩) → σ₂ = σ₁ ∧ e₂' = e₂) :
    iprop(|={E}=> tglWp E e₂ Φ) ⊢@{IProp GF} tglWp E e₁ Φ := by
  iapply twp_lift_pure_det_step hv
    (Hsafe := fun σ => Reducible.of_head ((Hsafe σ).elim fun _ hρ => hρ.ne_zero))
  intros σ e₂' σ₂ hp
  have heq : primStep ⟨e₁, σ⟩ = headStep ⟨e₁, σ⟩ :=
    primStep_eq_headStep ((Hsafe σ).elim fun _ hρ => hρ.ne_zero)
  exact Hdet σ e₂' σ₂ (heq ▸ hp)

/-! ## `PureExec_discrete` integration -/

/-- From a single `PureStep_discrete e₁ e₂` (deterministic, state-preserving, safe),
take one step. Used by the `n+1` case of `twp_pure_step_fupd`. -/
theorem twp_lift_pure_det_step_of_pureStep
    {E : CoPset} {Φ : Val rT → IProp GF} {e₁ e₂ : Exp rT}
    (h : PureStep e₁ e₂) :
    iprop(|={E}=> tglWp E e₂ Φ) ⊢@{IProp GF} tglWp E e₁ Φ := by
  -- The first reducibility witness gives us a non-value status.
  have hv : e₁.toVal? = none := Exp.toVal?_eq_none.mpr <| val_stuck <| h.safe default
  iapply twp_lift_pure_det_step hv h.safe
  intros σ e₂' σ₂ hp
  have hpt := h.det σ
  by_contra hne
  have hother : (⟨e₂', σ₂⟩ : Cfg rT) ≠ ⟨e₂, σ⟩ := by
    intro heq
    cases heq
    exact hne ⟨rfl, rfl⟩
  -- Determinacy: `primStep ⟨e₁,σ⟩ = dirac ⟨e₂,σ⟩`, so a positive-mass outcome must
  -- *be* `⟨e₂,σ⟩` (via the measurability-free `dirac_singleton_pos'`), contradicting
  -- `hother`.
  rw [hpt, possible_iff_pos, dirac_singleton_pos'] at hp
  exact hother hp.symm
  -- exact absurd (hsum_le.trans htot) (_root_.not_le.mpr hsum_gt)

theorem twp_pure_step_fupd
    {E : CoPset} {Φ : Val rT → IProp GF} {n : ℕ} {e₁ e₂ : Exp rT}
    (φ : Prop) [HEx : PureExec φ n e₁ e₂] (Hφ : φ) :
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
    ihave Hih := ih hrest
    iapply Hih
    iexact H

end ErisWpGS
end TotalEris
end ProbLang
