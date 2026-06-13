module

public import Metrology.TotalEris.Glm
public import Metrology.Iris.Fixpoint
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

/-! # `pgl_wp` — partial-correctness weakest precondition

Port of `clutch/theories/eris/weakestpre.v` `pgl_wp_pre` / `pgl_wp` section.

The Eris partial-correctness WP is the guarded fixpoint of `pglWpPre`, which
walks one program step via `glm` and recurses under a `▷`.

This file ports the **definition** + `unfold` + `value`. Structural lemmas
(`strong_mono`, `bind`, `fupd`) live in a follow-up file once the supporting
`glm` lemmas (`glm_mono_grading`, `glm_bind`, `glm_strong_mono`) are in
place. -/

/-- One unfolding of `pgl_wp`.

`pglWpPre wp E e₁ Φ` unconditionally takes `σ₁`, `ε₁` as inputs and a
state/error resource bundle; the *body* then case-splits on whether `e₁` is
a value:

* If `e₁ = some v`, return `|={E}=> stateInterp σ₁ ∗ errInterp ε₁ ∗ Φ v`
  (the resources flow back unchanged).
* Otherwise, open the fancy update to ∅ and step via `glm`, recursing
  under `▷` to satisfy contractiveness.

This shape (always-quantify, match-inside) mirrors `Metrology/Approxis/AppWeakestpre.lean` `wpPre`,
which is the only structure for which the Iris-Lean `Contractive` instance
proof completes within the default heartbeat budget. It is logically
equivalent to Rocq's top-level `match to_val e1 with ... end`. -/
abbrev pglWpPre [Countable rT] [MeasurableSingletonClass rT]
    (wp : CoPset → Exp rT → (Val rT → IProp GF) → IProp GF)
    (E : CoPset) (e₁ : Exp rT) (Φ : Val rT → IProp GF) : IProp GF :=
  iprop(∀ (σ₁ : State rT) (ε₁ : ENNReal),
    (stateInterp σ₁ ∗ errInterp (rT := rT) ε₁) -∗
      match e₁.toVal? with
      | some v => iprop(|={E}=>
          stateInterp σ₁ ∗ errInterp (rT := rT) ε₁ ∗ Φ v)
      | none => iprop(|={E, ∅}=>
          glm e₁ σ₁ ε₁ (fun ρ ε₂ =>
            iprop(▷ (|={∅, E}=>
              stateInterp ρ.state ∗ errInterp (rT := rT) ε₂ ∗ wp E ρ.expr Φ)))))

/-- The function space the fixpoint operates on. -/
abbrev PglWpType := CoPset → Exp rT → (Val rT → IProp GF) → IProp GF

/-- `pglWpPre` is `Contractive`: the only recursive use of the `wp`
parameter sits under `▷`, justifying the contractive step. -/
instance pglWpPre_contractive [Countable rT] [MeasurableSingletonClass rT] :
    Contractive (pglWpPre (rT := rT) (GF := GF)) where
  distLater_dist := by
    intro n wp wp' Hwp E e Φ
    refine forall_ne fun σ => ?_
    refine forall_ne fun ε => ?_
    refine wand_ne.ne (.of_eq rfl) ?_
    cases htv : e.toVal? with
    | some v => exact .of_eq rfl
    | none =>
      refine BIFUpdate.ne.ne ?_
      refine least_fixpoint_ne_outer (fun Ψ s => ?_) (.of_eq rfl)
      rcases s with ⟨ρ, ε'⟩
      refine or_ne.ne (.of_eq rfl) ?_
      refine or_ne.ne ?_ (.of_eq rfl)
      refine exists_ne fun R => ?_
      refine exists_ne fun ε₁ => ?_
      refine exists_ne fun X₂ => ?_
      refine exists_ne fun r => ?_
      refine sep_ne.ne (.of_eq rfl) ?_
      refine sep_ne.ne (.of_eq rfl) ?_
      refine sep_ne.ne (.of_eq rfl) ?_
      refine sep_ne.ne (.of_eq rfl) ?_
      refine forall_ne fun ρ' => ?_
      refine wand_ne.ne (.of_eq rfl) ?_
      refine BIFUpdate.ne.ne ?_
      refine or_ne.ne (.of_eq rfl) ?_
      apply Contractive.distLater_dist (f := later)
      intro m Hm
      refine BIFUpdate.ne.ne ?_
      refine sep_ne.ne (.of_eq rfl) ?_
      refine sep_ne.ne (.of_eq rfl) ?_
      exact DistLater.dist_lt (Hwp · · E ρ'.expr Φ) Hm

/-- The Eris partial-correctness weakest precondition. -/
noncomputable def pglWp [Countable rT] [MeasurableSingletonClass rT]
    (E : CoPset) (e : Exp rT) (Φ : Val rT → IProp GF) : IProp GF :=
  fixpoint (pglWpPre (rT := rT) (GF := GF)) E e Φ

-- omit [Countable rT] [MeasurableSingletonClass rT] in
/-- Fixpoint unfolding for `pglWp`. -/
theorem pglWp_unfold [Countable rT] [MeasurableSingletonClass rT]
    {E : CoPset} {e : Exp rT} {Φ : Val rT → IProp GF} :
    pglWp (GF := GF) E e Φ ≡ pglWpPre (pglWp (rT := rT) (GF := GF)) E e Φ :=
  (fixpoint_unfold ⟨pglWpPre, OFE.ne_of_contractive _⟩) E e Φ

/-! ## Value rules -/

-- omit [Countable rT] [MeasurableSingletonClass rT] in
/-- Value introduction (fupd-flavored). -/
theorem pglWp_value_fupd [Countable rT] [MeasurableSingletonClass rT]
    {E : CoPset} {v : Val rT} {Φ : Val rT → IProp GF} :
    iprop(|={E}=> Φ v) ⊢@{IProp GF} pglWp E (Exp.ofVal v) Φ := by
  iintro HΦ
  iapply pglWp_unfold
  unfold pglWpPre
  iintro %σ %ε ⟨Hσ, Hε⟩
  rw [Exp.toVal?_ofVal]
  imod HΦ with HΦ'
  imodintro
  isplitl [Hσ]; · iexact Hσ
  isplitl [Hε]; · iexact Hε
  iexact HΦ'

-- omit [Countable rT] [MeasurableSingletonClass rT] in
/-- Plain value introduction. -/
theorem pglWp_value [Countable rT] [MeasurableSingletonClass rT]
    {E : CoPset} {v : Val rT} {Φ : Val rT → IProp GF} :
    Φ v ⊢@{IProp GF} pglWp E (Exp.ofVal v) Φ := by
  iintro HΦ
  iapply pglWp_value_fupd
  imodintro
  iexact HΦ

-- omit [Countable rT] [MeasurableSingletonClass rT] in
/-- General value form: from `e.toVal? = some v`, introduce `pglWp E e Φ`
from `Φ v`. -/
theorem pglWp_value_of_toVal [Countable rT] [MeasurableSingletonClass rT]
    {E : CoPset} {e : Exp rT} {v : Val rT}
    {Φ : Val rT → IProp GF} (h : e.toVal? = some v) :
    Φ v ⊢@{IProp GF} pglWp E e Φ := by
  rw [← Exp.ofVal_of_toVal_some h]
  exact pglWp_value

end ErisWpGS
end TotalEris
end ProbLang
