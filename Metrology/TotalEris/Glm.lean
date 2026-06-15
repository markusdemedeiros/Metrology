module

public import Metrology.Iris.ErrorCredits
public import Metrology.Couplings.AdditiveCouplings
public import Metrology.Couplings.Couplings
public import Metrology.ProbLang.Exec
public import Metrology.ProbLang.Erasable
public import Metrology.ProbLang.Erasure
public import Metrology.ProbLang.CtxStep
public import Metrology.ProbLang.Metatheory
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

/-! # `glm` graded lifting modality -/

@[expose]
def Pgl {α : Type _} [MeasurableSpace α] (ε : ENNReal) (φ : α → Prop)
  (μ : MeasureTheory.Measure α) : Prop :=
  μ {x | ¬ φ x} ≤ ε

namespace Pgl

variable {α β : Type _} [MeasurableSpace α] [MeasurableSpace β]

/-- Monotonicity in the error grade. -/
theorem mono_grading {ε ε' : ENNReal} {φ : α → Prop} {μ : MeasureTheory.Measure α}
    (hε : ε ≤ ε') (h : Pgl ε φ μ) : Pgl ε' φ μ :=
  h.trans hε

/-- Monotonicity in the predicate (covariant). -/
theorem mono_pred {ε : ENNReal} {φ ψ : α → Prop} {μ : MeasureTheory.Measure α}
    (hφψ : ∀ a, φ a → ψ a) (h : Pgl ε φ μ) : Pgl ε ψ μ := by
  refine .trans (MeasureTheory.measure_mono ?_) h
  intro x hx hxφ; exact hx (hφψ x hxφ)

/-- On a countable measurable space, `Pgl 0` holds for the "positive mass"
predicate: a measure assigns zero mass to the set of points it gives zero mass
to (since that set is countable). -/
@[discrete]
theorem zero_positive [Countable α] (μ : MeasureTheory.Measure α) :
    Pgl 0 (fun a => 0 < μ {a}) μ := by
  show μ {x | ¬ (0 < μ {x})} ≤ 0
  have hset : {x : α | ¬ (0 < μ {x})} = {x | μ {x} = 0} := by
    ext x; simp [pos_iff_ne_zero]
  rw [hset]
  have hctble : ({x : α | μ {x} = 0}).Countable :=
    Set.Countable.mono (Set.subset_univ _) Set.countable_univ
  exact ((MeasureTheory.measure_null_iff_singleton hctble).mpr (fun _ hx => hx)).le

/-- `Possible`-native `Pgl 0`: an *atomic* measure assigns zero mass to the
complement of its `Possible`-support. This is the measurability-free /
countability-free reformulation of `zero_positive`: instead of `[Countable α]`
it takes `IsAtomicSupport μ` (the co-support `{x | μ{x}=0}` is null) and only
needs measurable singletons. `IsAtomicSupport μ ↔ Pgl 0 (Possible · μ) μ`, so
this is exactly the atomicity certificate the step rules feed to `glm'`. -/
theorem zero_possible [MeasurableSingletonClass α] {μ : MeasureTheory.Measure α}
    (h : IsAtomicSupport μ) : Pgl 0 (fun a => Possible a μ) μ := by
  show μ {x | ¬ Possible x μ} ≤ 0
  have hset : {x : α | ¬ Possible x μ} = {x | μ {x} = 0} := by
    ext x; simp [possible_iff_pos, pos_iff_ne_zero]
  rw [hset]; exact h.le

end Pgl

/-! ## `ErisWpGS` ghost-state class

Resources required by the Eris weakest precondition: the invariant ghost
state, a state interpretation, and an error-credit interpretation. Mirrors
Rocq `erisWpGS`. No spec side — Eris is a unary logic.  -/

class ErisWpGS (GF : BundledGFunctors) where
  hlc : HasLC
  invGS : InvGS_gen hlc GF
  stateInterp : State rT → IProp GF
  errInterp : ENNReal → IProp GF

attribute [reducible, instance] ErisWpGS.invGS

namespace ErisWpGS
variable {GF : BundledGFunctors}

-- TODO Should be a def
@[expose]
abbrev execStutter (P : ENNReal → IProp GF) (ε : ENNReal) : IProp GF := iprop%
  ⌜1 ≤ ε⌝ ∨ P ε

-- TODO: Rename execStutter.intro
theorem execStutter_free {P : ENNReal → IProp GF} {ε : ENNReal} :
    P ε ⊢ execStutter P ε := by
  iintro HP; iright; iexact HP

theorem execStutter_spend {P : ENNReal → IProp GF} {ε : ENNReal} (hε : 1 ≤ ε) :
    ⊢ execStutter (GF := GF) P ε := by
  iintro; ileft; ipureintro; exact hε

theorem execStutter_mono {P Q : ENNReal → IProp GF} {ε ε' : ENNReal} (hε : ε ≤ ε') :
    ((P ε -∗ Q ε') ∗ execStutter P ε) ⊢ execStutter (GF := GF) Q ε' := by
  iintro ⟨HM, HS⟩
  icases HS with ⟨%HVac | HP⟩
  · ileft; ipureintro; exact HVac.trans hε
  · iright; iapply HM; iexact HP

theorem execStutter_mono_pred {P Q : ENNReal → IProp GF} {ε : ENNReal} :
    ((P ε -∗ Q ε) ∗ execStutter P ε) ⊢ execStutter (GF := GF) Q ε :=
  execStutter_mono (_root_.le_refl ε)

variable [ErisWpGS (rT := rT) GF]

@[expose]
abbrev GlmState (rT : Type _) [ProbLang.ProbLangℝ rT] : Type _ := Cfg rT × ENNReal

instance : COFE (GlmState rT) := COFE.ofDiscrete _ Eq_Equivalence
instance : OFE.Discrete (GlmState rT) := ⟨id⟩
instance : OFE.Leibniz (GlmState rT) := ⟨id⟩

@[discrete]
abbrev glmPrimStep [Countable rT] [MeasurableSingletonClass rT]
    (e₁ : Exp rT) (σ₁ : State rT) (ε : ENNReal)
    (Z : Cfg rT → ENNReal → IProp GF) : IProp GF :=
  iprop(∃ (R : Cfg rT → Prop) (ε₁ : ENNReal) (X₂ : Cfg rT → ENNReal) (r : ENNReal),
    (⌜Discrete.Reducible e₁ σ₁⌝) ∗
    (⌜∀ ρ, X₂ ρ ≤ r⌝) ∗
    (⌜ε₁ + (∫⁻ ρ, X₂ ρ ∂(primStep ⟨e₁, σ₁⟩)) ≤ ε⌝) ∗
    (⌜Pgl ε₁ R (primStep ⟨e₁, σ₁⟩)⌝) ∗
    (∀ (ρ : Cfg rT), (⌜R ρ⌝) -∗
      |={∅}=> execStutter (Z ρ) (X₂ ρ)))

abbrev glmPrimStep' (e₁ : Exp rT) (σ₁ : State rT) (ε : ENNReal)
    (Z : Cfg rT → ENNReal → IProp GF) : IProp GF := iprop%
  ∃ (R : Cfg rT → Prop) (ε₁ : ENNReal) (X₂ : Cfg rT → ENNReal) (r : ENNReal),
    (⌜Reducible e₁ σ₁⌝) ∗
    (⌜MeasurableSet {ρ | R ρ}⌝) ∗
    (⌜∀ ρ, X₂ ρ ≤ r⌝) ∗
    (⌜ε₁ + (∫⁻ ρ, X₂ ρ ∂(primStep ⟨e₁, σ₁⟩)) ≤ ε⌝) ∗
    (⌜Pgl ε₁ R (primStep ⟨e₁, σ₁⟩)⌝) ∗
    (∀ (ρ : Cfg rT), (⌜R ρ⌝) -∗
      |={∅}=> execStutter (Z ρ) (X₂ ρ))

-- TODO: Rename me to not reference state steps
abbrev glmStateStep (e₁ : Exp rT) (σ₁ : State rT) (ε : ENNReal)
   (Φ : GlmState rT → IProp GF) : IProp GF := iprop%
  ∃ (α : Loc) (t : Tape),
    ⌜σ₁.tapes[α]? = some t ∧ 0 < t.bound⌝ ∗
    ∃ (R : State rT → Prop) (ε₁ : ENNReal) (X₂ : State rT → ENNReal) (r : ENNReal),
      (⌜∀ σ', X₂ σ' ≤ r⌝) ∗
      (⌜ε₁ + (∫⁻ σ', X₂ σ' ∂(tapePresample σ₁ α)) ≤ ε⌝) ∗
      (⌜Pgl ε₁ R (tapePresample σ₁ α)⌝) ∗
      (∀ (σ' : State rT), ⌜R σ'⌝ -∗
        |={∅}=> execStutter (fun ε'' => Φ (⟨e₁, σ'⟩, ε'')) (X₂ σ'))

/-- Countability-free analogue of `glmStateStep` carrying a measurability witness
`⌜MeasurableSet {σ' | R σ'}⌝` for the support predicate `R`. The witness is needed
downstream (total adequacy) to evaluate the `tapePresample`-mass on `{R}` and its
complement via `measure_add_measure_compl`. Mirrors `glmPrimStep'`. -/
abbrev glmStateStep' (e₁ : Exp rT) (σ₁ : State rT) (ε : ENNReal)
   (Φ : GlmState rT → IProp GF) : IProp GF := iprop%
  ∃ (α : Loc) (t : Tape),
    ⌜σ₁.tapes[α]? = some t ∧ 0 < t.bound⌝ ∗
    ∃ (R : State rT → Prop) (ε₁ : ENNReal) (X₂ : State rT → ENNReal) (r : ENNReal),
      (⌜MeasurableSet {σ' | R σ'}⌝) ∗
      (⌜∀ σ', X₂ σ' ≤ r⌝) ∗
      (⌜ε₁ + (∫⁻ σ', X₂ σ' ∂(tapePresample σ₁ α)) ≤ ε⌝) ∗
      (⌜Pgl ε₁ R (tapePresample σ₁ α)⌝) ∗
      (∀ (σ' : State rT), ⌜R σ'⌝ -∗
        |={∅}=> execStutter (fun ε'' => Φ (⟨e₁, σ'⟩, ε'')) (X₂ σ'))

@[discrete] -- glmPre'
abbrev glmPre [Countable rT] [MeasurableSingletonClass rT]
    (Z : Cfg rT → ENNReal → IProp GF)
    (Φ : GlmState rT → IProp GF) : GlmState rT → IProp GF :=
  fun ⟨ρ, ε⟩ => iprop%
    (∀ (ε' : ENNReal), (⌜ε < ε'⌝) -∗
        |={∅}=> execStutter (fun ε'' => Φ (ρ, ε'')) ε') ∨
    glmPrimStep ρ.expr ρ.state ε Z ∨
    glmStateStep ρ.expr ρ.state ε Φ

abbrev glmPre' (Z : Cfg rT → ENNReal → IProp GF)
    (Φ : GlmState rT → IProp GF) : GlmState rT → IProp GF :=
  fun ⟨ρ, ε⟩ => iprop%
    (∀ (ε' : ENNReal), (⌜ε < ε'⌝) -∗
        |={∅}=> execStutter (fun ε'' => Φ (ρ, ε'')) ε') ∨
    glmPrimStep' ρ.expr ρ.state ε Z ∨
    glmStateStep' ρ.expr ρ.state ε Φ

@[expose, discrete] -- glm'
abbrev glm [Countable rT] [MeasurableSingletonClass rT] (e : Exp rT) (σ : State rT) (ε : ENNReal)
    (Z : Cfg rT → ENNReal → IProp GF) : IProp GF :=
  bi_least_fixpoint (glmPre (GF := GF) Z) ((⟨e, σ⟩, ε) : GlmState rT)

abbrev glm' (e : Exp rT) (σ : State rT) (ε : ENNReal)
    (Z : Cfg rT → ENNReal → IProp GF) : IProp GF :=
  bi_least_fixpoint (glmPre' (GF := GF) Z) ((⟨e, σ⟩, ε) : GlmState rT)

@[discrete] -- glmPre'_mono
instance glmPre_mono [Countable rT] [MeasurableSingletonClass rT] {Z : Cfg rT → ENNReal → IProp GF} :
    BIMonoPred (glmPre (GF := GF) (rT := rT) Z) where
  mono_pred {Φ Ψ _ _} := by
    iintro #Hwand %s Hs
    rcases s with ⟨ρ, ε⟩
    icases Hs with ⟨HOT | HPS | HSS⟩
    · ileft
      iintro %ε' %Hlt
      imod HOT $$ %ε' %Hlt with HS
      imodintro
      icases HS with ⟨%HVac | HP⟩
      · ileft; ipureintro; exact HVac
      · iright; iapply Hwand; iexact HP
    · iright; ileft
      icases HPS with ⟨%R, %ε₁, %X₂, %r, %Hred, %Hbnd, %Hexp, %Hpgl, HCont⟩
      iexists R, ε₁, X₂, r
      isplitr; · ipureintro; exact Hred
      isplitr; · ipureintro; exact Hbnd
      isplitr; · ipureintro; exact Hexp
      isplitr; · ipureintro; exact Hpgl
      iintro %ρ' HR
      ihave HC := HCont $$ %ρ' HR
      imod HC
      imodintro
      iexact HC
    · iright; iright
      icases HSS with ⟨%α, %t, %Hαt, %R, %ε₁, %X₂, %r, %Hbnd, %Hexp, %Hpgl, HCont⟩
      iexists α, t
      isplitr; · ipureintro; exact Hαt
      iexists R, ε₁, X₂, r
      isplitr; · ipureintro; exact Hbnd
      isplitr; · ipureintro; exact Hexp
      isplitr; · ipureintro; exact Hpgl
      iintro %σ' %HR
      ihave HC := HCont $$ %σ' %HR
      imod HC with HS
      imodintro
      icases HS with ⟨%HVac | HP⟩
      · ileft; ipureintro; exact HVac
      · iright; iapply Hwand; iexact HP
  mono_pred_ne.ne {_ s s'} hd := by
    have := eq_of_dist_discrete_leibniz hd; subst this; exact .of_eq rfl

instance glmPre'_mono {Z : Cfg rT → ENNReal → IProp GF} : BIMonoPred (glmPre' (GF := GF) (rT := rT) Z) where
  mono_pred {Φ Ψ _ _} := by
    iintro #Hwand %s Hs
    rcases s with ⟨ρ, ε⟩
    icases Hs with ⟨HOT | HPS | HSS⟩
    · ileft
      iintro %ε' %Hlt
      imod HOT $$ %ε' %Hlt with HS
      imodintro
      icases HS with ⟨%HVac | HP⟩
      · ileft; ipureintro; exact HVac
      · iright; iapply Hwand; iexact HP
    · iright; ileft
      icases HPS with ⟨%R, %ε₁, %X₂, %r, %Hred, %HRmeas, %Hbnd, %Hexp, %Hpgl, HCont⟩
      iexists R, ε₁, X₂, r
      iframe %Hred %HRmeas %Hbnd %Hexp %Hpgl
      iintro %ρ' HR
      ihave HC := HCont $$ %ρ' HR
      imod HC
      imodintro
      iexact HC
    · iright; iright
      icases HSS with ⟨%α, %t, %Hαt, %R, %ε₁, %X₂, %r, %HRmeas, %Hbnd, %Hexp, %Hpgl, HCont⟩
      iexists α, t
      iframe %Hαt
      iexists R, ε₁, X₂, r
      iframe %HRmeas %Hbnd %Hexp %Hpgl
      iintro %σ' %HR
      ihave HC := HCont $$ %σ' %HR
      imod HC with HS
      imodintro
      icases HS with ⟨%HVac | HP⟩
      · ileft; ipureintro; exact HVac
      · iright; iapply Hwand; iexact HP
  mono_pred_ne.ne {_ s s'} hd := by
    have := eq_of_dist_discrete_leibniz hd; subst this; exact .of_eq rfl

@[discrete] -- glm'_unfold
theorem glm_unfold [Countable rT] [MeasurableSingletonClass rT] {e : Exp rT} {σ : State rT} {ε : ENNReal}
    {Z : Cfg rT → ENNReal → IProp GF} :
    glm (GF := GF) e σ ε Z ≡
      glmPre (GF := GF) Z
        (fun s => glm s.1.expr s.1.state s.2 Z)
        ((⟨e, σ⟩, ε) : GlmState rT) :=
  least_fixpoint_unfold _

theorem glm'_unfold {e : Exp rT} {σ : State rT} {ε : ENNReal}
    {Z : Cfg rT → ENNReal → IProp GF} :
    glm' (GF := GF) e σ ε Z ≡
      glmPre' (GF := GF) Z
        (fun s => glm' s.1.expr s.1.state s.2 Z)
        ((⟨e, σ⟩, ε) : GlmState rT) :=
  least_fixpoint_unfold _

@[discrete] -- glm'_strong_ind
theorem glm_strong_ind [Countable rT] [MeasurableSingletonClass rT]
    {Z : Cfg rT → ENNReal → IProp GF}
    {Ψ : GlmState rT → IProp GF} [NonExpansive Ψ] :
    iprop(□ (∀ s, glmPre Z
              (fun s' => iprop(Ψ s' ∧ bi_least_fixpoint (glmPre Z) s')) s
              -∗ Ψ s)) ⊢@{IProp GF}
      (∀ s, bi_least_fixpoint (glmPre Z) s -∗ Ψ s) := by
  iintro #HM
  iapply least_fixpoint_ind (F := glmPre Z) (Φ := Ψ)
  iexact HM

theorem glm'_strong_ind {Z : Cfg rT → ENNReal → IProp GF} {Ψ : GlmState rT → IProp GF} [NonExpansive Ψ] :
    iprop(□ (∀ s, glmPre' Z
              (fun s' => iprop(Ψ s' ∧ bi_least_fixpoint (glmPre' Z) s')) s
              -∗ Ψ s)) ⊢@{IProp GF}
      (∀ s, bi_least_fixpoint (glmPre' Z) s -∗ Ψ s) := by
  iintro #HM
  iapply least_fixpoint_ind (F := glmPre' Z) (Φ := Ψ)
  iexact HM

@[discrete] -- glm'_strong_mono
theorem glm_strong_mono [Countable rT] [MeasurableSingletonClass rT]
    {e : Exp rT} {σ : State rT} {ε : ENNReal} {Z₁ Z₂ : Cfg rT → ENNReal → IProp GF} :
    iprop((∀ ρ ε', Z₁ ρ ε' -∗ Z₂ ρ ε') ∗ glm e σ ε Z₁) ⊢@{IProp GF}
      glm e σ ε Z₂ := by
  iintro ⟨HZ, HG⟩
  letI Ψ : GlmState rT → IProp GF := fun s => iprop(
    (∀ ρ ε', Z₁ ρ ε' -∗ Z₂ ρ ε') -∗ bi_least_fixpoint (glmPre Z₂) s)
  letI : NonExpansive Ψ := by
    constructor
    intro n s s' hd
    have : s = s' := OFE.Leibniz.eq_of_eqv (OFE.Discrete.discrete_0 hd)
    subst this; exact .of_eq rfl
  -- Apply the iter to derive `Ψ ⟨..., ε⟩` from `HG`.
  ihave HΨ : iprop(Ψ ((⟨e, σ⟩, ε) : GlmState rT)) $$ [HG]
  · iapply least_fixpoint_iter (F := glmPre Z₁) (Φ := Ψ)
    swap; · iexact HG
    -- Discharge: `□ (∀ y, glmPre Z₁ Ψ y -∗ Ψ y)`.
    iintro !> %s HF
    iintro Hwand
    iapply least_fixpoint_unfold_mpr (glmPre Z₂)
    rcases s with ⟨ρ, ε⟩
    icases HF with ⟨HOT | HPS | HSS⟩
    · ileft
      iintro %ε' %Hlt
      imod HOT $$ %ε' %Hlt with HS
      imodintro
      icases HS with ⟨%HVac | HP⟩
      · ileft; ipureintro; exact HVac
      · iright
        iapply HP; iexact Hwand
    · iright; ileft
      icases HPS with ⟨%R, %ε₁, %X₂, %r, %Hred, %Hbnd, %Hexp, %Hpgl, HCont⟩
      iexists R, ε₁, X₂, r
      isplitr; · ipureintro; exact Hred
      isplitr; · ipureintro; exact Hbnd
      isplitr; · ipureintro; exact Hexp
      isplitr; · ipureintro; exact Hpgl
      iintro %ρ' HR
      ihave HC := HCont $$ %ρ' HR
      imod HC with HS
      imodintro
      icases HS with ⟨%HVac | HC1⟩
      · ileft; ipureintro; exact HVac
      · iright
        iapply Hwand; iexact HC1
    · iright; iright
      icases HSS with ⟨%α, %t, %Hαt, %R, %ε₁, %X₂, %r, %Hbnd, %Hexp, %Hpgl, HCont⟩
      iexists α, t
      isplitr; · ipureintro; exact Hαt
      iexists R, ε₁, X₂, r
      isplitr; · ipureintro; exact Hbnd
      isplitr; · ipureintro; exact Hexp
      isplitr; · ipureintro; exact Hpgl
      iintro %σ' %HR
      ihave HC := HCont $$ %σ' %HR
      imod HC with HS
      imodintro
      icases HS with ⟨%HVac | HP⟩
      · ileft; ipureintro; exact HVac
      · iright
        iapply HP; iexact Hwand
  iapply HΨ; iexact HZ


theorem glm'_strong_mono
    {e : Exp rT} {σ : State rT} {ε : ENNReal} {Z₁ Z₂ : Cfg rT → ENNReal → IProp GF} :
    iprop((∀ ρ ε', Z₁ ρ ε' -∗ Z₂ ρ ε') ∗ glm' e σ ε Z₁) ⊢@{IProp GF}
      glm' e σ ε Z₂ := by
  iintro ⟨HZ, HG⟩
  letI Ψ : GlmState rT → IProp GF := fun s => iprop(
    (∀ ρ ε', Z₁ ρ ε' -∗ Z₂ ρ ε') -∗ bi_least_fixpoint (glmPre' Z₂) s)
  letI : NonExpansive Ψ := by
    constructor
    intro n s s' hd
    have : s = s' := OFE.Leibniz.eq_of_eqv (OFE.Discrete.discrete_0 hd)
    subst this; exact .of_eq rfl
  -- Apply the iter to derive `Ψ ⟨..., ε⟩` from `HG`.
  ihave HΨ : iprop(Ψ ((⟨e, σ⟩, ε) : GlmState rT)) $$ [HG]
  · iapply least_fixpoint_iter (F := glmPre' Z₁) (Φ := Ψ)
    swap; · iexact HG
    -- Discharge: `□ (∀ y, glmPre Z₁ Ψ y -∗ Ψ y)`.
    iintro !> %s HF
    iintro Hwand
    iapply least_fixpoint_unfold_mpr (glmPre' Z₂)
    rcases s with ⟨ρ, ε⟩
    icases HF with ⟨HOT | HPS | HSS⟩
    · ileft
      iintro %ε' %Hlt
      imod HOT $$ %ε' %Hlt with HS
      imodintro
      icases HS with ⟨%HVac | HP⟩
      · ileft; ipureintro; exact HVac
      · iright
        iapply HP; iexact Hwand
    · iright; ileft
      icases HPS with ⟨%R, %ε₁, %X₂, %r, %Hred, %HRmeas, %Hbnd, %Hexp, %Hpgl, HCont⟩
      iexists R, ε₁, X₂, r
      isplitr; · ipureintro; exact Hred
      isplitr; · ipureintro; exact HRmeas
      isplitr; · ipureintro; exact Hbnd
      isplitr; · ipureintro; exact Hexp
      isplitr; · ipureintro; exact Hpgl
      iintro %ρ' HR
      ihave HC := HCont $$ %ρ' HR
      imod HC with HS
      imodintro
      icases HS with ⟨%HVac | HC1⟩
      · ileft; ipureintro; exact HVac
      · iright
        iapply Hwand; iexact HC1
    · iright; iright
      icases HSS with ⟨%α, %t, %Hαt, %R, %ε₁, %X₂, %r, %HRmeas, %Hbnd, %Hexp, %Hpgl, HCont⟩
      iexists α, t
      isplitr; · ipureintro; exact Hαt
      iexists R, ε₁, X₂, r
      isplitr; · ipureintro; exact HRmeas
      isplitr; · ipureintro; exact Hbnd
      isplitr; · ipureintro; exact Hexp
      isplitr; · ipureintro; exact Hpgl
      iintro %σ' %HR
      ihave HC := HCont $$ %σ' %HR
      imod HC with HS
      imodintro
      icases HS with ⟨%HVac | HP⟩
      · ileft; ipureintro; exact HVac
      · iright
        iapply HP; iexact Hwand
  iapply HΨ; iexact HZ

@[discrete] -- glm'_mono_grading
theorem glm_mono_grading [Countable rT] [MeasurableSingletonClass rT]
    {e : Exp rT} {σ : State rT} {ε ε' : ENNReal} {Z : Cfg rT → ENNReal → IProp GF} (Hε : ε ≤ ε') :
    glm e σ ε Z ⊢@{IProp GF} glm e σ ε' Z := by
  iintro HG
  ihave HG' := (BI.equiv_iff.mp glm_unfold).1 $$ HG
  iapply (BI.equiv_iff.mp glm_unfold).2
  icases HG' with ⟨HOT | HPS | HSS⟩
  · ileft
    iintro %ε'' %Hlt'
    have Hlt : ε < ε'' := _root_.lt_of_le_of_lt Hε Hlt'
    ispecialize HOT $$ %ε'' %Hlt
    iexact HOT
  · iright; ileft
    icases HPS with ⟨%R, %ε₁, %X₂, %r, %Hred, %Hbnd, %Hexp, %Hpgl, HCont⟩
    iexists R, ε₁, X₂, r
    isplitr; · ipureintro; exact Hred
    isplitr; · ipureintro; exact Hbnd
    isplitr; · ipureintro; exact _root_.le_trans Hexp Hε
    isplitr; · ipureintro; exact Hpgl
    iexact HCont
  · iright; iright
    icases HSS with ⟨%α, %t, %Hαt, %R, %ε₁, %X₂, %r, %Hbnd, %Hexp, %Hpgl, HCont⟩
    iexists α, t
    isplitr; · ipureintro; exact Hαt
    iexists R, ε₁, X₂, r
    isplitr; · ipureintro; exact Hbnd
    isplitr; · ipureintro; exact _root_.le_trans Hexp Hε
    isplitr; · ipureintro; exact Hpgl
    iexact HCont

theorem glm'_mono_grading
    {e : Exp rT} {σ : State rT} {ε ε' : ENNReal} {Z : Cfg rT → ENNReal → IProp GF} (Hε : ε ≤ ε') :
    glm' e σ ε Z ⊢@{IProp GF} glm' e σ ε' Z := by
  iintro HG
  ihave HG' := (BI.equiv_iff.mp glm'_unfold).1 $$ HG
  iapply (BI.equiv_iff.mp glm'_unfold).2
  icases HG' with ⟨HOT | HPS | HSS⟩
  · ileft
    iintro %ε'' %Hlt'
    have Hlt : ε < ε'' := _root_.lt_of_le_of_lt Hε Hlt'
    ispecialize HOT $$ %ε'' %Hlt
    iexact HOT
  · iright; ileft
    icases HPS with ⟨%R, %ε₁, %X₂, %r, %Hred, %HRmeas, %Hbnd, %Hexp, %Hpgl, HCont⟩
    iexists R, ε₁, X₂, r
    isplitr; · ipureintro; exact Hred
    isplitr; · ipureintro; exact HRmeas
    isplitr; · ipureintro; exact Hbnd
    isplitr; · ipureintro; exact _root_.le_trans Hexp Hε
    isplitr; · ipureintro; exact Hpgl
    iexact HCont
  · iright; iright
    icases HSS with ⟨%α, %t, %Hαt, %R, %ε₁, %X₂, %r, %HRmeas, %Hbnd, %Hexp, %Hpgl, HCont⟩
    iexists α, t
    isplitr; · ipureintro; exact Hαt
    iexists R, ε₁, X₂, r
    isplitr; · ipureintro; exact HRmeas
    isplitr; · ipureintro; exact Hbnd
    isplitr; · ipureintro; exact _root_.le_trans Hexp Hε
    isplitr; · ipureintro; exact Hpgl
    iexact HCont

@[discrete] -- glm'_strong_mono_grading
theorem glm_strong_mono_grading [Countable rT] [MeasurableSingletonClass rT] {e : Exp rT} {σ : State rT} {ε ε' : ENNReal}
    {Z₁ Z₂ : Cfg rT → ENNReal → IProp GF} (Hε : ε ≤ ε') :
    iprop((∀ ρ ε'', Z₁ ρ ε'' -∗ Z₂ ρ ε'') ∗ glm e σ ε Z₁) ⊢@{IProp GF}
      glm e σ ε' Z₂ := by
  iintro ⟨HZ, HG⟩
  iapply glm_mono_grading Hε
  iapply glm_strong_mono
  isplitl [HZ]
  · iexact HZ
  iexact HG

theorem glm'_strong_mono_grading {e : Exp rT} {σ : State rT} {ε ε' : ENNReal}
    {Z₁ Z₂ : Cfg rT → ENNReal → IProp GF} (Hε : ε ≤ ε') :
    iprop((∀ ρ ε'', Z₁ ρ ε'' -∗ Z₂ ρ ε'') ∗ glm' e σ ε Z₁) ⊢@{IProp GF}
      glm' e σ ε' Z₂ := by
  iintro ⟨HZ, HG⟩
  iapply glm'_mono_grading Hε
  iapply glm'_strong_mono
  iframe

@[discrete] -- glm'_mono_pred
theorem glm_mono_pred [Countable rT] [MeasurableSingletonClass rT] {e : Exp rT} {σ : State rT} {ε : ENNReal}
    {Z₁ Z₂ : Cfg rT → ENNReal → IProp GF} :
    iprop((□ (∀ ρ ε', Z₁ ρ ε' -∗ Z₂ ρ ε')) ∗ glm e σ ε Z₁) ⊢@{IProp GF}
      glm e σ ε Z₂ := by
  iintro ⟨#HZ, HG⟩
  unfold glm
  iapply (least_fixpoint_strong_mono (glmPre Z₁) (glmPre Z₂))
    $$ [] HG
  iintro !> %Φ %s HF
  rcases s with ⟨ρ, ε⟩
  icases HF with ⟨HOT | HPS | HSS⟩
  · ileft
    iintro %ε' %Hlt
    imod HOT $$ %ε' %Hlt with HS
    imodintro
    iexact HS
  · iright; ileft
    icases HPS with ⟨%R, %ε₁, %X₂, %r, %Hred, %Hbnd, %Hexp, %Hpgl, HCont⟩
    iexists R, ε₁, X₂, r
    isplitr; · ipureintro; exact Hred
    isplitr; · ipureintro; exact Hbnd
    isplitr; · ipureintro; exact Hexp
    isplitr; · ipureintro; exact Hpgl
    iintro %ρ' HR
    ihave HC := HCont $$ %ρ' HR
    imod HC
    imodintro
    icases HC with ⟨%HVac | HC1⟩
    · ileft; ipureintro; exact HVac
    · iright; iapply HZ; iexact HC1
  · iright; iright
    icases HSS with ⟨%α, %t, %Hαt, %R, %ε₁, %X₂, %r, %Hbnd, %Hexp, %Hpgl, HCont⟩
    iexists α, t
    isplitr; · ipureintro; exact Hαt
    iexists R, ε₁, X₂, r
    isplitr; · ipureintro; exact Hbnd
    isplitr; · ipureintro; exact Hexp
    isplitr; · ipureintro; exact Hpgl
    iintro %σ' %HR
    ihave HC := HCont $$ %σ' %HR
    imod HC
    imodintro
    iexact HC


theorem glm'_mono_pred {e : Exp rT} {σ : State rT} {ε : ENNReal}
    {Z₁ Z₂ : Cfg rT → ENNReal → IProp GF} :
    iprop((□ (∀ ρ ε', Z₁ ρ ε' -∗ Z₂ ρ ε')) ∗ glm' e σ ε Z₁) ⊢@{IProp GF}
      glm' e σ ε Z₂ := by
  iintro ⟨#HZ, HG⟩
  unfold glm'
  iapply (least_fixpoint_strong_mono (glmPre' Z₁) (glmPre' Z₂))
    $$ [] HG
  iintro !> %Φ %s HF
  rcases s with ⟨ρ, ε⟩
  icases HF with ⟨HOT | HPS | HSS⟩
  · ileft
    iintro %ε' %Hlt
    imod HOT $$ %ε' %Hlt with HS
    imodintro
    iexact HS
  · iright; ileft
    icases HPS with ⟨%R, %ε₁, %X₂, %r, %Hred, %HRmeas, %Hbnd, %Hexp, %Hpgl, HCont⟩
    iexists R, ε₁, X₂, r
    isplitr; · ipureintro; exact Hred
    isplitr; · ipureintro; exact HRmeas
    isplitr; · ipureintro; exact Hbnd
    isplitr; · ipureintro; exact Hexp
    isplitr; · ipureintro; exact Hpgl
    iintro %ρ' HR
    ihave HC := HCont $$ %ρ' HR
    imod HC
    imodintro
    icases HC with ⟨%HVac | HC1⟩
    · ileft; ipureintro; exact HVac
    · iright; iapply HZ; iexact HC1
  · iright; iright
    icases HSS with ⟨%α, %t, %Hαt, %R, %ε₁, %X₂, %r, %HRmeas, %Hbnd, %Hexp, %Hpgl, HCont⟩
    iexists α, t
    isplitr; · ipureintro; exact Hαt
    iexists R, ε₁, X₂, r
    isplitr; · ipureintro; exact HRmeas
    isplitr; · ipureintro; exact Hbnd
    isplitr; · ipureintro; exact Hexp
    isplitr; · ipureintro; exact Hpgl
    iintro %σ' %HR
    ihave HC := HCont $$ %σ' %HR
    imod HC
    imodintro
    iexact HC

@[discrete] -- glm'_bind
theorem glm_bind [Countable rT] [MeasurableSingletonClass rT]
    {K : Ectx rT} {e : Exp rT} {σ : State rT} {ε : ENNReal} {Z : Cfg rT → ENNReal → IProp GF} :
    glm e σ ε (fun ρ ε' => Z ⟨K.fill ρ.expr, ρ.state⟩ ε') ⊢@{IProp GF}
      glm (K.fill e) σ ε Z := by
  iintro HG
  classical
  let Kinv : Exp rT → Option (Exp rT) := Function.partialInv K.fill
  have Kinv_left : ∀ e', Kinv (K.fill e') = some e' :=
    Function.partialInv_left (Ectx.fill_injective K)
  letI Z' : Cfg rT → ENNReal → IProp GF :=
    fun ρ ε' => Z ⟨K.fill ρ.expr, ρ.state⟩ ε'
  letI Φ : GlmState rT → IProp GF :=
    fun s => bi_least_fixpoint (glmPre Z) ((⟨K.fill s.1.expr, s.1.state⟩, s.2) : GlmState rT)
  letI : NonExpansive Φ := nonExpansive_of_discrete_leibniz Φ
  ihave HΦ : iprop(Φ ((⟨e, σ⟩, ε) : GlmState rT)) $$ [HG]
  · iapply least_fixpoint_iter (F := glmPre Z') (Φ := Φ)
    swap; · iexact HG
    iintro !> %s HF
    rcases s with ⟨ρ, ε'⟩
    iapply least_fixpoint_unfold_mpr (glmPre Z)
    icases HF with ⟨HOT | HPS | HSS⟩
    · -- OT branch.
      ileft
      iintro %ε'' %Hlt
      imod HOT $$ %ε'' %Hlt with HS
      imodintro
      icases HS with ⟨%HVac | HP⟩
      · ileft; ipureintro; exact HVac
      · iright; iexact HP
    · -- prim_step branch.
      iright; ileft
      icases HPS with ⟨%R, %ε₁, %X₂, %r, %Hred, %Hbnd, %Hexp, %Hpgl, HCont⟩
      iexists (fun ρ' => ∃ ρ'', ρ' = K.fillCfg ρ'' ∧ R ρ''), ε₁,
        (fun ρ' => (Kinv ρ'.expr).elim 0 (fun e' => X₂ ⟨e', ρ'.state⟩)),
        r
      have Hsv : ¬ ρ.expr.isValue := Discrete.val_stuck Hred.choose_spec
      isplitr; · ipureintro; exact Hred.fill K
      isplitr
      · ipureintro
        intro ρ'
        cases h : Kinv ρ'.expr with
        | none => simp [h, Option.elim]
        | some e' => simp [h, Option.elim]; exact Hbnd ⟨e', ρ'.state⟩
      isplitr
      · ipureintro
        show ε₁ + (∫⁻ a, (Kinv a.expr).elim 0 (fun e' => X₂ ⟨e', a.state⟩) ∂
                   primStep ⟨K.fill ρ.expr, ρ.state⟩) ≤ ε'
        rw [primStep_fill Hsv]
        rw [MeasureTheory.lintegral_map Measurable.of_discrete Measurable.of_discrete]
        -- Goal: ε₁ + ∫⁻ a, ... at K.fillCfg a ... ∂primStep ⟨ρ.expr, ρ.state⟩ ≤ ε'
        -- The integrand simplifies via Kinv_left at K.fill a.expr.
        refine _root_.le_trans (_root_.le_of_eq ?_) Hexp
        congr 1
        refine MeasureTheory.lintegral_congr_ae (Filter.Eventually.of_forall fun a => ?_)
        show (Kinv (K.fillCfg a).expr).elim 0 (fun e' => X₂ ⟨e', (K.fillCfg a).state⟩) = X₂ a
        simp only [Ectx.fillCfg, Kinv_left, Option.elim]
      isplitr
      · ipureintro
        show primStep ⟨K.fill ρ.expr, ρ.state⟩ {x | ¬ ∃ ρ'', x = K.fillCfg ρ'' ∧ R ρ''} ≤ ε₁
        rw [primStep_fill Hsv]
        rw [MeasureTheory.Measure.map_apply Measurable.of_discrete .of_discrete]
        refine _root_.le_trans (_root_.le_of_eq ?_) Hpgl
        congr 1
        ext a
        simp only [Set.mem_preimage, Set.mem_setOf_eq, not_exists, not_and]
        constructor
        · intro h hR; exact h a rfl hR
        · intro hR ρ''' hEq hR'''
          have : ρ''' = a := Ectx.fillCfg_injective K hEq.symm
          exact hR (this ▸ hR''')
      iintro %ρ' HR'
      icases HR' with ⟨%ρ'', %heq, %HR⟩
      subst heq
      ihave HC := HCont $$ %ρ'' %HR
      imod HC with HS
      imodintro
      -- Reduce `(Kinv (K.fillCfg ρ'').expr).elim ...` to `X₂ ρ''`.
      simp only [Ectx.fillCfg, Kinv_left, Option.elim]
      icases HS with ⟨%HVac | HC1⟩
      · ileft; ipureintro; exact HVac
      · iright; iexact HC1
    · -- state_step branch. K does not affect the state; the same
      -- `α, t, R, X₂, ε₁` data transports directly. The continuation
      -- produces `Φ (⟨ρ.expr, σ'⟩, _)` which under `Φ` (= bi_least_fixpoint
      -- at K.fillCfg) gives the K-filled glm-fixpoint.
      iright; iright
      icases HSS with ⟨%α, %t, %Hαt, %R, %ε₁, %X₂, %r, %Hbnd, %Hexp, %Hpgl, HCont⟩
      iexists α, t
      isplitr; · ipureintro; exact Hαt
      iexists R, ε₁, X₂, r
      isplitr; · ipureintro; exact Hbnd
      isplitr; · ipureintro; exact Hexp
      isplitr; · ipureintro; exact Hpgl
      iintro %σ' %HR
      ihave HC := HCont $$ %σ' %HR
      imod HC
      imodintro
      iexact HC
  -- `Φ ⟨e, σ, ε⟩ = bi_least_fixpoint (glmPre Z) (⟨K.fill e, σ⟩, ε) = glm (K.fill e) σ ε Z`
  -- by definitional unfolding (Φ is `letI`-bound, `glm` is `@[reducible]`).
  iexact HΦ

-- This one might actually be hard
theorem glm'_bind
    {K : Ectx rT} {e : Exp rT} {σ : State rT} {ε : ENNReal} {Z : Cfg rT → ENNReal → IProp GF} :
    glm' e σ ε (fun ρ ε' => Z ⟨K.fill ρ.expr, ρ.state⟩ ε') ⊢@{IProp GF}
      glm' (K.fill e) σ ε Z := by
  iintro HG
  classical
  let Kinv : Exp rT → Option (Exp rT) := Function.partialInv K.fill
  have Kinv_left : ∀ e', Kinv (K.fill e') = some e' :=
    Function.partialInv_left (Ectx.fill_injective K)
  letI Z' : Cfg rT → ENNReal → IProp GF :=
    fun ρ ε' => Z ⟨K.fill ρ.expr, ρ.state⟩ ε'
  letI Φ : GlmState rT → IProp GF :=
    fun s => bi_least_fixpoint (glmPre' Z) ((⟨K.fill s.1.expr, s.1.state⟩, s.2) : GlmState rT)
  letI : NonExpansive Φ := nonExpansive_of_discrete_leibniz Φ
  ihave HΦ : iprop(Φ ((⟨e, σ⟩, ε) : GlmState rT)) $$ [HG]
  · iapply least_fixpoint_iter (F := glmPre' Z') (Φ := Φ)
    swap; · iexact HG
    iintro !> %s HF
    rcases s with ⟨ρ, ε'⟩
    iapply least_fixpoint_unfold_mpr (glmPre' Z)
    icases HF with ⟨HOT | HPS | HSS⟩
    · ileft
      iintro %ε'' %Hlt
      imod HOT $$ %ε'' %Hlt with HS
      imodintro
      icases HS with ⟨%HVac | HP⟩
      · ileft; ipureintro; exact HVac
      · iright; iexact HP
    · iright; ileft
      icases HPS with ⟨%R, %ε₁, %X₂, %r, %Hred, %HRmeas, %Hbnd, %Hexp, %Hpgl, HCont⟩
      iexists (fun ρ' => ∃ ρ'', ρ' = K.fillCfg ρ'' ∧ R ρ''), ε₁,
        (fun ρ' => (Kinv ρ'.expr).elim 0 (fun e' => X₂ ⟨e', ρ'.state⟩)),
        r
      have Hsv : ¬ ρ.expr.isValue := val_stuck Hred
      -- The transported support predicate is the (measurable) image of `{R}` under
      -- the measurable embedding `K.fillCfg`.
      have hR'set : {ρ' : Cfg rT | ∃ ρ'', ρ' = K.fillCfg ρ'' ∧ R ρ''}
          = K.fillCfg '' {ρ'' | R ρ''} := by
        ext ρ'; simp only [Set.mem_setOf_eq, Set.mem_image]
        exact ⟨fun ⟨ρ'', heq, hR⟩ => ⟨ρ'', hR, heq.symm⟩,
          fun ⟨ρ'', hR, heq⟩ => ⟨ρ'', heq.symm, hR⟩⟩
      have hR'meas : MeasurableSet {ρ' : Cfg rT | ∃ ρ'', ρ' = K.fillCfg ρ'' ∧ R ρ''} :=
        hR'set ▸ Ectx.measurableSet_fillCfg_image K HRmeas
      isplitr; · ipureintro; exact Hred.fill K
      isplitr; · ipureintro; exact hR'meas
      isplitr
      · ipureintro
        intro ρ'
        cases h : Kinv ρ'.expr with
        | none => simp [h, Option.elim]
        | some e' => simp [h, Option.elim]; exact Hbnd ⟨e', ρ'.state⟩
      isplitr
      · ipureintro
        show ε₁ + (∫⁻ a, (Kinv a.expr).elim 0 (fun e' => X₂ ⟨e', a.state⟩) ∂ primStep ⟨K.fill ρ.expr, ρ.state⟩) ≤ ε'
        rw [primStep_fill Hsv]
        -- Push the (arbitrary, possibly non-measurable) integrand `X₂'` through the
        -- pushforward with the *inequality* `lintegral_map_le` — which needs **no**
        -- measurability of the integrand (only the change-of-variables ≤ direction),
        -- sidestepping the `Countable rT` requirement entirely.
        refine _root_.le_trans ?_ Hexp
        gcongr ε₁ + ?_
        refine _root_.le_trans (MeasureTheory.lintegral_map_le _ K.fillCfg) (_root_.le_of_eq ?_)
        refine MeasureTheory.lintegral_congr_ae (Filter.Eventually.of_forall fun a => ?_)
        show (Kinv (K.fillCfg a).expr).elim 0 (fun e' => X₂ ⟨e', (K.fillCfg a).state⟩) = X₂ a
        simp only [Ectx.fillCfg, Kinv_left, Option.elim]
      isplitr
      · ipureintro
        show primStep ⟨K.fill ρ.expr, ρ.state⟩ {x | ¬ ∃ ρ'', x = K.fillCfg ρ'' ∧ R ρ''} ≤ ε₁
        rw [primStep_fill Hsv]
        rw [MeasureTheory.Measure.map_apply ?G1 ?G2]
        case G1 => measurability
        -- G2: `{x | ¬R' x}` is the complement of the measurable transported support
        -- `{R'}` (now available from the carried `MeasurableSet {R}`).
        case G2 => exact hR'meas.compl
        refine _root_.le_trans (_root_.le_of_eq ?_) Hpgl
        congr 1
        ext a
        simp only [Set.mem_preimage, Set.mem_setOf_eq, not_exists, not_and]
        constructor
        · intro h hR; exact h a rfl hR
        · intro hR ρ''' hEq hR'''
          have : ρ''' = a := Ectx.fillCfg_injective K hEq.symm
          exact hR (this ▸ hR''')
      iintro %ρ' HR'
      icases HR' with ⟨%ρ'', %heq, %HR⟩
      subst heq
      ihave HC := HCont $$ %ρ'' %HR
      imod HC with HS
      imodintro
      simp only [Ectx.fillCfg, Kinv_left, Option.elim]
      icases HS with ⟨%HVac | HC1⟩
      · ileft; ipureintro; exact HVac
      · iright; iexact HC1
    · iright; iright
      icases HSS with ⟨%α, %t, %Hαt, %R, %ε₁, %X₂, %r, %HRmeas, %Hbnd, %Hexp, %Hpgl, HCont⟩
      iexists α, t
      isplitr; · ipureintro; exact Hαt
      iexists R, ε₁, X₂, r
      isplitr; · ipureintro; exact HRmeas
      isplitr; · ipureintro; exact Hbnd
      isplitr; · ipureintro; exact Hexp
      isplitr; · ipureintro; exact Hpgl
      iintro %σ' %HR
      ihave HC := HCont $$ %σ' %HR
      imod HC
      imodintro
      iexact HC
  iexact HΦ

/-! ## Introduction rules for `glm` -/


@[discrete] -- glm'_prim_step
theorem glm_prim_step [Countable rT] [MeasurableSingletonClass rT]
    {e : Exp rT} {σ : State rT} {ε : ENNReal}
    {Z : Cfg rT → ENNReal → IProp GF} :
    iprop(∃ (R : Cfg rT → Prop) (ε₁ : ENNReal) (X₂ : Cfg rT → ENNReal) (r : ENNReal),
      ⌜Discrete.Reducible e σ⌝ ∗
      ⌜∀ ρ, X₂ ρ ≤ r⌝ ∗
      ⌜ε₁ + (∫⁻ ρ, X₂ ρ ∂(primStep ⟨e, σ⟩)) ≤ ε⌝ ∗
      ⌜Pgl ε₁ R (primStep ⟨e, σ⟩)⌝ ∗
      (∀ (ρ : Cfg rT), (⌜R ρ⌝) -∗ |={∅}=> execStutter (Z ρ) (X₂ ρ))) ⊢@{IProp GF}
        glm e σ ε Z := by
  iintro HPS
  unfold glm
  iapply least_fixpoint_unfold_mpr (glmPre Z)
  iright; ileft
  iexact HPS

theorem glm'_prim_step
    {e : Exp rT} {σ : State rT} {ε : ENNReal}
    {Z : Cfg rT → ENNReal → IProp GF} :
    iprop(∃ (R : Cfg rT → Prop) (ε₁ : ENNReal) (X₂ : Cfg rT → ENNReal) (r : ENNReal),
      ⌜Reducible e σ⌝ ∗
      ⌜MeasurableSet {ρ | R ρ}⌝ ∗
      ⌜∀ ρ, X₂ ρ ≤ r⌝ ∗
      ⌜ε₁ + (∫⁻ ρ, X₂ ρ ∂(primStep ⟨e, σ⟩)) ≤ ε⌝ ∗
      ⌜Pgl ε₁ R (primStep ⟨e, σ⟩)⌝ ∗
      (∀ (ρ : Cfg rT), (⌜R ρ⌝) -∗ |={∅}=> execStutter (Z ρ) (X₂ ρ))) ⊢@{IProp GF}
        glm' e σ ε Z := by
  iintro HPS
  unfold glm'
  iapply least_fixpoint_unfold_mpr (glmPre' Z)
  iright; ileft
  iexact HPS

-- TODO: Rename me
@[discrete] -- glm'_state_step
theorem glm_state_step [Countable rT] [MeasurableSingletonClass rT]
    {e : Exp rT} {σ : State rT} {ε : ENNReal} {Z : Cfg rT → ENNReal → IProp GF} :
    iprop(∃ (α : Loc) (t : Tape),
        ⌜σ.tapes[α]? = some t ∧ 0 < t.bound⌝ ∗
        ∃ (R : State rT → Prop) (ε₁ : ENNReal) (X₂ : State rT → ENNReal) (r : ENNReal),
          ⌜∀ σ', X₂ σ' ≤ r⌝ ∗
          ⌜ε₁ + (∫⁻ σ', X₂ σ' ∂(tapePresample σ α)) ≤ ε⌝ ∗
          ⌜Pgl ε₁ R (tapePresample σ α)⌝ ∗
          (∀ (σ' : State rT), ⌜R σ'⌝ -∗
            |={∅}=> execStutter (fun ε'' => glm e σ' ε'' Z) (X₂ σ'))) ⊢@{IProp GF}
          glm e σ ε Z := by
  iintro HSS
  unfold glm
  iapply least_fixpoint_unfold_mpr (glmPre Z)
  iright; iright
  iexact HSS

theorem glm'_state_step  {e : Exp rT} {σ : State rT} {ε : ENNReal} {Z : Cfg rT → ENNReal → IProp GF} :
    iprop(∃ (α : Loc) (t : Tape),
        ⌜σ.tapes[α]? = some t ∧ 0 < t.bound⌝ ∗
        ∃ (R : State rT → Prop) (ε₁ : ENNReal) (X₂ : State rT → ENNReal) (r : ENNReal),
          ⌜MeasurableSet {σ' | R σ'}⌝ ∗
          ⌜∀ σ', X₂ σ' ≤ r⌝ ∗
          ⌜ε₁ + (∫⁻ σ', X₂ σ' ∂(tapePresample σ α)) ≤ ε⌝ ∗
          ⌜Pgl ε₁ R (tapePresample σ α)⌝ ∗
          (∀ (σ' : State rT), ⌜R σ'⌝ -∗
            |={∅}=> execStutter (fun ε'' => glm' e σ' ε'' Z) (X₂ σ'))) ⊢@{IProp GF}
          glm' e σ ε Z := by
  iintro HSS
  unfold glm'
  iapply least_fixpoint_unfold_mpr (glmPre' Z)
  iright; iright
  iexact HSS

@[discrete] -- glm_credit_bump
theorem glm_credit_bump [Countable rT] [MeasurableSingletonClass rT]
    {e : Exp rT} {σ : State rT} {ε : ENNReal} {Z : Cfg rT → ENNReal → IProp GF} :
    iprop(∀ (ε' : ENNReal), ⌜ε < ε'⌝ -∗
      |={∅}=> execStutter (fun ε'' => glm e σ ε'' Z) ε') ⊢@{IProp GF}
        glm e σ ε Z := by
  iintro HOT
  unfold glm
  iapply least_fixpoint_unfold_mpr (glmPre Z)
  ileft
  iexact HOT


theorem glm'_credit_bump
    {e : Exp rT} {σ : State rT} {ε : ENNReal} {Z : Cfg rT → ENNReal → IProp GF} :
    iprop(∀ (ε' : ENNReal), ⌜ε < ε'⌝ -∗
      |={∅}=> execStutter (fun ε'' => glm' e σ ε'' Z) ε') ⊢@{IProp GF}
        glm' e σ ε Z := by
  iintro HOT
  unfold glm'
  iapply least_fixpoint_unfold_mpr (glmPre' Z)
  ileft
  iexact HOT

end ErisWpGS

end TotalEris
end ProbLang
