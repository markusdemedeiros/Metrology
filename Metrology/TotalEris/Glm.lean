module

public import Metrology.Iris.ErrorCredits
public import Metrology.Couplings.AdditiveCouplings
public import Metrology.Couplings.Couplings
public import Metrology.ProbLang.Exec
public import Metrology.ProbLang.Erasable
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
namespace TotalEris

/-! # `glm` graded lifting modality

Port of `clutch/theories/eris/weakestpre.v` `glm` section. `glm` is the
program-step coupling modality used by both `pgl_wp` (partial) and `tgl_wp`
(total) Eris WPs.

The Rocq version has three disjuncts:
1. Out-of-thin-air error credits — bump `ε` up to any `ε' > ε` paying nothing.
2. `prim_step` with adversarial composition — take one program step, pay
   per-outcome error.
3. `state_step` on an active tape — presample without taking a program step.

This Lean port currently supports disjuncts 1 and 2; the presampling
disjunct will be added when `PresampleRules.lean` is ported (it requires
`stateStep` / `getActive` infrastructure that hasn't been ported yet). The
fixpoint state already has the shape `(Cfg × ENNReal)` so the third disjunct
can be added without breaking existing clients. -/

/-! ## `Pgl` — probabilistic graded lift

`Pgl ε φ μ` says: `μ` assigns at most `ε` mass to the complement of `φ`. -/

/-- `Pgl ε φ μ`: the measure `μ` puts at most `ε` mass on `¬φ`. Rocq:
`pgl μ f ε := prob μ (λ a, negb (bool_decide (f a))) ≤ ε`. -/
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
theorem zero_positive [Countable α] (μ : MeasureTheory.Measure α) :
    Pgl 0 (fun a => 0 < μ {a}) μ := by
  show μ {x | ¬ (0 < μ {x})} ≤ 0
  have hset : {x : α | ¬ (0 < μ {x})} = {x | μ {x} = 0} := by
    ext x; simp [pos_iff_ne_zero]
  rw [hset]
  have hctble : ({x : α | μ {x} = 0}).Countable :=
    Set.Countable.mono (Set.subset_univ _) Set.countable_univ
  exact ((MeasureTheory.measure_null_iff_singleton hctble).mpr (fun _ hx => hx)).le

end Pgl

/-! ## `ErisWpGS` ghost-state class

Resources required by the Eris weakest precondition: the invariant ghost
state, a state interpretation, and an error-credit interpretation. Mirrors
Rocq `erisWpGS`. No spec side — Eris is a unary logic.  -/

class ErisWpGS (GF : BundledGFunctors) where
  hlc : Bool
  invGS : InvGS_gen hlc GF
  stateInterp : State → IProp GF
  errInterp : ENNReal → IProp GF

attribute [reducible, instance] ErisWpGS.invGS

namespace ErisWpGS
variable {GF : BundledGFunctors}

/-! ## `execStutter` — credit-bump primitive

The Rocq `exec_stutter` modality says: there is a small slack `(R, ε₁, ε₂)`
splitting of the budget such that, *modulo* a `tgl (dret tt) R ε₁` coupling,
the body `P` holds at `ε₂`. Because the underlying distribution is `dret tt`
this collapses to a binary choice: either we have `1 ≤ ε` and the coupling
is vacuous, or `R tt` is forced and `P ε` follows.

We use the propositional collapsed form `execStutter₁` (`exec_stutter_1` in
Rocq) as the working definition — it is easier to reason about in Lean and
provably equivalent to the relational form. -/

/-- Propositional collapse of `exec_stutter`: either we already have ≥ 1 unit
of error (so any conclusion follows vacuously), or the body holds. -/
@[expose]
abbrev execStutter (P : ENNReal → IProp GF) (ε : ENNReal) : IProp GF :=
  iprop(⌜1 ≤ ε⌝ ∨ P ε)

/-- If you have `P ε`, you have `execStutter P ε`. -/
theorem execStutter_free {P : ENNReal → IProp GF} {ε : ENNReal} :
    P ε ⊢ execStutter P ε := by
  iintro HP; iright; iexact HP

/-- If you have `1 ≤ ε`, you have `execStutter P ε` for any `P`. -/
theorem execStutter_spend {P : ENNReal → IProp GF} {ε : ENNReal} (hε : 1 ≤ ε) :
    ⊢ execStutter (GF := GF) P ε := by
  iintro; ileft; ipure_intro; exact hε

/-- Combined monotonicity: any grade ↑ and body ↦ Q at the new grade. -/
theorem execStutter_mono {P Q : ENNReal → IProp GF} {ε ε' : ENNReal}
    (hε : ε ≤ ε') :
    iprop((P ε -∗ Q ε') ∗ execStutter P ε) ⊢ execStutter (GF := GF) Q ε' := by
  iintro ⟨HM, HS⟩
  icases HS with ⟨%HVac | HP⟩
  · ileft; ipure_intro; exact _root_.le_trans HVac hε
  · iright; iapply HM; iexact HP

/-- Body monotonicity at a fixed grade. -/
theorem execStutter_mono_pred {P Q : ENNReal → IProp GF} {ε : ENNReal} :
    iprop((P ε -∗ Q ε) ∗ execStutter P ε) ⊢ execStutter (GF := GF) Q ε :=
  execStutter_mono (_root_.le_refl ε)

variable [ErisWpGS GF]

/-! ## `glm` fixpoint state and pre-functor

The fixpoint operates on `(Cfg × ENNReal)` and produces an iProp. Rocq:
```
Definition glm_pre Z Φ : cfg × nonnegreal → iProp Σ :=
  λ '((e1, σ1), ε), <three disjuncts>.
Definition glm' Z := bi_least_fixpoint (glm_pre Z).
Definition glm e σ ε Z := glm' Z ((e, σ), ε).
```
-/

/-- Packed state for the `glm` fixpoint: a config paired with an error
budget. -/
@[expose]
abbrev GlmState : Type _ := Cfg × ENNReal

instance : COFE GlmState := COFE.ofDiscrete _ Eq_Equivalence
instance : OFE.Discrete GlmState := ⟨id⟩
instance : OFE.Leibniz GlmState := ⟨id⟩

/-- The `prim_step` disjunct, factored out: a relation `R`, an outer error
`ε₁`, and a per-outcome continuation `X₂` bounded by some `r`, such that
`primStep ⟨e₁, σ₁⟩` lifts `R` with slack `ε₁`, the expected total error is
within budget, and the body `Z` holds on every `R`-related successor under
the empty mask. -/
abbrev glmPrimStep
    (e₁ : Exp) (σ₁ : State) (ε : ENNReal)
    (Z : Cfg → ENNReal → IProp GF) : IProp GF :=
  iprop(∃ (R : Cfg → Prop) (ε₁ : ENNReal) (X₂ : Cfg → ENNReal) (r : ENNReal),
    (⌜Reducible e₁ σ₁⌝) ∗
    (⌜∀ ρ, X₂ ρ ≤ r⌝) ∗
    (⌜ε₁ + (∫⁻ ρ, X₂ ρ ∂(primStep ⟨e₁, σ₁⟩)) ≤ ε⌝) ∗
    (⌜Pgl ε₁ R (primStep ⟨e₁, σ₁⟩)⌝) ∗
    (∀ (ρ : Cfg), (⌜R ρ⌝) -∗
      |={∅}=> execStutter (Z ρ) (X₂ ρ)))

/-- One-step `glm` pre-functor. Disjuncts:

1. *Out-of-thin-air* — pay nothing and bump `ε` to any `ε' > ε`, then
   continue at `ε'`.
2. *Prim-step* — take one program step; see `glmPrimStep`.

The third (presampling) disjunct will be added when `PresampleRules.lean`
is ported. -/
abbrev glmPre
    (Z : Cfg → ENNReal → IProp GF)
    (Φ : GlmState → IProp GF) : GlmState → IProp GF :=
  fun ⟨ρ, ε⟩ => iprop%
    (∀ (ε' : ENNReal), (⌜ε < ε'⌝) -∗
        |={∅}=> execStutter (fun ε'' => Φ (ρ, ε'')) ε') ∨
    glmPrimStep ρ.expr ρ.state ε Z

/-- `glm e σ ε Z` is the least fixpoint of `glmPre Z`, evaluated at
`(⟨e, σ⟩, ε)`. -/
@[expose]
abbrev glm (e : Exp) (σ : State) (ε : ENNReal)
    (Z : Cfg → ENNReal → IProp GF) : IProp GF :=
  bi_least_fixpoint (glmPre (GF := GF) Z) ((⟨e, σ⟩, ε) : GlmState)

/-- The pre-functor is monotone in `Φ`. -/
instance glmPre_mono {Z : Cfg → ENNReal → IProp GF} :
    BIMonoPred (glmPre (GF := GF) Z) where
  mono_pred {Φ Ψ _ _} := by
    iintro #Hwand %s Hs
    rcases s with ⟨ρ, ε⟩
    icases Hs with ⟨HOT | HPS⟩
    · ileft
      iintro %ε' %Hlt
      imod HOT $$ %ε' %Hlt with HS
      imodintro
      icases HS with ⟨%HVac | HP⟩
      · ileft; ipure_intro; exact HVac
      · iright; iapply Hwand; iexact HP
    · iright
      icases HPS with ⟨%R, %ε₁, %X₂, %r, %Hred, %Hbnd, %Hexp, %Hpgl, HCont⟩
      iexists R, ε₁, X₂, r
      isplitr; · ipure_intro; exact Hred
      isplitr; · ipure_intro; exact Hbnd
      isplitr; · ipure_intro; exact Hexp
      isplitr; · ipure_intro; exact Hpgl
      iintro %ρ' HR
      ihave HC := HCont $$ %ρ' HR
      imod HC
      imodintro
      iexact HC
  mono_pred_ne.ne {_ s s'} hd := by
    have := eq_of_dist_discrete_leibniz hd; subst this; exact .of_eq rfl

/-- Unfolding equation: `glm` equals one application of the pre-functor at
the fixpoint. -/
theorem glm_unfold {e : Exp} {σ : State} {ε : ENNReal}
    {Z : Cfg → ENNReal → IProp GF} :
    glm (GF := GF) e σ ε Z ≡
      glmPre (GF := GF) Z
        (fun s => glm s.1.expr s.1.state s.2 Z)
        ((⟨e, σ⟩, ε) : GlmState) :=
  least_fixpoint_unfold _

/-- Strong monotonicity in the body `Z` under a *spatial* continuation wand.

Uses the standard "carry the wand through the fixpoint" trick: the
non-expansive predicate `Ψ` packs the wand as a parameter, so each iteration
of `least_fixpoint_iter` reuses the same shared wand at every fixpoint point
without requiring `□`.

Mirrors Rocq's `glm_strong_mono` (specialised to equal grading; the
ε-relaxation form would compose with `glm_mono_grading`, deferred). -/
theorem glm_strong_mono {e : Exp} {σ : State} {ε : ENNReal}
    {Z₁ Z₂ : Cfg → ENNReal → IProp GF} :
    iprop((∀ ρ ε', Z₁ ρ ε' -∗ Z₂ ρ ε') ∗ glm e σ ε Z₁) ⊢@{IProp GF}
      glm e σ ε Z₂ := by
  iintro ⟨HZ, HG⟩
  letI Ψ : GlmState → IProp GF := fun s => iprop(
    (∀ ρ ε', Z₁ ρ ε' -∗ Z₂ ρ ε') -∗ bi_least_fixpoint (glmPre Z₂) s)
  letI : NonExpansive Ψ := by
    constructor
    intro n s s' hd
    have : s = s' := OFE.Leibniz.eq_of_eqv (OFE.Discrete.discrete_0 hd)
    subst this; exact .of_eq rfl
  -- Apply the iter to derive `Ψ ⟨..., ε⟩` from `HG`.
  ihave HΨ : iprop(Ψ ((⟨e, σ⟩, ε) : GlmState)) $$ [HG]
  · iapply least_fixpoint_iter (F := glmPre Z₁) (Φ := Ψ)
    swap; · iexact HG
    -- Discharge: `□ (∀ y, glmPre Z₁ Ψ y -∗ Ψ y)`.
    iintro !> %s HF
    iintro Hwand
    iapply least_fixpoint_unfold_2 (glmPre Z₂)
    rcases s with ⟨ρ, ε⟩
    icases HF with ⟨HOT | HPS⟩
    · ileft
      iintro %ε' %Hlt
      imod HOT $$ %ε' %Hlt with HS
      imodintro
      icases HS with ⟨%HVac | HP⟩
      · ileft; ipure_intro; exact HVac
      · iright
        -- HP : Ψ ⟨ρ, ε''⟩ = wand -∗ bi_least_fixpoint (glmPre Z₂) ⟨ρ, ε''⟩
        iapply HP; iexact Hwand
    · iright
      icases HPS with ⟨%R, %ε₁, %X₂, %r, %Hred, %Hbnd, %Hexp, %Hpgl, HCont⟩
      iexists R, ε₁, X₂, r
      isplitr; · ipure_intro; exact Hred
      isplitr; · ipure_intro; exact Hbnd
      isplitr; · ipure_intro; exact Hexp
      isplitr; · ipure_intro; exact Hpgl
      iintro %ρ' HR
      ihave HC := HCont $$ %ρ' HR
      imod HC with HS
      imodintro
      icases HS with ⟨%HVac | HC1⟩
      · ileft; ipure_intro; exact HVac
      · iright
        -- HC1 : Z₁ ρ' (X₂ ρ') (leaf, not recursive — `Z` in `glmPre` is the leaf)
        -- Goal: Z₂ ρ' (X₂ ρ')
        iapply Hwand; iexact HC1
  iapply HΨ; iexact HZ

/-- Monotonicity in the error grade: `ε ≤ ε' → glm e σ ε Z ⊢ glm e σ ε' Z`.
Direct single-step weakening of the bound in both disjuncts (the recursive
calls are unchanged). Rocq: `glm_mono_grading`. -/
theorem glm_mono_grading {e : Exp} {σ : State} {ε ε' : ENNReal}
    {Z : Cfg → ENNReal → IProp GF} (Hε : ε ≤ ε') :
    glm e σ ε Z ⊢@{IProp GF} glm e σ ε' Z := by
  iintro HG
  ihave HG' := (BI.equiv_iff.mp glm_unfold).1 $$ HG
  iapply (BI.equiv_iff.mp glm_unfold).2
  icases HG' with ⟨HOT | HPS⟩
  · ileft
    iintro %ε'' %Hlt'
    have Hlt : ε < ε'' := _root_.lt_of_le_of_lt Hε Hlt'
    ispecialize HOT $$ %ε'' %Hlt
    iexact HOT
  · iright
    icases HPS with ⟨%R, %ε₁, %X₂, %r, %Hred, %Hbnd, %Hexp, %Hpgl, HCont⟩
    iexists R, ε₁, X₂, r
    isplitr; · ipure_intro; exact Hred
    isplitr; · ipure_intro; exact Hbnd
    isplitr; · ipure_intro; exact _root_.le_trans Hexp Hε
    isplitr; · ipure_intro; exact Hpgl
    iexact HCont

/-- Monotonicity in the body `Z` under an *intuitionistic* continuation
entailment. Specialised, easier-to-use form of `glm_strong_mono`. -/
theorem glm_mono_pred {e : Exp} {σ : State} {ε : ENNReal}
    {Z₁ Z₂ : Cfg → ENNReal → IProp GF} :
    iprop((□ (∀ ρ ε', Z₁ ρ ε' -∗ Z₂ ρ ε')) ∗ glm e σ ε Z₁) ⊢@{IProp GF}
      glm e σ ε Z₂ := by
  iintro ⟨#HZ, HG⟩
  unfold glm
  iapply (least_fixpoint_strong_mono (glmPre Z₁) (glmPre Z₂))
    $$ [] HG
  iintro !> %Φ %s HF
  rcases s with ⟨ρ, ε⟩
  icases HF with ⟨HOT | HPS⟩
  · ileft
    iintro %ε' %Hlt
    imod HOT $$ %ε' %Hlt with HS
    imodintro
    iexact HS
  · iright
    icases HPS with ⟨%R, %ε₁, %X₂, %r, %Hred, %Hbnd, %Hexp, %Hpgl, HCont⟩
    iexists R, ε₁, X₂, r
    isplitr; · ipure_intro; exact Hred
    isplitr; · ipure_intro; exact Hbnd
    isplitr; · ipure_intro; exact Hexp
    isplitr; · ipure_intro; exact Hpgl
    iintro %ρ' HR
    ihave HC := HCont $$ %ρ' HR
    imod HC
    imodintro
    icases HC with ⟨%HVac | HC1⟩
    · ileft; ipure_intro; exact HVac
    · iright; iapply HZ; iexact HC1

/-- Evaluation-context bind for `glm`: a `glm` derivation at `e` with
continuation lifted through `K` produces a `glm` at `K.fill e` with the
unlifted continuation. Rocq: `weakestpre.v:367`.

Uses `least_fixpoint_iter` with `Φ s := bi_least_fixpoint (glmPre Z) ⟨K.fillCfg s.1, s.2⟩`.
The outer `e` does NOT need to be a non-value — Lean's `Hsv` (the
non-value-ness needed for `primStep_fill`) is derived per-iteration from the
prim-step branch's `Reducible` witness via `val_stuck`. -/
theorem glm_bind {K : Ectx} {e : Exp} {σ : State} {ε : ENNReal}
    {Z : Cfg → ENNReal → IProp GF} :
    glm e σ ε (fun ρ ε' => Z ⟨K.fill ρ.expr, ρ.state⟩ ε') ⊢@{IProp GF}
      glm (K.fill e) σ ε Z := by
  iintro HG
  classical
  let Kinv : Exp → Option Exp := Function.partialInv K.fill
  have Kinv_left : ∀ e', Kinv (K.fill e') = some e' :=
    Function.partialInv_left (Ectx.fill_injective K)
  letI Z' : Cfg → ENNReal → IProp GF :=
    fun ρ ε' => Z ⟨K.fill ρ.expr, ρ.state⟩ ε'
  letI Φ : GlmState → IProp GF :=
    fun s => bi_least_fixpoint (glmPre Z) ((⟨K.fill s.1.expr, s.1.state⟩, s.2) : GlmState)
  letI : NonExpansive Φ := nonExpansive_of_discrete_leibniz Φ
  ihave HΦ : iprop(Φ ((⟨e, σ⟩, ε) : GlmState)) $$ [HG]
  · iapply least_fixpoint_iter (F := glmPre Z') (Φ := Φ)
    swap; · iexact HG
    iintro !> %s HF
    rcases s with ⟨ρ, ε'⟩
    iapply least_fixpoint_unfold_2 (glmPre Z)
    icases HF with ⟨HOT | HPS⟩
    · -- OT branch.
      ileft
      iintro %ε'' %Hlt
      imod HOT $$ %ε'' %Hlt with HS
      imodintro
      icases HS with ⟨%HVac | HP⟩
      · ileft; ipure_intro; exact HVac
      · iright; iexact HP
    · -- prim_step branch.
      iright
      icases HPS with ⟨%R, %ε₁, %X₂, %r, %Hred, %Hbnd, %Hexp, %Hpgl, HCont⟩
      iexists (fun ρ' => ∃ ρ'', ρ' = K.fillCfg ρ'' ∧ R ρ''), ε₁,
        (fun ρ' => (Kinv ρ'.expr).elim 0 (fun e' => X₂ ⟨e', ρ'.state⟩)),
        r
      have Hsv : ¬ ρ.expr.isValue := val_stuck Hred.choose_spec
      isplitr; · ipure_intro; exact Hred.fill K
      isplitr
      · ipure_intro
        intro ρ'
        cases h : Kinv ρ'.expr with
        | none => simp [h, Option.elim]
        | some e' => simp [h, Option.elim]; exact Hbnd ⟨e', ρ'.state⟩
      isplitr
      · ipure_intro
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
      · ipure_intro
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
      · ileft; ipure_intro; exact HVac
      · iright; iexact HC1
  -- `Φ ⟨e, σ, ε⟩ = bi_least_fixpoint (glmPre Z) (⟨K.fill e, σ⟩, ε) = glm (K.fill e) σ ε Z`
  -- by definitional unfolding (Φ is `letI`-bound, `glm` is `@[reducible]`).
  iexact HΦ

/-! ## Introduction rules for `glm` -/

/-- *Right-introduction* for the `prim_step` disjunct: from the appropriate
coupling data, conclude `glm e σ ε Z`. Equivalent to Rocq's `glm_prim_step`. -/
theorem glm_prim_step {e : Exp} {σ : State} {ε : ENNReal}
    {Z : Cfg → ENNReal → IProp GF} :
    iprop(∃ (R : Cfg → Prop) (ε₁ : ENNReal) (X₂ : Cfg → ENNReal) (r : ENNReal),
      ⌜Reducible e σ⌝ ∗
      ⌜∀ ρ, X₂ ρ ≤ r⌝ ∗
      ⌜ε₁ + (∫⁻ ρ, X₂ ρ ∂(primStep ⟨e, σ⟩)) ≤ ε⌝ ∗
      ⌜Pgl ε₁ R (primStep ⟨e, σ⟩)⌝ ∗
      (∀ (ρ : Cfg), (⌜R ρ⌝) -∗ |={∅}=> execStutter (Z ρ) (X₂ ρ))) ⊢@{IProp GF}
        glm e σ ε Z := by
  iintro HPS
  unfold glm
  iapply least_fixpoint_unfold_2 (glmPre Z)
  iright
  iexact HPS

/-- *Right-introduction* for the out-of-thin-air disjunct. -/
theorem glm_credit_bump {e : Exp} {σ : State} {ε : ENNReal}
    {Z : Cfg → ENNReal → IProp GF} :
    iprop(∀ (ε' : ENNReal), ⌜ε < ε'⌝ -∗
      |={∅}=> execStutter (fun ε'' => glm e σ ε'' Z) ε') ⊢@{IProp GF}
        glm e σ ε Z := by
  iintro HOT
  unfold glm
  iapply least_fixpoint_unfold_2 (glmPre Z)
  ileft
  iexact HOT

end ErisWpGS

end TotalEris
end ProbLang
