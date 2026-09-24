module

public import Metrology.Iris.SpecUpdate
public import Metrology.Iris.ErrorCredits
public import Metrology.Iris.Fixpoint
public import Metrology.Couplings.AdditiveCouplings
public import Metrology.Couplings.Couplings
public import Metrology.ProbLang.Syntax.LocallyClosed
public import Metrology.ProbLang.Exec
public import Metrology.ProbLang.Erasable
public import Metrology.ProbLang.Erasure
public import Iris.BI.Lib.Fixpoint
public import Iris.ProofMode.Classes
public import Iris.ProofMode.InstancesUpdates

@[expose] public section


open Std Iris Iris.Std Iris.BI Iris.ProofMode OFE COFE ProbLang

namespace ProbLang

-- For the Approxis layer, carry the abstract real type `rT` as a section variable.


variable {rT : Type _} [ProbLang.ProbLangℝ rT]


/-! ## Approxis ghost state class -/

/-- Resources required by the Approxis weakest precondition: the spec-side
update modality, the invariant ghost state, a state interpretation, and an
error-credit interpretation. -/
class ApproxisWpGS {rT : Type _} [ProbLangℝ rT] [MeasurableSingletonClass rT]
    (GF : BundledGFunctors) extends SpecUpdateGS rT GF where
  hlc : HasLC
  invGS : InvGS_gen hlc GF
  stateInterp : State rT → IProp GF
  errInterp : ENNReal → IProp GF

attribute [reducible, instance] ApproxisWpGS.invGS

namespace ApproxisWpGS
variable {GF : BundledGFunctors} [ApproxisWpGS (rT := rT) GF]

/-! `spec_coupl` modality

Lets us optionally prepend spec-side execution steps and erasable
distributions on both sides before establishing the body `Z`. -/

/-- The packaged state for `spec_coupl`'s fixpoint: `(σ, (e', σ'), ε)` collapsed
into a single tuple so we can write a `BIMonoPred` over it. -/
abbrev SpecCouplState (rT : Type _) [ProbLangℝ rT] [MeasurableSingletonClass rT] :
    Type _ := (State rT) × (Cfg rT) × ENNReal

instance : COFE (SpecCouplState rT) := COFE.ofDiscrete _
instance : OFE.Discrete (SpecCouplState rT) := ⟨id⟩

/-- The third (coupling) disjunct of `specCouplPre`, factored out for clarity.

There exist:
* a relation `S` between LHS states and RHS configurations;
* a number of spec-side steps `n`;
* erasable distributions `μ₁` on the LHS, `μ₁'` on the RHS;
* an outer error budget `ε₁`;
* a per-RHS-config error continuation `X₂` bounded by some `r`;

such that `μ₁` and `μ₁' >>= pexecN n` are `AddCoupl`-coupled at `S` with slack
`ε₁`, and `ε₁ + 𝔼[X₂]` (under the bound measure) doesn't exceed `ε`. The
continuation `Φ` is invoked on every `(σ₂, ⟨e₂', σ₂'⟩)` related by `S`, with
the local error `X₂ ⟨e₂', σ₂'⟩`. -/
abbrev specCouplCouple (E : CoPset)
    (σ₁ : State rT) (e₁' : Exp rT) (σ₁' : State rT) (ε : ENNReal)
    (Φ : SpecCouplState rT → IProp GF) : IProp GF :=
  iprop(∃ (S : State rT → Cfg rT → Prop) (n : Nat)
          (μ₁ : MeasureTheory.Measure (State rT)) (μ₁' : MeasureTheory.Measure (State rT))
          (ε₁ : ENNReal) (X₂ : Cfg rT → ENNReal) (r : ENNReal),
    (⌜AddCoupl ε₁ {p : State rT × (Cfg rT) | S p.1 p.2} μ₁ (μ₁'.bind (fun σ => pexecN n ⟨e₁', σ⟩))⌝)
    ∗
    (⌜Measurable X₂⌝) ∗
    (⌜∀ ρ, X₂ ρ ≤ r⌝) ∗
    (⌜ε₁ + (∫⁻ ρ, X₂ ρ ∂(μ₁'.bind (fun σ => pexecN n ⟨e₁', σ⟩))) ≤ ε⌝) ∗
    (⌜ErasableExpr μ₁ σ₁⌝) ∗
    (⌜ErasableExpr μ₁' σ₁'⌝) ∗
    (∀ (σ₂ : State rT) (e₂' : Exp rT) (σ₂' : State rT),
      (⌜S σ₂ ⟨e₂', σ₂'⟩⌝) -∗ |={E}=> Φ
      ((σ₂, (⟨e₂', σ₂'⟩ : Cfg rT), X₂ ⟨e₂', σ₂'⟩) : SpecCouplState rT)))

/-- The pre-functor whose least fixpoint is `specCoupl`.

⚠️ **Must be `abbrev`, not `def`** — the `BIMonoPred` and `specCoupl_mono`
proofs rely on `iexact` seeing through to the body when the `Φ` argument
varies. Demoting this to `def` will break those proofs with
`iexact: cannot unify specCouplPre E Z Φ s and specCouplPre E Z Ψ s`. -/
abbrev specCouplPre (E : CoPset) (Z : State rT → Cfg rT → ENNReal → IProp GF)
    (Φ : SpecCouplState rT → IProp GF) : SpecCouplState rT → IProp GF :=
  fun ⟨σ₁, ⟨e₁', σ₁'⟩, ε⟩ => iprop%
    ⌜1 ≤ ε⌝ ∨
    Z σ₁ ⟨e₁', σ₁'⟩ ε ∨
    specCouplCouple E σ₁ e₁' σ₁' ε Φ

abbrev specCoupl (E : CoPset) (σ : State rT) (e' : Exp rT) (σ' : State rT) (ε : ENNReal)
    (Z : State rT → Cfg rT → ENNReal → IProp GF) : IProp GF :=
  bi_least_fixpoint (specCouplPre (GF := GF) E Z)
    ((σ, (⟨e', σ'⟩ : Cfg rT), ε) : SpecCouplState rT)

omit [ApproxisWpGS (rT := rT) GF] in
/-- `SpecCouplState` is discrete, so every function out of it is non-expansive. -/
theorem specCouplState_ne {Φ : SpecCouplState rT → IProp GF} : NonExpansive Φ where
  ne _ _ _ hd := .of_eq (congrArg Φ (OFE.Discrete.discrete_0 hd))

macro "spec_trivial_left" : tactic => `(tactic| (isplitr; · ipureintro; trivial))
macro "spec_trivial_cases" : tactic => `(tactic| repeat spec_trivial_left)

/-- `specCouplPre` is monotone in its `Φ` argument.

The placeholder body `⌜1 ≤ ε⌝ ∨ Z σ ρ' ε` doesn't actually use `Φ`, so
monotonicity is trivial. (Once the third coupling-disjunct is restored, the
quantifier-under-fupd case will appeal to `Hwand`.) -/
instance specCouplPre_mono {E : CoPset} {Z : State rT → Cfg rT → ENNReal → IProp GF} :
    BIMonoPred (specCouplPre (GF := GF) E Z) where
  mono_pred {Φ Ψ _ _} := by
    iintro #Hwand %s Hs
    icases Hs with ⟨HVac | HZ | HCpl⟩
    · ileft; iexact HVac
    · iright; ileft; iexact HZ
    · iright; iright
      icases HCpl with ⟨%S, %n, %μ₁, %μ₁', %ε₁, %X₂, %r, %Hc, %HX₂meas, %Hb, %Hexp, %Herase₁,
        %Herase₂, Hcont⟩
      iexists S, n, μ₁, μ₁', ε₁, X₂, r
      spec_trivial_cases
      iintro %σ₂ %e₂' %σ₂' %HS
      imod Hcont $$ %σ₂ %e₂' %σ₂' %HS with HΦ
      imodintro
      iapply Hwand $$ HΦ
  mono_pred_ne := specCouplState_ne

/-- Trivial introduction: if `1 ≤ ε`, the coupling holds vacuously. -/
theorem specCoupl_err_ge_1 {E : CoPset} {σ : State rT} {e' : Exp rT} {σ' : State rT} {ε : ENNReal}
    {Z : State rT → Cfg rT → ENNReal → IProp GF} (hε : 1 ≤ ε) : ⊢ specCoupl E σ e' σ' ε Z := by
  iapply least_fixpoint_unfold_mpr (specCouplPre E Z)
  ileft
  ipureintro
  exact hε

/-- `Z`-introduction: from the body `Z`, conclude the coupling. -/
theorem specCoupl_ret {E : CoPset} {σ : State rT} {e' : Exp rT} {σ' : State rT}
    {ε : ENNReal} {Z : State rT → Cfg rT → ENNReal → IProp GF} :
    Z σ ⟨e', σ'⟩ ε ⊢@{IProp GF} specCoupl E σ e' σ' ε Z := by
  iintro HZ
  iapply least_fixpoint_unfold_mpr (specCouplPre E Z)
  iright
  ileft
  iexact HZ

/-- Coupling-case introduction: if there's an erasable-distribution coupling that
sequences into a continuation eventually establishing the body, then the
modality holds.

The continuation argument is given against `specCoupl` itself (corecursive
shape), matching Rocq's `spec_coupl_rec`. -/
theorem specCoupl_rec {E : CoPset} {σ : State rT} {e' : Exp rT} {σ' : State rT}
    {ε : ENNReal} {Z : State rT → Cfg rT → ENNReal → IProp GF} :
    specCouplCouple E σ e' σ' ε
        (fun s => specCoupl E s.1 s.2.1.expr s.2.1.state s.2.2 Z)
      ⊢@{IProp GF} specCoupl E σ e' σ' ε Z := by
  iintro HCpl
  unfold specCoupl
  iapply (least_fixpoint_unfold_mpr (specCouplPre E Z))
  unfold specCouplPre
  iright
  iright
  iexact HCpl

/-- Unfolding equation for `specCoupl`: it equals one application of the
pre-functor at the fixpoint. -/
theorem specCoupl_unfold {E : CoPset} {σ : State rT} {e' : Exp rT} {σ' : State rT}
    {ε : ENNReal} {Z : State rT → Cfg rT → ENNReal → IProp GF} :
    specCoupl (GF := GF) E σ e' σ' ε Z =
      specCouplPre (GF := GF) E Z
        (fun s => specCoupl E s.1 s.2.1.expr s.2.1.state s.2.2 Z)
        ((σ, (⟨e', σ'⟩ : Cfg rT), ε) : SpecCouplState rT) :=
  least_fixpoint_unfold _

/-- Strong monotonicity of `specCoupl`: a *persistent* continuation entailment
lifts through the modality.

The continuation hypothesis is required to be intuitionistic (`□`) because we
need it inside the fixpoint induction, which works under a `□`-modality. -/
theorem specCoupl_mono {E : CoPset} {σ : State rT} {e' : Exp rT} {σ' : State rT}
    {ε : ENNReal} {Z₁ Z₂ : State rT → Cfg rT → ENNReal → IProp GF} :
    iprop((□ (∀ σ' ρ' ε', Z₁ σ' ρ' ε' -∗ Z₂ σ' ρ' ε')) ∗
        specCoupl E σ e' σ' ε Z₁) ⊢@{IProp GF}
      specCoupl E σ e' σ' ε Z₂ := by
  iintro ⟨#HZ, HC⟩
  unfold specCoupl
  iapply (least_fixpoint_strong_mono (specCouplPre E Z₁) (specCouplPre E Z₂))
    $$ [] HC
  iintro !> %Φ %s HF
  icases HF with ⟨HVac | HZ1 | HCpl⟩
  · ileft; iexact HVac
  · iright; ileft
    iapply HZ $$ HZ1
  · iright; iright
    icases HCpl with ⟨%S, %n, %μ₁, %μ₁', %ε₁, %X₂, %r,
      %HCpl_coupl, %HCpl_meas, %HCpl_bnd, %HCpl_exp, %HCpl_e1, %HCpl_e2, HCpl_cont⟩
    iexists S, n, μ₁, μ₁', ε₁, X₂, r
    spec_trivial_cases
    iexact HCpl_cont

/-- Bind for `specCoupl` (spatial-continuation form): chain a `spec_coupl` with a
continuation that itself produces a `spec_coupl`. Requires `E1 ⊆ E2`.

The continuation `(∀ ..., Z₁ ... -∗ specCoupl E2 ...)` is **spatial**, not
intuitionistic — so Rocq's `iApply (spec_coupl_bind with "[-H] H")` framing
idiom translates: the caller can `irevert` other spatial hypotheses into the
goal first, making them universally-quantified inputs to the bind body.

Proof uses `least_fixpoint_iter` with `Φ s := HZ -∗ specCoupl E2 s.1 ... Z₂`
so the spatial HZ is wand-bound inside the iteration. -/
theorem specCoupl_bind {E1 E2 : CoPset} {σ : State rT} {e' : Exp rT} {σ' : State rT}
    {ε : ENNReal} {Z₁ Z₂ : State rT → Cfg rT → ENNReal → IProp GF}
    (HE : E1 ⊆ E2) :
    iprop((∀ σ₂ ρ₂ ε', Z₁ σ₂ ρ₂ ε' -∗ specCoupl E2 σ₂ ρ₂.expr ρ₂.state ε' Z₂) ∗
        specCoupl E1 σ e' σ' ε Z₁) ⊢@{IProp GF}
      specCoupl E2 σ e' σ' ε Z₂ := by
  iintro ⟨HZ, HC⟩
  -- Pack HZ into the iteration target: `Φ s := HZ -∗ specCoupl E2 s.1 ... Z₂`.
  -- Then the body need only intro HZ to recover spatial access.
  let HZty : IProp GF :=
    iprop(∀ σ₂ ρ₂ ε', Z₁ σ₂ ρ₂ ε' -∗ specCoupl E2 σ₂ ρ₂.expr ρ₂.state ε' Z₂)
  let Φ : SpecCouplState rT → IProp GF := fun s =>
    iprop(HZty -∗ specCoupl E2 s.1 s.2.1.expr s.2.1.state s.2.2 Z₂)
  have HΦne : NonExpansive Φ := specCouplState_ne
  -- Apply iter; the resulting `Φ s` is `HZty -∗ specCoupl E2 s.1 ... Z₂`,
  -- which we close by feeding HZ.
  ihave Hiter := least_fixpoint_iter (F := specCouplPre E1 Z₁) (Φ := Φ)
    $$ [] %((σ, (⟨e', σ'⟩ : Cfg rT), ε) : SpecCouplState rT) HC
  swap
  · -- After iteration, Hiter : Φ (σ, ⟨e', σ'⟩, ε), feed HZ.
    iapply Hiter $$ HZ
  -- Goal: `□ (∀ y, specCouplPre E1 Z₁ Φ y -∗ Φ y)`.
  iintro !> %s HF HZ
  icases HF with ⟨%HVac | HZ1 | HCpl⟩
  · iapply (specCoupl_err_ge_1 (GF := GF)
      (E := E2) (σ := s.1) (e' := s.2.1.expr) (σ' := s.2.1.state)
      (ε := s.2.2) (Z := Z₂) HVac)
  · iapply HZ $$ HZ1
  · iapply specCoupl_rec
    icases HCpl with ⟨%S, %n, %μ₁, %μ₁', %ε₁, %X₂, %r,
      %HCpl_coupl, %HCpl_meas, %HCpl_bnd, %HCpl_exp, %HCpl_e1, %HCpl_e2, HCpl_cont⟩
    iexists S, n, μ₁, μ₁', ε₁, X₂, r
    spec_trivial_cases
    iintro %σ₂ %e₂' %σ₂' %HS
    -- The recursive body produces `HZ -∗ specCoupl E2 ...` after applying
    -- HCpl_cont; we feed HZ to close. Mask plumbing: E2 → E1 → close.
    imod (BIFUpdate.subset HE) with Hclose
    ispecialize HCpl_cont $$ %σ₂ %e₂' %σ₂' %HS
    imod HCpl_cont
    imod Hclose
    imodintro
    iapply HCpl_cont $$ HZ

/-- Spatial-continuation mono for `specCoupl`, derived from `specCoupl_bind` +
`specCoupl_ret`. -/
theorem specCoupl_mono_spatial {E : CoPset} {σ : State rT} {e' : Exp rT} {σ' : State rT}
    {ε : ENNReal} {Z₁ Z₂ : State rT → Cfg rT → ENNReal → IProp GF} :
    iprop((∀ σ' ρ' ε', Z₁ σ' ρ' ε' -∗ Z₂ σ' ρ' ε') ∗
        specCoupl E σ e' σ' ε Z₁) ⊢@{IProp GF}
      specCoupl E σ e' σ' ε Z₂ := by
  iintro ⟨HZ, HC⟩
  iapply specCoupl_bind (E1 := E) (E2 := E) Std.LawfulSet.subset_refl
  iframe HC
  iintro %σ₂ %ρ₂ %ε₂ Hz1
  iapply specCoupl_ret
  iapply HZ $$ Hz1

/-! ## `prog_coupl` modality

Couples *exactly one* program step against any number of spec steps and an
erasable distribution. Used by `wp_pre` for the non-value case. -/

/-- `prog_coupl e₁ σ₁ e₁' σ₁' ε Z` says: `(e₁, σ₁)` is reducible, and there
exist a number `n` of spec steps, an erasable RHS state distribution `μ₁'`,
and a per-(LHS-cfg, RHS-cfg) error continuation `X₂` bounded by some `r`,
such that for any pair of `[0,1]`-bounded test functions `h₁`, `h₂` with
`h₁ a ≤ h₂ b + X₂ a b`, the expectations satisfy
`𝔼[h₁ over primStep] ≤ 𝔼[h₂ over μ₁' >>= pexecN n] + ε`. The body `Z`
produces the post-state under the empty mask. -/
abbrev progCoupl (e₁ : Exp rT) (σ₁ : State rT) (e₁' : Exp rT) (σ₁' : State rT) (ε : ENNReal)
    (Z : Exp rT → State rT → Exp rT → State rT → ENNReal → IProp GF) : IProp GF :=
  iprop(∃ (n : Nat) (μ₁' : MeasureTheory.Measure (State rT))
          (X₂ : Cfg rT → Cfg rT → ENNReal),
    (⌜Reducible e₁ σ₁⌝) ∗
    (⌜∃ r : ENNReal, ∀ ρ₁ ρ₂, X₂ ρ₁ ρ₂ ≤ r⌝) ∗
    (⌜ExpCoupl ε X₂ (primStep ⟨e₁, σ₁⟩) (μ₁'.bind (fun σ => pexecN n ⟨e₁', σ⟩))⌝) ∗
    (⌜ErasableExpr μ₁' σ₁'⌝) ∗
    (∀ (e₂ : Exp rT) (σ₂ : State rT) (e₂' : Exp rT) (σ₂' : State rT),
      |={∅}=> Z e₂ σ₂ e₂' σ₂' (X₂ ⟨e₂, σ₂⟩ ⟨e₂', σ₂'⟩)))

/-- Outer non-expansiveness of `specCoupl` in its body `Z` at a single
distance `n`. The fixed-`n` form is what we need for the structural walk in
`wpPre_contractive`. -/
theorem specCoupl_ne {n : Nat} {E : CoPset} {σ : State rT} {e' : Exp rT} {σ' : State rT}
    {ε : ENNReal} {Z₁ Z₂ : State rT → Cfg rT → ENNReal → IProp GF}
    (HZ : ∀ σ ρ ε, Z₁ σ ρ ε ≡{n}≡ Z₂ σ ρ ε) :
    specCoupl E σ e' σ' ε Z₁ ≡{n}≡ specCoupl E σ e' σ' ε Z₂ := by
  unfold specCoupl
  refine least_fixpoint_ne_outer (fun _ s => ?_) (.of_eq rfl)
  exact or_ne.ne (.of_eq rfl) (or_ne.ne (HZ s.1 s.2.1 s.2.2) (.of_eq rfl))

/-- Outer non-expansiveness of `progCoupl` in its continuation `Z`. -/
theorem progCoupl_ne {n : Nat} {e₁ : Exp rT} {σ₁ : State rT} {e₁' : Exp rT} {σ₁' : State rT}
    {ε : ENNReal} {Z₁ Z₂ : Exp rT → State rT → Exp rT → State rT → ENNReal → IProp GF}
    (HZ : ∀ e₂ σ₂ e₂' σ₂' ε', Z₁ e₂ σ₂ e₂' σ₂' ε' ≡{n}≡ Z₂ e₂ σ₂ e₂' σ₂' ε') :
    progCoupl e₁ σ₁ e₁' σ₁' ε Z₁ ≡{n}≡ progCoupl e₁ σ₁ e₁' σ₁' ε Z₂ := by
  refine exists_ne fun _ => exists_ne fun _ => exists_ne fun _ => ?_
  -- The four leading conjuncts (`Reducible`, the bound, the expectation bound and
  -- `ErasableExpr`) are pure `Prop`s, so only the continuation moves.
  refine sep_ne.ne (.of_eq rfl) <| sep_ne.ne (.of_eq rfl) <| sep_ne.ne (.of_eq rfl) <|
    sep_ne.ne (.of_eq rfl) ?_
  exact forall_ne fun _ => forall_ne fun _ => forall_ne fun _ => forall_ne fun _ =>
    BIFUpdate.ne.ne (HZ _ _ _ _ _)

/-- Monotonicity of `progCoupl` under a continuation rewrite. -/
theorem progCoupl_mono {e₁ : Exp rT} {σ₁ : State rT} {e₁' : Exp rT} {σ₁' : State rT}
    {ε : ENNReal} {Z₁ Z₂ : Exp rT → State rT → Exp rT → State rT → ENNReal → IProp GF} :
    iprop((∀ e₂ σ₂ e₂' σ₂' ε', Z₁ e₂ σ₂ e₂' σ₂' ε' -∗ Z₂ e₂ σ₂ e₂' σ₂' ε') ∗
        progCoupl e₁ σ₁ e₁' σ₁' ε Z₁) ⊢@{IProp GF}
      progCoupl e₁ σ₁ e₁' σ₁' ε Z₂ := by
  iintro ⟨HZ, HCpl⟩
  icases HCpl with ⟨%n, %μ₁', %X₂, %Hred, %Hbnd, %Hexp, %Heras, HCont⟩
  iexists n, μ₁', X₂
  spec_trivial_cases
  iintro %e₂ %σ₂ %e₂' %σ₂'
  ihave HZ' := HCont $$ %e₂ %σ₂ %e₂' %σ₂'
  imod HZ'
  imodintro
  iapply HZ $$ HZ'

/-! ## Weakest precondition

WP is the guarded fixpoint of `wp_pre`. The pre takes a recursive `wp`
parameter and produces, for each expression `e₁` and post `Φ`, a coupling
update that:
* if `e₁` is a value, closes with `Φ v`,
* otherwise, takes one program step (via `prog_coupl`) and recurses. -/

/-- `wp_pre wp E e Φ`: one unfolding of the WP fixpoint.

Marked `abbrev` (not `def`) so `ispecialize`/`iapply` see through the
forall-wand body without needing an explicit `unfold` step. -/
abbrev wpPre
    (wp : CoPset → Exp rT → ((Val rT) → IProp GF) → IProp GF)
    (E : CoPset) (e₁ : Exp rT) (Φ : Val rT → IProp GF) : IProp GF :=
  iprop(∀ (σ₁ : State rT) (e₁' : Exp rT) (σ₁' : State rT) (ε₁ : ENNReal),
    (stateInterp (rT := rT) σ₁ ∗ SpecUpdateGS.specInterp (rT := rT) ⟨e₁', σ₁'⟩ ∗
      errInterp (rT := rT) ε₁) -∗
      |={E, ∅}=> specCoupl ∅ σ₁ e₁' σ₁' ε₁ (fun σ₂ ρ' ε₂ =>
        match e₁.toVal? with
        | some v => iprop(|={∅, E}=>
            stateInterp (rT := rT) σ₂ ∗ SpecUpdateGS.specInterp (rT := rT) ρ' ∗
              errInterp (rT := rT) ε₂ ∗ Φ v)
        | none => progCoupl e₁ σ₂ ρ'.expr ρ'.state ε₂ (fun e₃ σ₃ e₃' σ₃' ε₃ =>
            iprop(▷ specCoupl ∅ σ₃ e₃' σ₃' ε₃ (fun σ₄ ρ'' ε₄ =>
              iprop(|={∅, E}=>
                stateInterp (rT := rT) σ₄ ∗ SpecUpdateGS.specInterp (rT := rT) ρ'' ∗
                  errInterp (rT := rT) ε₄ ∗ wp E e₃ Φ))))))

/-- The function space `CoPset → Exp rT → ((Val rT) → IProp GF) → IProp GF`, packaged as
the type the fixpoint operates over. -/
abbrev WpType := CoPset → Exp rT → ((Val rT) → IProp GF) → IProp GF

/-- The structural walk through `wpPre`: forall, wand, fupd, fixpoint unfold for
`specCoupl`, the `match` on `e.toVal?`, the `progCoupl` body, and the inner
`▷ specCoupl` where the `▷` lets the recursive `wp` only be related at `m < n`.

Both `wpPre_contractive` (which varies the recursive `wp`) and `wp_ne_aux`
(which varies the post) are instances of this walk. -/
theorem wpPre_ne_aux {n : Nat} {wp wp' : WpType (rT := rT) (GF := GF)} {E : CoPset}
    {e : Exp rT} {Φ Ψ : Val rT → IProp GF} (HΦ : ∀ v, Φ v ≡{n}≡ Ψ v)
    (Hwp : ∀ m, m < n → ∀ e₃ : Exp rT, wp E e₃ Φ ≡{m}≡ wp' E e₃ Ψ) :
    wpPre wp E e Φ ≡{n}≡ wpPre wp' E e Ψ := by
  refine forall_ne fun _ => forall_ne fun _ => forall_ne fun _ => forall_ne fun _ => ?_
  refine wand_ne.ne (.of_eq rfl) (BIFUpdate.ne.ne ?_)
  refine least_fixpoint_ne_outer (fun _ _ => ?_) (.of_eq rfl)
  refine or_ne.ne (.of_eq rfl) (or_ne.ne ?_ (.of_eq rfl))
  cases htv : e.toVal? with
  | some v =>
    exact BIFUpdate.ne.ne <| sep_ne.ne (.of_eq rfl) <| sep_ne.ne (.of_eq rfl) <|
      sep_ne.ne (.of_eq rfl) (HΦ v)
  | none =>
    refine progCoupl_ne fun e₃ _ _ _ _ => ?_
    apply Contractive.distLater_dist (f := later)
    intro m Hm
    refine specCoupl_ne fun _ _ _ => ?_
    exact BIFUpdate.ne.ne <| sep_ne.ne (.of_eq rfl) <| sep_ne.ne (.of_eq rfl) <|
      sep_ne.ne (.of_eq rfl) (Hwp m Hm e₃)

/-- `wpPre` is `Contractive` in its first argument: the only recursive use of
the `wp` parameter inside the body sits under a `▷` (`later`) modality. -/
instance wpPre_contractive : Contractive (wpPre (rT := rT) (GF := GF)) where
  distLater_dist Hwp E _ Φ :=
    wpPre_ne_aux (fun _ => .of_eq rfl) fun _ Hm e₃ => DistLater.dist_lt (Hwp · · E e₃ Φ) Hm

/-- The Approxis weakest precondition. -/
noncomputable def wp (E : CoPset) (e : Exp rT) (Φ : Val rT → IProp GF) : IProp GF :=
  fixpoint (wpPre (rT := rT) (GF := GF)) E e Φ

/-- Fixpoint unfolding for `wp`. Pointwise consequence of `OFE.fixpoint_unfold`
applied to `wpPre`. -/
theorem wp_unfold {E : CoPset} {e : Exp rT} {Φ : Val rT → IProp GF} :
    wp (GF := GF) E e Φ = wpPre (wp (GF := GF)) E e Φ :=
  congrFun (congrFun (congrFun
    (fixpoint_unfold ⟨wpPre, OFE.ne_of_contractive _⟩) E) e) Φ

/-- `wp_unfold` in entailment form; the direction the proofs below feed hypotheses through. -/
theorem wp_unfold_mp {E : CoPset} {e : Exp rT} {Φ : Val rT → IProp GF} :
    wp (GF := GF) E e Φ ⊢@{IProp GF} wpPre (wp (GF := GF)) E e Φ :=
  (BI.equiv_iff.mp wp_unfold).1

/-- The `progCoupl` continuation of `wpPre`'s non-value branch, named so the
`(Z := …)` arguments below need not respell it. -/
noncomputable abbrev wpProgBody (E : CoPset) (Φ : Val rT → IProp GF)
    (e₃ : Exp rT) (σ₃ : State rT) (e₃' : Exp rT) (σ₃' : State rT) (ε₃ : ENNReal) : IProp GF :=
  iprop(▷ specCoupl ∅ σ₃ e₃' σ₃' ε₃ (fun σ₄ ρ'' ε₄ =>
    iprop(|={∅, E}=>
      stateInterp (rT := rT) σ₄ ∗ SpecUpdateGS.specInterp (rT := rT) ρ'' ∗
        errInterp (rT := rT) ε₄ ∗ wp E e₃ Φ)))

/-- The catch-all every `progCoupl` intro rule asks for: at error `1` the body is
vacuous, so `wpProgBody` holds outright. -/
theorem wpProgBody_err_ge_1 {E : CoPset} {Φ : Val rT → IProp GF} :
    ⊢@{IProp GF} □ ∀ (e₃ : Exp rT) (σ₃ : State rT) (e₃' : Exp rT) (σ₃' : State rT),
      wpProgBody E Φ e₃ σ₃ e₃' σ₃' 1 := by
  iintro !> %e₃ %σ₃ %e₃' %σ₃' !>
  iapply (specCoupl_err_ge_1 (_root_.le_refl _))

/-! ## WP structural lemmas -/

/-- Value introduction (fupd-flavored): `|={E}=> Φ v` proves
`wp E (Exp.ofVal v) Φ`. -/
theorem wp_value_fupd {E : CoPset} {v : Val rT} {Φ : Val rT → IProp GF} :
    iprop(|={E}=> Φ v) ⊢@{IProp GF} wp E (Exp.ofVal v) Φ := by
  iintro HΦ
  iapply wp_unfold
  unfold wpPre
  iintro %σ₁ %e₁' %σ₁' %ε₁ ⟨Hσ, Hs, Hε⟩
  rw [Exp.toVal?_ofVal]
  imod (BIFUpdate.subset (E1 := E) (E2 := ∅) Std.LawfulSet.empty_subset)
    with Hclose
  imodintro
  iapply specCoupl_ret
  imod Hclose
  imod HΦ
  imodintro
  iframe

/-- Plain value introduction: `Φ v ⊢ wp E (Exp.ofVal v) Φ`. -/
theorem wp_value {E : CoPset} {v : Val rT} {Φ : Val rT → IProp GF} :
    Φ v ⊢@{IProp GF} wp E (Exp.ofVal v) Φ := by
  iintro HΦ
  iapply wp_value_fupd
  imodintro
  iexact HΦ

/-- General value form: from any expression `e` that is a value (`e.toVal? = some v`),
introduce `wp E e Φ` from `Φ v`. -/
theorem wp_value_of_toVal {E : CoPset} {e : Exp rT} {v : Val rT} {Φ : Val rT → IProp GF}
    (h : e.toVal? = some v) :
    Φ v ⊢@{IProp GF} wp E e Φ := by
  rw [← Exp.ofVal_of_toVal_some h]
  exact wp_value

/-- The post-condition transformer `HΦ` packaged for `wp_strong_mono'`. -/
abbrev wpStrongMonoCont (E2 : CoPset) (Φ Ψ : Val rT → IProp GF) : IProp GF :=
  iprop(□ ∀ σ ρ v ε,
    (stateInterp (rT := rT) σ ∗ SpecUpdateGS.specInterp (rT := rT) ρ ∗ errInterp (rT := rT) ε ∗ Φ v)
    ={E2}=∗
      stateInterp (rT := rT) σ ∗ SpecUpdateGS.specInterp (rT := rT) ρ ∗ errInterp (rT := rT) ε ∗
        Ψ v)

/-- The Löb invariant for `wp_strong_mono'`: a single iprop universally
quantified over all the relevant parameters, suitable for `loeb_wand`. -/
noncomputable abbrev wpStrongMonoStmt : IProp GF :=
  iprop(∀ (E1 E2 : CoPset) (e : Exp rT) (Φ Ψ : Val rT → IProp GF),
    ⌜E1 ⊆ E2⌝ -∗
    wp E1 e Φ -∗ wpStrongMonoCont E2 Φ Ψ -∗ wp E2 e Ψ)

/-- Strong monotonicity of `wp` (Löb-induction-based variant matching Rocq's
`wp_strong_mono'`). -/
theorem wp_strong_mono' {E1 E2 : CoPset} {e : Exp rT} {Φ Ψ : Val rT → IProp GF}
    (HE : E1 ⊆ E2) :
    iprop(wp E1 e Φ ∗ wpStrongMonoCont E2 Φ Ψ) ⊢@{IProp GF} wp E2 e Ψ := by
  iintro ⟨HW, HΦ⟩
  have Hloeb : ⊢@{IProp GF} wpStrongMonoStmt (rT := rT) := by
    iapply loeb_wand
    iintro !> IH %E1' %E2' %e' %Φ' %Ψ' %HE' HW' #HΦ'
    iapply wp_unfold
    ihave HW' := wp_unfold_mp $$ HW'
    iintro %σ₁ %e₁' %σ₁' %ε₁ ⟨Hσ, Hs, Hε⟩
    imod (BIFUpdate.subset HE') with Hclose
    ispecialize HW' $$ %σ₁ %e₁' %σ₁' %ε₁ [$Hσ $Hs $Hε]
    imod HW' with HW'
    imodintro
    iapply specCoupl_bind (E1 := ∅) (E2 := ∅) Std.LawfulSet.subset_refl
    iframe HW'
    iintro %σ₂ %ρ₂ %ε₂ HZ₁
    cases htv : e'.toVal? with
    | some v =>
      iapply specCoupl_ret
      imod HZ₁ with ⟨Hσ', Hs', Hε', HΦv⟩
      imod Hclose
      iapply HΦ' $$ [Hσ' Hs' Hε' HΦv]
      iframe
    | none =>
      iapply specCoupl_ret
      iapply progCoupl_mono
      iframe HZ₁
      iintro %e₃ %σ₃ %e₃' %σ₃' %ε₃ HCont !>
      iapply specCoupl_mono_spatial
      iframe HCont
      iintro %σ₄ %ρ₄ %ε₄ HInner
      imod HInner with ⟨Hσ', Hs', Hε', HwpInner⟩
      imod Hclose
      imodintro
      iframe
      iapply IH $$ %E1' %E2' %e₃ %Φ' %Ψ' %HE' HwpInner HΦ'
  iapply Hloeb $$ %E1 %E2 %e %Φ %Ψ %HE HW HΦ

theorem wp_wand {E : CoPset} {e : Exp rT} {Φ Ψ : Val rT → IProp GF} :
    iprop(wp E e Φ ∗ □ (∀ v, Φ v -∗ Ψ v)) ⊢@{IProp GF} wp E e Ψ := by
  iintro ⟨HW, #HΦ⟩
  iapply wp_strong_mono' (E1 := E) (E2 := E) (Φ := Φ) (Ψ := Ψ) Std.LawfulSet.subset_refl
  iframe HW
  iintro !> %σ %ρ %v %ε ⟨Hσ, Hs, Hε, HΦv⟩ !>
  iframe
  iapply HΦ $$ [$]

/-- Inside fancy-update absorption: if the post is `|={E}=> Φ v`, we can collapse it. -/
theorem wp_fupd {E : CoPset} {e : Exp rT} {Φ : Val rT → IProp GF} :
    wp E e (fun v => iprop(|={E}=> Φ v)) ⊢@{IProp GF} wp E e Φ := by
  iintro HW
  iapply wp_strong_mono' (E1 := E) (E2 := E) Std.LawfulSet.subset_refl
  iframe HW
  iintro !> %σ %ρ %v %ε ⟨Hσ, Hs, Hε, HΦ⟩
  imod HΦ
  iframe

/-- Fancy-update absorbs into `wp` from outside. -/
theorem fupd_wp {E : CoPset} {e : Exp rT} {Φ : Val rT → IProp GF} :
    iprop(|={E}=> wp E e Φ) ⊢@{IProp GF} wp E e Φ := by
  iintro HF
  iapply wp_unfold
  unfold wpPre
  iintro %σ₁ %e₁' %σ₁' %ε₁ Hres
  imod HF with HW
  ihave HW' := wp_unfold_mp $$ HW
  ispecialize HW' $$ %σ₁ %e₁' %σ₁' %ε₁ Hres
  iexact HW'

/-! ## Easy derived WP lemmas

All of these derive from `wp_strong_mono'` / `wp_wand` and the existing
`specCoupl`/`progCoupl` primitives. -/

/-- Strong monotonicity of `wp` with an intuitionistic continuation wand (the
`□`-variant of `wp_strong_mono'`). Follows directly from the spatial form. -/
theorem wp_strong_mono {E1 E2 : CoPset} {e : Exp rT} {Φ Ψ : Val rT → IProp GF}
    (HE : E1 ⊆ E2) :
    iprop(wp E1 e Φ ∗ wpStrongMonoCont E2 Φ Ψ) ⊢@{IProp GF} wp E2 e Ψ :=
  wp_strong_mono' HE

/-- Monotonicity of `wp` under pointwise entailment of the postcondition. -/
theorem wp_mono {E : CoPset} {e : Exp rT} {Φ Ψ : Val rT → IProp GF}
    (HΦ : ∀ v, Φ v ⊢@{IProp GF} Ψ v) :
    wp E e Φ ⊢@{IProp GF} wp E e Ψ := by
  iintro HW
  iapply wp_wand (Φ := Φ) (Ψ := Ψ)
  iframe HW
  iintro !> %v HΦv
  iapply HΦ $$ HΦv

/-- Mask monotonicity for `wp`: enlarging the mask is sound. -/
theorem wp_mask_mono {E1 E2 : CoPset} {e : Exp rT} {Φ : Val rT → IProp GF}
    (HE : E1 ⊆ E2) :
    wp E1 e Φ ⊢@{IProp GF} wp E2 e Φ := by
  iintro HW
  iapply wp_strong_mono' (Φ := Φ) (Ψ := Φ) HE
  iframe HW
  iintro !> %σ %ρ %v %ε ⟨Hσ, Hs, Hε, HΦ⟩ !>
  iframe

/-- Post-wand — spatial variant with frame, derived from `wp_wand`. -/
theorem wp_wand_l {E : CoPset} {e : Exp rT} {Φ Ψ : Val rT → IProp GF} :
    iprop(□ (∀ v, Φ v -∗ Ψ v) ∗ wp E e Φ) ⊢@{IProp GF} wp E e Ψ := by
  iintro ⟨#HΦ, HW⟩
  iapply wp_wand (Φ := Φ) (Ψ := Ψ)
  iframe HW
  iintro !>; iexact HΦ

/-- `wp_wand` with arguments swapped. -/
theorem wp_wand_r {E : CoPset} {e : Exp rT} {Φ Ψ : Val rT → IProp GF} :
    iprop(wp E e Φ ∗ □ (∀ v, Φ v -∗ Ψ v)) ⊢@{IProp GF} wp E e Ψ :=
  wp_wand

/-! ### Measure-theoretic plumbing for the coupling-intro rules -/

/-- `pexecN` is a sub-probability: it never gains mass. -/
theorem pexecN_univ_le_one (n : Nat) (ρ : Cfg rT) : (pexecN n ρ) Set.univ ≤ 1 := by
  induction n generalizing ρ with
  | zero => simp
  | succ k ih =>
    rw [pexecN_succ, MeasureTheory.Measure.bind_apply (by measurability)
      pexecN_measurable.aemeasurable]
    calc ∫⁻ a, (pexecN k a) Set.univ ∂(stepOrFinal ρ)
        ≤ ∫⁻ _, 1 ∂(stepOrFinal ρ) := MeasureTheory.lintegral_mono fun a => ih a
      _ = (stepOrFinal ρ) Set.univ := by simp
      _ ≤ 1 := by
          by_cases hv : ρ.expr.isValue
          · rw [stepOrFinal_isValue hv]; simp
          · rw [stepOrFinal_not_isValue hv]; exact primStep_univ_le_one ρ

/-- A constant integrates to at most itself against a sub-probability measure. -/
theorem lintegral_const_le {α : Type _} [MeasurableSpace α] {ν : MeasureTheory.Measure α}
    (hν : ν Set.univ ≤ 1) (c : ENNReal) : ∫⁻ _, c ∂ν ≤ c := by
  rw [MeasureTheory.lintegral_const]
  calc c * ν Set.univ ≤ c * 1 := by gcongr
    _ = c := mul_one c

/-- The spec-side measure of `specCouplCouple` is a sub-probability. -/
theorem bindPexecN_univ_le_one {n : Nat} {e' : Exp rT}
    {μ : MeasureTheory.Measure (State rT)} (hμ : μ Set.univ ≤ 1) :
    (μ.bind (fun σ => pexecN n ⟨e', σ⟩)) Set.univ ≤ 1 := by
  have hk : Measurable (fun σ : State rT => pexecN n (⟨e', σ⟩ : Cfg rT)) := by fun_prop
  rw [MeasureTheory.Measure.bind_apply MeasurableSet.univ hk.aemeasurable]
  calc ∫⁻ σ, (pexecN n ⟨e', σ⟩) Set.univ ∂μ
      ≤ ∫⁻ _, 1 ∂μ := MeasureTheory.lintegral_mono fun σ => pexecN_univ_le_one n _
    _ ≤ 1 := lintegral_const_le hμ 1

/-- Outside the discrete `urand` fragment `primStep` is atomic, so its positive-mass atoms
carry all of its mass. -/
theorem concentrated_primStep_support (e : Exp rT) (σ : State rT) (hne : e.decomp.2 ≠ .urand) :
    Concentrated (primStep ⟨e, σ⟩) {ρ : Cfg rT | 0 < primStep ⟨e, σ⟩ {ρ}} := by
  have heq : ({ρ : Cfg rT | 0 < primStep ⟨e, σ⟩ {ρ}}ᶜ)
      = {ρ : Cfg rT | (primStep ⟨e, σ⟩) {ρ} = 0} := by
    ext ρ; simp [pos_iff_ne_zero]
  show (primStep ⟨e, σ⟩) _ = 0
  rw [heq]
  exact primStep_atomic e σ hne

/-- The common tail of the coupling-shift arguments: once `h₁`'s integral is bounded by
that of the clamped shift `(h₂ + ε₂) ⊓ 1` with slack `ε₁`, it is bounded by `h₂`'s own with
slack `ε`. The clamp is what keeps the shifted test function `[0,1]`-bounded. -/
theorem lintegral_le_of_clamped {α β : Type _} [MeasurableSpace α] [MeasurableSpace β]
    {μ : MeasureTheory.Measure α} {ν : MeasureTheory.Measure β}
    {h₁ : α → ENNReal} {h₂ : β → ENNReal} {ε₁ ε₂ ε : ENNReal}
    (Hε : ε₁ + ε₂ ≤ ε) (hν : ν Set.univ ≤ 1)
    (H : (∫⁻ a, h₁ a ∂μ) ≤ (∫⁻ b, (h₂ b + ε₂) ⊓ 1 ∂ν) + ε₁) :
    (∫⁻ a, h₁ a ∂μ) ≤ (∫⁻ b, h₂ b ∂ν) + ε := by
  refine H.trans ?_
  calc (∫⁻ b, (h₂ b + ε₂) ⊓ 1 ∂ν) + ε₁
      ≤ (∫⁻ b, (h₂ b + ε₂) ∂ν) + ε₁ := by gcongr; exact inf_le_left
    _ = (∫⁻ b, h₂ b ∂ν) + ε₂ * ν Set.univ + ε₁ := by
        rw [MeasureTheory.lintegral_add_right _ measurable_const,
          MeasureTheory.lintegral_const, mul_comm]
    _ ≤ (∫⁻ b, h₂ b ∂ν) + ε₂ + ε₁ := by
        gcongr
        calc ε₂ * ν Set.univ ≤ ε₂ * 1 := by gcongr
          _ = ε₂ := mul_one _
    _ ≤ (∫⁻ b, h₂ b ∂ν) + ε := by rw [add_assoc, add_comm ε₂ ε₁]; gcongr

/-- The degenerate branch of those arguments: at `1 ≤ ε₂` the slack already covers a
`[0,1]`-bounded integrand against a sub-probability measure. -/
theorem lintegral_le_of_one_le {α β : Type _} [MeasurableSpace α] [MeasurableSpace β]
    {μ : MeasureTheory.Measure α} {ν : MeasureTheory.Measure β}
    {h₁ : α → ENNReal} {h₂ : β → ENNReal} {ε₁ ε₂ ε : ENNReal}
    (Hε : ε₁ + ε₂ ≤ ε) (hε₂ : 1 ≤ ε₂) (hμ : μ Set.univ ≤ 1) (Hh₁ : ∀ a, h₁ a ≤ 1) :
    (∫⁻ a, h₁ a ∂μ) ≤ (∫⁻ b, h₂ b ∂ν) + ε :=
  calc (∫⁻ a, h₁ a ∂μ) ≤ ∫⁻ _, 1 ∂μ := MeasureTheory.lintegral_mono Hh₁
    _ ≤ 1 := lintegral_const_le hμ 1
    _ ≤ ε₂ := hε₂
    _ ≤ ε := _root_.le_trans _root_.le_add_self Hε
    _ ≤ _ := _root_.le_add_self

/-- An `AddCoupl` with slack `ε₁` becomes an `ExpCoupl` with slack `ε` for any cost `Y`
that stays below `ε₂` on `R`-related pairs — the cost off `R` is unconstrained because
`[0,1]`-bounded test functions make the bound there vacuous. -/
theorem expCoupl_of_addCoupl {α β : Type _} [MeasurableSpace α] [MeasurableSpace β]
    {μ : MeasureTheory.Measure α} {ν : MeasureTheory.Measure β} {R : α → β → Prop}
    {Y : α → β → ENNReal} {ε₁ ε₂ ε : ENNReal}
    (Hε : ε₁ + ε₂ ≤ ε) (hμ : μ Set.univ ≤ 1) (hν : ν Set.univ ≤ 1)
    (HY : ∀ a b, R a b → Y a b ≤ ε₂)
    (Hcpl : AddCoupl ε₁ {p : α × β | R p.1 p.2} μ ν) :
    ExpCoupl ε Y μ ν := by
  intro h₁ h₂ Hh₁meas Hh₂meas Hh₁ Hh₂ Hh₁h₂
  by_cases hε₂ : ε₂ ≤ 1
  · refine lintegral_le_of_clamped Hε hν ?_
    have := Hcpl ⟨h₁, Hh₁meas, Hh₁⟩
      ⟨fun b => (h₂ b + ε₂) ⊓ 1, (Hh₂meas.add_const _).inf measurable_const,
        fun _ => inf_le_right⟩
      (fun {a b} (hab : R a b) =>
        le_inf ((Hh₁h₂ a b).trans (by gcongr; exact HY a b hab)) (Hh₁ a))
    simpa using this
  · exact lintegral_le_of_one_le Hε (_root_.not_le.mp hε₂).le hμ Hh₁

/-- Shifting an `ExpCoupl`'s cost by a constant `ε₂` costs `ε₂` of extra slack. -/
theorem expCoupl_add_const {α β : Type _} [MeasurableSpace α] [MeasurableSpace β]
    {μ : MeasureTheory.Measure α} {ν : MeasureTheory.Measure β} {X₂ : α → β → ENNReal}
    {ε₁ ε₂ ε : ENNReal} (Hε : ε₁ + ε₂ ≤ ε) (hμ : μ Set.univ ≤ 1) (hν : ν Set.univ ≤ 1)
    (H : ExpCoupl ε₁ X₂ μ ν) : ExpCoupl ε (fun a b => X₂ a b + ε₂) μ ν := by
  intro h₁ h₂ Hh₁meas Hh₂meas Hh₁ Hh₂ Hh₁h₂
  by_cases hε₂ : ε₂ ≤ 1
  · refine lintegral_le_of_clamped Hε hν ?_
    refine H h₁ (fun b => (h₂ b + ε₂) ⊓ 1) Hh₁meas
      ((Hh₂meas.add_const _).inf measurable_const) Hh₁ (fun _ => inf_le_right) ?_
    intro a b
    by_cases hlt : h₂ b + ε₂ ≤ 1
    · rw [inf_of_le_left hlt]
      calc h₁ a ≤ h₂ b + (X₂ a b + ε₂) := Hh₁h₂ a b
        _ = (h₂ b + ε₂) + X₂ a b := by ring
    · rw [inf_of_le_right (_root_.not_le.mp hlt).le]
      exact le_add_right (Hh₁ a)
  · exact lintegral_le_of_one_le Hε (_root_.not_le.mp hε₂).le hμ Hh₁

/-- Coupling-case introduction for `specCoupl` with the six side conditions of
`specCouplCouple` supplied as Lean hypotheses. Every `specCoupl` intro rule below is
this lemma at a particular choice of witnesses. -/
theorem specCoupl_couple {E : CoPset} {σ₁ : State rT} {e₁' : Exp rT} {σ₁' : State rT}
    {ε : ENNReal} {Z : State rT → Cfg rT → ENNReal → IProp GF}
    {S : State rT → Cfg rT → Prop} {n : Nat} {ε₁ r : ENNReal} {X₂ : Cfg rT → ENNReal}
    {μ₁ μ₁' : MeasureTheory.Measure (State rT)}
    (Hcpl : AddCoupl ε₁ {p : State rT × (Cfg rT) | S p.1 p.2} μ₁
              (μ₁'.bind (fun σ => pexecN n ⟨e₁', σ⟩)))
    (HX₂meas : Measurable X₂) (Hbnd : ∀ ρ, X₂ ρ ≤ r)
    (Hexp : ε₁ + (∫⁻ ρ, X₂ ρ ∂(μ₁'.bind (fun σ => pexecN n ⟨e₁', σ⟩))) ≤ ε)
    (Heras₁ : ErasableExpr μ₁ σ₁) (Heras₁' : ErasableExpr μ₁' σ₁') :
    iprop(∀ (σ₂ : State rT) (e₂' : Exp rT) (σ₂' : State rT),
        (⌜S σ₂ ⟨e₂', σ₂'⟩⌝) -∗ |={E}=>
          specCoupl E σ₂ e₂' σ₂' (X₂ ⟨e₂', σ₂'⟩) Z) ⊢@{IProp GF}
      specCoupl E σ₁ e₁' σ₁' ε Z := by
  iintro H
  iapply specCoupl_rec
  iexists S, n, μ₁, μ₁', ε₁, X₂, r
  spec_trivial_cases
  iexact H

/-! ### `specCoupl` — derived lemmas -/

/-- Degenerate-coupling reduction: `specCoupl` at any ε₂ reduces to
`|={E}=> specCoupl E σ e' σ' ε₁ Z` when `ε₁ ≤ ε₂`. The trick: take `n = 0`,
dirac-dirac distributions so the coupling-and-bind collapse. -/
theorem fupd_specCoupl_of_le {E : CoPset} {σ : State rT} {e' : Exp rT} {σ' : State rT}
    {ε₁ ε₂ : ENNReal} {Z : State rT → Cfg rT → ENNReal → IProp GF}
    (Hε : ε₁ ≤ ε₂) :
    iprop(|={E}=> specCoupl E σ e' σ' ε₁ Z) ⊢@{IProp GF}
      specCoupl E σ e' σ' ε₂ Z := by
  iintro HF
  iapply (specCoupl_couple (S := fun s c => s = σ ∧ c = ⟨e', σ'⟩) (n := 0)
    (μ₁ := MeasureTheory.Measure.dirac σ) (μ₁' := MeasureTheory.Measure.dirac σ')
    (ε₁ := ε₂ - ε₁) (X₂ := fun _ => ε₁) (r := ε₁)
    (Hcpl := by
      show AddCoupl (ε₂ - ε₁) _ (MeasureTheory.Measure.dirac σ) _
      rw [MeasureTheory.Measure.dirac_bind (by fun_prop)]
      simp only [pexecN_zero]
      exact AddCoupl.dirac _ ⟨rfl, rfl⟩)
    (HX₂meas := measurable_const) (Hbnd := fun _ => _root_.le_refl _)
    (Hexp := by
      refine _root_.le_trans ?_ (tsub_add_cancel_of_le Hε).le
      gcongr
      exact lintegral_const_le (bindPexecN_univ_le_one (by simp)) ε₁)
    (Heras₁ := ErasableExpr.dret σ) (Heras₁' := ErasableExpr.dret σ'))
  iintro %σ₂ %e₂' %σ₂' %HS'
  obtain ⟨rfl, HS'⟩ := HS'
  cases HS'
  iexact HF

/-- Monotonicity of `specCoupl` in the error bound. -/
theorem specCoupl_mono_err {E : CoPset} {σ : State rT} {e' : Exp rT} {σ' : State rT}
    {ε₁ ε₂ : ENNReal} {Z : State rT → Cfg rT → ENNReal → IProp GF}
    (Hε : ε₁ ≤ ε₂) :
    specCoupl E σ e' σ' ε₁ Z ⊢@{IProp GF} specCoupl E σ e' σ' ε₂ Z := by
  iintro HS
  iapply fupd_specCoupl_of_le Hε
  imodintro
  iexact HS

/-- Fancy-update absorbs into `specCoupl`: the `ε₁ = ε` case of
`fupd_specCoupl_of_le`. -/
theorem fupd_specCoupl {E : CoPset} {σ : State rT} {e' : Exp rT} {σ' : State rT}
    {ε : ENNReal} {Z : State rT → Cfg rT → ENNReal → IProp GF} :
    iprop(|={E}=> specCoupl E σ e' σ' ε Z) ⊢@{IProp GF}
      specCoupl E σ e' σ' ε Z :=
  fupd_specCoupl_of_le (_root_.le_refl _)

/-- Induction principle for `specCoupl`. Mirrors Rocq's `spec_coupl_ind`.

To prove `Ψ` of `specCoupl ε`, it suffices to show that `specCouplPre`
applied to `(Ψ ∧ specCoupl)` implies `Ψ` (an "intuitionistic step
hypothesis"). -/
theorem specCoupl_ind {E : CoPset} {Ψ Z : State rT → Cfg rT → ENNReal → IProp GF} :
    iprop(□ (∀ (σ : State rT) (c : Cfg rT) (ε : ENNReal),
        specCouplPre E Z (fun s => iprop(Ψ s.1 s.2.1 s.2.2 ∧
            specCoupl E s.1 s.2.1.expr s.2.1.state s.2.2 Z))
          ((σ, c, ε) : SpecCouplState rT) -∗ Ψ σ c ε)) ⊢@{IProp GF}
      ∀ (σ : State rT) (e' : Exp rT) (σ' : State rT) (ε : ENNReal),
        specCoupl E σ e' σ' ε Z -∗ Ψ σ ⟨e', σ'⟩ ε := by
  iintro #IH %σ %e' %σ' %ε HC
  -- Lift Ψ to SpecCouplState.
  let Ψ' : SpecCouplState rT → IProp GF := fun s => Ψ s.1 s.2.1 s.2.2
  have HΨne : NonExpansive Ψ' := specCouplState_ne
  -- Apply least_fixpoint_ind.
  iapply (least_fixpoint_ind (F := specCouplPre (GF := GF) E Z) (Φ := Ψ'))
    $$ [] %((σ, (⟨e', σ'⟩ : Cfg rT), ε) : SpecCouplState rT) HC
  iintro !> %s HF
  obtain ⟨σ'', c, ε'⟩ := s
  iapply IH $$ %σ'' %c %ε' HF

/-- General erasable-coupling intro for `specCoupl` with expectation bound on
the per-configuration error. Mirrors Rocq's `spec_coupl_erasables_exp`. -/
theorem specCoupl_erasables_exp {E : CoPset} {σ₁ : State rT} {e₁' : Exp rT} {σ₁' : State rT}
    {ε₁ ε : ENNReal} {Z : State rT → Cfg rT → ENNReal → IProp GF}
    {R : State rT → State rT → Prop}
    {μ₁ : MeasureTheory.Measure (State rT)} {μ₁' : MeasureTheory.Measure (State rT)}
    {X₂ : State rT → ENNReal} {r : ENNReal}
    (Hcpl : AddCoupl ε₁ {p : State rT × (State rT) | R p.1 p.2} μ₁ μ₁')
    (HX₂meas : Measurable X₂)
    (Heras₁ : ErasableExpr μ₁ σ₁) (Heras₁' : ErasableExpr μ₁' σ₁')
    (Hbnd : ∀ σ', X₂ σ' ≤ r)
    (Hexp : ε₁ + ∫⁻ σ', X₂ σ' ∂μ₁' ≤ ε) :
    iprop(∀ (σ₂ σ₂' : State rT), (⌜R σ₂ σ₂'⌝) -∗ |={E}=>
        specCoupl E σ₂ e₁' σ₂' (X₂ σ₂') Z) ⊢@{IProp GF}
      specCoupl E σ₁ e₁' σ₁' ε Z := by
  iintro H
  -- At `n = 0` the spec-side measure is the pushforward of `μ₁'` along `⟨e₁', ·⟩`.
  have heq : (μ₁' : MeasureTheory.Measure (State rT)).bind (fun σ => pexecN 0 ⟨e₁', σ⟩) =
      μ₁'.map (fun σ => (⟨e₁', σ⟩ : Cfg rT)) := by
    simp only [pexecN_zero]
    exact MeasureTheory.Measure.bind_dirac_eq_map _ (by fun_prop)
  iapply (specCoupl_couple (S := fun σ₂ c => R σ₂ c.state ∧ c.expr = e₁') (n := 0)
    (μ₁ := μ₁) (μ₁' := μ₁') (ε₁ := ε₁) (X₂ := fun ρ => X₂ ρ.state) (r := r)
    (Hcpl := by
      rw [heq, ← MeasureTheory.Measure.map_id (μ := μ₁)]
      exact AddCoupl.map (f := id) (g := fun σ => (⟨e₁', σ⟩ : Cfg rT))
        (by fun_prop) (by fun_prop) (fun {σ σ'} HR => ⟨HR, rfl⟩) Hcpl)
    (HX₂meas := HX₂meas.comp Cfg.measurable_state) (Hbnd := fun _ => Hbnd _)
    (Hexp := by
      refine _root_.le_trans ?_ Hexp
      gcongr
      rw [heq, MeasureTheory.lintegral_map (by fun_prop) (by fun_prop)])
    (Heras₁ := Heras₁) (Heras₁' := Heras₁'))
  iintro %σ₂ %e₂' %σ₂' %HS
  obtain ⟨HR, rfl⟩ := HS
  iapply H $$ %σ₂ %σ₂' %HR

/-- Specialization of `specCoupl_erasables_exp` with a constant per-config cost
`ε₂`. The error bound becomes `ε₁ + ε₂ ≤ ε`. -/
theorem specCoupl_erasables {E : CoPset} {σ₁ : State rT} {e₁' : Exp rT} {σ₁' : State rT}
    {ε₁ ε₂ ε : ENNReal} {Z : State rT → Cfg rT → ENNReal → IProp GF}
    {R : State rT → State rT → Prop}
    {μ₁ : MeasureTheory.Measure (State rT)} {μ₁' : MeasureTheory.Measure (State rT)}
    (Hε : ε₁ + ε₂ ≤ ε)
    (Hcpl : AddCoupl ε₁ {p : State rT × (State rT) | R p.1 p.2} μ₁ μ₁')
    (Heras₁ : ErasableExpr μ₁ σ₁) (Heras₁' : ErasableExpr μ₁' σ₁') :
    iprop(∀ (σ₂ σ₂' : State rT), (⌜R σ₂ σ₂'⌝) -∗ |={E}=>
        specCoupl E σ₂ e₁' σ₂' ε₂ Z) ⊢@{IProp GF}
      specCoupl E σ₁ e₁' σ₁' ε Z := by
  iintro H
  have Hexp_bnd : ε₁ + ∫⁻ _, ε₂ ∂μ₁' ≤ ε := by
    refine _root_.le_trans ?_ Hε
    rw [MeasureTheory.lintegral_const, ErasableExpr.mass Heras₁', mul_one]
  iapply (specCoupl_erasables_exp (X₂ := fun _ => ε₂) (r := ε₂) Hcpl measurable_const Heras₁ Heras₁'
    (fun _ => _root_.le_refl _) Hexp_bnd)
  iintro %σ₂ %σ₂' %HR
  iapply H $$ %σ₂ %σ₂' %HR

/-- LHS-erasable + spec-side `pexecN n`-coupling intro for `specCoupl`.

The relation `R` connects the LHS-state (sampled from `μ₁`) to a spec config
(sampled from `pexecN n ⟨e₁', σ₁'⟩`). Mirrors Rocq's `spec_coupl_erasable_steps`. -/
theorem specCoupl_erasable_steps {E : CoPset} {σ₁ : State rT} {e₁' : Exp rT} {σ₁' : State rT}
    {n : Nat} {ε₁ ε₂ ε : ENNReal} {Z : State rT → Cfg rT → ENNReal → IProp GF}
    {R : State rT → Cfg rT → Prop} {μ₁ : MeasureTheory.Measure (State rT)}
    (Hε : ε₁ + ε₂ ≤ ε)
    (Hcpl : AddCoupl ε₁ {p : State rT × (Cfg rT) | R p.1 p.2} μ₁ (pexecN n ⟨e₁', σ₁'⟩))
    (Heras₁ : ErasableExpr μ₁ σ₁) :
    iprop(∀ (σ₂ : State rT) (e₂' : Exp rT) (σ₂' : State rT),
        (⌜R σ₂ ⟨e₂', σ₂'⟩⌝) -∗ |={E}=>
          specCoupl E σ₂ e₂' σ₂' ε₂ Z) ⊢@{IProp GF}
      specCoupl E σ₁ e₁' σ₁' ε Z := by
  iintro H
  iapply (specCoupl_couple (S := R) (n := n) (μ₁ := μ₁)
    (μ₁' := MeasureTheory.Measure.dirac σ₁') (ε₁ := ε₁) (X₂ := fun _ => ε₂) (r := ε₂)
    (Hcpl := by rwa [MeasureTheory.Measure.dirac_bind (by fun_prop)])
    (HX₂meas := measurable_const) (Hbnd := fun _ => _root_.le_refl _)
    (Hexp := by
      refine _root_.le_trans ?_ Hε
      gcongr
      exact lintegral_const_le (bindPexecN_univ_le_one (by simp)) ε₂)
    (Heras₁ := Heras₁) (Heras₁' := ErasableExpr.dret σ₁'))
  iintro %σ₂ %e₂' %σ₂' %HR
  iapply H $$ %σ₂ %e₂' %σ₂' %HR

/-- Pure-step specialization: LHS is the singleton `dirac σ₁`, RHS is `pexecN n`.
Mirrors Rocq's `spec_coupl_steps`. -/
theorem specCoupl_steps {E : CoPset} {σ₁ : State rT} {e₁' : Exp rT} {σ₁' : State rT}
    {n : Nat} {ε₁ ε₂ ε : ENNReal} {Z : State rT → Cfg rT → ENNReal → IProp GF}
    {R : State rT → Cfg rT → Prop}
    (Hε : ε₁ + ε₂ ≤ ε)
    (Hcpl : AddCoupl ε₁ {p : State rT × (Cfg rT) | R p.1 p.2}
              (MeasureTheory.Measure.dirac σ₁) (pexecN n ⟨e₁', σ₁'⟩)) :
    iprop(∀ (σ₂ : State rT) (e₂' : Exp rT) (σ₂' : State rT),
        (⌜R σ₂ ⟨e₂', σ₂'⟩⌝) -∗ |={E}=>
          specCoupl E σ₂ e₂' σ₂' ε₂ Z) ⊢@{IProp GF}
      specCoupl E σ₁ e₁' σ₁' ε Z := by
  iintro H
  iapply (specCoupl_erasable_steps Hε Hcpl (ErasableExpr.dret σ₁)) $$ H

/-- Deterministic-step specialization: if `pexecN n ⟨e₁', σ₁'⟩ = dirac ⟨e₂', σ₂'⟩`
(the spec side takes `n` steps and lands deterministically on `⟨e₂', σ₂'⟩`),
then a `specCoupl` at `(e₂', σ₂')` gives one at `(e₁', σ₁')` for free. -/
theorem specCoupl_steps_det {E : CoPset} {σ : State rT} {e₁' : Exp rT} {σ₁' : State rT}
    {e₂' : Exp rT} {σ₂' : State rT} {n : Nat} {ε : ENNReal}
    {Z : State rT → Cfg rT → ENNReal → IProp GF}
    (Hstep : pexecN n ⟨e₁', σ₁'⟩ = MeasureTheory.Measure.dirac ⟨e₂', σ₂'⟩) :
    specCoupl E σ e₂' σ₂' ε Z ⊢@{IProp GF}
      specCoupl E σ e₁' σ₁' ε Z := by
  iintro HS
  iapply (specCoupl_couple (S := fun s c => s = σ ∧ c = ⟨e₂', σ₂'⟩) (n := n)
    (μ₁ := MeasureTheory.Measure.dirac σ) (μ₁' := MeasureTheory.Measure.dirac σ₁')
    (ε₁ := 0) (X₂ := fun _ => ε) (r := ε)
    (Hcpl := by
      show AddCoupl 0 _ (MeasureTheory.Measure.dirac σ) _
      rw [MeasureTheory.Measure.dirac_bind (by fun_prop), Hstep]
      exact AddCoupl.dirac _ ⟨rfl, rfl⟩)
    (HX₂meas := measurable_const) (Hbnd := fun _ => _root_.le_refl _)
    (Hexp := by
      rw [zero_add]
      exact lintegral_const_le (bindPexecN_univ_le_one (by simp)) ε)
    (Heras₁ := ErasableExpr.dret σ) (Heras₁' := ErasableExpr.dret σ₁'))
  iintro %σ₂ %e₂'' %σ₂'' %HS' !>
  obtain ⟨rfl, HS'⟩ := HS'
  cases HS'
  iexact HS

/-- Single spec-side step landing anywhere in a
measurable set `S` carrying the spec step measure.

Countability-free generalization of `specCoupl_step`. The trivial coupling
`dirac σ₁` vs `primStep ⟨e₁', σ₁'⟩` is refined on the left by
`AddCoupl.concentrated_L` at `{σ₁}` (pinning the LHS sample, which for a `dirac`
needs only measurable singletons) and on the right by `AddCoupl.concentrated_R`
at `S` — replacing `AddCoupl.pos_R`'s atom enumeration on both sides. -/
theorem specCoupl_step_concentrated {E : CoPset} {σ₁ : State rT} {e₁' : Exp rT} {σ₁' : State rT}
    {ε : ENNReal} {Z : State rT → Cfg rT → ENNReal → IProp GF}
    {S : Set (Cfg rT)} (Hred : Reducible e₁' σ₁')
    (hSmeas : MeasurableSet S) (hSconc : Concentrated (primStep ⟨e₁', σ₁'⟩) S) :
    iprop(∀ (e₂' : Exp rT) (σ₂' : State rT),
        (⌜(⟨e₂', σ₂'⟩ : Cfg rT) ∈ S⌝) -∗ |={E}=>
          specCoupl E σ₁ e₂' σ₂' ε Z) ⊢@{IProp GF}
      specCoupl E σ₁ e₁' σ₁' ε Z := by
  iintro H
  have Hε : (0 : ENNReal) + ε ≤ ε := by rw [zero_add]
  have hprob_rhs : (primStep ⟨e₁', σ₁'⟩) Set.univ = 1 := by
    haveI := prim_step_mass Hred
    exact MeasureTheory.IsProbabilityMeasure.measure_univ
  have Htrivial : AddCoupl 0 Set.univ (MeasureTheory.Measure.dirac σ₁) (primStep ⟨e₁', σ₁'⟩) :=
    RelCoupl.exact (RelCoupl.trivial (by simp) hprob_rhs)
  have hdirac : (MeasureTheory.Measure.dirac σ₁ : MeasureTheory.Measure (State rT))
      (({σ₁} : Set (State rT))ᶜ) = 0 := by
    rw [MeasureTheory.Measure.dirac_apply' _ (by measurability)]; simp
  have hpexec1 : pexecN 1 ⟨e₁', σ₁'⟩ = primStep ⟨e₁', σ₁'⟩ := by
    rw [pexecN_one, stepOrFinal_not_isValue (val_stuck Hred)]
  have HcplR : AddCoupl 0 {p : State rT × (Cfg rT) | (fun σ c => σ = σ₁ ∧ c ∈ S) p.1 p.2}
        (MeasureTheory.Measure.dirac σ₁) (pexecN 1 ⟨e₁', σ₁'⟩) := by
    rw [hpexec1]
    refine AddCoupl.mono_rel ?_
      (AddCoupl.concentrated_R hSmeas hSconc
        (AddCoupl.concentrated_L (MeasurableSet.singleton σ₁) hdirac Htrivial))
    rintro ⟨σ, c⟩ ⟨⟨_, hσ⟩, hc⟩
    exact ⟨hσ, hc⟩
  iapply (specCoupl_steps (n := 1) (R := fun σ c => σ = σ₁ ∧ c ∈ S)
    (ε₁ := 0) (ε₂ := ε) (Hε := Hε) HcplR)
  iintro %σ₂ %e₂' %σ₂' %HR
  obtain ⟨rfl, Hmem⟩ := HR
  iapply H $$ %e₂' %σ₂' %Hmem

/-- Single-step specialization: when `(e₁', σ₁')` is reducible, every
positive-measure spec successor lets us land on a `specCoupl` at the
post-step config. Mirrors Rocq's `spec_coupl_step`.

Discrete corollary of `specCoupl_step_concentrated` at the atom set. -/
@[discrete]
theorem specCoupl_step {E : CoPset} {σ₁ : State rT} {e₁' : Exp rT} {σ₁' : State rT}
    {ε : ENNReal} {Z : State rT → Cfg rT → ENNReal → IProp GF}
    (Hred : Discrete.Reducible e₁' σ₁')
    (hne : e₁'.decomp.2 ≠ .urand := by no_urand) :
    iprop(∀ (e₂' : Exp rT) (σ₂' : State rT),
        (⌜0 < primStep ⟨e₁', σ₁'⟩ {⟨e₂', σ₂'⟩}⌝) -∗ |={E}=>
          specCoupl E σ₁ e₂' σ₂' ε Z) ⊢@{IProp GF}
      specCoupl E σ₁ e₁' σ₁' ε Z := by
  refine specCoupl_step_concentrated (S := {ρ : Cfg rT | 0 < primStep ⟨e₁', σ₁'⟩ {ρ}})
    Hred.toReducible (measurableSet_primStep_support e₁' σ₁')
    (concentrated_primStep_support e₁' σ₁' hne)

/-! ## `progCoupl` — derived lemmas -/

/-- `progCoupl` implies reducibility of the program. -/
theorem progCoupl_reducible {e₁ : Exp rT} {σ₁ : State rT} {e₁' : Exp rT} {σ₁' : State rT}
    {ε : ENNReal} {Z : Exp rT → State rT → Exp rT → State rT → ENNReal → IProp GF} :
    progCoupl e₁ σ₁ e₁' σ₁' ε Z ⊢@{IProp GF} ⌜Reducible e₁ σ₁⌝ := by
  iintro HCpl
  icases HCpl with ⟨%n, %μ₁', %X₂, %Hred, _⟩
  ipureintro; exact Hred

/-- Introduction rule for `progCoupl`, with its four side conditions as Lean hypotheses. -/
theorem progCoupl_intro {e₁ : Exp rT} {σ₁ : State rT} {e₁' : Exp rT} {σ₁' : State rT}
    {ε : ENNReal} {Z : Exp rT → State rT → Exp rT → State rT → ENNReal → IProp GF}
    {n : Nat} {μ₁' : MeasureTheory.Measure (State rT)} {r : ENNReal}
    {X₂ : Cfg rT → Cfg rT → ENNReal}
    (Hred : Reducible e₁ σ₁) (Hbnd : ∀ ρ₁ ρ₂, X₂ ρ₁ ρ₂ ≤ r)
    (Hexp : ExpCoupl ε X₂ (primStep ⟨e₁, σ₁⟩) (μ₁'.bind (fun σ => pexecN n ⟨e₁', σ⟩)))
    (Heras : ErasableExpr μ₁' σ₁') :
    iprop(∀ (e₂ : Exp rT) (σ₂ : State rT) (e₂' : Exp rT) (σ₂' : State rT),
        |={∅}=> Z e₂ σ₂ e₂' σ₂' (X₂ ⟨e₂, σ₂⟩ ⟨e₂', σ₂'⟩)) ⊢@{IProp GF}
      progCoupl e₁ σ₁ e₁' σ₁' ε Z := by
  iintro H
  iexists n, μ₁', X₂
  isplitr; · ipureintro; exact Hred
  isplitr; · ipureintro; exact ⟨r, Hbnd⟩
  isplitr; · ipureintro; exact Hexp
  isplitr; · ipureintro; exact Heras
  iexact H

/-- One spec step out of a reducible configuration: `dirac σ₁' >>= pexecN 1 ⟨e₁', ·⟩` is
just `primStep ⟨e₁', σ₁'⟩`. -/
theorem dirac_bind_pexecN_one {e₁' : Exp rT} {σ₁' : State rT} (Hred' : Reducible e₁' σ₁') :
    (MeasureTheory.Measure.dirac σ₁' : MeasureTheory.Measure (State rT)).bind
      (fun σ => pexecN 1 ⟨e₁', σ⟩) = primStep ⟨e₁', σ₁'⟩ := by
  rw [MeasureTheory.Measure.dirac_bind (by fun_prop), pexecN_one,
    stepOrFinal_not_isValue (val_stuck Hred')]

/-- Strong monotonicity of `progCoupl`: given a wand that can consume an extra
fact "`⟨e₂, σ₂⟩ ∈ S`" for any measurable set `S` carrying the step measure, and
a persistent "catch-all" `Z₂` at error `1`, we can lift the monotonicity.

Used by `progCoupl_strengthen` and indirectly by `prog_coupl_ctx_bind`.

The new `X₂'` is `X₂` on `S` and `1` off it. The expectation bound works because
`primStep ⟨e₁, σ₁⟩` is concentrated on `S`, so integrating
`h₁'(a) := if a ∈ S then h₁ a else 0` is the same as integrating `h₁`, and on `S`
the new `X₂'` agrees with the old `X₂`.

`S` is a parameter rather than a fixed set because there is no single canonical
choice: in the discrete fragment one takes the atom set (`primStep_atomic`), and
for the continuous sampler one takes the value set (`Atomic'`). Both are instances
of "measurable and conull", which is all the proof ever uses. -/
theorem progCoupl_strong_mono {e₁ : Exp rT} {σ₁ : State rT} {e₁' : Exp rT} {σ₁' : State rT}
    {ε : ENNReal} {Z₁ Z₂ : Exp rT → State rT → Exp rT → State rT → ENNReal → IProp GF}
    {S : Set (Cfg rT)} (hSmeas : MeasurableSet S)
    (hSconc : Concentrated (primStep ⟨e₁, σ₁⟩) S) :
    iprop((□ ∀ e₂ σ₂ e₂' σ₂', Z₂ e₂ σ₂ e₂' σ₂' 1) ∗
          (∀ e₂ σ₂ e₂' σ₂' ε',
             ⌜(⟨e₂, σ₂⟩ : Cfg rT) ∈ S⌝ ∗ Z₁ e₂ σ₂ e₂' σ₂' ε' -∗
               Z₂ e₂ σ₂ e₂' σ₂' ε') ∗
          progCoupl e₁ σ₁ e₁' σ₁' ε Z₁) ⊢@{IProp GF}
      progCoupl e₁ σ₁ e₁' σ₁' ε Z₂ := by
  iintro ⟨#H1F, Hm, HCpl⟩
  icases HCpl with ⟨%n, %μ₁', %X₂, %Hred, %Hbnd, %Hexp, %Heras, HCont⟩
  obtain ⟨r, Hr⟩ := Hbnd
  classical
  -- New error function: X₂' a b = X₂ a b on the carrying set, else 1.
  have Hbnd' : ∀ a b, (if a ∈ S then X₂ a b else 1) ≤ max r 1 := by
    intro a b
    split_ifs with h
    · exact (Hr a b).trans (le_max_left _ _)
    · exact le_max_right _ _
  have Hexp' : ExpCoupl ε (fun a b => if a ∈ S then X₂ a b else 1)
      (primStep ⟨e₁, σ₁⟩) (μ₁'.bind (fun σ => pexecN n ⟨e₁', σ⟩)) := by
    intro h₁ h₂ Hh₁meas Hh₂meas Hh₁ Hh₂ Hh₁h₂
    -- h₁'(a) := h₁(a) on `S`, else 0. Since `S` is conull, this does not change
    -- the integral; and off `S` the bound is trivial because `X₂' = 1 ≥ h₁'`.
    let h₁' : Cfg rT → ENNReal := fun a => if a ∈ S then h₁ a else 0
    have hcongr : (∫⁻ a, h₁ a ∂(primStep ⟨e₁, σ₁⟩)) = ∫⁻ a, h₁' a ∂(primStep ⟨e₁, σ₁⟩) := by
      refine MeasureTheory.lintegral_congr_ae ?_
      rw [Filter.eventuallyEq_iff_exists_mem]
      refine ⟨S, ?_, ?_⟩
      · rw [MeasureTheory.mem_ae_iff]; exact hSconc
      · intro a ha
        simp only [h₁', if_pos ha]
    rw [hcongr]
    have hh₁'meas : Measurable h₁' :=
      Measurable.ite hSmeas Hh₁meas measurable_const
    refine Hexp h₁' h₂ hh₁'meas Hh₂meas ?_ Hh₂ ?_
    · intro a; simp only [h₁']; split_ifs; exacts [Hh₁ a, zero_le]
    · intro a b
      simp only [h₁']
      split_ifs with h
      · have hb := Hh₁h₂ a b
        simp only [if_pos h] at hb
        exact hb
      · exact (zero_le).trans le_self_add
  iapply (progCoupl_intro (r := max r 1) Hred Hbnd' Hexp' Heras)
  -- Continuation: for each (e₂, σ₂, e₂', σ₂'), case on membership in `S`.
  iintro %e₂ %σ₂ %e₂' %σ₂'
  by_cases hmem : (⟨e₂, σ₂⟩ : Cfg rT) ∈ S
  · -- In the carrying set: use Hm ∘ HCont.
    simp only [if_pos hmem]
    ihave HZ₁ := HCont $$ %e₂ %σ₂ %e₂' %σ₂'
    imod HZ₁ with HZ₁
    imodintro
    iapply Hm $$ %e₂ %σ₂ %e₂' %σ₂' %(X₂ ⟨e₂, σ₂⟩ ⟨e₂', σ₂'⟩) [HZ₁]
    isplitr; · ipureintro; exact hmem
    iexact HZ₁
  · -- Outside: X₂' = 1, use the catchall.
    simp only [if_neg hmem]
    imodintro
    iexact H1F

/-- Enriches the continuation's hypothesis with the
disjunction "either `⟨e₂, σ₂⟩` lies in a measurable set carrying the step
measure, or the local error bound is already ≥ 1". -/
theorem progCoupl_strengthen {e₁ : Exp rT} {σ₁ : State rT} {e₁' : Exp rT} {σ₁' : State rT}
    {ε : ENNReal} {Z : Exp rT → State rT → Exp rT → State rT → ENNReal → IProp GF}
    {S : Set (Cfg rT)} (hSmeas : MeasurableSet S)
    (hSconc : Concentrated (primStep ⟨e₁, σ₁⟩) S) :
    iprop((□ ∀ e₂ σ₂ e₂' σ₂', Z e₂ σ₂ e₂' σ₂' 1) ∗
          progCoupl e₁ σ₁ e₁' σ₁' ε Z) ⊢@{IProp GF}
      progCoupl e₁ σ₁ e₁' σ₁' ε
        (fun e₂ σ₂ e₂' σ₂' ε' =>
          iprop(⌜(⟨e₂, σ₂⟩ : Cfg rT) ∈ S ∨ 1 ≤ ε'⌝ ∧
                Z e₂ σ₂ e₂' σ₂' ε')) := by
  iintro ⟨#H1F, HCpl⟩
  iapply (progCoupl_strong_mono hSmeas hSconc)
  isplitr
  · iintro !> %e₂ %σ₂ %e₂' %σ₂'
    isplitr; · ipureintro; exact .inr (_root_.le_refl _)
    iexact H1F
  iframe HCpl
  iintro %e₂ %σ₂ %e₂' %σ₂' %ε' ⟨%Hmem, HZ⟩
  isplitr; · ipureintro; exact .inl Hmem
  iexact HZ

/-- `progCoupl_ctx_bind` specialized to ProbLang's `(Ectx rT)`: a program coupling
at `e₁` with continuation receiving the filled-in expression lifts to one at
`K.fill e₁`, provided `e₁` is not a value.

Concrete-(Ectx rT) port: instead of Rocq's classical `Kinv` constructed inside the
proof, we use `Function.partialInv K.fill`. The expectation bound argument
goes through `lintegral_map` + `primStep_fill hv` (the pushforward formula). -/
theorem progCoupl_ctx_bind {K : Ectx rT} {e₁ : Exp rT} {σ₁ : State rT} {e₁' : Exp rT}
    {σ₁' : State rT}
    {ε : ENNReal} {Z : Exp rT → State rT → Exp rT → State rT → ENNReal → IProp GF}
    (hv : ¬ e₁.isValue) :
    iprop((□ ∀ e₂ σ₂ e₂' σ₂', Z e₂ σ₂ e₂' σ₂' 1) ∗
          progCoupl e₁ σ₁ e₁' σ₁' ε
            (fun e₂ => Z (K.fill e₂))) ⊢@{IProp GF}
      progCoupl (K.fill e₁) σ₁ e₁' σ₁' ε Z := by
  iintro ⟨#H1F, HCpl⟩
  icases HCpl with ⟨%n, %μ₁', %X₂, %Hred, %Hbnd, %Hexp, %Heras, HCont⟩
  obtain ⟨r, Hr⟩ := Hbnd
  classical
  -- Inverse of `K.fill`.
  let Kinv : Exp rT → Option (Exp rT) := Function.partialInv K.fill
  have Kinv_left : ∀ e, Kinv (K.fill e) = some e :=
    Function.partialInv_left (Ectx.fill_injective K)
  -- New error function: `X₂` pulled back along `Kinv`, and 1 where `Kinv` fails.
  have Hbnd' : ∀ (a b : Cfg rT), (match Kinv a.expr with
      | some e' => X₂ ⟨e', a.state⟩ b
      | none => 1) ≤ max r 1 := by
    intro a b
    cases Kinv a.expr with
    | none => exact le_max_right _ _
    | some e' => exact (Hr _ _).trans (le_max_left _ _)
  have Hexp' : ExpCoupl ε (fun a b => match Kinv a.expr with
        | some e' => X₂ ⟨e', a.state⟩ b
        | none => 1)
      (primStep ⟨K.fill e₁, σ₁⟩) (μ₁'.bind (fun σ => pexecN n ⟨e₁', σ⟩)) := by
    intro h₁ h₂ Hh₁meas Hh₂meas Hh₁ Hh₂ Hh₁h₂
    -- Pull back h₁ along K.fill: h₁'(ρ) := h₁ ⟨K.fill ρ.expr, ρ.state⟩.
    let h₁' : Cfg rT → ENNReal := fun ρ => h₁ ⟨K.fill ρ.expr, ρ.state⟩
    have hh₁'meas : Measurable h₁' :=
      Hh₁meas.comp (Ectx.fillCfg.measurable K)
    -- Step 1: ∫ h₁ ∂primStep⟨K.fill e₁, σ₁⟩ = ∫ h₁' ∂primStep⟨e₁, σ₁⟩.
    have hmap : (∫⁻ a, h₁ a ∂(primStep ⟨K.fill e₁, σ₁⟩)) =
                ∫⁻ ρ, h₁' ρ ∂(primStep ⟨e₁, σ₁⟩) := by
      rw [primStep_fill hv]
      rw [MeasureTheory.lintegral_map Hh₁meas (by fun_prop)]
    rw [hmap]
    -- Step 2: apply Hexp to h₁', h₂.
    refine Hexp h₁' h₂ hh₁'meas Hh₂meas ?_ Hh₂ ?_
    · intro ρ; exact Hh₁ _
    · intro ρ b
      -- `Kinv_left` collapses the new cost at `⟨K.fill ρ.expr, ρ.state⟩` to `X₂ ρ b`,
      -- and `ρ = ⟨ρ.expr, ρ.state⟩` definitionally.
      have := Hh₁h₂ ⟨K.fill ρ.expr, ρ.state⟩ b
      simp only [Kinv_left] at this
      exact this
  iapply (progCoupl_intro (r := max r 1) (Hred.fill K) Hbnd' Hexp' Heras)
  -- Continuation: case on Kinv e₂.
  iintro %e₂ %σ₂ %e₂' %σ₂'
  cases hKinv : Kinv e₂ with
  | none =>
    -- Unreachable: X₂' a b = 1 here.
    imodintro
    iexact H1F
  | some e₃ =>
    -- e₂ = K.fill e₃.
    have he₂ : K.fill e₃ = e₂ :=
      ((Function.Injective.isPartialInv (Ectx.fill_injective K)) e₃ e₂).1 hKinv
    ihave HZ := HCont $$ %e₃ %σ₂ %e₂' %σ₂'
    imod HZ with HZ
    imodintro
    rw [← he₂]
    iexact HZ

/-! ### `progCoupl` — coupling-intro lemmas

General-purpose "construct a `progCoupl` from a raw expectation-bound" lemmas.
These all take `n = 1` spec step, `μ₁' = dirac σ₁'`, and collapse
`pexecN 1 ⟨e₁', ·⟩` to `primStep` via `stepOrFinal_not_isValue`. -/

/-- `prog_coupl_steps_adv'` — one-spec-step intro with an adversarial per-cfg
error `X₂` bounded by 1. Mirrors Rocq's `prog_coupl_steps_adv'`. -/
theorem progCoupl_steps_adv' {e₁ : Exp rT} {σ₁ : State rT} {e₁' : Exp rT} {σ₁' : State rT}
    {ε : ENNReal} {Z : Exp rT → State rT → Exp rT → State rT → ENNReal → IProp GF}
    {X₂ : Cfg rT → Cfg rT → ENNReal}
    (Hred : Reducible e₁ σ₁) (Hred' : Reducible e₁' σ₁')
    (Hbnd : ∀ ρ₁ ρ₂, X₂ ρ₁ ρ₂ ≤ 1)
    (Hcpl : ExpCoupl ε X₂ (primStep ⟨e₁, σ₁⟩) (primStep ⟨e₁', σ₁'⟩)) :
    iprop(∀ (e₂ : Exp rT) (σ₂ : State rT) (e₂' : Exp rT) (σ₂' : State rT),
        |={∅}=> Z e₂ σ₂ e₂' σ₂' (X₂ ⟨e₂, σ₂⟩ ⟨e₂', σ₂'⟩)) ⊢@{IProp GF}
      progCoupl e₁ σ₁ e₁' σ₁' ε Z := by
  iintro Hcnt
  iapply (progCoupl_intro (n := 1) (μ₁' := MeasureTheory.Measure.dirac σ₁') (r := 1)
    Hred Hbnd (dirac_bind_pexecN_one Hred' ▸ Hcpl) (ErasableExpr.dret σ₁'))
  iexact Hcnt

/-- `prog_coupl_steps_adv` — with an additive `ε₂` slack added to the
per-config error. Derived from `progCoupl_steps_adv'` by shifting `X₂ + ε₂`. -/
theorem progCoupl_steps_adv {e₁ : Exp rT} {σ₁ : State rT} {e₁' : Exp rT} {σ₁' : State rT}
    {ε₁ ε₂ ε : ENNReal} {Z : Exp rT → State rT → Exp rT → State rT → ENNReal → IProp GF}
    {X₂ : Cfg rT → Cfg rT → ENNReal}
    (Hε : ε₁ + ε₂ ≤ ε)
    (Hred : Reducible e₁ σ₁) (Hred' : Reducible e₁' σ₁')
    (Hbnd : ∀ ρ₁ ρ₂, X₂ ρ₁ ρ₂ ≤ 1)
    (Hcpl : ExpCoupl ε₁ X₂ (primStep ⟨e₁, σ₁⟩) (primStep ⟨e₁', σ₁'⟩)) :
    iprop(∀ (e₂ : Exp rT) (σ₂ : State rT) (e₂' : Exp rT) (σ₂' : State rT),
        |={∅}=> Z e₂ σ₂ e₂' σ₂' (X₂ ⟨e₂, σ₂⟩ ⟨e₂', σ₂'⟩ + ε₂)) ⊢@{IProp GF}
      progCoupl e₁ σ₁ e₁' σ₁' ε Z := by
  iintro Hcnt
  -- Cost `X₂ + ε₂`, bounded by `1 + ε₂`; the extra `ε₂` comes out of the slack.
  iapply (progCoupl_intro (n := 1) (μ₁' := MeasureTheory.Measure.dirac σ₁') (r := 1 + ε₂)
    (Hred := Hred) (Hbnd := fun a b => by gcongr; exact Hbnd a b)
    (Hexp := dirac_bind_pexecN_one Hred' ▸ expCoupl_add_const Hε (primStep_univ_le_one _)
      (primStep_univ_le_one _) Hcpl)
    (Heras := ErasableExpr.dret σ₁'))
  iexact Hcnt

/-- `prog_coupl_steps` — given an `AddCoupl` between program steps and a
catch-all at `ε = 1`, construct a `progCoupl`. Mirrors Rocq's `prog_coupl_steps`
via the `Y := if (R ∧ ε₂ ≤ 1) then ε₂ else 1` indicator trick. -/
theorem progCoupl_steps {e₁ : Exp rT} {σ₁ : State rT} {e₁' : Exp rT} {σ₁' : State rT}
    {ε₁ ε₂ ε : ENNReal} {R : Cfg rT → Cfg rT → Prop}
    {Z : Exp rT → State rT → Exp rT → State rT → ENNReal → IProp GF}
    (Hε : ε₁ + ε₂ ≤ ε)
    (Hred : Reducible e₁ σ₁) (Hred' : Reducible e₁' σ₁')
    (Hcpl : AddCoupl ε₁ {p : Cfg rT × (Cfg rT) | R p.1 p.2}
              (primStep ⟨e₁, σ₁⟩) (primStep ⟨e₁', σ₁'⟩)) :
    iprop((□ ∀ e₂ σ₂ e₂' σ₂', Z e₂ σ₂ e₂' σ₂' 1) ∗
          (∀ (e₂ : Exp rT) (σ₂ : State rT) (e₂' : Exp rT) (σ₂' : State rT),
            (⌜R ⟨e₂, σ₂⟩ ⟨e₂', σ₂'⟩⌝) -∗ |={∅}=>
              Z e₂ σ₂ e₂' σ₂' ε₂)) ⊢@{IProp GF}
      progCoupl e₁ σ₁ e₁' σ₁' ε Z := by
  iintro ⟨#H1F, Hcnt⟩
  classical
  -- Indicator Y: use ε₂ when (R ρ₁ ρ₂ ∧ ε₂ ≤ 1), else 1.
  let Y : Cfg rT → Cfg rT → ENNReal := fun ρ₁ ρ₂ =>
    if R ρ₁ ρ₂ ∧ ε₂ ≤ 1 then ε₂ else 1
  have HY_bnd : ∀ ρ₁ ρ₂, Y ρ₁ ρ₂ ≤ 1 := by
    intro ρ₁ ρ₂
    simp only [Y]
    split_ifs with h
    · exact h.2
    · exact _root_.le_refl _
  have HY_exp : ExpCoupl ε Y (primStep ⟨e₁, σ₁⟩) (primStep ⟨e₁', σ₁'⟩) :=
    expCoupl_of_addCoupl Hε (primStep_univ_le_one _) (primStep_univ_le_one _)
      (fun a b hab => by
        simp only [Y]
        split_ifs with h
        · exact _root_.le_refl _
        · exact (_root_.not_le.mp fun hc => h ⟨hab, hc⟩).le)
      Hcpl
  iapply (progCoupl_steps_adv' (Hred := Hred) (Hred' := Hred')
    (X₂ := Y) HY_bnd HY_exp)
  iintro %e₂ %σ₂ %e₂' %σ₂'
  simp only [Y]
  split_ifs with h
  · iapply Hcnt $$ %e₂ %σ₂ %e₂' %σ₂'
    ipureintro; exact h.1
  · imodintro
    iexact H1F

/-- `prog_coupl_step_l_erasable_adv` — LHS takes one program step, RHS stays
at `e₁'` but its state is sampled from an erasable `μ₁'`. Adversarial `X₂`
indexed by LHS-cfg and RHS-state. -/
theorem progCoupl_step_l_erasable_adv {e₁ : Exp rT} {σ₁ : State rT} {e₁' : Exp rT} {σ₁' : State rT}
    {μ₁' : MeasureTheory.Measure (State rT)} {ε : ENNReal}
    {Z : Exp rT → State rT → Exp rT → State rT → ENNReal → IProp GF}
    {X₂ : Cfg rT → State rT → ENNReal}
    (Hred : Reducible e₁ σ₁)
    (Heras : ErasableExpr μ₁' σ₁')
    (Hbnd : ∀ ρ₁ σ₂', X₂ ρ₁ σ₂' ≤ 1)
    (Hcpl : ExpCoupl ε (fun a (b : Cfg rT) => X₂ a b.state) (primStep ⟨e₁, σ₁⟩)
      (μ₁'.bind (fun σ => MeasureTheory.Measure.dirac ⟨e₁', σ⟩))) :
    iprop((□ ∀ e₂ σ₂ e₂' σ₂', Z e₂ σ₂ e₂' σ₂' 1) ∗
          (∀ (e₂ : Exp rT) (σ₂ : State rT) (σ₂' : State rT),
            |={∅}=> Z e₂ σ₂ e₁' σ₂' (X₂ ⟨e₂, σ₂⟩ σ₂'))) ⊢@{IProp GF}
      progCoupl e₁ σ₁ e₁' σ₁' ε Z := by
  iintro ⟨#H1F, Hcnt⟩
  classical
  -- n = 0, spec doesn't step. The Y indicator: X₂ when RHS-expr is e₁', else 1.
  have Hbnd' : ∀ (ρ₁ ρ₂ : Cfg rT), (if ρ₂.expr = e₁' then X₂ ρ₁ ρ₂.state else 1) ≤ 1 := by
    intro ρ₁ ρ₂
    split_ifs with h
    · exact Hbnd _ _
    · exact _root_.le_refl _
  have Hexp' : ExpCoupl ε (fun ρ₁ ρ₂ => if ρ₂.expr = e₁' then X₂ ρ₁ ρ₂.state else 1)
      (primStep ⟨e₁, σ₁⟩) (μ₁'.bind (fun σ => pexecN 0 ⟨e₁', σ⟩)) := by
    intro h₁ h₂ Hh₁meas Hh₂meas Hh₁ Hh₂ Hh₁h₂
    simp only [pexecN_zero]
    -- Both integrals live on `{b | b.expr = e₁'}`, so replacing `h₂` by its pullback
    -- `h₂' b := h₂ ⟨e₁', b.state⟩` changes neither side, and on that set the new cost
    -- is the old `X₂`.
    have Hh₂'meas : Measurable (fun b : Cfg rT => h₂ ⟨e₁', b.state⟩) := Hh₂meas.comp (by fun_prop)
    have := Hcpl h₁ (fun b => h₂ ⟨e₁', b.state⟩) Hh₁meas Hh₂'meas Hh₁ (fun _ => Hh₂ _)
      (fun a b => by simpa using Hh₁h₂ a ⟨e₁', b.state⟩)
    rw [MeasureTheory.Measure.bind_dirac_eq_map _ (by fun_prop),
      MeasureTheory.lintegral_map Hh₂'meas (by fun_prop)] at this
    rwa [MeasureTheory.Measure.bind_dirac_eq_map _ (by fun_prop),
      MeasureTheory.lintegral_map Hh₂meas (by fun_prop)]
  iapply (progCoupl_intro (n := 0) (μ₁' := μ₁') (r := 1) Hred Hbnd' Hexp' Heras)
  iintro %e₂ %σ₂ %e₂' %σ₂'
  by_cases he : e₂' = e₁'
  · subst he
    simp only [↓reduceIte]
    ihave HZ := Hcnt $$ %e₂ %σ₂ %σ₂'
    iexact HZ
  · simp only [if_neg he]
    imodintro
    iexact H1F

/-- `prog_coupl_step_l_erasable` — non-adversarial LHS-only step. The coupling
hypothesis gives `AddCoupl ε₁ R (primStep e₁ σ₁) μ₁'`, and the continuation
consumes the R-relation on reachable pairs. -/
theorem progCoupl_step_l_erasable {e₁ : Exp rT} {σ₁ : State rT} {e₁' : Exp rT} {σ₁' : State rT}
    {μ₁' : MeasureTheory.Measure (State rT)} {ε₁ ε₂ ε : ENNReal}
    {Z : Exp rT → State rT → Exp rT → State rT → ENNReal → IProp GF}
    {R : Cfg rT → State rT → Prop}
    (Hε : ε₁ + ε₂ ≤ ε)
    (Hred : Reducible e₁ σ₁)
    (Hcpl : AddCoupl ε₁ {p : Cfg rT × (State rT) | R p.1 p.2} (primStep ⟨e₁, σ₁⟩) μ₁')
    (Heras : ErasableExpr μ₁' σ₁') :
    iprop((□ ∀ e₂ σ₂ e₂' σ₂', Z e₂ σ₂ e₂' σ₂' 1) ∗
          (∀ (e₂ : Exp rT) (σ₂ : State rT) (σ₂' : State rT),
            (⌜R ⟨e₂, σ₂⟩ σ₂'⌝) -∗ |={∅}=>
              Z e₂ σ₂ e₁' σ₂' ε₂)) ⊢@{IProp GF}
      progCoupl e₁ σ₁ e₁' σ₁' ε Z := by
  iintro ⟨#H1F, Hcnt⟩
  classical
  -- Y: ε₂ when R ρ₁ σ₂' ∧ ε₂ ≤ 1, else 1.
  let Y : Cfg rT → State rT → ENNReal := fun ρ₁ σ₂' =>
    if R ρ₁ σ₂' ∧ ε₂ ≤ 1 then ε₂ else 1
  have HY_bnd : ∀ ρ₁ σ₂', Y ρ₁ σ₂' ≤ 1 := fun ρ₁ σ₂' => by
    simp only [Y]; split_ifs with h; exacts [h.2, _root_.le_refl _]
  -- Push `Hcpl` along `σ ↦ ⟨e₁', σ⟩`, then read the indicator `Y` off the relation.
  have Hcpl' : AddCoupl ε₁ {p : Cfg rT × (Cfg rT) | R p.1 p.2.state} (primStep ⟨e₁, σ₁⟩)
      (μ₁'.bind (fun σ => MeasureTheory.Measure.dirac (⟨e₁', σ⟩ : Cfg rT))) := by
    rw [MeasureTheory.Measure.bind_dirac_eq_map _ (by fun_prop),
      ← MeasureTheory.Measure.map_id (μ := primStep ⟨e₁, σ₁⟩)]
    exact AddCoupl.map (f := id) (g := fun σ => (⟨e₁', σ⟩ : Cfg rT))
      (by fun_prop) (by fun_prop) (fun {_ _} HR => HR) Hcpl
  have hν : (μ₁'.bind (fun σ => MeasureTheory.Measure.dirac (⟨e₁', σ⟩ : Cfg rT))) Set.univ ≤ 1 := by
    rw [MeasureTheory.Measure.bind_dirac_eq_map _ (by fun_prop),
      MeasureTheory.Measure.map_apply (by fun_prop) MeasurableSet.univ]
    simp [ErasableExpr.mass Heras]
  have HY_exp : ExpCoupl ε (fun a (b : Cfg rT) => Y a b.state) (primStep ⟨e₁, σ₁⟩)
      (μ₁'.bind (fun σ => MeasureTheory.Measure.dirac ⟨e₁', σ⟩)) :=
    expCoupl_of_addCoupl Hε (primStep_univ_le_one _) hν
      (fun a b hab => by
        simp only [Y]
        split_ifs with h
        · exact _root_.le_refl _
        · exact (_root_.not_le.mp fun hc => h ⟨hab, hc⟩).le)
      Hcpl'
  iapply (progCoupl_step_l_erasable_adv (Hred := Hred) (Heras := Heras)
    (X₂ := Y) HY_bnd HY_exp)
  iframe H1F
  iintro %e₂ %σ₂ %σ₂'
  simp only [Y]
  split_ifs with h
  · iapply Hcnt $$ %e₂ %σ₂ %σ₂'
    ipureintro; exact h.1
  · imodintro
    iexact H1F

/-- `prog_coupl_step_l_dret` — LHS-only step with spec staying at exactly
`(e₁', σ₁')` (RHS is `dirac σ₁'`). Specialization of `_step_l_erasable`. -/
theorem progCoupl_step_l_dret {e₁ : Exp rT} {σ₁ : State rT} {e₁' : Exp rT} {σ₁' : State rT}
    {ε₁ ε₂ ε : ENNReal} {R : Cfg rT → State rT → Prop}
    {Z : Exp rT → State rT → Exp rT → State rT → ENNReal → IProp GF}
    (Hε : ε₁ + ε₂ ≤ ε)
    (Hred : Reducible e₁ σ₁)
    (Hcpl : AddCoupl ε₁ {p : Cfg rT × (State rT) | R p.1 p.2}
              (primStep ⟨e₁, σ₁⟩) (MeasureTheory.Measure.dirac σ₁')) :
    iprop((□ ∀ e₂ σ₂ e₂' σ₂', Z e₂ σ₂ e₂' σ₂' 1) ∗
          (∀ (e₂ : Exp rT) (σ₂ : State rT),
            (⌜R ⟨e₂, σ₂⟩ σ₁'⌝) -∗ |={∅}=>
              Z e₂ σ₂ e₁' σ₁' ε₂)) ⊢@{IProp GF}
      progCoupl e₁ σ₁ e₁' σ₁' ε Z := by
  iintro ⟨#H1F, H⟩
  classical
  -- `dirac σ₁'` is concentrated on `{σ₁'}`, so the coupling relation may be
  -- refined to force the RHS sample `p.2 = σ₁'` — countability-free, via
  -- `AddCoupl.concentrated_R` (the continuous analogue of `pos_R`'s RHS half).
  have hconc : (MeasureTheory.Measure.dirac σ₁' : MeasureTheory.Measure (State rT)) {σ₁'}ᶜ = 0 := by
    rw [MeasureTheory.Measure.dirac_apply' _ (by measurability)]; simp
  have HcplR : AddCoupl ε₁ {p : Cfg rT × (State rT) | R p.1 p.2 ∧ p.2 = σ₁'}
      (primStep ⟨e₁, σ₁⟩) (MeasureTheory.Measure.dirac σ₁') := by
    refine AddCoupl.mono_rel ?_
      (AddCoupl.concentrated_R (MeasurableSet.singleton σ₁') hconc Hcpl)
    rintro ⟨ρ, σ⟩ ⟨HR, hmem⟩
    exact ⟨HR, hmem⟩
  iapply (progCoupl_step_l_erasable (μ₁' := MeasureTheory.Measure.dirac σ₁')
    (Hε := Hε) (Hred := Hred)
    (R := fun ρ σ => R ρ σ ∧ σ = σ₁') HcplR (ErasableExpr.dret σ₁'))
  iframe H1F
  iintro %e₂ %σ₂ %σ₂' %HR'
  obtain ⟨HR, rfl⟩ := HR'
  iapply H $$ %e₂ %σ₂ %HR

/-- Pure LHS-step, landing anywhere in a
measurable set `S` carrying the step measure.

Countability-free generalization of `progCoupl_step_l`. The coupling against
`dirac σ₁'` is the trivial one, refined on the left by `AddCoupl.concentrated_L`
instead of by `AddCoupl.pos_R`'s atom enumeration. -/
theorem progCoupl_step_l_concentrated {e₁ : Exp rT} {σ₁ : State rT} {e₁' : Exp rT} {σ₁' : State rT}
    {ε : ENNReal} {Z : Exp rT → State rT → Exp rT → State rT → ENNReal → IProp GF}
    {S : Set (Cfg rT)} (Hred : Reducible e₁ σ₁)
    (hSmeas : MeasurableSet S) (hSconc : Concentrated (primStep ⟨e₁, σ₁⟩) S) :
    iprop((□ ∀ e₂ σ₂ e₂' σ₂', Z e₂ σ₂ e₂' σ₂' 1) ∗
          (∀ (e₂ : Exp rT) (σ₂ : State rT),
            (⌜(⟨e₂, σ₂⟩ : Cfg rT) ∈ S⌝) -∗ |={∅}=>
              Z e₂ σ₂ e₁' σ₁' ε)) ⊢@{IProp GF}
      progCoupl e₁ σ₁ e₁' σ₁' ε Z := by
  iintro ⟨#H1F, H⟩
  classical
  have hprob_lhs : (primStep ⟨e₁, σ₁⟩) Set.univ = 1 := by
    haveI := prim_step_mass Hred
    exact MeasureTheory.IsProbabilityMeasure.measure_univ
  have Htrivial : AddCoupl 0 Set.univ (primStep ⟨e₁, σ₁⟩)
      (MeasureTheory.Measure.dirac σ₁') :=
    RelCoupl.exact (RelCoupl.trivial hprob_lhs (by simp))
  have Hε : (0 : ENNReal) + ε ≤ ε := by rw [zero_add]
  -- Refine the (trivial) relation on the left by `S`, countability-free.
  have HcplR : AddCoupl 0 {p : Cfg rT × (State rT) | (fun ρ _ => ρ ∈ S) p.1 p.2}
      (primStep ⟨e₁, σ₁⟩) (MeasureTheory.Measure.dirac σ₁') := by
    refine AddCoupl.mono_rel ?_ (AddCoupl.concentrated_L hSmeas hSconc Htrivial)
    rintro ⟨ρ, σ⟩ ⟨_, hρ⟩
    exact hρ
  iapply (progCoupl_step_l_dret (ε₁ := 0) (ε₂ := ε)
    (R := fun ρ _ => ρ ∈ S)
    (Hε := Hε) (Hred := Hred) HcplR)
  iframe H1F
  iintro %e₂ %σ₂ %Hmem
  iapply H $$ %e₂ %σ₂ %Hmem

/-! ## WP — outer OFE instances and `IntoVal`-style value intros -/

/-- General value introduction: from `e.toVal? = some v` and `|={E}=> Φ v`,
conclude `wp E e Φ`. -/
theorem wp_value_fupd_of_toVal {E : CoPset} {e : Exp rT} {v : Val rT}
    {Φ : Val rT → IProp GF} (h : e.toVal? = some v) :
    iprop(|={E}=> Φ v) ⊢@{IProp GF} wp E e Φ := by
  rw [← Exp.ofVal_of_toVal_some h]
  exact wp_value_fupd

/-- `wp` is non-expansive in its post. Proof mirrors Rocq's `wp_ne`:
strong induction on OFE distance `n`, `wp_unfold` on both sides, structural
walk through `wpPre` (same shape as `wpPre_contractive`), and IH at `m < n`
under the `▷` in the non-value branch. -/
theorem wp_ne_aux {E : CoPset} {e : Exp rT} {Φ Ψ : Val rT → IProp GF} {n : Nat}
    (HΦ : ∀ v, Φ v ≡{n}≡ Ψ v) : wp (GF := GF) E e Φ ≡{n}≡ wp E e Ψ := by
  induction n using Nat.strong_induction_on generalizing e Φ Ψ with
  | _ n IH =>
    have heq1 : wp (GF := GF) E e Φ ≡{n}≡ wpPre wp E e Φ :=
      OFE.eq_dist_1 wp_unfold n
    have heq2 : wp (GF := GF) E e Ψ ≡{n}≡ wpPre wp E e Ψ :=
      OFE.eq_dist_1 wp_unfold n
    refine heq1.trans (OFE.Dist.trans ?_ heq2.symm)
    exact wpPre_ne_aux HΦ fun m Hm _ => IH m Hm fun v => OFE.Dist.lt (HΦ v) Hm

instance wp_ne {E : CoPset} {e : Exp rT} :
    NonExpansive ((wp (GF := GF)) E e) where
  ne _ _ _ H := wp_ne_aux H

-- TODO: `wp_contractive` — `wp` is `Contractive` in its post when the head
-- is *not* a value. Needs structural `wp_unfold` walk under the
-- `e.toVal? = none` branch; dual to `wpPre_contractive` restricted to `none`.

/-! ## WP — structural lemmas (deferred, need more infra or Löb) -/

/-- The Löb-induction statement for `wp_bind`. -/
noncomputable abbrev wpBindStmt (K : Ectx rT) : IProp GF :=
  iprop(∀ (E : CoPset) (e : Exp rT) (Φ : Val rT → IProp GF),
    wp E e (fun v => wp E (K.fill (Exp.ofVal v)) Φ) -∗ wp E (K.fill e) Φ)

/-- `wp_bind` specialized to ProbLang's concrete `(Ectx rT)`.

Proved via Löb induction: under `loeb_wand`, we case-split on `e.toVal?`.
* Value case (`some v`): `e = ofVal v`, so `K.fill e = K.fill (ofVal v)`.
  After `fupd_specCoupl`, unfold the inner `wp E (K.fill (ofVal v)) Φ` directly.
* Non-value case: lift the inner `progCoupl` from `e` to `K.fill e` via
  `progCoupl_ctx_bind`, then rewrite the inner `wp E e₃ (λ v => wp E (K.fill (ofVal v)) Φ)`
  to `wp E (K.fill e₃) Φ` using the IH under `▷`. -/
theorem wp_bind {K : Ectx rT} {E : CoPset} {e : Exp rT} {Φ : Val rT → IProp GF} :
    wp E e (fun v => wp E (K.fill (Exp.ofVal v)) Φ) ⊢@{IProp GF}
      wp E (K.fill e) Φ := by
  have Hloeb : ⊢@{IProp GF} wpBindStmt (GF := GF) K := by
    iapply loeb_wand
    iintro !> IH %E' %e' %Φ' HW
    iapply wp_unfold
    unfold wpPre
    iintro %σ₁ %e₁' %σ₁' %ε₁ ⟨Hσ, Hs, Hε⟩
    ihave HW' := wp_unfold_mp $$ HW
    ispecialize HW' $$ %σ₁ %e₁' %σ₁' %ε₁ [$Hσ $Hs $Hε]
    imod HW'
    imodintro
    iapply specCoupl_bind (E1 := ∅) (E2 := ∅) Std.LawfulSet.subset_refl
    iframe HW'
    iintro %σ₂ %ρ₂ %ε₂ HBody
    cases htv : e'.toVal? with
    | some v =>
      -- `e' = ofVal v`, so the outer match is on `(K.fill (ofVal v)).toVal?`.
      iapply fupd_specCoupl
      rw [(show e' = Exp.ofVal v from (Exp.ofVal_of_toVal_some htv).symm)]
      imod HBody with ⟨Hσ', Hs', Hε', HInner⟩
      ihave HInner' := wp_unfold_mp $$ HInner
      ispecialize HInner' $$ %σ₂ %ρ₂.expr %ρ₂.state %ε₂ [$Hσ' $Hs' $Hε']
      imod HInner'
      imodintro
      iexact HInner'
    | none =>
      -- e'.toVal? = none, so ¬ e'.isValue; hence (K.fill e').toVal? = none too.
      have hv : ¬ e'.isValue := Exp.toVal?_eq_none.mp htv
      have hvKfill : ¬ (K.fill e').isValue := fun hKv =>
        hv (Ectx.fill_isValue hKv)
      have hKfillnone : (K.fill e').toVal? = none :=
        Exp.toVal?_eq_none.mpr hvKfill
      iapply specCoupl_ret
      simp only [hKfillnone]
      -- Both `HBody` and the goal are now `progCoupl`s whose bodies differ only in the
      -- innermost `wp`. Rewrite that with the IH (`progCoupl_mono`), then lift `e'` to
      -- `K.fill e'` (`progCoupl_ctx_bind`); the `iapply`s stack in the reverse order.
      iapply (progCoupl_ctx_bind (K := K) (e₁ := e') (Z := wpProgBody E' Φ') hv)
      isplitr; · iapply wpProgBody_err_ge_1
      iapply (progCoupl_mono
        (Z₁ := wpProgBody E' (fun v => wp E' (K.fill (Exp.ofVal v)) Φ')))
      iframe HBody
      iintro %e₃ %σ₃ %e₃' %σ₃' %ε₃ HLater !>
      iapply specCoupl_mono_spatial
      iframe HLater
      iintro %σ₄ %ρ₄ %ε₄ HF
      imod HF with ⟨Hσ', Hs', Hε', HwpInner⟩
      imodintro
      iframe Hσ' Hs' Hε'
      iapply IH $$ %E' %e₃ %Φ' HwpInner
  iapply Hloeb $$ %E %e %Φ

-- `wp_step_fupd` is proved below, after `wp_frame_l` (which it depends on).

-- TODO: `wp_atomic` — for atomic `e`, an inner `|={E2, E1}=>` can be absorbed.
-- In ProbLang every head step is atomic (reduces to a value or single `primStep`),
-- so this unfolds without an `Atomic` typeclass. (State rT) with an explicit
-- "atomic" predicate over `e`, or restrict to expressions of the form
-- `v` | `headAtomic`.

/-- `spec_update_wp` — the spec-side update modality absorbs into `wp`.
Uses `specCoupl_steps_det` to "consume" the deterministic spec steps. -/
theorem specUpdate_wp {E : CoPset} {e : Exp rT} {Φ : Val rT → IProp GF} :
    specUpdate rT E (wp E e Φ) ⊢@{IProp GF} wp E e Φ := by
  unfold specUpdate
  iintro HS
  iapply wp_unfold
  unfold wpPre
  iintro %σ₁ %e₁' %σ₁' %ε₁ ⟨Hσ, Hs, Hε⟩
  ispecialize HS $$ %(⟨e₁', σ₁'⟩ : Cfg rT) Hs
  imod HS with ⟨%ρ', %n, %Hstep, Hs', HW⟩
  cases ρ' with
  | mk e₂' σ₂' =>
    ihave HW' := wp_unfold_mp $$ HW
    ispecialize HW' $$ %σ₁ %e₂' %σ₂' %ε₁ [$Hσ $Hs' $Hε]
    imod HW'
    imodintro
    iapply specCoupl_steps_det Hstep $$ HW'

/-- Löb-induction statement for `wp_specUpdate`. -/
noncomputable abbrev wpSpecUpdateStmt : IProp GF :=
  iprop(∀ (E : CoPset) (e : Exp rT) (Φ : Val rT → IProp GF),
    wp E e (fun v => specUpdate rT E (Φ v)) -∗ wp E e Φ)

/-- Dually to `specUpdate_wp`, a `specUpdate` in the postcondition absorbs
into `wp`. Löb induction matching the Rocq proof. -/
theorem wp_specUpdate {E : CoPset} {e : Exp rT} {Φ : Val rT → IProp GF} :
    wp E e (fun v => specUpdate rT E (Φ v)) ⊢@{IProp GF} wp E e Φ := by
  have Hloeb : ⊢@{IProp GF} wpSpecUpdateStmt (rT := rT) (GF := GF) := by
    iapply loeb_wand
    iintro !> IH %E' %e' %Φ' HW
    iapply wp_unfold
    unfold wpPre
    iintro %σ₁ %e₁' %σ₁' %ε₁ ⟨Hσ, Hs, Hε⟩
    ihave HW' := wp_unfold_mp $$ HW
    ispecialize HW' $$ %σ₁ %e₁' %σ₁' %ε₁ [$Hσ $Hs $Hε]
    imod HW'
    imodintro
    iapply specCoupl_bind (E1 := ∅) (E2 := ∅) Std.LawfulSet.subset_refl
    iframe HW'
    iintro %σ₂ %ρ₂ %ε₂ HBody
    cases htv : e'.toVal? with
    | some v =>
      -- `fupd_specCoupl` opens a `|={∅}=>` in front of the goal; absorb `HBody` and the
      -- spec update under it, then close the mask back down to ∅.
      iapply fupd_specCoupl
      imod HBody with ⟨Hσ', Hs', Hε', HUpd⟩
      ispecialize HUpd $$ %ρ₂ Hs'
      imod HUpd with ⟨%ρ₃, %n, %Hstep, Hs'', HΦv⟩
      cases ρ₃ with
      | mk e₃' σ₃' =>
        imod (BIFUpdate.subset (E1 := E') (E2 := ∅) Std.LawfulSet.empty_subset)
          with Hclose
        imodintro
        iapply specCoupl_steps_det Hstep
        iapply specCoupl_ret
        imod Hclose
        imodintro
        iframe
    | none =>
      iapply specCoupl_ret
      iapply (progCoupl_mono (Z₁ := wpProgBody E' (fun v => specUpdate rT E' (Φ' v))))
      iframe HBody
      iintro %e₃ %σ₃ %e₃' %σ₃' %ε₃ HLater !>
      iapply specCoupl_mono_spatial
      iframe HLater
      iintro %σ₄ %ρ₄ %ε₄ HF
      imod HF with ⟨Hσ', Hs', Hε', HwpInner⟩
      imodintro
      iframe Hσ' Hs' Hε'
      iapply IH $$ %E' %e₃ %Φ' HwpInner
  iapply Hloeb $$ %E %e %Φ

/-! ## WP — derived framing lemmas (all from `wp_strong_mono'`) -/

/-- Löb invariant for `wp_frame_l`. -/
noncomputable abbrev wpFrameLStmt : IProp GF :=
  iprop(∀ (E : CoPset) (e : Exp rT) (R : IProp GF) (Φ : Val rT → IProp GF),
    R -∗ wp E e Φ -∗ wp E e (fun v => iprop(R ∗ Φ v)))

/-- Left-frame: a spatial `R` can be carried through a `wp`. Proved via Löb
induction directly — `wp_wand` isn't usable because it requires a persistent
wand that can't capture the spatial `R`. -/
theorem wp_frame_l {E : CoPset} {e : Exp rT} {R : IProp GF} {Φ : Val rT → IProp GF} :
    iprop(R ∗ wp E e Φ) ⊢@{IProp GF} wp E e (fun v => iprop(R ∗ Φ v)) := by
  have Hloeb : ⊢@{IProp GF} wpFrameLStmt (rT := rT) (GF := GF) := by
    iapply loeb_wand
    iintro !> IH %E' %e' %R' %Φ' HR HW
    iapply wp_unfold
    unfold wpPre
    iintro %σ₁ %e₁' %σ₁' %ε₁ ⟨Hσ, Hs, Hε⟩
    ihave HW' := wp_unfold_mp $$ HW
    ispecialize HW' $$ %σ₁ %e₁' %σ₁' %ε₁ [$Hσ $Hs $Hε]
    imod HW'
    imodintro
    iapply specCoupl_mono_spatial
    iframe HW'
    iintro %σ₂ %ρ₂ %ε₂ HBody
    cases htv : e'.toVal? with
    | some v =>
      imod HBody with ⟨Hσ', Hs', Hε', HΦv⟩
      simp only []
      imodintro
      iframe
    | none =>
      iapply progCoupl_mono
      iframe HBody
      iintro %e₃ %σ₃ %e₃' %σ₃' %ε₃ HLater !>
      iapply specCoupl_mono_spatial
      iframe HLater
      iintro %σ₄ %ρ₄ %ε₄ HFinal
      imod HFinal with ⟨Hσ', Hs', Hε', HwpInner⟩
      imodintro
      iframe
      iapply IH $$ %E' %e₃ %R' %Φ' HR HwpInner
  iintro ⟨HR, HW⟩
  iapply Hloeb $$ %E %e %R %Φ HR HW

/-- Right-frame: symmetric variant, derived from `wp_frame_l` + `wp_wand`. -/
theorem wp_frame_r {E : CoPset} {e : Exp rT} {R : IProp GF} {Φ : Val rT → IProp GF} :
    iprop(wp E e Φ ∗ R) ⊢@{IProp GF} wp E e (fun v => iprop(Φ v ∗ R)) := by
  iintro ⟨HW, HR⟩
  iapply (wp_wand (Φ := fun v => iprop(R ∗ Φ v)) (Ψ := fun v => iprop(Φ v ∗ R)))
  isplitl [HW HR]
  · iapply (wp_frame_l (R := R) (Φ := Φ))
    iframe HR
    iexact HW
  iintro !> %v ⟨HRv, HΦv⟩
  iframe

-- `wp_frame_step_l` and `wp_frame_step_r` are proved below, after
-- `wp_step_fupd` (which they depend on).

/-- Frame-wand: if `wp`'s post consumes `R` to produce `Φ`, and we hold `R`
spatially outside, we can discharge `R` to conclude `wp` at `Φ`. -/
theorem wp_frame_wand {E : CoPset} {e : Exp rT} {R : IProp GF} {Φ : Val rT → IProp GF} :
    iprop(R ∗ wp E e (fun v => iprop(R -∗ Φ v))) ⊢@{IProp GF} wp E e Φ := by
  iintro ⟨HR, HW⟩
  iapply (wp_wand (Φ := fun v => iprop(R ∗ (R -∗ Φ v))) (Ψ := Φ))
  isplitl [HR HW]
  · iapply (wp_frame_l (R := R) (Φ := fun v => iprop(R -∗ Φ v)))
    iframe HR
    iexact HW
  iintro !> %v ⟨HRv, HW'⟩
  iapply HW' $$ HRv

/-- Step-indexed fupd insertion. The `|={E1}[E2]▷=> P`
token delivers `P` after one step, which the inner wp's post consumes. -/
theorem wp_step_fupd {E1 E2 : CoPset} {e : Exp rT} {P : IProp GF} {Φ : Val rT → IProp GF}
    (HE : E2 ⊆ E1) (hv : e.toVal? = none) :
    iprop((|={E1, E2}=> ▷ |={E2, E1}=> P) ∗ wp E2 e (fun v => iprop(P -∗ Φ v))) ⊢@{IProp GF}
      wp E1 e Φ := by
  iintro ⟨HR, HW⟩
  iapply wp_unfold
  unfold wpPre
  iintro %σ₁ %e₁' %σ₁' %ε₁ ⟨Hσ, Hs, Hε⟩
  ihave HW' := wp_unfold_mp $$ HW
  imod HR with HR
  ispecialize HW' $$ %σ₁ %e₁' %σ₁' %ε₁ [$Hσ $Hs $Hε]
  imod HW' with HW'
  imodintro
  iapply specCoupl_mono_spatial
  iframe HW'
  iintro %σ₂ %ρ₂ %ε₂ HBody
  simp only [hv]
  iapply progCoupl_mono
  iframe HBody
  iintro %e₃ %σ₃ %e₃' %σ₃' %ε₃ HLater !>
  iapply specCoupl_mono_spatial
  iframe HLater
  iintro %σ₄ %ρ₄ %ε₄ HFinal
  imod HFinal with ⟨Hσ', Hs', Hε', HwpInner⟩
  imod HR with HR
  imodintro
  iframe Hσ' Hs' Hε'
  iapply wp_mask_mono HE
  iapply (wp_wand (Φ := fun v => iprop(P ∗ (P -∗ Φ v))) (Ψ := Φ))
  isplitl [HwpInner HR]
  · iapply (wp_frame_l (R := P) (Φ := fun v => iprop(P -∗ Φ v)))
    iframe HR
    iexact HwpInner
  iintro !> %v ⟨HP, HWand⟩
  iapply HWand $$ HP

/-- Step-indexed framing (left variant). Use `wp_step_fupd` with post
`R -∗ R ∗ Φ v`, via `wp_wand` to tack on the wand. -/
theorem wp_frame_step_l {E1 E2 : CoPset} {e : Exp rT} {R : IProp GF} {Φ : Val rT → IProp GF}
    (HE : E2 ⊆ E1) (hv : e.toVal? = none) :
    iprop((|={E1, E2}=> ▷ |={E2, E1}=> R) ∗ wp E2 e Φ) ⊢@{IProp GF}
      wp E1 e (fun v => iprop(R ∗ Φ v)) := by
  iintro ⟨HR, HW⟩
  iapply (wp_step_fupd (Φ := fun v => iprop(R ∗ Φ v)) HE hv)
  iframe HR
  iapply (wp_wand (Φ := Φ) (Ψ := fun v => iprop(R -∗ R ∗ Φ v)))
  iframe HW
  iintro !> %v HΦ HR'
  iframe

/-- Step-indexed framing (right variant). -/
theorem wp_frame_step_r {E1 E2 : CoPset} {e : Exp rT} {R : IProp GF} {Φ : Val rT → IProp GF}
    (HE : E2 ⊆ E1) (hv : e.toVal? = none) :
    iprop(wp E2 e Φ ∗ (|={E1, E2}=> ▷ |={E2, E1}=> R)) ⊢@{IProp GF}
      wp E1 e (fun v => iprop(Φ v ∗ R)) := by
  iintro ⟨HW, HR⟩
  iapply (wp_step_fupd (Φ := fun v => iprop(Φ v ∗ R)) HE hv)
  iframe HR
  iapply (wp_wand (Φ := Φ) (Ψ := fun v => iprop(R -∗ Φ v ∗ R)))
  iframe HW
  iintro !> %v HΦ HR'
  iframe

/-- `◇`-absorption: `◇ (wp E e Φ) ⊢ wp E e Φ`. Goes via
`◇ wp ⊢ ◇ (|={E}=> wp) ⊢ |={E}=> wp ⊢ wp`. -/
instance isExcept0_wp {E : CoPset} {e : Exp rT} {Φ : Val rT → IProp GF} :
    IsExcept0 (wp (GF := GF) E e Φ) where
  is_except0 := (except0_mono fupd_intro).trans (BIFUpdate.except0.trans fupd_wp)

/-- `iframe` across a weakest precondition: framing `R` out of every
post-condition frames it out of the `wp`. -/
instance frame_wp {p : Bool} {E : CoPset} {e : Exp rT} {R : IProp GF}
    {Φ Ψ : Val rT → IProp GF} [inst : ∀ v, Frame p R (Φ v) (Ψ v)] :
    Frame p R (wp E e Φ) (wp E e Ψ) where
  frame := wp_frame_l.trans (wp_mono fun v => (inst v).frame)

/-- `ihave`/`ispecialize` may add a same-mask fancy update in front of a `wp`
goal. -/
instance addModal_fupd_wp {E : CoPset} {e : Exp rT} {P : IProp GF}
    {Φ : Val rT → IProp GF} : AddModal iprop(|={E}=> P) P (wp E e Φ) where
  add_modal := fupd_frame_right.trans <| (BIFUpdate.mono wand_elim_right).trans fupd_wp

/-- `iMod` on basic-update: given `|==> P`, absorb via `bupd ⊆ fupd`. -/
instance elimModal_bupd_wp {p : Bool} {io : InOut} {E : CoPset} {e : Exp rT} {P : IProp GF}
    {Φ : Val rT → IProp GF} :
    ElimModal True p io false iprop(|==> P) P (wp E e Φ) (wp E e Φ) where
  elim_modal _ := (sep_mono_left intuitionisticallyIf_elim).trans <|
    (sep_mono_left BIUpdateFUpdate.fupd_of_bupd).trans <|
    fupd_frame_right.trans <| (BIFUpdate.mono wand_elim_right).trans fupd_wp

/-- `iMod` on fancy-update at the same mask. -/
instance elimModal_fupd_wp {p : Bool} {io : InOut} {E : CoPset} {e : Exp rT} {P : IProp GF}
    {Φ : Val rT → IProp GF} :
    ElimModal True p io false iprop(|={E}=> P) P (wp E e Φ) (wp E e Φ) where
  elim_modal _ := (sep_mono_left intuitionisticallyIf_elim).trans <|
    fupd_frame_right.trans <| (BIFUpdate.mono wand_elim_right).trans fupd_wp

/-- `iMod` on `specUpdate` hypotheses absorbing into a `wp`. -/
instance elimModal_specUpdate_wp {io : InOut} {E : CoPset} {e : Exp rT} {P : IProp GF}
    {Φ : Val rT → IProp GF} :
    ElimModal True false io false (specUpdate rT E P) P (wp E e Φ) (wp E e Φ) where
  elim_modal _ := by
    simp only [Bool.false_eq_true, ↓reduceIte, intuitionisticallyIf]
    iintro ⟨HP, Hcnt⟩
    iapply specUpdate_wp
    iintro %ρ Hρ
    ispecialize HP $$ %ρ Hρ
    imod HP with ⟨%ρ', %n, %Hstep, Hρ', HPv⟩
    imodintro
    iexists ρ', n
    isplitr; · ipureintro; exact Hstep
    iframe Hρ'
    iapply Hcnt $$ HPv

/-- `iMod` on `specUpdateN` hypotheses absorbing into a `wp`. -/
instance elimModal_specUpdateN_wp {n : Nat} {io : InOut} {E : CoPset} {e : Exp rT} {P : IProp GF}
    {Φ : Val rT → IProp GF} :
    ElimModal True false io false (specUpdateN rT n E P) P (wp E e Φ) (wp E e Φ) where
  elim_modal _ := by
    simp only [Bool.false_eq_true, ↓reduceIte, intuitionisticallyIf]
    iintro ⟨HP, Hcnt⟩
    ihave HP' := specUpdateN_specUpdate $$ HP
    iapply specUpdate_wp
    iintro %ρ Hρ
    ispecialize HP' $$ %ρ Hρ
    imod HP' with ⟨%ρ', %n', %Hstep, Hρ', HPv⟩
    imodintro
    iexists ρ', n'
    isplitr; · ipureintro; exact Hstep
    iframe Hρ'
    iapply Hcnt $$ HPv

/-! ## Lifting lemmas (ports `clutch/theories/approxis/lifting.v`)

Translate the operational semantics rules into WP rules. These sit directly
on top of `wp_unfold` + the `specCoupl` / `progCoupl` modalities. -/

/-- The most general lifting lemma.
Directly restates `wp_unfold` so callers don't have to unfold `wpPre`. -/
theorem wp_lift_step_couple {E : CoPset} {e₁ : Exp rT} {Φ : Val rT → IProp GF} :
    iprop(∀ (σ₁ : State rT) (e₁' : Exp rT) (σ₁' : State rT) (ε₁ : ENNReal),
      (stateInterp (rT := rT) σ₁ ∗ SpecUpdateGS.specInterp (rT := rT) ⟨e₁', σ₁'⟩ ∗
        errInterp (rT := rT) ε₁) -∗
        |={E, ∅}=> specCoupl ∅ σ₁ e₁' σ₁' ε₁ (fun σ₂ ρ' ε₂ =>
          match e₁.toVal? with
          | some v => iprop(|={∅, E}=>
              stateInterp (rT := rT) σ₂ ∗ SpecUpdateGS.specInterp (rT := rT) ρ' ∗
                errInterp (rT := rT) ε₂ ∗ Φ v)
          | none => progCoupl e₁ σ₂ ρ'.expr ρ'.state ε₂ (fun e₃ σ₃ e₃' σ₃' ε₃ =>
              iprop(▷ specCoupl ∅ σ₃ e₃' σ₃' ε₃ (fun σ₄ ρ'' ε₄ =>
                iprop(|={∅, E}=>
                  stateInterp (rT := rT) σ₄ ∗ SpecUpdateGS.specInterp (rT := rT) ρ'' ∗
                    errInterp (rT := rT) ε₄ ∗ wp E e₃ Φ)))))) ⊢@{IProp GF}
      wp E e₁ Φ := by
  iintro H
  iapply wp_unfold
  unfold wpPre
  iexact H

/-- Only spec-side coupling, no LHS step.
After the spec-coupling we must re-establish `wp E e₁ Φ`. -/
theorem wp_lift_step_spec_couple {E : CoPset} {e₁ : Exp rT} {Φ : Val rT → IProp GF} :
    iprop(∀ (σ₁ : State rT) (e₁' : Exp rT) (σ₁' : State rT) (ε₁ : ENNReal),
      (stateInterp (rT := rT) σ₁ ∗ SpecUpdateGS.specInterp (rT := rT) ⟨e₁', σ₁'⟩ ∗
        errInterp (rT := rT) ε₁) -∗
        |={E, ∅}=> specCoupl ∅ σ₁ e₁' σ₁' ε₁ (fun σ₂ ρ' ε₂ =>
          iprop(|={∅, E}=>
            stateInterp (rT := rT) σ₂ ∗ SpecUpdateGS.specInterp (rT := rT) ρ' ∗
              errInterp (rT := rT) ε₂ ∗
              wp E e₁ Φ))) ⊢@{IProp GF}
      wp E e₁ Φ := by
  iintro H
  iapply wp_lift_step_couple
  iintro %σ₁ %e₁' %σ₁' %ε₁ ⟨Hσ, Hs, Hε⟩
  ispecialize H $$ %σ₁ %e₁' %σ₁' %ε₁ [$Hσ $Hs $Hε]
  imod H
  imodintro
  iapply specCoupl_bind (E1 := ∅) (E2 := ∅) Std.LawfulSet.subset_refl
  iframe H
  iintro %σ₂ %ρ₂ %ε₂ HInner
  iapply fupd_specCoupl
  imod HInner with ⟨Hσ', Hs', Hε', HW⟩
  ihave HW' := wp_unfold_mp $$ HW
  ispecialize HW' $$ %σ₂ %ρ₂.expr %ρ₂.state %ε₂ [$Hσ' $Hs' $Hε']
  imod HW'
  imodintro
  iexact HW'

/-- One program step against any `progCoupl`,
no spec-only coupling prefix. Requires `e₁` is not a value. -/
theorem wp_lift_step_prog_couple {E : CoPset} {e₁ : Exp rT} {Φ : Val rT → IProp GF}
    (Hv : e₁.toVal? = none) :
    iprop(∀ (σ₁ : State rT) (e₁' : Exp rT) (σ₁' : State rT) (ε₁ : ENNReal),
      (stateInterp (rT := rT) σ₁ ∗ SpecUpdateGS.specInterp (rT := rT) ⟨e₁', σ₁'⟩ ∗
        errInterp (rT := rT) ε₁) -∗
        |={E, ∅}=> progCoupl e₁ σ₁ e₁' σ₁' ε₁ (fun e₂ σ₂ e₂' σ₂' ε₂ =>
          iprop(▷ |={∅, E}=>
            stateInterp (rT := rT) σ₂ ∗ SpecUpdateGS.specInterp (rT := rT) ⟨e₂',
              σ₂'⟩ ∗ errInterp (rT := rT) ε₂ ∗
              wp E e₂ Φ))) ⊢@{IProp GF}
      wp E e₁ Φ := by
  iintro H
  iapply wp_lift_step_couple
  iintro %σ₁ %e₁' %σ₁' %ε₁ ⟨Hσ, Hs, Hε⟩
  ispecialize H $$ %σ₁ %e₁' %σ₁' %ε₁ [$Hσ $Hs $Hε]
  imod H
  imodintro
  iapply specCoupl_ret
  simp only [Hv]
  iapply (progCoupl_mono (Z₁ := fun e₂ σ₂ e₂' σ₂' ε₂ =>
    iprop(▷ |={∅, E}=>
      stateInterp (rT := rT) σ₂ ∗ SpecUpdateGS.specInterp (rT := rT) ⟨e₂', σ₂'⟩ ∗
        errInterp (rT := rT) ε₂ ∗
        wp E e₂ Φ)))
  iframe H
  iintro %e₂ %σ₂ %e₂' %σ₂' %ε₂ HL !>
  iapply specCoupl_ret
  iexact HL

/-- Single LHS step, no spec-side coupling,
results under a later, landing anywhere in a measurable set carrying the step
measure.

Countability-free generalization of `wp_lift_step_later`. The carrying set is a
*family* `S : State rT → Set (Cfg rT)` because the start state `σ₁` is bound
inside the assertion, so the set may depend on it. -/
theorem wp_lift_step_later_concentrated {E : CoPset} {e₁ : Exp rT} {Φ : Val rT → IProp GF}
    {S : State rT → Set (Cfg rT)} (Hv : e₁.toVal? = none)
    (hSmeas : ∀ σ₁, MeasurableSet (S σ₁))
    (hSconc : ∀ σ₁, Concentrated (primStep ⟨e₁, σ₁⟩) (S σ₁)) :
    iprop(∀ (σ₁ : State rT), stateInterp (rT := rT) σ₁ -∗ |={E, ∅}=>
      (⌜Reducible e₁ σ₁⌝) ∗
      ∀ (e₂ : Exp rT) (σ₂ : State rT),
        (⌜(⟨e₂, σ₂⟩ : Cfg rT) ∈ S σ₁⌝) -∗ |={∅}=> iprop(▷ |={∅, E}=>
          stateInterp (rT := rT) σ₂ ∗ wp E e₂ Φ)) ⊢@{IProp GF}
      wp E e₁ Φ := by
  iintro H
  iapply wp_lift_step_couple
  iintro %σ₁ %e₁' %σ₁' %ε₁ ⟨Hσ, Hs, Hε⟩
  ispecialize H $$ %σ₁ [$Hσ]
  imod H with ⟨%Hred, H⟩
  imodintro
  iapply specCoupl_ret
  simp only [Hv]
  iapply (progCoupl_step_l_concentrated (Z := wpProgBody E Φ) Hred (hSmeas σ₁) (hSconc σ₁))
  isplitr; · iapply wpProgBody_err_ge_1
  iintro %e₂ %σ₂ %Hmem
  ispecialize H $$ %e₂ %σ₂ %Hmem
  imod H
  iintro !> !>
  iapply specCoupl_ret
  imod H with ⟨Hσ', HwpNew⟩
  imodintro
  iframe

/-- Single LHS step, no spec-side coupling, results
under a later.

Discrete corollary of `wp_lift_step_later_concentrated` at the atom set. -/
@[discrete]
theorem wp_lift_step_later {E : CoPset} {e₁ : Exp rT} {Φ : Val rT → IProp GF}
    (Hv : e₁.toVal? = none) (hne : e₁.decomp.2 ≠ .urand := by no_urand) :
    iprop(∀ (σ₁ : State rT), stateInterp (rT := rT) σ₁ -∗ |={E, ∅}=>
      (⌜Discrete.Reducible e₁ σ₁⌝) ∗
      ∀ (e₂ : Exp rT) (σ₂ : State rT),
        (⌜0 < primStep ⟨e₁, σ₁⟩ {⟨e₂, σ₂⟩}⌝) -∗ |={∅}=> iprop(▷ |={∅, E}=>
          stateInterp (rT := rT) σ₂ ∗ wp E e₂ Φ)) ⊢@{IProp GF}
      wp E e₁ Φ := by
  iintro H
  iapply (wp_lift_step_later_concentrated
    (S := fun σ₁ => {ρ : Cfg rT | 0 < primStep ⟨e₁, σ₁⟩ {ρ}}) Hv
    (fun σ₁ => measurableSet_primStep_support e₁ σ₁)
    (fun σ₁ => concentrated_primStep_support e₁ σ₁ hne))
  iintro %σ₁ Hσ
  ispecialize H $$ %σ₁ [$Hσ]
  imod H with ⟨%Hred, H⟩
  imodintro
  isplitr; · ipureintro; exact Hred.toReducible
  iintro %e₂ %σ₂ %Hmem
  iapply H $$ %e₂ %σ₂ %Hmem

/-- Like `wp_lift_step_later_concentrated` but with
the `▷` flipped inside. -/
theorem wp_lift_step_concentrated {E : CoPset} {e₁ : Exp rT} {Φ : Val rT → IProp GF}
    {S : State rT → Set (Cfg rT)} (Hv : e₁.toVal? = none)
    (hSmeas : ∀ σ₁, MeasurableSet (S σ₁))
    (hSconc : ∀ σ₁, Concentrated (primStep ⟨e₁, σ₁⟩) (S σ₁)) :
    iprop(∀ (σ₁ : State rT), stateInterp (rT := rT) σ₁ -∗ |={E, ∅}=>
      (⌜Reducible e₁ σ₁⌝) ∗
      ▷ ∀ (e₂ : Exp rT) (σ₂ : State rT),
        (⌜(⟨e₂, σ₂⟩ : Cfg rT) ∈ S σ₁⌝) -∗ |={∅, E}=>
          stateInterp (rT := rT) σ₂ ∗ wp E e₂ Φ) ⊢@{IProp GF}
      wp E e₁ Φ := by
  iintro H
  iapply (wp_lift_step_later_concentrated Hv hSmeas hSconc)
  iintro %σ₁ Hσ
  ispecialize H $$ %σ₁ [$Hσ]
  imod H with ⟨%Hred, H⟩
  imodintro
  isplitr; · ipureintro; exact Hred
  iintro %e₂ %σ₂ %Hmem !> !>
  iapply H $$ %e₂ %σ₂ %Hmem

/-- Coupling between LHS and RHS primStep. -/
theorem wp_lift_prim_steps_coupl {E : CoPset} {e₁ : Exp rT} {Φ : Val rT → IProp GF}
    (Hv : e₁.toVal? = none) :
    iprop(∀ (σ₁ : State rT) (e₁' : Exp rT) (σ₁' : State rT) (ε : ENNReal),
      (stateInterp (rT := rT) σ₁ ∗ SpecUpdateGS.specInterp (rT := rT) ⟨e₁', σ₁'⟩ ∗
        errInterp (rT := rT) ε) -∗
        |={E, ∅}=>
        ∃ (R : Cfg rT → Cfg rT → Prop) (ε₁ ε₂ : ENNReal),
          (⌜ε₁ + ε₂ ≤ ε⌝) ∗
          (⌜Reducible e₁ σ₁⌝) ∗
          (⌜Reducible e₁' σ₁'⌝) ∗
          (⌜AddCoupl ε₁ {p : Cfg rT × (Cfg rT) | R p.1 p.2}
              (primStep ⟨e₁, σ₁⟩) (primStep ⟨e₁', σ₁'⟩)⌝) ∗
          (∀ (e₂ : Exp rT) (σ₂ : State rT) (e₂' : Exp rT) (σ₂' : State rT),
            (⌜R ⟨e₂, σ₂⟩ ⟨e₂', σ₂'⟩⌝) -∗ |={∅}=> iprop(▷ |={∅, E}=>
              stateInterp (rT := rT) σ₂ ∗ SpecUpdateGS.specInterp (rT := rT) ⟨e₂', σ₂'⟩ ∗
                errInterp (rT := rT) ε₂ ∗ wp E e₂ Φ))) ⊢@{IProp GF}
      wp E e₁ Φ := by
  iintro H
  iapply wp_lift_step_couple
  iintro %σ₁ %e₁' %σ₁' %ε ⟨Hσ, Hs, Hε⟩
  ispecialize H $$ %σ₁ %e₁' %σ₁' %ε [$Hσ $Hs $Hε]
  imod H with ⟨%R, %ε₁, %ε₂, %Hεsum, %Hred, %Hred', %Hcpl, H⟩
  imodintro
  iapply specCoupl_ret
  simp only [Hv]
  iapply (progCoupl_steps (Z := wpProgBody E Φ) Hεsum Hred Hred' Hcpl)
  isplitr; · iapply wpProgBody_err_ge_1
  iintro %e₂ %σ₂ %e₂' %σ₂' %HR
  ispecialize H $$ %e₂ %σ₂ %e₂' %σ₂' %HR
  imod H
  iintro !> !>
  iapply specCoupl_ret
  imod H with ⟨Hσ', Hs', Hε', Hwp'⟩
  imodintro
  iframe

-- DISCRETE: `wp_lift_prim_step_l_dret (Hv : e₁.toVal? = none) :`
--   `(∀ σ₁ e₁' σ₁' ε, stateInterp σ₁ ∗ specInterp ⟨e₁', σ₁'⟩ ∗ errInterp ε -∗ |={E,∅}=>`
--   `∃ R ε₁ ε₂, ⌜ε₁ + ε₂ ≤ ε⌝ ∗ ⌜Discrete.Reducible e₁ σ₁⌝ ∗`
--   `⌜AddCoupl ε₁ {p | R p.1 p.2} (primStep ⟨e₁, σ₁⟩) (dirac σ₁')⌝ ∗ …) ⊢ wp E e₁ Φ`

/-- LHS step, RHS erasable distribution. -/
theorem wp_lift_prim_step_l_erasable {E : CoPset} {e₁ : Exp rT} {Φ : Val rT → IProp GF}
    (Hv : e₁.toVal? = none) :
    iprop(∀ (σ₁ : State rT) (e₁' : Exp rT) (σ₁' : State rT) (ε : ENNReal),
      (stateInterp (rT := rT) σ₁ ∗ SpecUpdateGS.specInterp (rT := rT) ⟨e₁', σ₁'⟩ ∗
        errInterp (rT := rT) ε) -∗
        |={E, ∅}=>
        ∃ (R : Cfg rT → State rT → Prop) (μ₁' : MeasureTheory.Measure (State rT))
          (ε₁ ε₂ : ENNReal),
          (⌜ε₁ + ε₂ ≤ ε⌝) ∗
          (⌜Reducible e₁ σ₁⌝) ∗
          (⌜ErasableExpr μ₁' σ₁'⌝) ∗
          (⌜AddCoupl ε₁ {p : Cfg rT × (State rT) | R p.1 p.2}
              (primStep ⟨e₁, σ₁⟩) μ₁'⌝) ∗
          (∀ (e₂ : Exp rT) (σ₂ : State rT) (σ₂' : State rT),
            (⌜R ⟨e₂, σ₂⟩ σ₂'⌝) -∗ |={∅}=> iprop(▷ |={∅, E}=>
              stateInterp (rT := rT) σ₂ ∗ SpecUpdateGS.specInterp (rT := rT) ⟨e₁', σ₂'⟩ ∗
                errInterp (rT := rT) ε₂ ∗ wp E e₂ Φ))) ⊢@{IProp GF}
      wp E e₁ Φ := by
  iintro H
  iapply wp_lift_step_couple
  iintro %σ₁ %e₁' %σ₁' %ε ⟨Hσ, Hs, Hε⟩
  ispecialize H $$ %σ₁ %e₁' %σ₁' %ε [$Hσ $Hs $Hε]
  imod H with ⟨%R, %μ₁', %ε₁, %ε₂, %Hεsum, %Hred, %Heras, %Hcpl, H⟩
  imodintro
  iapply specCoupl_ret
  simp only [Hv]
  iapply (progCoupl_step_l_erasable (Z := wpProgBody E Φ) Hεsum Hred Hcpl Heras)
  isplitr; · iapply wpProgBody_err_ge_1
  iintro %e₂ %σ₂ %σ₂' %HR
  ispecialize H $$ %e₂ %σ₂ %σ₂' %HR
  imod H
  iintro !> !>
  iapply specCoupl_ret
  imod H with ⟨Hσ', Hs', Hε', Hwp'⟩
  imodintro
  iframe

/-- Atomic step with mask-shifting
fupd, landing anywhere in a measurable set carrying the step measure.

Countability-free generalization of `wp_lift_atomic_step_fupd`. For a genuinely
atomic redex the natural instantiation is `S σ₁ := {ρ | ρ.1.isValue}`, whose
carrying hypothesis is exactly `Atomic'` — which holds for the continuous
sampler (`ProbLang.Atomic.urand'`). -/
theorem wp_lift_atomic_step_fupd_concentrated {E1 E2 : CoPset} {e₁ : Exp rT}
    {Φ : Val rT → IProp GF} {S : State rT → Set (Cfg rT)} (Hv : e₁.toVal? = none)
    (hSmeas : ∀ σ₁, MeasurableSet (S σ₁))
    (hSconc : ∀ σ₁, Concentrated (primStep ⟨e₁, σ₁⟩) (S σ₁)) :
    iprop(∀ (σ₁ : State rT), stateInterp (rT := rT) σ₁ -∗ |={E1}=>
      (⌜Reducible e₁ σ₁⌝) ∗
      ∀ (e₂ : Exp rT) (σ₂ : State rT),
        (⌜(⟨e₂, σ₂⟩ : Cfg rT) ∈ S σ₁⌝) -∗ |={E1}[E2]▷=>
          stateInterp (rT := rT) σ₂ ∗
          (match e₂.toVal? with | some v => Φ v | none => iprop(False))) ⊢@{IProp GF}
      wp E1 e₁ Φ := by
  iintro H
  iapply (wp_lift_step_later_concentrated Hv hSmeas hSconc)
  iintro %σ₁ Hσ
  ispecialize H $$ %σ₁ [$Hσ]
  imod H with ⟨%Hred, H⟩
  imod (BIFUpdate.subset (E1 := E1) (E2 := ∅) Std.LawfulSet.empty_subset)
    with Hclose
  imodintro
  isplitr; · ipureintro; exact Hred
  iintro %e₂ %σ₂ %Hmem
  imod Hclose
  ispecialize H $$ %e₂ %σ₂ %Hmem
  imod H
  imod (BIFUpdate.subset (E1 := E2) (E2 := ∅) Std.LawfulSet.empty_subset)
    with Hclose
  iintro !> !>
  imod Hclose
  cases htv : e₂.toVal? with
  | some v =>
    imod H with ⟨Hσ', HΦ⟩
    imodintro
    iframe Hσ'
    iapply wp_value_of_toVal htv $$ HΦ
  | none =>
    imod H with ⟨Hσ', HΦ⟩
    iexfalso
    iexact HΦ

/-- Atomic step with mask-shifting fupd. -/
@[discrete]
theorem wp_lift_atomic_step_fupd {E1 E2 : CoPset} {e₁ : Exp rT}
    {Φ : Val rT → IProp GF}
    (Hv : e₁.toVal? = none) (hne : e₁.decomp.2 ≠ .urand := by no_urand) :
    iprop(∀ (σ₁ : State rT), stateInterp (rT := rT) σ₁ -∗ |={E1}=>
      (⌜Discrete.Reducible e₁ σ₁⌝) ∗
      ∀ (e₂ : Exp rT) (σ₂ : State rT),
        (⌜0 < primStep ⟨e₁, σ₁⟩ {⟨e₂, σ₂⟩}⌝) -∗ |={E1}[E2]▷=>
          stateInterp (rT := rT) σ₂ ∗
          (match e₂.toVal? with | some v => Φ v | none => iprop(False))) ⊢@{IProp GF}
      wp E1 e₁ Φ := by
  iintro H
  iapply (wp_lift_atomic_step_fupd_concentrated (E2 := E2)
    (S := fun σ₁ => {ρ : Cfg rT | 0 < primStep ⟨e₁, σ₁⟩ {ρ}}) Hv
    (fun σ₁ => measurableSet_primStep_support e₁ σ₁)
    (fun σ₁ => concentrated_primStep_support e₁ σ₁ hne))
  iintro %σ₁ Hσ
  ispecialize H $$ %σ₁ [$Hσ]
  imod H with ⟨%Hred, H⟩
  imodintro
  isplitr; · ipureintro; exact Hred.toReducible
  iintro %e₂ %σ₂ %Hpstep
  iapply H $$ %e₂ %σ₂ %Hpstep

/-- Atomic step without mask shift on the
inner step, landing anywhere in a measurable set carrying the step measure. -/
theorem wp_lift_atomic_step_concentrated {E : CoPset} {e₁ : Exp rT}
    {Φ : Val rT → IProp GF} {S : State rT → Set (Cfg rT)} (Hv : e₁.toVal? = none)
    (hSmeas : ∀ σ₁, MeasurableSet (S σ₁))
    (hSconc : ∀ σ₁, Concentrated (primStep ⟨e₁, σ₁⟩) (S σ₁)) :
    iprop(∀ (σ₁ : State rT), stateInterp (rT := rT) σ₁ -∗ |={E}=>
      (⌜Reducible e₁ σ₁⌝) ∗
      ▷ ∀ (e₂ : Exp rT) (σ₂ : State rT),
        (⌜(⟨e₂, σ₂⟩ : Cfg rT) ∈ S σ₁⌝) -∗ |={E}=>
          stateInterp (rT := rT) σ₂ ∗
          (match e₂.toVal? with | some v => Φ v | none => iprop(False))) ⊢@{IProp GF}
      wp E e₁ Φ := by
  iintro H
  iapply (wp_lift_atomic_step_fupd_concentrated (E2 := E) Hv hSmeas hSconc)
  iintro %σ₁ Hσ
  ispecialize H $$ %σ₁ [$Hσ]
  imod H with ⟨%Hred, H⟩
  imodintro
  isplitr; · ipureintro; exact Hred
  iintro %e₂ %σ₂ %Hmem !> !>
  iapply H $$ %e₂ %σ₂ %Hmem

/-- Atomic step without mask shift on the inner step. -/
@[discrete]
theorem wp_lift_atomic_step {E : CoPset} {e₁ : Exp rT} {Φ : Val rT → IProp GF}
    (Hv : e₁.toVal? = none) (hne : e₁.decomp.2 ≠ .urand := by no_urand) :
    iprop(∀ (σ₁ : State rT), stateInterp (rT := rT) σ₁ -∗ |={E}=>
      (⌜Discrete.Reducible e₁ σ₁⌝) ∗
      ▷ ∀ (e₂ : Exp rT) (σ₂ : State rT),
        (⌜0 < primStep ⟨e₁, σ₁⟩ {⟨e₂, σ₂⟩}⌝) -∗ |={E}=>
          stateInterp (rT := rT) σ₂ ∗
          (match e₂.toVal? with | some v => Φ v | none => iprop(False))) ⊢@{IProp GF}
      wp E e₁ Φ := by
  iintro H
  iapply wp_lift_atomic_step_fupd (E2 := E) Hv hne
  iintro %σ₁ Hσ
  ispecialize H $$ %σ₁ [$Hσ]
  imod H with ⟨%Hred, H⟩
  imodintro
  isplitr; · ipureintro; exact Hred
  iintro %e₂ %σ₂ %Hpstep !> !>
  iapply H $$ %e₂ %σ₂ %Hpstep

/-- Pure deterministic step,
countability-free.

The pure family is discrete for a different reason than the sampling rules: not
atoms, but `PureStep_discrete`'s `primStep {⟨e₂,σ⟩} = 1` phrasing. The
measure-theoretic `PureStep` instead gives `primStep ⟨e₁,σ⟩ = dirac ⟨e₂,σ⟩`, so
the carrying set is simply the singleton `{⟨e₂, σ₁⟩}` — measurable, and conull
under a `dirac` with no countability anywhere. -/
theorem wp_lift_pure_det_step_concentrated {E E' : CoPset} {e₁ e₂ : Exp rT}
    {Φ : Val rT → IProp GF} (Hpure : PureStep e₁ e₂) :
    iprop(|={E}[E']▷=> wp E e₂ Φ) ⊢@{IProp GF} wp E e₁ Φ := by
  iintro H
  have Hv : e₁.toVal? = none := by
    rcases htv : e₁.toVal? with _ | v
    · rfl
    · exact absurd (Exp.toVal?_isValue htv) (val_stuck (Hpure.safe default))
  iapply (wp_lift_step_concentrated (S := fun σ₁ => {(⟨e₂, σ₁⟩ : Cfg rT)}) Hv
    (fun σ₁ => by measurability)
    (fun σ₁ => by
      show (primStep ⟨e₁, σ₁⟩) _ = 0
      rw [Hpure.det σ₁, MeasureTheory.Measure.dirac_apply' _ (by measurability)]
      simp))
  iintro %σ₁ Hσ
  imod H
  imod (BIFUpdate.subset (E1 := E') (E2 := ∅) Std.LawfulSet.empty_subset)
    with Hclose
  imodintro
  isplitr; · ipureintro; exact Hpure.safe σ₁
  iintro !> %e₂' %σ₂ %Hmem
  have heq : (⟨e₂', σ₂⟩ : Cfg rT) = ⟨e₂, σ₁⟩ := Hmem
  cases heq
  imod Hclose
  imod H
  imodintro
  iframe Hσ
  iexact H

end ApproxisWpGS

namespace ApproxisWpGS
variable {GF : BundledGFunctors} [ApproxisWpGS (rT := rT) GF]

/-! ### Countability-free pure-step rules

Same three rules on the measure-theoretic `PureStep` / `PureExec` rather than
their `_discrete` counterparts, so they hold for a diffuse `rT`. -/

/-- Single `PureStep`, countability-free. -/
theorem wp_pure_step_one' {E : CoPset} {e₁ e₂ : Exp rT} {Φ : Val rT → IProp GF}
    (Hstep : PureStep e₁ e₂) :
    iprop(▷ wp E e₂ Φ) ⊢@{IProp GF} wp E e₁ Φ := by
  iintro H
  iapply (ApproxisWpGS.wp_lift_pure_det_step_concentrated (E' := E) Hstep)
  imodintro; iintro !>; imodintro; iexact H

/-- `PureExec` step lifting (n-step `step_fupd` form),
countability-free. -/
theorem wp_pure_step_fupd' {E E' : CoPset} {e₁ e₂ : Exp rT} {φ : Prop} {n : Nat}
    {Φ : Val rT → IProp GF}
    [Hex : PureExec φ n e₁ e₂] (Hφ : φ) :
    iprop(|={E}[E']▷=>^[n] wp E e₂ Φ) ⊢@{IProp GF} wp E e₁ Φ := by
  have Hsteps := Hex.pure_exec Hφ
  clear Hex
  induction n generalizing e₁ with
  | zero =>
    simp only [nsteps] at Hsteps
    subst Hsteps
    simp only [Nat.repeat]
    iintro H; iexact H
  | succ n IH =>
    obtain ⟨c, Hstep, Hrest⟩ := Hsteps
    simp only [Nat.repeat]
    iintro H
    iapply (ApproxisWpGS.wp_lift_pure_det_step_concentrated Hstep)
    imod H; imodintro; iintro !>; imod H; imodintro
    iapply (IH Hrest) $$ H

/-- `PureExec` step lifting (n-step `▷` form),
countability-free. -/
theorem wp_pure_step_later' {E : CoPset} {e₁ e₂ : Exp rT} {φ : Prop} {n : Nat}
    {Φ : Val rT → IProp GF}
    [Hex : PureExec φ n e₁ e₂] (Hφ : φ) :
    iprop(▷^[n] wp E e₂ Φ) ⊢@{IProp GF} wp E e₁ Φ := by
  refine BI.Entails.trans ?_ (wp_pure_step_fupd' (E := E) (E' := E)
    (e₁ := e₁) (e₂ := e₂) (n := n) (Hex := Hex) Hφ)
  induction n with
  | zero =>
    exact .rfl
  | succ n ih =>
    refine (BI.later_mono ih).trans ?_
    simp only [Nat.repeat]
    iintro H
    imodintro; iintro !>; imodintro; iexact H

/-! ## (Ectx rT)-lifting lemmas (ports `clutch/theories/approxis/ectx_lifting.v`)

Specialize `Lifting` to head-step semantics using `headStep`/`Discrete.Reducible.of_head`.
-/

/-- Head-step specialization. -/
theorem wp_lift_head_step_prog_couple {E : CoPset} {e₁ : Exp rT} {Φ : Val rT → IProp GF}
    (Hv : e₁.toVal? = none) :
    iprop(∀ (σ₁ : State rT) (e₁' : Exp rT) (σ₁' : State rT) (ε₁ : ENNReal),
      (stateInterp (rT := rT) σ₁ ∗ SpecUpdateGS.specInterp (rT := rT) ⟨e₁', σ₁'⟩ ∗
        errInterp (rT := rT) ε₁) -∗
        |={E, ∅}=> (⌜∃ ρ : Cfg rT, 0 < headStep ⟨e₁, σ₁⟩ {ρ}⌝) ∗
        progCoupl e₁ σ₁ e₁' σ₁' ε₁ (fun e₂ σ₂ e₂' σ₂' ε₂ =>
          iprop(▷ |={∅, E}=>
            stateInterp (rT := rT) σ₂ ∗ SpecUpdateGS.specInterp (rT := rT) ⟨e₂',
              σ₂'⟩ ∗ errInterp (rT := rT) ε₂ ∗
              wp E e₂ Φ))) ⊢@{IProp GF}
      wp E e₁ Φ := by
  iintro H
  iapply wp_lift_step_prog_couple Hv
  iintro %σ₁ %e₁' %σ₁' %ε₁ ⟨Hσ, Hs, Hε⟩
  ispecialize H $$ %σ₁ %e₁' %σ₁' %ε₁ [$Hσ $Hs $Hε]
  imod H with ⟨%_Hhred, H⟩
  imodintro
  iexact H

/-- Atomic head-step without mask shift. -/
@[discrete]
theorem wp_lift_atomic_head_step {E : CoPset} {e₁ : Exp rT} {Φ : Val rT → IProp GF}
    (Hv : e₁.toVal? = none)
    (Hlc : e₁.IsLocallyClosed := by is_lc)
    (hne : e₁.decomp.2 ≠ .urand := by no_urand) :
    iprop(∀ (σ₁ : State rT), stateInterp (rT := rT) σ₁ -∗ |={E}=>
      (⌜∃ ρ : Cfg rT, 0 < headStep ⟨e₁, σ₁⟩ {ρ}⌝) ∗
      ▷ ∀ (e₂ : Exp rT) (σ₂ : State rT),
        (⌜0 < headStep ⟨e₁, σ₁⟩ {⟨e₂, σ₂⟩}⌝) -∗ |={E}=>
          stateInterp (rT := rT) σ₂ ∗
          (match e₂.toVal? with | some v => Φ v | none => iprop(False))) ⊢@{IProp GF}
      wp E e₁ Φ := by
  iintro H
  iapply wp_lift_atomic_step Hv hne
  iintro %σ₁ Hσ
  ispecialize H $$ %σ₁ [$Hσ]
  imod H with ⟨%Hhred, H⟩
  imodintro
  have Hhr : HeadReducible e₁ σ₁ :=
    let ⟨ρ, hρ⟩ := Hhred; fun hz => by rw [hz] at hρ; simp at hρ
  isplitr; · ipureintro; exact Reducible.toDiscrete hne (reducible_of_headReducible Hlc Hhr)
  iintro !> %e₂ %σ₂ %Hpstep
  have hpos : 0 < headStep ⟨e₁, σ₁⟩ {⟨e₂, σ₂⟩} :=
    primStep_eq_headStep (Exp.decompItem_none_of_lc_headReducible Hlc Hhr) ▸ Hpstep
  iapply H $$ %e₂ %σ₂ %hpos

/-! ### Countability-free head-step rules

The head-step rules gate on `headStep` rather than `primStep`. Head-reducibility
is established *inside* the assertion (from the state interpretation), so the
carrying set cannot simply be required to carry `primStep` at every `σ₁` — at a
state where `e₁` is not head-reducible the redex may sit under a context and
`primStep` moves elsewhere. The trick is to pad the carrying set to `Set.univ`
off the head-reducible states, where concentration is free. -/

open scoped Classical in
omit [ApproxisWpGS (rT := rT) GF] in
/-- The padded carrying set is measurable. -/
theorem measurableSet_headPad {e₁ : Exp rT} {S : State rT → Set (Cfg rT)}
    (hSmeas : ∀ σ₁, MeasurableSet (S σ₁)) (σ₁ : State rT) :
    MeasurableSet (if HeadReducible e₁ σ₁ then S σ₁ else Set.univ) := by
  split_ifs; exacts [hSmeas σ₁, MeasurableSet.univ]

open scoped Classical in
omit [ApproxisWpGS (rT := rT) GF] in
/-- The padded carrying set carries `primStep`: on head-reducible states `primStep` is
`headStep`, and elsewhere the set is `Set.univ`. -/
theorem concentrated_headPad {e₁ : Exp rT} {S : State rT → Set (Cfg rT)}
    (Hlc : e₁.IsLocallyClosed)
    (hSconc : ∀ σ₁, HeadReducible e₁ σ₁ → Concentrated (headStep ⟨e₁, σ₁⟩) (S σ₁))
    (σ₁ : State rT) :
    Concentrated (primStep ⟨e₁, σ₁⟩) (if HeadReducible e₁ σ₁ then S σ₁ else Set.univ) := by
  split_ifs with hhr
  · rw [primStep_eq_headStep (Exp.decompItem_none_of_lc_headReducible Hlc hhr)]
    exact hSconc σ₁ hhr
  · exact Concentrated.univ

open scoped Classical in
/-- Countability-free `wp_lift_head_step`. -/
theorem wp_lift_head_step_concentrated {E : CoPset} {e₁ : Exp rT} {Φ : Val rT → IProp GF}
    {S : State rT → Set (Cfg rT)} (Hv : e₁.toVal? = none)
    (Hlc : e₁.IsLocallyClosed := by is_lc)
    (hSmeas : ∀ σ₁, MeasurableSet (S σ₁))
    (hSconc : ∀ σ₁, HeadReducible e₁ σ₁ → Concentrated (headStep ⟨e₁, σ₁⟩) (S σ₁)) :
    iprop(∀ (σ₁ : State rT), stateInterp (rT := rT) σ₁ -∗ |={E, ∅}=>
      (⌜HeadReducible e₁ σ₁⌝) ∗
      ▷ ∀ (e₂ : Exp rT) (σ₂ : State rT),
        (⌜(⟨e₂, σ₂⟩ : Cfg rT) ∈ S σ₁⌝) -∗ |={∅, E}=>
          stateInterp (rT := rT) σ₂ ∗ wp E e₂ Φ) ⊢@{IProp GF}
      wp E e₁ Φ := by
  iintro H
  iapply (wp_lift_step_concentrated
    (S := fun σ₁ => if HeadReducible e₁ σ₁ then S σ₁ else Set.univ) Hv
    (measurableSet_headPad hSmeas) (concentrated_headPad Hlc hSconc))
  iintro %σ₁ Hσ
  ispecialize H $$ %σ₁ [$Hσ]
  imod H with ⟨%Hhred, H⟩
  imodintro
  isplitr; · ipureintro; exact reducible_of_headReducible Hlc Hhred
  iintro !> %e₂ %σ₂ %Hmem
  rw [if_pos Hhred] at Hmem
  iapply H $$ %e₂ %σ₂ %Hmem

open scoped Classical in
/-- Countability-free
`wp_lift_atomic_head_step_fupd`. -/
theorem wp_lift_atomic_head_step_fupd_concentrated {E1 E2 : CoPset} {e₁ : Exp rT}
    {Φ : Val rT → IProp GF} {S : State rT → Set (Cfg rT)} (Hv : e₁.toVal? = none)
    (Hlc : e₁.IsLocallyClosed := by is_lc)
    (hSmeas : ∀ σ₁, MeasurableSet (S σ₁))
    (hSconc : ∀ σ₁, HeadReducible e₁ σ₁ → Concentrated (headStep ⟨e₁, σ₁⟩) (S σ₁)) :
    iprop(∀ (σ₁ : State rT), stateInterp (rT := rT) σ₁ -∗ |={E1}=>
      (⌜HeadReducible e₁ σ₁⌝) ∗
      ∀ (e₂ : Exp rT) (σ₂ : State rT),
        (⌜(⟨e₂, σ₂⟩ : Cfg rT) ∈ S σ₁⌝) -∗ |={E1}[E2]▷=>
          stateInterp (rT := rT) σ₂ ∗
          (match e₂.toVal? with | some v => Φ v | none => iprop(False))) ⊢@{IProp GF}
      wp E1 e₁ Φ := by
  iintro H
  iapply (wp_lift_atomic_step_fupd_concentrated
    (S := fun σ₁ => if HeadReducible e₁ σ₁ then S σ₁ else Set.univ) Hv
    (measurableSet_headPad hSmeas) (concentrated_headPad Hlc hSconc))
  iintro %σ₁ Hσ
  ispecialize H $$ %σ₁ [$Hσ]
  imod H with ⟨%Hhred, H⟩
  imodintro
  isplitr; · ipureintro; exact reducible_of_headReducible Hlc Hhred
  iintro %e₂ %σ₂ %Hmem
  rw [if_pos Hhred] at Hmem
  iapply H $$ %e₂ %σ₂ %Hmem

open scoped Classical in
/-- Countability-free
`wp_lift_atomic_head_step`. -/
theorem wp_lift_atomic_head_step_concentrated {E : CoPset} {e₁ : Exp rT}
    {Φ : Val rT → IProp GF} {S : State rT → Set (Cfg rT)} (Hv : e₁.toVal? = none)
    (Hlc : e₁.IsLocallyClosed := by is_lc)
    (hSmeas : ∀ σ₁, MeasurableSet (S σ₁))
    (hSconc : ∀ σ₁, HeadReducible e₁ σ₁ → Concentrated (headStep ⟨e₁, σ₁⟩) (S σ₁)) :
    iprop(∀ (σ₁ : State rT), stateInterp (rT := rT) σ₁ -∗ |={E}=>
      (⌜HeadReducible e₁ σ₁⌝) ∗
      ▷ ∀ (e₂ : Exp rT) (σ₂ : State rT),
        (⌜(⟨e₂, σ₂⟩ : Cfg rT) ∈ S σ₁⌝) -∗ |={E}=>
          stateInterp (rT := rT) σ₂ ∗
          (match e₂.toVal? with | some v => Φ v | none => iprop(False))) ⊢@{IProp GF}
      wp E e₁ Φ := by
  iintro H
  iapply (wp_lift_atomic_head_step_fupd_concentrated (E2 := E) Hv Hlc hSmeas hSconc)
  iintro %σ₁ Hσ
  ispecialize H $$ %σ₁ [$Hσ]
  imod H with ⟨%Hhred, H⟩
  imodintro
  isplitr; · ipureintro; exact Hhred
  iintro %e₂ %σ₂ %Hmem !> !>
  iapply H $$ %e₂ %σ₂ %Hmem

-- DISCRETE: `wp_lift_pure_det_head_step (_Hv : e₁.toVal? = none) (Hlc : e₁.IsLocallyClosed)`
--   `(Hsafe : ∀ σ₁, ∃ ρ, 0 < headStep ⟨e₁, σ₁⟩ {ρ})`
--   `(Hdet : ∀ σ₁ e₂' σ₂, 0 < headStep ⟨e₁, σ₁⟩ {⟨e₂', σ₂⟩} → σ₂ = σ₁ ∧ e₂' = e₂) :`
--   `(|={E}[E']▷=> wp E e₂ Φ) ⊢ wp E e₁ Φ`

-- DISCRETE: `wp_lift_pure_det_head_step'` — same hypotheses, `▷`-form:
--   `(▷ wp E e₂ Φ) ⊢ wp E e₁ Φ`

end ApproxisWpGS

end ProbLang
