module

public import Metrology.Iris.SpecUpdate
public import Metrology.Iris.ErrorCredits
public import Metrology.Iris.Fixpoint
public import Metrology.Couplings.AdditiveCouplings
public import Metrology.Couplings.Couplings
public import Metrology.ProbLang.Exec
public import Metrology.ProbLang.Erasable
public import Iris.BI.Lib.Fixpoint
public import Iris.ProofMode.Classes
public import Iris.ProofMode.InstancesUpdates

@[expose] public section

open Std Iris Iris.Std Iris.BI Iris.ProofMode OFE COFE ProbLang

namespace ProbLang

-- For the Approxis layer, carry the abstract real type `rT` as a section variable.


variable {rT : Type _} [ProbLang.ProbLangℝ rT] [Countable rT] [MeasurableSingletonClass rT]


/-! ## Approxis ghost state class -/

/-- Resources required by the Approxis weakest precondition: the spec-side
update modality, the invariant ghost state, a state interpretation, and an
error-credit interpretation. -/
class ApproxisWpGS {rT : Type _} [ProbLangℝ rT] [Countable rT] [MeasurableSingletonClass rT]
    (GF : BundledGFunctors) extends SpecUpdateGS rT GF where
  hlc : Bool
  invGS : InvGS_gen hlc GF
  stateInterp : (State rT) → IProp GF
  errInterp : ENNReal → IProp GF

attribute [reducible, instance] ApproxisWpGS.invGS

namespace ApproxisWpGS
variable {GF : BundledGFunctors} [ApproxisWpGS (rT := rT) GF]

/-! `spec_coupl` modality

Lets us optionally prepend spec-side execution steps and erasable
distributions on both sides before establishing the body `Z`. -/

/-- The packaged state for `spec_coupl`'s fixpoint: `(σ, (e', σ'), ε)` collapsed
into a single tuple so we can write a `BIMonoPred` over it. -/
abbrev SpecCouplState (rT : Type _) [ProbLangℝ rT] [Countable rT] [MeasurableSingletonClass rT] :
    Type _ := (State rT) × (Cfg rT) × ENNReal

instance : COFE (SpecCouplState rT) := COFE.ofDiscrete _ Eq_Equivalence
instance : OFE.Discrete (SpecCouplState rT) := ⟨id⟩
instance : OFE.Leibniz (SpecCouplState rT) := ⟨id⟩

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
    (σ₁ : (State rT)) (e₁' : (Exp rT)) (σ₁' : (State rT)) (ε : ENNReal)
    (Φ : SpecCouplState rT → IProp GF) : IProp GF :=
  iprop(∃ (S : (State rT) → (Cfg rT) → Prop) (n : Nat)
          (μ₁ : MeasureTheory.Measure (State rT)) (μ₁' : MeasureTheory.Measure (State rT))
          (ε₁ : ENNReal) (X₂ : (Cfg rT) → ENNReal) (r : ENNReal),
    (⌜AddCoupl ε₁ {p : (State rT) × (Cfg rT) | S p.1 p.2} μ₁ (μ₁'.bind (fun σ => pexecN n ⟨e₁', σ⟩))⌝) ∗
    (⌜∀ ρ, X₂ ρ ≤ r⌝) ∗
    (⌜ε₁ + (∫⁻ ρ, X₂ ρ ∂(μ₁'.bind (fun σ => pexecN n ⟨e₁', σ⟩))) ≤ ε⌝) ∗
    (⌜Erasable μ₁ σ₁⌝) ∗
    (⌜Erasable μ₁' σ₁'⌝) ∗
    (∀ (σ₂ : (State rT)) (e₂' : (Exp rT)) (σ₂' : (State rT)),
      (⌜S σ₂ ⟨e₂', σ₂'⟩⌝) -∗ |={E}=> Φ ((σ₂, (⟨e₂', σ₂'⟩ : (Cfg rT)), X₂ ⟨e₂', σ₂'⟩) : SpecCouplState rT)))

/-- The pre-functor whose least fixpoint is `specCoupl`.

⚠️ **Must be `abbrev`, not `def`** — the `BIMonoPred` and `specCoupl_mono`
proofs rely on `iexact` seeing through to the body when the `Φ` argument
varies. Demoting this to `def` will break those proofs with
`iexact: cannot unify specCouplPre E Z Φ s and specCouplPre E Z Ψ s`. -/
abbrev specCouplPre (E : CoPset) (Z : (State rT) → (Cfg rT) → ENNReal → IProp GF)
    (Φ : SpecCouplState rT → IProp GF) : SpecCouplState rT → IProp GF :=
  fun ⟨σ₁, ⟨e₁', σ₁'⟩, ε⟩ => iprop%
    ⌜1 ≤ ε⌝ ∨
    Z σ₁ ⟨e₁', σ₁'⟩ ε ∨
    specCouplCouple E σ₁ e₁' σ₁' ε Φ

abbrev specCoupl (E : CoPset) (σ : (State rT)) (e' : (Exp rT)) (σ' : (State rT)) (ε : ENNReal)
    (Z : (State rT) → (Cfg rT) → ENNReal → IProp GF) : IProp GF :=
  bi_least_fixpoint (specCouplPre (GF := GF) E Z)
    ((σ, (⟨e', σ'⟩ : (Cfg rT)), ε) : SpecCouplState rT)

macro "spec_trivial_left" : tactic => `(tactic| (isplitr; · ipure_intro; trivial))
macro "spec_trivial_cases" : tactic => `(tactic| repeat spec_trivial_left)

/-- `specCouplPre` is monotone in its `Φ` argument.

The placeholder body `⌜1 ≤ ε⌝ ∨ Z σ ρ' ε` doesn't actually use `Φ`, so
monotonicity is trivial. (Once the third coupling-disjunct is restored, the
quantifier-under-fupd case will appeal to `Hwand`.) -/
instance specCouplPre_mono {E : CoPset} {Z : (State rT) → (Cfg rT) → ENNReal → IProp GF} :
    BIMonoPred (specCouplPre (GF := GF) E Z) where
  mono_pred {Φ Ψ _ _} := by
    iintro #Hwand %s Hs
    icases Hs with ⟨HVac | HZ | HCpl⟩
    · ileft; iexact HVac
    · iright; ileft; iexact HZ
    · iright; iright
      icases HCpl with ⟨%S, %n, %μ₁, %μ₁', %ε₁, %X₂, %r, %Hc, %Hb, %Hexp, %Herase₁, %Herase₂, Hcont⟩
      iexists S, n, μ₁, μ₁', ε₁, X₂, r
      spec_trivial_cases
      iintro %σ₂ %e₂' %σ₂' %HS
      imod Hcont $$ %σ₂ %e₂' %σ₂' %HS with HΦ
      imodintro
      iapply Hwand
      iexact HΦ
  mono_pred_ne.ne {_ s s'} hd := by
    have : s = s' := OFE.Leibniz.eq_of_eqv (OFE.Discrete.discrete_0 hd)
    subst this; exact .of_eq rfl

/-- Trivial introduction: if `1 ≤ ε`, the coupling holds vacuously. -/
theorem specCoupl_err_ge_1 {E : CoPset} {σ : (State rT)} {e' : (Exp rT)} {σ' : (State rT)} {ε : ENNReal}
    {Z : (State rT) → (Cfg rT) → ENNReal → IProp GF} (hε : 1 ≤ ε) : ⊢ specCoupl E σ e' σ' ε Z := by
  iapply least_fixpoint_unfold_2 (specCouplPre E Z)
  ileft
  ipure_intro
  exact hε

/-- `Z`-introduction: from the body `Z`, conclude the coupling. -/
theorem specCoupl_ret {E : CoPset} {σ : (State rT)} {e' : (Exp rT)} {σ' : (State rT)}
    {ε : ENNReal} {Z : (State rT) → (Cfg rT) → ENNReal → IProp GF} :
    Z σ ⟨e', σ'⟩ ε ⊢@{IProp GF} specCoupl E σ e' σ' ε Z := by
  iintro HZ
  iapply least_fixpoint_unfold_2 (specCouplPre E Z)
  iright
  ileft
  iexact HZ

/-- Coupling-case introduction: if there's an erasable-distribution coupling that
sequences into a continuation eventually establishing the body, then the
modality holds.

The continuation argument is given against `specCoupl` itself (corecursive
shape), matching Rocq's `spec_coupl_rec`. -/
theorem specCoupl_rec {E : CoPset} {σ : (State rT)} {e' : (Exp rT)} {σ' : (State rT)}
    {ε : ENNReal} {Z : (State rT) → (Cfg rT) → ENNReal → IProp GF} :
    specCouplCouple E σ e' σ' ε
        (fun s => specCoupl E s.1 s.2.1.expr s.2.1.state s.2.2 Z)
      ⊢@{IProp GF} specCoupl E σ e' σ' ε Z := by
  iintro HCpl
  unfold specCoupl
  iapply (least_fixpoint_unfold_2 (specCouplPre E Z))
  unfold specCouplPre
  iright
  iright
  iexact HCpl

/-- Unfolding equation for `specCoupl`: it equals one application of the
pre-functor at the fixpoint. -/
theorem specCoupl_unfold {E : CoPset} {σ : (State rT)} {e' : (Exp rT)} {σ' : (State rT)}
    {ε : ENNReal} {Z : (State rT) → (Cfg rT) → ENNReal → IProp GF} :
    specCoupl (GF := GF) E σ e' σ' ε Z ≡
      specCouplPre (GF := GF) E Z
        (fun s => specCoupl E s.1 s.2.1.expr s.2.1.state s.2.2 Z)
        ((σ, (⟨e', σ'⟩ : (Cfg rT)), ε) : SpecCouplState rT) :=
  least_fixpoint_unfold _

/-- Strong monotonicity of `specCoupl`: a *persistent* continuation entailment
lifts through the modality.

The continuation hypothesis is required to be intuitionistic (`□`) because we
need it inside the fixpoint induction, which works under a `□`-modality. -/
theorem specCoupl_mono {E : CoPset} {σ : (State rT)} {e' : (Exp rT)} {σ' : (State rT)}
    {ε : ENNReal} {Z₁ Z₂ : (State rT) → (Cfg rT) → ENNReal → IProp GF} :
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
      %HCpl_coupl, %HCpl_bnd, %HCpl_exp, %HCpl_e1, %HCpl_e2, HCpl_cont⟩
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
theorem specCoupl_bind {E1 E2 : CoPset} {σ : (State rT)} {e' : (Exp rT)} {σ' : (State rT)}
    {ε : ENNReal} {Z₁ Z₂ : (State rT) → (Cfg rT) → ENNReal → IProp GF}
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
  have HΦne : NonExpansive Φ := by
    constructor
    intro _ s s' hd
    have heq : s = s' := OFE.Leibniz.eq_of_eqv (OFE.Discrete.discrete_0 hd)
    subst heq; exact .of_eq rfl
  -- Apply iter; the resulting `Φ s` is `HZty -∗ specCoupl E2 s.1 ... Z₂`,
  -- which we close by feeding HZ.
  ihave Hiter := least_fixpoint_iter (F := specCouplPre E1 Z₁) (Φ := Φ)
    $$ [] %((σ, (⟨e', σ'⟩ : (Cfg rT)), ε) : SpecCouplState rT) HC
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
      %HCpl_coupl, %HCpl_bnd, %HCpl_exp, %HCpl_e1, %HCpl_e2, HCpl_cont⟩
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
    iapply HCpl_cont
    iexact HZ

/-- Spatial-continuation mono for `specCoupl`, derived from `specCoupl_bind` +
`specCoupl_ret`. -/
theorem specCoupl_mono_spatial {E : CoPset} {σ : (State rT)} {e' : (Exp rT)} {σ' : (State rT)}
    {ε : ENNReal} {Z₁ Z₂ : (State rT) → (Cfg rT) → ENNReal → IProp GF} :
    iprop((∀ σ' ρ' ε', Z₁ σ' ρ' ε' -∗ Z₂ σ' ρ' ε') ∗
        specCoupl E σ e' σ' ε Z₁) ⊢@{IProp GF}
      specCoupl E σ e' σ' ε Z₂ := by
  iintro ⟨HZ, HC⟩
  iapply specCoupl_bind (E1 := E) (E2 := E) Std.LawfulSet.subset_refl
  isplitr [HC]
  swap
  · iexact HC
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
abbrev progCoupl (e₁ : (Exp rT)) (σ₁ : (State rT)) (e₁' : (Exp rT)) (σ₁' : (State rT)) (ε : ENNReal)
    (Z : (Exp rT) → (State rT) → (Exp rT) → (State rT) → ENNReal → IProp GF) : IProp GF :=
  iprop(∃ (n : Nat) (μ₁' : MeasureTheory.Measure (State rT))
          (X₂ : (Cfg rT) → (Cfg rT) → ENNReal),
    (⌜Reducible e₁ σ₁⌝) ∗
    (⌜∃ r : ENNReal, ∀ ρ₁ ρ₂, X₂ ρ₁ ρ₂ ≤ r⌝) ∗
    (⌜∀ (h₁ h₂ : (Cfg rT) → ENNReal),
        (∀ a, h₁ a ≤ 1) → (∀ b, h₂ b ≤ 1) →
        (∀ a b, h₁ a ≤ h₂ b + X₂ a b) →
        (∫⁻ a, h₁ a ∂(primStep ⟨e₁, σ₁⟩)) ≤
          (∫⁻ b, h₂ b ∂(μ₁'.bind (fun σ => pexecN n ⟨e₁', σ⟩))) + ε⌝) ∗
    (⌜Erasable μ₁' σ₁'⌝) ∗
    (∀ (e₂ : (Exp rT)) (σ₂ : (State rT)) (e₂' : (Exp rT)) (σ₂' : (State rT)),
      |={∅}=> Z e₂ σ₂ e₂' σ₂' (X₂ ⟨e₂, σ₂⟩ ⟨e₂', σ₂'⟩)))

/-- Outer non-expansiveness of `specCoupl` in its body `Z` at a single
distance `n`. The fixed-`n` form is what we need for the structural walk in
`wpPre_contractive`. -/
theorem specCoupl_ne {n : Nat} {E : CoPset} {σ : (State rT)} {e' : (Exp rT)} {σ' : (State rT)}
    {ε : ENNReal} {Z₁ Z₂ : (State rT) → (Cfg rT) → ENNReal → IProp GF}
    (HZ : ∀ σ ρ ε, Z₁ σ ρ ε ≡{n}≡ Z₂ σ ρ ε) :
    specCoupl E σ e' σ' ε Z₁ ≡{n}≡ specCoupl E σ e' σ' ε Z₂ := by
  unfold specCoupl
  refine least_fixpoint_ne_outer (fun Ψ s => ?_) (.of_eq rfl)
  refine or_ne.ne (.of_eq rfl) ?_
  refine or_ne.ne (HZ s.1 s.2.1 s.2.2) ?_
  exact .of_eq rfl

/-- Outer non-expansiveness of `progCoupl` in its continuation `Z`. -/
theorem progCoupl_ne {n : Nat} {e₁ : (Exp rT)} {σ₁ : (State rT)} {e₁' : (Exp rT)} {σ₁' : (State rT)}
    {ε : ENNReal} {Z₁ Z₂ : (Exp rT) → (State rT) → (Exp rT) → (State rT) → ENNReal → IProp GF}
    (HZ : ∀ e₂ σ₂ e₂' σ₂' ε', Z₁ e₂ σ₂ e₂' σ₂' ε' ≡{n}≡ Z₂ e₂ σ₂ e₂' σ₂' ε') :
    progCoupl e₁ σ₁ e₁' σ₁' ε Z₁ ≡{n}≡ progCoupl e₁ σ₁ e₁' σ₁' ε Z₂ := by
  refine exists_ne fun n' => ?_
  refine exists_ne fun μ₁' => ?_
  refine exists_ne fun X₂ => ?_
  refine sep_ne.ne (.of_eq rfl) ?_  -- Reducible : Prop
  refine sep_ne.ne (.of_eq rfl) ?_  -- ∃ r, bound : Prop
  refine sep_ne.ne (.of_eq rfl) ?_  -- expectation bound : Prop
  refine sep_ne.ne (.of_eq rfl) ?_  -- Erasable : Prop
  refine forall_ne fun e₂ => ?_
  refine forall_ne fun σ₂ => ?_
  refine forall_ne fun e₂' => ?_
  refine forall_ne fun σ₂' => ?_
  exact BIFUpdate.ne.ne (HZ _ _ _ _ _)

/-- Monotonicity of `progCoupl` under a continuation rewrite. -/
theorem progCoupl_mono {e₁ : (Exp rT)} {σ₁ : (State rT)} {e₁' : (Exp rT)} {σ₁' : (State rT)}
    {ε : ENNReal} {Z₁ Z₂ : (Exp rT) → (State rT) → (Exp rT) → (State rT) → ENNReal → IProp GF} :
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
    (wp : CoPset → (Exp rT) → ((Val rT) → IProp GF) → IProp GF)
    (E : CoPset) (e₁ : (Exp rT)) (Φ : (Val rT) → IProp GF) : IProp GF :=
  iprop(∀ (σ₁ : (State rT)) (e₁' : (Exp rT)) (σ₁' : (State rT)) (ε₁ : ENNReal),
    (stateInterp (rT := rT) σ₁ ∗ SpecUpdateGS.specInterp (rT := rT) ⟨e₁', σ₁'⟩ ∗ errInterp (rT := rT) ε₁) -∗
      |={E, ∅}=> specCoupl ∅ σ₁ e₁' σ₁' ε₁ (fun σ₂ ρ' ε₂ =>
        match e₁.toVal? with
        | some v => iprop(|={∅, E}=>
            stateInterp (rT := rT) σ₂ ∗ SpecUpdateGS.specInterp (rT := rT) ρ' ∗ errInterp (rT := rT) ε₂ ∗ Φ v)
        | none => progCoupl e₁ σ₂ ρ'.expr ρ'.state ε₂ (fun e₃ σ₃ e₃' σ₃' ε₃ =>
            iprop(▷ specCoupl ∅ σ₃ e₃' σ₃' ε₃ (fun σ₄ ρ'' ε₄ =>
              iprop(|={∅, E}=>
                stateInterp (rT := rT) σ₄ ∗ SpecUpdateGS.specInterp (rT := rT) ρ'' ∗ errInterp (rT := rT) ε₄ ∗
                  wp E e₃ Φ))))))

/-- The function space `CoPset → (Exp rT) → ((Val rT) → IProp GF) → IProp GF`, packaged as
the type the fixpoint operates over. -/
abbrev WpType := CoPset → (Exp rT) → ((Val rT) → IProp GF) → IProp GF

/-- `wpPre` is `Contractive` in its first argument: the only recursive use of
the `wp` parameter inside the body sits under a `▷` (`later`) modality, so a
`distLater n`-related pair of `wp` arguments produces `dist n`-related bodies.

The structural walk mirrors the body of `wpPre`: forall, wand, fupd, fixpoint
unfold for `specCoupl`, the `match` on `e₁.toVal?`, the `progCoupl` body, and
the inner `▷ specCoupl` where the `▷` justifies the contractive step. -/
instance wpPre_contractive : Contractive (wpPre (rT := rT) (GF := GF)) where
  distLater_dist := by
    intro n wp wp' Hwp E e₁ Φ
    refine forall_ne fun σ₁ => ?_
    refine forall_ne fun e₁' => ?_
    refine forall_ne fun σ₁' => ?_
    refine forall_ne fun ε₁ => ?_
    refine wand_ne.ne (.of_eq rfl) ?_
    refine BIFUpdate.ne.ne ?_
    refine least_fixpoint_ne_outer (fun Ψ s => ?_) (.of_eq rfl)
    refine or_ne.ne (.of_eq rfl) ?_
    refine or_ne.ne ?_ (.of_eq rfl)
    cases htv : e₁.toVal? with
    | some v => exact .of_eq rfl
    | none =>
      refine progCoupl_ne fun e₃ σ₃ e₃' σ₃' ε₃ => ?_
      apply Contractive.distLater_dist (f := later)
      intro m Hm
      refine specCoupl_ne fun σ₄ ρ'' ε₄ => ?_
      refine BIFUpdate.ne.ne ?_
      refine sep_ne.ne (.of_eq rfl) ?_
      refine sep_ne.ne (.of_eq rfl) ?_
      refine sep_ne.ne (.of_eq rfl) ?_
      exact DistLater.dist_lt (Hwp · · E e₃ Φ) Hm

/-- The Approxis weakest precondition. -/
noncomputable def wp (E : CoPset) (e : (Exp rT)) (Φ : (Val rT) → IProp GF) : IProp GF :=
  fixpoint (wpPre (rT := rT) (GF := GF)) E e Φ

/-- Fixpoint unfolding for `wp`. Pointwise consequence of `OFE.fixpoint_unfold`
applied to `wpPre`. -/
theorem wp_unfold {E : CoPset} {e : (Exp rT)} {Φ : (Val rT) → IProp GF} :
    wp (GF := GF) E e Φ ≡ wpPre (wp (GF := GF)) E e Φ :=
  (fixpoint_unfold ⟨wpPre, OFE.ne_of_contractive _⟩) E e Φ

/-! ## WP structural lemmas -/

/-- Value introduction (fupd-flavored): `|={E}=> Φ v` proves
`wp E (Exp.ofVal v) Φ`. -/
theorem wp_value_fupd {E : CoPset} {v : (Val rT)} {Φ : (Val rT) → IProp GF} :
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
  isplitl [Hσ]; · iassumption
  isplitl [Hs]; · iassumption
  isplitl [Hε]; · iassumption
  iassumption

/-- Plain value introduction: `Φ v ⊢ wp E (Exp.ofVal v) Φ`. -/
theorem wp_value {E : CoPset} {v : (Val rT)} {Φ : (Val rT) → IProp GF} :
    Φ v ⊢@{IProp GF} wp E (Exp.ofVal v) Φ := by
  iintro HΦ
  iapply wp_value_fupd
  imodintro
  iexact HΦ

/-- General value form: from any expression `e` that is a value (`e.toVal? = some v`),
introduce `wp E e Φ` from `Φ v`. -/
theorem wp_value_of_toVal {E : CoPset} {e : (Exp rT)} {v : (Val rT)} {Φ : (Val rT) → IProp GF}
    (h : e.toVal? = some v) :
    Φ v ⊢@{IProp GF} wp E e Φ := by
  rw [← Exp.ofVal_of_toVal_some h]
  exact wp_value

/-- The post-condition transformer `HΦ` packaged for `wp_strong_mono'`. -/
abbrev wpStrongMonoCont (E2 : CoPset) (Φ Ψ : (Val rT) → IProp GF) : IProp GF :=
  iprop(□ ∀ σ ρ v ε,
    (stateInterp (rT := rT) σ ∗ SpecUpdateGS.specInterp (rT := rT) ρ ∗ errInterp (rT := rT) ε ∗ Φ v) ={E2}=∗
      stateInterp (rT := rT) σ ∗ SpecUpdateGS.specInterp (rT := rT) ρ ∗ errInterp (rT := rT) ε ∗ Ψ v)

/-- The Löb invariant for `wp_strong_mono'`: a single iprop universally
quantified over all the relevant parameters, suitable for `loeb_wand`. -/
noncomputable abbrev wpStrongMonoStmt : IProp GF :=
  iprop(∀ (E1 E2 : CoPset) (e : (Exp rT)) (Φ Ψ : (Val rT) → IProp GF),
    ⌜E1 ⊆ E2⌝ -∗
    wp E1 e Φ -∗ wpStrongMonoCont E2 Φ Ψ -∗ wp E2 e Ψ)

/-- Strong monotonicity of `wp` (Löb-induction-based variant matching Rocq's
`wp_strong_mono'`). -/
theorem wp_strong_mono' {E1 E2 : CoPset} {e : (Exp rT)} {Φ Ψ : (Val rT) → IProp GF}
    (HE : E1 ⊆ E2) :
    iprop(wp E1 e Φ ∗ wpStrongMonoCont E2 Φ Ψ) ⊢@{IProp GF} wp E2 e Ψ := by
  iintro ⟨HW, HΦ⟩
  have Hloeb : ⊢@{IProp GF} wpStrongMonoStmt (rT := rT) := by
    iapply loeb_wand
    iintro !>
    iintro IH
    iintro %E1' %E2' %e' %Φ' %Ψ' %HE' HW' #HΦ'
    iapply wp_unfold
    ihave HW' := (BI.equiv_iff.mp wp_unfold).1 $$ HW'
    iintro %σ₁ %e₁' %σ₁' %ε₁ ⟨Hσ, Hs, Hε⟩
    imod (BIFUpdate.subset HE') with Hclose
    ispecialize HW' $$ %σ₁ %e₁' %σ₁' %ε₁ [Hσ Hs Hε]
    · isplitl [Hσ]; · iassumption
      isplitl [Hs] <;> iassumption
    imod HW' with HW'
    imodintro
    iapply specCoupl_bind (E1 := ∅) (E2 := ∅) Std.LawfulSet.subset_refl
    isplitr [HW']
    swap
    · iexact HW'
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
      isplitr [HZ₁]
      swap
      · iexact HZ₁
      iintro %e₃ %σ₃ %e₃' %σ₃' %ε₃ HCont
      iintro !>
      iapply specCoupl_mono_spatial
      isplitr [HCont]
      swap
      · iexact HCont
      iintro %σ₄ %ρ₄ %ε₄ HInner
      imod HInner with ⟨Hσ', Hs', Hε', HwpInner⟩
      imod Hclose
      imodintro
      iframe
      iapply IH $$ %E1' %E2' %e₃ %Φ' %Ψ' %HE' HwpInner
      iexact HΦ'
  iapply Hloeb $$ %E1 %E2 %e %Φ %Ψ %HE HW HΦ

theorem wp_wand {E : CoPset} {e : (Exp rT)} {Φ Ψ : (Val rT) → IProp GF} :
    iprop(wp E e Φ ∗ □ (∀ v, Φ v -∗ Ψ v)) ⊢@{IProp GF} wp E e Ψ := by
  iintro ⟨HW, #HΦ⟩
  iapply wp_strong_mono' (E1 := E) (E2 := E) (Φ := Φ) (Ψ := Ψ) Std.LawfulSet.subset_refl
  isplitl [HW]; · iassumption
  iintro !> %σ %ρ %v %ε ⟨Hσ, Hs, Hε, HΦv⟩
  imodintro
  iframe
  iapply HΦ $$ [$]

/-- Inside fancy-update absorption: if the post is `|={E}=> Φ v`, we can collapse it. -/
theorem wp_fupd {E : CoPset} {e : (Exp rT)} {Φ : (Val rT) → IProp GF} :
    wp E e (fun v => iprop(|={E}=> Φ v)) ⊢@{IProp GF} wp E e Φ := by
  iintro HW
  iapply wp_strong_mono' (E1 := E) (E2 := E) Std.LawfulSet.subset_refl
  isplitl [HW]; · iassumption
  iintro !> %σ %ρ %v %ε ⟨Hσ, Hs, Hε, HΦ⟩
  imod HΦ
  iframe

/-- Fancy-update absorbs into `wp` from outside. -/
theorem fupd_wp {E : CoPset} {e : (Exp rT)} {Φ : (Val rT) → IProp GF} :
    iprop(|={E}=> wp E e Φ) ⊢@{IProp GF} wp E e Φ := by
  iintro HF
  iapply wp_unfold
  unfold wpPre
  iintro %σ₁ %e₁' %σ₁' %ε₁ Hres
  -- Consume the outer fupd, getting `wp E e Φ`.
  imod HF with HW
  -- HW : wp E e Φ. Use the BI bidirectional implication from wp_unfold.
  ihave HW' := (BI.equiv_iff.mp wp_unfold).1 $$ HW
  -- HW' has type `wpPre wp E e Φ`, which is an `abbrev` reducing to a forall-wand.
  ispecialize HW' $$ %σ₁ %e₁' %σ₁' %ε₁ Hres
  iexact HW'

/-! ## Easy derived WP lemmas

All of these derive from `wp_strong_mono'` / `wp_wand` and the existing
`specCoupl`/`progCoupl` primitives. -/

/-- Strong monotonicity of `wp` with an intuitionistic continuation wand (the
`□`-variant of `wp_strong_mono'`). Follows directly from the spatial form. -/
theorem wp_strong_mono {E1 E2 : CoPset} {e : (Exp rT)} {Φ Ψ : (Val rT) → IProp GF}
    (HE : E1 ⊆ E2) :
    iprop(wp E1 e Φ ∗ wpStrongMonoCont E2 Φ Ψ) ⊢@{IProp GF} wp E2 e Ψ :=
  wp_strong_mono' HE

/-- Monotonicity of `wp` under pointwise entailment of the postcondition. -/
theorem wp_mono {E : CoPset} {e : (Exp rT)} {Φ Ψ : (Val rT) → IProp GF}
    (HΦ : ∀ v, Φ v ⊢@{IProp GF} Ψ v) :
    wp E e Φ ⊢@{IProp GF} wp E e Ψ := by
  iintro HW
  iapply wp_wand (Φ := Φ) (Ψ := Ψ)
  isplitl [HW]; · iassumption
  iintro !> %v HΦv
  iapply HΦ $$ HΦv

/-- Mask monotonicity for `wp`: enlarging the mask is sound. -/
theorem wp_mask_mono {E1 E2 : CoPset} {e : (Exp rT)} {Φ : (Val rT) → IProp GF}
    (HE : E1 ⊆ E2) :
    wp E1 e Φ ⊢@{IProp GF} wp E2 e Φ := by
  iintro HW
  iapply wp_strong_mono' (Φ := Φ) (Ψ := Φ) HE
  isplitl [HW]; · iassumption
  iintro !> %σ %ρ %v %ε ⟨Hσ, Hs, Hε, HΦ⟩
  imodintro
  iframe

/-- Post-wand — spatial variant with frame, derived from `wp_wand`. -/
theorem wp_wand_l {E : CoPset} {e : (Exp rT)} {Φ Ψ : (Val rT) → IProp GF} :
    iprop(□ (∀ v, Φ v -∗ Ψ v) ∗ wp E e Φ) ⊢@{IProp GF} wp E e Ψ := by
  iintro ⟨#HΦ, HW⟩
  iapply wp_wand (Φ := Φ) (Ψ := Ψ)
  isplitl [HW]; · iassumption
  iintro !>; iexact HΦ

/-- `wp_wand` with arguments swapped. -/
theorem wp_wand_r {E : CoPset} {e : (Exp rT)} {Φ Ψ : (Val rT) → IProp GF} :
    iprop(wp E e Φ ∗ □ (∀ v, Φ v -∗ Ψ v)) ⊢@{IProp GF} wp E e Ψ :=
  wp_wand

/-! ### `specCoupl` — derived lemmas -/

/-- Degenerate-coupling reduction: `specCoupl` at any ε₂ reduces to
`|={E}=> specCoupl E σ e' σ' ε₁ Z` when `ε₁ ≤ ε₂`. The trick: take `n = 0`,
dirac-dirac distributions so the coupling-and-bind collapse. -/
theorem fupd_specCoupl_of_le {E : CoPset} {σ : (State rT)} {e' : (Exp rT)} {σ' : (State rT)}
    {ε₁ ε₂ : ENNReal} {Z : (State rT) → (Cfg rT) → ENNReal → IProp GF}
    (Hε : ε₁ ≤ ε₂) :
    iprop(|={E}=> specCoupl E σ e' σ' ε₁ Z) ⊢@{IProp GF}
      specCoupl E σ e' σ' ε₂ Z := by
  iintro HF
  iapply specCoupl_rec
  iexists (fun s c => s = σ ∧ c = ⟨e', σ'⟩), 0,
    MeasureTheory.Measure.dirac σ, MeasureTheory.Measure.dirac σ',
    (ε₂ - ε₁), (fun _ => ε₁), ε₁
  isplitr
  · ipure_intro
    show AddCoupl (ε₂ - ε₁) _ (MeasureTheory.Measure.dirac σ) _
    rw [MeasureTheory.Measure.dirac_bind Measurable.of_discrete]
    simp only [pexecN_zero]
    exact AddCoupl.dirac _ ⟨rfl, rfl⟩
  isplitr; · ipure_intro; intro _; exact _root_.le_refl _
  isplitr
  · ipure_intro
    set μ := (MeasureTheory.Measure.dirac σ').bind (fun s => pexecN 0 ⟨e', s⟩)
    have hmass : μ .univ ≤ 1 := by
      show μ Set.univ ≤ 1
      simp [μ, MeasureTheory.Measure.dirac_bind Measurable.of_discrete]
    calc (ε₂ - ε₁) + ∫⁻ _, ε₁ ∂μ
        = (ε₂ - ε₁) + ε₁ * μ .univ := by
            rw [MeasureTheory.lintegral_const, mul_comm]
      _ ≤ (ε₂ - ε₁) + ε₁ * 1 := by gcongr
      _ = (ε₂ - ε₁) + ε₁ := by rw [mul_one]
      _ = ε₂ := tsub_add_cancel_of_le Hε
  isplitr; · ipure_intro; exact Erasable.dret σ
  isplitr; · ipure_intro; exact Erasable.dret σ'
  iintro %σ₂ %e₂' %σ₂' %HS'
  obtain ⟨rfl, HS'⟩ := HS'
  cases HS'
  iexact HF

/-- Monotonicity of `specCoupl` in the error bound. -/
theorem specCoupl_mono_err {E : CoPset} {σ : (State rT)} {e' : (Exp rT)} {σ' : (State rT)}
    {ε₁ ε₂ : ENNReal} {Z : (State rT) → (Cfg rT) → ENNReal → IProp GF}
    (Hε : ε₁ ≤ ε₂) :
    specCoupl E σ e' σ' ε₁ Z ⊢@{IProp GF} specCoupl E σ e' σ' ε₂ Z := by
  iintro HS
  iapply fupd_specCoupl_of_le Hε
  imodintro
  iexact HS

/-- Fancy-update absorbs into `specCoupl`: the `ε₁ = ε` case of
`fupd_specCoupl_of_le`. -/
theorem fupd_specCoupl {E : CoPset} {σ : (State rT)} {e' : (Exp rT)} {σ' : (State rT)}
    {ε : ENNReal} {Z : (State rT) → (Cfg rT) → ENNReal → IProp GF} :
    iprop(|={E}=> specCoupl E σ e' σ' ε Z) ⊢@{IProp GF}
      specCoupl E σ e' σ' ε Z :=
  fupd_specCoupl_of_le (_root_.le_refl _)

/-- Induction principle for `specCoupl`. Mirrors Rocq's `spec_coupl_ind`.

To prove `Ψ` of `specCoupl ε`, it suffices to show that `specCouplPre`
applied to `(Ψ ∧ specCoupl)` implies `Ψ` (an "intuitionistic step
hypothesis"). -/
theorem specCoupl_ind {E : CoPset} {Ψ Z : (State rT) → (Cfg rT) → ENNReal → IProp GF} :
    iprop(□ (∀ (σ : (State rT)) (c : (Cfg rT)) (ε : ENNReal),
        specCouplPre E Z (fun s => iprop(Ψ s.1 s.2.1 s.2.2 ∧
            specCoupl E s.1 s.2.1.expr s.2.1.state s.2.2 Z))
          ((σ, c, ε) : SpecCouplState rT) -∗ Ψ σ c ε)) ⊢@{IProp GF}
      ∀ (σ : (State rT)) (e' : (Exp rT)) (σ' : (State rT)) (ε : ENNReal),
        specCoupl E σ e' σ' ε Z -∗ Ψ σ ⟨e', σ'⟩ ε := by
  iintro #IH %σ %e' %σ' %ε HC
  -- Lift Ψ to SpecCouplState.
  let Ψ' : SpecCouplState rT → IProp GF := fun s => Ψ s.1 s.2.1 s.2.2
  have HΨne : NonExpansive Ψ' := by
    constructor
    intro _ s s' hd
    have heq : s = s' := OFE.Leibniz.eq_of_eqv (OFE.Discrete.discrete_0 hd)
    subst heq; exact .of_eq rfl
  -- Apply least_fixpoint_ind.
  iapply (least_fixpoint_ind (F := specCouplPre (GF := GF) E Z) (Φ := Ψ'))
    $$ [] %((σ, (⟨e', σ'⟩ : (Cfg rT)), ε) : SpecCouplState rT) HC
  iintro !> %s HF
  obtain ⟨σ'', c, ε'⟩ := s
  iapply IH $$ %σ'' %c %ε'
  iexact HF

/-- General erasable-coupling intro for `specCoupl` with expectation bound on
the per-configuration error. Mirrors Rocq's `spec_coupl_erasables_exp`. -/
theorem specCoupl_erasables_exp {E : CoPset} {σ₁ : (State rT)} {e₁' : (Exp rT)} {σ₁' : (State rT)}
    {ε₁ ε : ENNReal} {Z : (State rT) → (Cfg rT) → ENNReal → IProp GF}
    {R : (State rT) → (State rT) → Prop}
    {μ₁ : MeasureTheory.Measure (State rT)} {μ₁' : MeasureTheory.Measure (State rT)}
    {X₂ : (State rT) → ENNReal} {r : ENNReal}
    (Hcpl : AddCoupl ε₁ {p : (State rT) × (State rT) | R p.1 p.2} μ₁ μ₁')
    (Heras₁ : Erasable μ₁ σ₁) (Heras₁' : Erasable μ₁' σ₁')
    (Hbnd : ∀ σ', X₂ σ' ≤ r)
    (Hexp : ε₁ + ∫⁻ σ', X₂ σ' ∂μ₁' ≤ ε) :
    iprop(∀ (σ₂ σ₂' : (State rT)), (⌜R σ₂ σ₂'⌝) -∗ |={E}=>
        specCoupl E σ₂ e₁' σ₂' (X₂ σ₂') Z) ⊢@{IProp GF}
      specCoupl E σ₁ e₁' σ₁' ε Z := by
  iintro H
  iapply specCoupl_rec
  iexists (fun σ₂ c => R σ₂ c.state ∧ c.expr = e₁'), 0, μ₁, μ₁',
    ε₁, (fun ρ => X₂ ρ.state), r
  isplitr
  · ipure_intro
    show AddCoupl ε₁ _ μ₁ ((μ₁').bind (fun σ => pexecN 0 ⟨e₁', σ⟩))
    simp only [pexecN_zero]
    rw [MeasureTheory.Measure.bind_dirac_eq_map _ Measurable.of_discrete,
        ← MeasureTheory.Measure.map_id (μ := μ₁)]
    exact AddCoupl.map (f := id) (g := fun σ => (⟨e₁', σ⟩ : (Cfg rT)))
      Measurable.of_discrete Measurable.of_discrete
      (fun {σ σ'} HR => ⟨HR, rfl⟩) Hcpl
  isplitr
  · ipure_intro; exact fun _ => Hbnd _
  isplitr
  · ipure_intro
    refine _root_.le_trans ?_ Hexp
    gcongr
    have heq : (μ₁' : MeasureTheory.Measure (State rT)).bind (fun σ => pexecN 0 ⟨e₁', σ⟩) =
        μ₁'.map (fun σ => (⟨e₁', σ⟩ : (Cfg rT))) := by
      simp only [pexecN_zero]
      exact MeasureTheory.Measure.bind_dirac_eq_map _ Measurable.of_discrete
    rw [heq, MeasureTheory.lintegral_map Measurable.of_discrete Measurable.of_discrete]
  isplitr; · ipure_intro; exact Heras₁
  isplitr; · ipure_intro; exact Heras₁'
  iintro %σ₂ %e₂' %σ₂' %HS
  obtain ⟨HR, rfl⟩ := HS
  iapply H $$ %σ₂ %σ₂' %HR

/-- Specialization of `specCoupl_erasables_exp` with a constant per-config cost
`ε₂`. The error bound becomes `ε₁ + ε₂ ≤ ε`. -/
theorem specCoupl_erasables {E : CoPset} {σ₁ : (State rT)} {e₁' : (Exp rT)} {σ₁' : (State rT)}
    {ε₁ ε₂ ε : ENNReal} {Z : (State rT) → (Cfg rT) → ENNReal → IProp GF}
    {R : (State rT) → (State rT) → Prop}
    {μ₁ : MeasureTheory.Measure (State rT)} {μ₁' : MeasureTheory.Measure (State rT)}
    (Hε : ε₁ + ε₂ ≤ ε)
    (Hcpl : AddCoupl ε₁ {p : (State rT) × (State rT) | R p.1 p.2} μ₁ μ₁')
    (Heras₁ : Erasable μ₁ σ₁) (Heras₁' : Erasable μ₁' σ₁') :
    iprop(∀ (σ₂ σ₂' : (State rT)), (⌜R σ₂ σ₂'⌝) -∗ |={E}=>
        specCoupl E σ₂ e₁' σ₂' ε₂ Z) ⊢@{IProp GF}
      specCoupl E σ₁ e₁' σ₁' ε Z := by
  iintro H
  have Hexp_bnd : ε₁ + ∫⁻ _, ε₂ ∂μ₁' ≤ ε := by
    refine _root_.le_trans ?_ Hε
    rw [MeasureTheory.lintegral_const, Erasable.mass Heras₁', mul_one]
  iapply (specCoupl_erasables_exp (X₂ := fun _ => ε₂) (r := ε₂) Hcpl Heras₁ Heras₁'
    (fun _ => _root_.le_refl _) Hexp_bnd)
  iintro %σ₂ %σ₂' %HR
  iapply H $$ %σ₂ %σ₂' %HR

/-- LHS-erasable + spec-side `pexecN n`-coupling intro for `specCoupl`.

The relation `R` connects the LHS-state (sampled from `μ₁`) to a spec config
(sampled from `pexecN n ⟨e₁', σ₁'⟩`). Mirrors Rocq's `spec_coupl_erasable_steps`. -/
theorem specCoupl_erasable_steps {E : CoPset} {σ₁ : (State rT)} {e₁' : (Exp rT)} {σ₁' : (State rT)}
    {n : Nat} {ε₁ ε₂ ε : ENNReal} {Z : (State rT) → (Cfg rT) → ENNReal → IProp GF}
    {R : (State rT) → (Cfg rT) → Prop} {μ₁ : MeasureTheory.Measure (State rT)}
    (Hε : ε₁ + ε₂ ≤ ε)
    (Hcpl : AddCoupl ε₁ {p : (State rT) × (Cfg rT) | R p.1 p.2} μ₁ (pexecN n ⟨e₁', σ₁'⟩))
    (Heras₁ : Erasable μ₁ σ₁) :
    iprop(∀ (σ₂ : (State rT)) (e₂' : (Exp rT)) (σ₂' : (State rT)),
        (⌜R σ₂ ⟨e₂', σ₂'⟩⌝) -∗ |={E}=>
          specCoupl E σ₂ e₂' σ₂' ε₂ Z) ⊢@{IProp GF}
      specCoupl E σ₁ e₁' σ₁' ε Z := by
  iintro H
  iapply specCoupl_rec
  iexists R, n, μ₁, MeasureTheory.Measure.dirac σ₁', ε₁, (fun _ => ε₂), ε₂
  isplitr
  · ipure_intro
    show AddCoupl ε₁ _ μ₁ ((MeasureTheory.Measure.dirac σ₁').bind (fun s => pexecN n ⟨e₁', s⟩))
    rw [MeasureTheory.Measure.dirac_bind Measurable.of_discrete]
    exact Hcpl
  isplitr; · ipure_intro; intro _; exact _root_.le_refl _
  isplitr
  · ipure_intro
    refine _root_.le_trans ?_ Hε
    rw [MeasureTheory.Measure.dirac_bind Measurable.of_discrete,
        MeasureTheory.lintegral_const]
    gcongr
    -- pexecN is a sub-probability: total mass ≤ 1. Prove by induction on n.
    have hmass : ∀ m (ρ : (Cfg rT)), (pexecN m ρ) Set.univ ≤ 1 := by
      intro m
      induction m with
      | zero => intro ρ; simp [pexecN_zero]
      | succ k ih =>
        intro ρ
        rw [pexecN_succ]
        rw [MeasureTheory.Measure.bind_apply MeasurableSet.of_discrete
              Measurable.of_discrete.aemeasurable]
        calc ∫⁻ a, (pexecN k a) Set.univ ∂(stepOrFinal ρ)
            ≤ ∫⁻ _, 1 ∂(stepOrFinal ρ) := MeasureTheory.lintegral_mono fun a => ih a
          _ = (stepOrFinal ρ) Set.univ := by simp
          _ ≤ 1 := by
              by_cases hv : ρ.expr.isValue
              · rw [stepOrFinal_isValue hv]; simp
              · rw [stepOrFinal_not_isValue hv]; exact primStep_univ_le_one ρ
    calc ε₂ * (pexecN n ⟨e₁', σ₁'⟩) .univ
        ≤ ε₂ * 1 := by gcongr; exact hmass n _
      _ = ε₂ := mul_one _
  isplitr; · ipure_intro; exact Heras₁
  isplitr; · ipure_intro; exact Erasable.dret σ₁'
  iintro %σ₂ %e₂' %σ₂' %HR
  iapply H $$ %σ₂ %e₂' %σ₂' %HR

/-- Pure-step specialization: LHS is the singleton `dirac σ₁`, RHS is `pexecN n`.
Mirrors Rocq's `spec_coupl_steps`. -/
theorem specCoupl_steps {E : CoPset} {σ₁ : (State rT)} {e₁' : (Exp rT)} {σ₁' : (State rT)}
    {n : Nat} {ε₁ ε₂ ε : ENNReal} {Z : (State rT) → (Cfg rT) → ENNReal → IProp GF}
    {R : (State rT) → (Cfg rT) → Prop}
    (Hε : ε₁ + ε₂ ≤ ε)
    (Hcpl : AddCoupl ε₁ {p : (State rT) × (Cfg rT) | R p.1 p.2}
              (MeasureTheory.Measure.dirac σ₁) (pexecN n ⟨e₁', σ₁'⟩)) :
    iprop(∀ (σ₂ : (State rT)) (e₂' : (Exp rT)) (σ₂' : (State rT)),
        (⌜R σ₂ ⟨e₂', σ₂'⟩⌝) -∗ |={E}=>
          specCoupl E σ₂ e₂' σ₂' ε₂ Z) ⊢@{IProp GF}
      specCoupl E σ₁ e₁' σ₁' ε Z := by
  iintro H
  iapply (specCoupl_erasable_steps Hε Hcpl (Erasable.dret σ₁))
  iexact H

/-- Deterministic-step specialization: if `pexecN n ⟨e₁', σ₁'⟩ = dirac ⟨e₂', σ₂'⟩`
(the spec side takes `n` steps and lands deterministically on `⟨e₂', σ₂'⟩`),
then a `specCoupl` at `(e₂', σ₂')` gives one at `(e₁', σ₁')` for free. -/
theorem specCoupl_steps_det {E : CoPset} {σ : (State rT)} {e₁' : (Exp rT)} {σ₁' : (State rT)}
    {e₂' : (Exp rT)} {σ₂' : (State rT)} {n : Nat} {ε : ENNReal}
    {Z : (State rT) → (Cfg rT) → ENNReal → IProp GF}
    (Hstep : pexecN n ⟨e₁', σ₁'⟩ = MeasureTheory.Measure.dirac ⟨e₂', σ₂'⟩) :
    specCoupl E σ e₂' σ₂' ε Z ⊢@{IProp GF}
      specCoupl E σ e₁' σ₁' ε Z := by
  iintro HS
  iapply specCoupl_rec
  iexists (fun s c => s = σ ∧ c = ⟨e₂', σ₂'⟩), n,
    MeasureTheory.Measure.dirac σ, MeasureTheory.Measure.dirac σ₁',
    (0 : ENNReal), (fun _ => ε), ε
  isplitr
  · ipure_intro
    show AddCoupl 0 _ (MeasureTheory.Measure.dirac σ) _
    rw [MeasureTheory.Measure.dirac_bind Measurable.of_discrete, Hstep]
    exact AddCoupl.dirac _ ⟨rfl, rfl⟩
  isplitr; · ipure_intro; intro _; exact _root_.le_refl _
  isplitr
  · ipure_intro
    -- 0 + ∫ ε ∂(dirac σ₁'.bind (pexecN n ⟨e₁', ·⟩)) ≤ ε.
    set μ := (MeasureTheory.Measure.dirac σ₁').bind (fun s => pexecN n ⟨e₁', s⟩)
    have hmass : μ .univ ≤ 1 := by
      show μ Set.univ ≤ 1
      simp [μ, MeasureTheory.Measure.dirac_bind Measurable.of_discrete, Hstep]
    calc (0 : ENNReal) + ∫⁻ _, ε ∂μ
        = ε * μ .univ := by
            rw [zero_add, MeasureTheory.lintegral_const, mul_comm]
      _ ≤ ε * 1 := by gcongr
      _ = ε := mul_one _
  isplitr; · ipure_intro; exact Erasable.dret σ
  isplitr; · ipure_intro; exact Erasable.dret σ₁'
  iintro %σ₂ %e₂'' %σ₂'' %HS'
  imodintro
  obtain ⟨rfl, HS'⟩ := HS'
  cases HS'
  iexact HS

/-- Single-step specialization: when `(e₁', σ₁')` is reducible, every
positive-measure spec successor lets us land on a `specCoupl` at the
post-step config. Mirrors Rocq's `spec_coupl_step`. -/
theorem specCoupl_step {E : CoPset} {σ₁ : (State rT)} {e₁' : (Exp rT)} {σ₁' : (State rT)}
    {ε : ENNReal} {Z : (State rT) → (Cfg rT) → ENNReal → IProp GF}
    (Hred : Reducible e₁' σ₁') :
    iprop(∀ (e₂' : (Exp rT)) (σ₂' : (State rT)),
        (⌜0 < primStep ⟨e₁', σ₁'⟩ {⟨e₂', σ₂'⟩}⌝) -∗ |={E}=>
          specCoupl E σ₁ e₂' σ₂' ε Z) ⊢@{IProp GF}
      specCoupl E σ₁ e₁' σ₁' ε Z := by
  iintro H
  have Hε : (0 : ENNReal) + ε ≤ ε := by rw [zero_add]
  have hprob_lhs : (MeasureTheory.Measure.dirac σ₁ : MeasureTheory.Measure (State rT)) .univ = 1 := by
    simp
  have hprob_rhs : (primStep ⟨e₁', σ₁'⟩) .univ = 1 := by
    haveI := prim_step_mass ⟨e₁', σ₁'⟩ Hred
    exact MeasureTheory.IsProbabilityMeasure.measure_univ
  have Htrivial : AddCoupl 0 Set.univ (MeasureTheory.Measure.dirac σ₁) (primStep ⟨e₁', σ₁'⟩) :=
    RelCoupl.exact (RelCoupl.trivial hprob_lhs hprob_rhs)
  have Hpos := AddCoupl.pos_R Htrivial
  have hnotval : ¬ e₁'.isValue := fun hv => by
    obtain ⟨ρ, hρ⟩ := Hred
    exact val_stuck hρ hv
  have hpexec1 : pexecN 1 ⟨e₁', σ₁'⟩ = primStep ⟨e₁', σ₁'⟩ := by
    rw [pexecN_one, stepOrFinal_not_isValue hnotval]
  have HcplR : AddCoupl 0 {p : (State rT) × (Cfg rT) | (fun σ c => σ = σ₁ ∧
        0 < primStep ⟨e₁', σ₁'⟩ {c}) p.1 p.2}
        (MeasureTheory.Measure.dirac σ₁) (pexecN 1 ⟨e₁', σ₁'⟩) := by
    rw [hpexec1]
    refine AddCoupl.mono_rel ?_ Hpos
    rintro ⟨σ, c⟩ ⟨_, hσ, hc⟩
    refine ⟨?_, ?_⟩
    · by_contra hne
      apply hσ
      rw [MeasureTheory.Measure.dirac_apply' _ MeasurableSet.of_discrete]
      simp [Ne.symm hne]
    · exact pos_iff_ne_zero.mpr hc
  iapply (specCoupl_steps (n := 1) (R := fun σ c => σ = σ₁ ∧
    0 < primStep ⟨e₁', σ₁'⟩ {c}) (ε₁ := 0) (ε₂ := ε) (Hε := Hε) HcplR)
  iintro %σ₂ %e₂' %σ₂' %HR
  obtain ⟨rfl, Hpos'⟩ := HR
  iapply H $$ %e₂' %σ₂' %Hpos'

/-! ## `progCoupl` — derived lemmas -/

/-- `progCoupl` implies reducibility of the program. -/
theorem progCoupl_reducible {e₁ : (Exp rT)} {σ₁ : (State rT)} {e₁' : (Exp rT)} {σ₁' : (State rT)}
    {ε : ENNReal} {Z : (Exp rT) → (State rT) → (Exp rT) → (State rT) → ENNReal → IProp GF} :
    progCoupl e₁ σ₁ e₁' σ₁' ε Z ⊢@{IProp GF} ⌜Reducible e₁ σ₁⌝ := by
  iintro HCpl
  icases HCpl with ⟨%n, %μ₁', %X₂, %Hred, _⟩
  ipure_intro; exact Hred

/-- Strong monotonicity of `progCoupl`: given a wand that can consume an extra
fact "∃σ, primStep σ {a} > 0" (saying `a` is reachable from *some* start) and
a persistent "catch-all" `Z₂` at error `1`, we can lift the monotonicity.

Used by `progCoupl_strengthen` and indirectly by `prog_coupl_ctx_bind`.

Discrete-measure proof: the new `X₂'` is `X₂` on points reachable from some
start, else `1`. The expectation bound works because `primStep ⟨e₁, σ₁⟩` is
supported on `{a | 0 < primStep ⟨e₁, σ₁⟩ {a}}` ⊆ `{a | ∃σ, 0 < primStep ⟨e₁,σ⟩{a}}`,
and we integrate `h₁'(a) := if ∃σ-bound then h₁(a) else 0`, which ae-equals
`h₁` and satisfies the old pointwise bound. -/
theorem progCoupl_strong_mono {e₁ : (Exp rT)} {σ₁ : (State rT)} {e₁' : (Exp rT)} {σ₁' : (State rT)}
    {ε : ENNReal} {Z₁ Z₂ : (Exp rT) → (State rT) → (Exp rT) → (State rT) → ENNReal → IProp GF} :
    iprop((□ ∀ e₂ σ₂ e₂' σ₂', Z₂ e₂ σ₂ e₂' σ₂' 1) ∗
          (∀ e₂ σ₂ e₂' σ₂' ε',
             ⌜∃ σ, 0 < primStep ⟨e₁, σ⟩ {⟨e₂, σ₂⟩}⌝ ∗ Z₁ e₂ σ₂ e₂' σ₂' ε' -∗
               Z₂ e₂ σ₂ e₂' σ₂' ε') ∗
          progCoupl e₁ σ₁ e₁' σ₁' ε Z₁) ⊢@{IProp GF}
      progCoupl e₁ σ₁ e₁' σ₁' ε Z₂ := by
  iintro ⟨#H1F, Hm, HCpl⟩
  icases HCpl with ⟨%n, %μ₁', %X₂, %Hred, %Hbnd, %Hexp, %Heras, HCont⟩
  obtain ⟨r, Hr⟩ := Hbnd
  iexists n, μ₁'
  -- New error function: X₂' a b = X₂ a b if reachable from some start, else 1.
  classical
  iexists (fun a b => if ∃ σ, 0 < primStep ⟨e₁, σ⟩ {a} then X₂ a b else 1)
  isplitr; · ipure_intro; exact Hred
  -- Bound: max r 1 works.
  isplitr
  · ipure_intro
    refine ⟨max r 1, fun a b => ?_⟩
    show (if ∃ σ, 0 < primStep ⟨e₁, σ⟩ {a} then X₂ a b else 1) ≤ max r 1
    split_ifs with h
    · exact (Hr a b).trans (le_max_left _ _)
    · exact le_max_right _ _
  -- Expectation bound.
  isplitr
  · ipure_intro
    intro h₁ h₂ Hh₁ Hh₂ Hh₁h₂
    -- h₁'(a) := if reachable then h₁(a) else 0.
    let h₁' : (Cfg rT) → ENNReal :=
      fun a => if ∃ σ, 0 < primStep ⟨e₁, σ⟩ {a} then h₁ a else 0
    -- Step 1: ∫ h₁ = ∫ h₁' under primStep ⟨e₁, σ₁⟩.
    have hcongr : (∫⁻ a, h₁ a ∂(primStep ⟨e₁, σ₁⟩)) = ∫⁻ a, h₁' a ∂(primStep ⟨e₁, σ₁⟩) := by
      refine MeasureTheory.lintegral_congr_ae ?_
      refine MeasureTheory.ae_iff_of_countable.mpr ?_
      intro a ha
      simp only [h₁']
      have hexists : ∃ σ, 0 < primStep ⟨e₁, σ⟩ {a} := ⟨σ₁, pos_iff_ne_zero.mpr ha⟩
      rw [if_pos hexists]
    rw [hcongr]
    -- Step 2: apply Hexp to h₁', h₂.
    refine Hexp h₁' h₂ ?_ Hh₂ ?_
    · intro a; simp only [h₁']; split_ifs; exacts [Hh₁ a, zero_le _]
    · intro a b
      simp only [h₁']
      split_ifs with h
      · -- On reachable, X₂' = X₂, use original bound.
        have := Hh₁h₂ a b
        simpa [if_pos h] using this
      · exact (zero_le _).trans le_self_add
  isplitr; · ipure_intro; exact Heras
  -- Continuation: for each (e₂, σ₂, e₂', σ₂'), case on reachability.
  iintro %e₂ %σ₂ %e₂' %σ₂'
  by_cases hreach : ∃ σ, 0 < primStep ⟨e₁, σ⟩ {⟨e₂, σ₂⟩}
  · -- Reachable: use Hm ∘ HCont.
    simp only [if_pos hreach]
    ihave HZ₁ := HCont $$ %e₂ %σ₂ %e₂' %σ₂'
    imod HZ₁ with HZ₁
    imodintro
    iapply Hm $$ %e₂ %σ₂ %e₂' %σ₂' %(X₂ ⟨e₂, σ₂⟩ ⟨e₂', σ₂'⟩) [HZ₁]
    isplitr
    · ipure_intro; exact hreach
    iexact HZ₁
  · -- Unreachable: X₂' = 1, use the catchall.
    simp only [if_neg hreach]
    imodintro
    iexact H1F

/-- `progCoupl_strengthen` — enriches the continuation's hypothesis with the
disjunction "either there's some start state making the head step positive,
or the local error bound is already ≥ 1". -/
theorem progCoupl_strengthen {e₁ : (Exp rT)} {σ₁ : (State rT)} {e₁' : (Exp rT)} {σ₁' : (State rT)}
    {ε : ENNReal} {Z : (Exp rT) → (State rT) → (Exp rT) → (State rT) → ENNReal → IProp GF} :
    iprop((□ ∀ e₂ σ₂ e₂' σ₂', Z e₂ σ₂ e₂' σ₂' 1) ∗
          progCoupl e₁ σ₁ e₁' σ₁' ε Z) ⊢@{IProp GF}
      progCoupl e₁ σ₁ e₁' σ₁' ε
        (fun e₂ σ₂ e₂' σ₂' ε' =>
          iprop(⌜(∃ σ, 0 < primStep ⟨e₁, σ⟩ {⟨e₂, σ₂⟩}) ∨ 1 ≤ ε'⌝ ∧
                Z e₂ σ₂ e₂' σ₂' ε')) := by
  iintro ⟨#H1F, HCpl⟩
  iapply progCoupl_strong_mono
  isplitr
  · iintro !> %e₂ %σ₂ %e₂' %σ₂'
    isplitr
    · ipure_intro; exact .inr (_root_.le_refl _)
    iexact H1F
  isplitr [HCpl]
  swap
  · iexact HCpl
  iintro %e₂ %σ₂ %e₂' %σ₂' %ε' ⟨%Hreach, HZ⟩
  isplitr
  · ipure_intro; exact .inl Hreach
  iexact HZ

/-- `progCoupl_ctx_bind` specialized to ProbLang's `(Ectx rT)`: a program coupling
at `e₁` with continuation receiving the filled-in expression lifts to one at
`K.fill e₁`, provided `e₁` is not a value.

Concrete-(Ectx rT) port: instead of Rocq's classical `Kinv` constructed inside the
proof, we use `Function.partialInv K.fill`. The expectation bound argument
goes through `lintegral_map` + `primStep_fill hv` (the pushforward formula). -/
theorem progCoupl_ctx_bind {K : (Ectx rT)} {e₁ : (Exp rT)} {σ₁ : (State rT)} {e₁' : (Exp rT)} {σ₁' : (State rT)}
    {ε : ENNReal} {Z : (Exp rT) → (State rT) → (Exp rT) → (State rT) → ENNReal → IProp GF}
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
  let Kinv : (Exp rT) → Option (Exp rT) := Function.partialInv K.fill
  have Kinv_left : ∀ e, Kinv (K.fill e) = some e :=
    Function.partialInv_left (Ectx.fill_injective K)
  iexists n, μ₁'
  iexists (fun a b => match Kinv a.expr with
                     | some e' => X₂ ⟨e', a.state⟩ b
                     | none => 1)
  isplitr; · ipure_intro; exact Hred.fill K
  -- Bound: max r 1.
  isplitr
  · ipure_intro
    refine ⟨max r 1, fun a b => ?_⟩
    show (match Kinv a.expr with
          | some e' => X₂ ⟨e', a.state⟩ b
          | none => 1) ≤ max r 1
    cases Kinv a.expr with
    | none => exact le_max_right _ _
    | some e' => exact (Hr _ _).trans (le_max_left _ _)
  -- Expectation bound.
  isplitr
  · ipure_intro
    intro h₁ h₂ Hh₁ Hh₂ Hh₁h₂
    -- Pull back h₁ along K.fill: h₁'(ρ) := h₁ ⟨K.fill ρ.expr, ρ.state⟩.
    let h₁' : (Cfg rT) → ENNReal := fun ρ => h₁ ⟨K.fill ρ.expr, ρ.state⟩
    -- Step 1: ∫ h₁ ∂primStep⟨K.fill e₁, σ₁⟩ = ∫ h₁' ∂primStep⟨e₁, σ₁⟩.
    have hmap : (∫⁻ a, h₁ a ∂(primStep ⟨K.fill e₁, σ₁⟩)) =
                ∫⁻ ρ, h₁' ρ ∂(primStep ⟨e₁, σ₁⟩) := by
      rw [primStep_fill hv]
      rw [MeasureTheory.lintegral_map Measurable.of_discrete Measurable.of_discrete]
    rw [hmap]
    -- Step 2: apply Hexp to h₁', h₂.
    refine Hexp h₁' h₂ ?_ Hh₂ ?_
    · intro ρ; exact Hh₁ _
    · intro ρ b
      -- h₁' ρ = h₁ ⟨K.fill ρ.expr, ρ.state⟩ ≤ h₂ b + X₂' ⟨K.fill ρ.expr, ρ.state⟩ b
      -- and X₂' ⟨K.fill ρ.expr, ρ.state⟩ b = X₂ ρ b by Kinv_left.
      have := Hh₁h₂ ⟨K.fill ρ.expr, ρ.state⟩ b
      simp only [Kinv_left] at this
      -- Goal: h₁' ρ ≤ h₂ b + X₂ ρ b
      -- `this`: h₁ ⟨K.fill ρ.expr, ρ.state⟩ ≤ h₂ b + X₂ ⟨ρ.expr, ρ.state⟩ b
      -- ρ = ⟨ρ.expr, ρ.state⟩ definitionally.
      exact this
  isplitr; · ipure_intro; exact Heras
  -- Continuation: case on Kinv e₂.
  iintro %e₂ %σ₂ %e₂' %σ₂'
  cases hKinv : Kinv e₂ with
  | none =>
    -- Unreachable: X₂' a b = 1 here.
    simp only [hKinv]
    imodintro
    iexact H1F
  | some e₃ =>
    -- e₂ = K.fill e₃.
    have he₂ : K.fill e₃ = e₂ :=
      ((Function.Injective.isPartialInv (Ectx.fill_injective K)) e₃ e₂).1 hKinv
    simp only [hKinv]
    ihave HZ := HCont $$ %e₃ %σ₂ %e₂' %σ₂'
    imod HZ with HZ
    imodintro
    -- Goal: Z e₂ σ₂ e₂' σ₂' (X₂ ⟨e₃, σ₂⟩ ⟨e₂', σ₂'⟩)
    -- HZ:   Z (K.fill e₃) σ₂ e₂' σ₂' (X₂ ⟨e₃, σ₂⟩ ⟨e₂', σ₂'⟩)
    rw [← he₂]
    iexact HZ

/-! ### `progCoupl` — coupling-intro lemmas

General-purpose "construct a `progCoupl` from a raw expectation-bound" lemmas.
These all take `n = 1` spec step, `μ₁' = dirac σ₁'`, and collapse
`pexecN 1 ⟨e₁', ·⟩` to `primStep` via `stepOrFinal_not_isValue`. -/

/-- `prog_coupl_steps_adv'` — one-spec-step intro with an adversarial per-cfg
error `X₂` bounded by 1. Mirrors Rocq's `prog_coupl_steps_adv'`. -/
theorem progCoupl_steps_adv' {e₁ : (Exp rT)} {σ₁ : (State rT)} {e₁' : (Exp rT)} {σ₁' : (State rT)}
    {ε : ENNReal} {Z : (Exp rT) → (State rT) → (Exp rT) → (State rT) → ENNReal → IProp GF}
    {X₂ : (Cfg rT) → (Cfg rT) → ENNReal}
    (Hred : Reducible e₁ σ₁) (Hred' : Reducible e₁' σ₁')
    (Hbnd : ∀ ρ₁ ρ₂, X₂ ρ₁ ρ₂ ≤ 1)
    (Hcpl : ∀ (h₁ h₂ : (Cfg rT) → ENNReal),
        (∀ a, h₁ a ≤ 1) → (∀ b, h₂ b ≤ 1) →
        (∀ a b, h₁ a ≤ h₂ b + X₂ a b) →
        (∫⁻ a, h₁ a ∂(primStep ⟨e₁, σ₁⟩)) ≤
          (∫⁻ b, h₂ b ∂(primStep ⟨e₁', σ₁'⟩)) + ε) :
    iprop(∀ (e₂ : (Exp rT)) (σ₂ : (State rT)) (e₂' : (Exp rT)) (σ₂' : (State rT)),
        |={∅}=> Z e₂ σ₂ e₂' σ₂' (X₂ ⟨e₂, σ₂⟩ ⟨e₂', σ₂'⟩)) ⊢@{IProp GF}
      progCoupl e₁ σ₁ e₁' σ₁' ε Z := by
  iintro Hcnt
  iexists 1, (MeasureTheory.Measure.dirac σ₁'), X₂
  isplitr; · ipure_intro; exact Hred
  isplitr; · ipure_intro; exact ⟨1, Hbnd⟩
  isplitr
  · ipure_intro
    intro h₁ h₂ Hh₁ Hh₂ Hh₁h₂
    -- μ₁'.bind (pexecN 1 ⟨e₁', ·⟩) = dirac σ₁'.bind (primStep ∘ ⟨e₁', ·⟩)
    --   = primStep ⟨e₁', σ₁'⟩ (since reducible).
    have hnotval' : ¬ e₁'.isValue := fun hv => by
      obtain ⟨ρ, hρ⟩ := Hred'
      exact val_stuck hρ hv
    have heq : (MeasureTheory.Measure.dirac σ₁' : MeasureTheory.Measure (State rT)).bind
        (fun σ => pexecN 1 ⟨e₁', σ⟩) = primStep ⟨e₁', σ₁'⟩ := by
      rw [MeasureTheory.Measure.dirac_bind Measurable.of_discrete]
      rw [pexecN_one, stepOrFinal_not_isValue hnotval']
    rw [heq]
    exact Hcpl h₁ h₂ Hh₁ Hh₂ Hh₁h₂
  isplitr; · ipure_intro; exact Erasable.dret σ₁'
  iintro %e₂ %σ₂ %e₂' %σ₂'
  iapply Hcnt $$ %e₂ %σ₂ %e₂' %σ₂'

/-- `prog_coupl_steps_adv` — with an additive `ε₂` slack added to the
per-config error. Derived from `progCoupl_steps_adv'` by shifting `X₂ + ε₂`. -/
theorem progCoupl_steps_adv {e₁ : (Exp rT)} {σ₁ : (State rT)} {e₁' : (Exp rT)} {σ₁' : (State rT)}
    {ε₁ ε₂ ε : ENNReal} {Z : (Exp rT) → (State rT) → (Exp rT) → (State rT) → ENNReal → IProp GF}
    {X₂ : (Cfg rT) → (Cfg rT) → ENNReal}
    (Hε : ε₁ + ε₂ ≤ ε)
    (Hred : Reducible e₁ σ₁) (Hred' : Reducible e₁' σ₁')
    (Hbnd : ∀ ρ₁ ρ₂, X₂ ρ₁ ρ₂ ≤ 1)
    (Hcpl : ∀ (h₁ h₂ : (Cfg rT) → ENNReal),
        (∀ a, h₁ a ≤ 1) → (∀ b, h₂ b ≤ 1) →
        (∀ a b, h₁ a ≤ h₂ b + X₂ a b) →
        (∫⁻ a, h₁ a ∂(primStep ⟨e₁, σ₁⟩)) ≤
          (∫⁻ b, h₂ b ∂(primStep ⟨e₁', σ₁'⟩)) + ε₁) :
    iprop(∀ (e₂ : (Exp rT)) (σ₂ : (State rT)) (e₂' : (Exp rT)) (σ₂' : (State rT)),
        |={∅}=> Z e₂ σ₂ e₂' σ₂' (X₂ ⟨e₂, σ₂⟩ ⟨e₂', σ₂'⟩ + ε₂)) ⊢@{IProp GF}
      progCoupl e₁ σ₁ e₁' σ₁' ε Z := by
  iintro Hcnt
  -- Reduce to `progCoupl_steps_adv'` with error `X₂ + ε₂` and slack `ε`.
  -- But progCoupl_steps_adv' wants X₂ bounded by 1. Use 1+ε₂ as bound… actually
  -- the simpler route is to inline the witnesses with X₂ := fun a b => X₂ a b + ε₂
  -- and bound r := 1 + ε₂.
  iexists 1, (MeasureTheory.Measure.dirac σ₁'), (fun a b => X₂ a b + ε₂)
  isplitr; · ipure_intro; exact Hred
  isplitr
  · ipure_intro
    refine ⟨1 + ε₂, fun a b => ?_⟩
    show X₂ a b + ε₂ ≤ 1 + ε₂
    gcongr
    exact Hbnd a b
  isplitr
  · ipure_intro
    intro h₁ h₂ Hh₁ Hh₂ Hh₁h₂
    have hnotval' : ¬ e₁'.isValue := fun hv => by
      obtain ⟨ρ, hρ⟩ := Hred'
      exact val_stuck hρ hv
    have heq : (MeasureTheory.Measure.dirac σ₁' : MeasureTheory.Measure (State rT)).bind
        (fun σ => pexecN 1 ⟨e₁', σ⟩) = primStep ⟨e₁', σ₁'⟩ := by
      rw [MeasureTheory.Measure.dirac_bind Measurable.of_discrete]
      rw [pexecN_one, stepOrFinal_not_isValue hnotval']
    rw [heq]
    -- Use modified h₃(ρ) := min 1 (h₂ ρ + ε₂) to apply Hcpl.
    let h₃ : (Cfg rT) → ENNReal := fun ρ => (h₂ ρ + ε₂) ⊓ 1
    -- Alternative: since ENNReal is friendlier, skip the ⊓ 1 and just use h₂+ε₂
    -- directly. h₂ ρ + ε₂ may exceed 1 but that's fine — the hypotheses need
    -- ≤ 1 which we don't get without clamping. Use `min` for clamping.
    have hh₃_le_1 : ∀ a, h₃ a ≤ 1 := fun a => by
      simp only [h₃]; exact inf_le_right
    have hh₁h₃ : ∀ a b, h₁ a ≤ h₃ b + X₂ a b := by
      intro a b
      simp only [h₃]
      -- h₃ b = (h₂ b + ε₂) ⊓ 1. Show h₁ a ≤ min (h₂ b + ε₂) 1 + X₂ a b.
      -- Cases: if (h₂ b + ε₂) ≤ 1, min = h₂ b + ε₂, so goal is h₁ a ≤ h₂ b + ε₂ + X₂ a b.
      --   From Hh₁h₂: h₁ a ≤ h₂ b + (X₂ a b + ε₂), same thing (by comm/assoc).
      -- if (h₂ b + ε₂) > 1, min = 1 ≥ h₁ a (trivially).
      by_cases hlt : h₂ b + ε₂ ≤ 1
      · rw [inf_of_le_left hlt]
        -- h₁ a ≤ (h₂ b + ε₂) + X₂ a b = h₂ b + (X₂ a b + ε₂) by comm + assoc.
        calc h₁ a ≤ h₂ b + (X₂ a b + ε₂) := Hh₁h₂ a b
          _ = (h₂ b + ε₂) + X₂ a b := by ring
      · push Not at hlt
        rw [inf_of_le_right hlt.le]
        exact le_add_right (Hh₁ a)
    calc (∫⁻ a, h₁ a ∂(primStep ⟨e₁, σ₁⟩))
        ≤ (∫⁻ b, h₃ b ∂(primStep ⟨e₁', σ₁'⟩)) + ε₁ := Hcpl h₁ h₃ Hh₁ hh₃_le_1 hh₁h₃
      _ ≤ (∫⁻ b, (h₂ b + ε₂) ∂(primStep ⟨e₁', σ₁'⟩)) + ε₁ := by
            gcongr with b
            simp only [h₃]; exact inf_le_left
      _ = (∫⁻ b, h₂ b ∂(primStep ⟨e₁', σ₁'⟩)) + ε₂ * (primStep ⟨e₁', σ₁'⟩) .univ + ε₁ := by
            rw [MeasureTheory.lintegral_add_right _ measurable_const,
                MeasureTheory.lintegral_const, mul_comm]
      _ ≤ (∫⁻ b, h₂ b ∂(primStep ⟨e₁', σ₁'⟩)) + ε₂ * 1 + ε₁ := by
            gcongr
            haveI := prim_step_mass ⟨e₁', σ₁'⟩ Hred'
            exact MeasureTheory.IsProbabilityMeasure.measure_univ.le
      _ ≤ (∫⁻ b, h₂ b ∂(primStep ⟨e₁', σ₁'⟩)) + ε := by
            rw [mul_one, add_assoc, add_comm ε₂ ε₁]
            gcongr
  isplitr; · ipure_intro; exact Erasable.dret σ₁'
  iintro %e₂ %σ₂ %e₂' %σ₂'
  iapply Hcnt $$ %e₂ %σ₂ %e₂' %σ₂'

/-- `prog_coupl_steps` — given an `AddCoupl` between program steps and a
catch-all at `ε = 1`, construct a `progCoupl`. Mirrors Rocq's `prog_coupl_steps`
via the `Y := if (R ∧ ε₂ ≤ 1) then ε₂ else 1` indicator trick. -/
theorem progCoupl_steps {e₁ : (Exp rT)} {σ₁ : (State rT)} {e₁' : (Exp rT)} {σ₁' : (State rT)}
    {ε₁ ε₂ ε : ENNReal} {R : (Cfg rT) → (Cfg rT) → Prop}
    {Z : (Exp rT) → (State rT) → (Exp rT) → (State rT) → ENNReal → IProp GF}
    (Hε : ε₁ + ε₂ ≤ ε)
    (Hred : Reducible e₁ σ₁) (Hred' : Reducible e₁' σ₁')
    (Hcpl : AddCoupl ε₁ {p : (Cfg rT) × (Cfg rT) | R p.1 p.2}
              (primStep ⟨e₁, σ₁⟩) (primStep ⟨e₁', σ₁'⟩)) :
    iprop((□ ∀ e₂ σ₂ e₂' σ₂', Z e₂ σ₂ e₂' σ₂' 1) ∗
          (∀ (e₂ : (Exp rT)) (σ₂ : (State rT)) (e₂' : (Exp rT)) (σ₂' : (State rT)),
            (⌜R ⟨e₂, σ₂⟩ ⟨e₂', σ₂'⟩⌝) -∗ |={∅}=>
              Z e₂ σ₂ e₂' σ₂' ε₂)) ⊢@{IProp GF}
      progCoupl e₁ σ₁ e₁' σ₁' ε Z := by
  iintro ⟨#H1F, Hcnt⟩
  classical
  -- Indicator Y: use ε₂ when (R ρ₁ ρ₂ ∧ ε₂ ≤ 1), else 1.
  let Y : (Cfg rT) → (Cfg rT) → ENNReal := fun ρ₁ ρ₂ =>
    if R ρ₁ ρ₂ ∧ ε₂ ≤ 1 then ε₂ else 1
  have HY_bnd : ∀ ρ₁ ρ₂, Y ρ₁ ρ₂ ≤ 1 := by
    intro ρ₁ ρ₂
    simp only [Y]
    split_ifs with h
    · exact h.2
    · exact _root_.le_refl _
  have HY_exp : ∀ (h₁ h₂ : (Cfg rT) → ENNReal),
      (∀ a, h₁ a ≤ 1) → (∀ b, h₂ b ≤ 1) →
      (∀ a b, h₁ a ≤ h₂ b + Y a b) →
      (∫⁻ a, h₁ a ∂(primStep ⟨e₁, σ₁⟩)) ≤
        (∫⁻ b, h₂ b ∂(primStep ⟨e₁', σ₁'⟩)) + ε := by
    intro h₁ h₂ Hh₁ Hh₂ Hh₁h₂
    -- Case on ε₂ ≤ 1.
    by_cases hε₂ : ε₂ ≤ 1
    · -- On R-pairs, Y = ε₂ (since both ε₂ ≤ 1 and R hold).
      -- So h₁ a ≤ h₂ b + ε₂ on R, i.e. h₁ a ≤ (h₂ b + ε₂) on R.
      -- Apply Hcpl (which is an AddCoupl ε₁ on R) with test functions (h₁, h₂+ε₂⊓1).
      -- ∫ h₁ ≤ ∫ (h₂ + ε₂)⊓1 + ε₁ ≤ ∫ h₂ + ε₂ + ε₁ ≤ ε₂ + ε₁ ≤ ε.
      let h₃ : (Cfg rT) → ENNReal := fun b => (h₂ b + ε₂) ⊓ 1
      have Hh₃ : ∀ b, h₃ b ≤ 1 := fun _ => inf_le_right
      have Hh₁h₃ : ∀ a b, R a b → h₁ a ≤ h₃ b + 0 := by
        intro a b HR
        rw [add_zero]
        simp only [h₃, le_inf_iff]
        refine ⟨?_, Hh₁ a⟩
        have := Hh₁h₂ a b
        simp only [Y, if_pos (And.intro HR hε₂)] at this
        exact this
      have HAdd : (∫⁻ a, h₁ a ∂(primStep ⟨e₁, σ₁⟩)) ≤
          (∫⁻ b, h₃ b ∂(primStep ⟨e₁', σ₁'⟩)) + ε₁ := by
        have := Hcpl ⟨h₁, Measurable.of_discrete, Hh₁⟩ ⟨h₃, Measurable.of_discrete, Hh₃⟩
          (fun {a b} (hab : R a b) => by
            have := Hh₁h₃ a b hab
            rw [add_zero] at this
            exact this)
        simpa using this
      calc (∫⁻ a, h₁ a ∂(primStep ⟨e₁, σ₁⟩))
          ≤ (∫⁻ b, h₃ b ∂(primStep ⟨e₁', σ₁'⟩)) + ε₁ := HAdd
        _ ≤ (∫⁻ b, (h₂ b + ε₂) ∂(primStep ⟨e₁', σ₁'⟩)) + ε₁ := by
              gcongr with b; simp only [h₃]; exact inf_le_left
        _ = (∫⁻ b, h₂ b ∂(primStep ⟨e₁', σ₁'⟩)) + ε₂ * (primStep ⟨e₁', σ₁'⟩) .univ + ε₁ := by
              rw [MeasureTheory.lintegral_add_right _ measurable_const,
                  MeasureTheory.lintegral_const, mul_comm]
        _ ≤ (∫⁻ b, h₂ b ∂(primStep ⟨e₁', σ₁'⟩)) + ε₂ * 1 + ε₁ := by
              gcongr
              haveI := prim_step_mass ⟨e₁', σ₁'⟩ Hred'
              exact MeasureTheory.IsProbabilityMeasure.measure_univ.le
        _ ≤ (∫⁻ b, h₂ b ∂(primStep ⟨e₁', σ₁'⟩)) + ε := by
              rw [mul_one, add_assoc, add_comm ε₂ ε₁]; gcongr
    · -- ε₂ > 1: Y ≡ 1 everywhere, so h₁ a ≤ h₂ b + 1 on all pairs.
      -- Then ∫ h₁ ≤ primStep.univ = 1 (since primStep is a prob measure).
      -- And ∫ h₂ ≥ 0. So ∫ h₁ ≤ 1 ≤ ε₂ ≤ ε (chain of ≤).
      -- Need: ε₂ ≤ ε. From Hε: ε₁ + ε₂ ≤ ε, hence ε₂ ≤ ε.
      have hε₂_gt : 1 ≤ ε₂ := (_root_.not_le.mp hε₂).le
      have hε₂_le_ε : ε₂ ≤ ε := _root_.le_trans (by exact _root_.le_add_self) Hε
      have h_lhs : (∫⁻ a, h₁ a ∂(primStep ⟨e₁, σ₁⟩)) ≤ 1 := by
        calc (∫⁻ a, h₁ a ∂(primStep ⟨e₁, σ₁⟩))
            ≤ ∫⁻ _, 1 ∂(primStep ⟨e₁, σ₁⟩) := MeasureTheory.lintegral_mono Hh₁
          _ = (primStep ⟨e₁, σ₁⟩) .univ := by simp
          _ ≤ 1 := primStep_univ_le_one _
      calc (∫⁻ a, h₁ a ∂(primStep ⟨e₁, σ₁⟩))
          ≤ 1 := h_lhs
        _ ≤ ε₂ := hε₂_gt
        _ ≤ ε := hε₂_le_ε
        _ ≤ _ := le_add_self
  iapply (progCoupl_steps_adv' (Hred := Hred) (Hred' := Hred')
    (X₂ := Y) HY_bnd HY_exp)
  iintro %e₂ %σ₂ %e₂' %σ₂'
  simp only [Y]
  split_ifs with h
  · iapply Hcnt $$ %e₂ %σ₂ %e₂' %σ₂'
    ipure_intro; exact h.1
  · imodintro
    iexact H1F

/-- `prog_coupl_step_l_erasable_adv` — LHS takes one program step, RHS stays
at `e₁'` but its state is sampled from an erasable `μ₁'`. Adversarial `X₂`
indexed by LHS-cfg and RHS-state. -/
theorem progCoupl_step_l_erasable_adv {e₁ : (Exp rT)} {σ₁ : (State rT)} {e₁' : (Exp rT)} {σ₁' : (State rT)}
    {μ₁' : MeasureTheory.Measure (State rT)} {ε : ENNReal}
    {Z : (Exp rT) → (State rT) → (Exp rT) → (State rT) → ENNReal → IProp GF}
    {X₂ : (Cfg rT) → (State rT) → ENNReal}
    (Hred : Reducible e₁ σ₁)
    (Heras : Erasable μ₁' σ₁')
    (Hbnd : ∀ ρ₁ σ₂', X₂ ρ₁ σ₂' ≤ 1)
    (Hcpl : ∀ (h₁ h₂ : (Cfg rT) → ENNReal),
        (∀ a, h₁ a ≤ 1) → (∀ b, h₂ b ≤ 1) →
        (∀ a b, h₁ a ≤ h₂ b + X₂ a b.state) →
        (∫⁻ a, h₁ a ∂(primStep ⟨e₁, σ₁⟩)) ≤
          (∫⁻ b, h₂ b ∂(μ₁'.bind (fun σ => MeasureTheory.Measure.dirac ⟨e₁', σ⟩))) + ε) :
    iprop((□ ∀ e₂ σ₂ e₂' σ₂', Z e₂ σ₂ e₂' σ₂' 1) ∗
          (∀ (e₂ : (Exp rT)) (σ₂ : (State rT)) (σ₂' : (State rT)),
            |={∅}=> Z e₂ σ₂ e₁' σ₂' (X₂ ⟨e₂, σ₂⟩ σ₂'))) ⊢@{IProp GF}
      progCoupl e₁ σ₁ e₁' σ₁' ε Z := by
  iintro ⟨#H1F, Hcnt⟩
  classical
  -- n = 0, spec doesn't step. The Y indicator: X₂ when RHS-expr is e₁', else 1.
  iexists 0, μ₁'
  iexists (fun ρ₁ ρ₂ => if ρ₂.expr = e₁' then X₂ ρ₁ ρ₂.state else 1)
  isplitr; · ipure_intro; exact Hred
  isplitr
  · ipure_intro
    refine ⟨1, fun ρ₁ ρ₂ => ?_⟩
    show (if ρ₂.expr = e₁' then X₂ ρ₁ ρ₂.state else 1) ≤ 1
    split_ifs with h
    · exact Hbnd _ _
    · exact _root_.le_refl _
  isplitr
  · ipure_intro
    intro h₁ h₂ Hh₁ Hh₂ Hh₁h₂
    simp only [pexecN_zero]
    -- Goal: ∫ h₁ ∂primStep ≤ ∫ h₂ ∂(μ₁'.bind (dirac ∘ ⟨e₁', ·⟩)) + ε.
    -- The RHS integral is supported on {b | b.expr = e₁'}. Use lintegral_map
    -- to rewrite it as ∫ (h₂ ∘ ⟨e₁', ·⟩) ∂μ₁'. Then apply Hcpl with
    -- h₂'(b) := h₂ ⟨e₁', b.state⟩ which satisfies the pointwise bound.
    rw [MeasureTheory.Measure.bind_dirac_eq_map _ Measurable.of_discrete,
        MeasureTheory.lintegral_map Measurable.of_discrete Measurable.of_discrete]
    -- Now: ∫ h₁ ∂primStep ≤ ∫ (fun σ => h₂ ⟨e₁', σ⟩) ∂μ₁' + ε.
    -- We need: apply Hcpl with the "pulled-back" h₂.
    -- Hcpl is stated as: ∫ h₁ ∂primStep ≤ ∫ h₂' ∂(μ₁'.bind (dirac ∘ ⟨e₁', ·⟩)) + ε,
    -- where the h₂' satisfies Hh₁h₂' : h₁ a ≤ h₂' b + X₂ a b.state for all a, b.
    -- We'll invoke Hcpl with h₂' := fun b => h₂ ⟨e₁', b.state⟩. That way
    -- h₂' b = h₂ ⟨e₁', b.state⟩ everywhere, and Hcpl's conclusion integrates
    -- against μ₁'.bind, which we map back.
    let h₂' : (Cfg rT) → ENNReal := fun b => h₂ ⟨e₁', b.state⟩
    have Hh₂' : ∀ b, h₂' b ≤ 1 := fun _ => Hh₂ _
    have Hh₁h₂' : ∀ a b, h₁ a ≤ h₂' b + X₂ a b.state := by
      intro a b
      have := Hh₁h₂ a ⟨e₁', b.state⟩
      simpa using this
    have := Hcpl h₁ h₂' Hh₁ Hh₂' Hh₁h₂'
    rw [MeasureTheory.Measure.bind_dirac_eq_map _ Measurable.of_discrete,
        MeasureTheory.lintegral_map Measurable.of_discrete Measurable.of_discrete] at this
    exact this
  isplitr; · ipure_intro; exact Heras
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
theorem progCoupl_step_l_erasable {e₁ : (Exp rT)} {σ₁ : (State rT)} {e₁' : (Exp rT)} {σ₁' : (State rT)}
    {μ₁' : MeasureTheory.Measure (State rT)} {ε₁ ε₂ ε : ENNReal}
    {Z : (Exp rT) → (State rT) → (Exp rT) → (State rT) → ENNReal → IProp GF}
    {R : (Cfg rT) → (State rT) → Prop}
    (Hε : ε₁ + ε₂ ≤ ε)
    (Hred : Reducible e₁ σ₁)
    (Hcpl : AddCoupl ε₁ {p : (Cfg rT) × (State rT) | R p.1 p.2} (primStep ⟨e₁, σ₁⟩) μ₁')
    (Heras : Erasable μ₁' σ₁') :
    iprop((□ ∀ e₂ σ₂ e₂' σ₂', Z e₂ σ₂ e₂' σ₂' 1) ∗
          (∀ (e₂ : (Exp rT)) (σ₂ : (State rT)) (σ₂' : (State rT)),
            (⌜R ⟨e₂, σ₂⟩ σ₂'⌝) -∗ |={∅}=>
              Z e₂ σ₂ e₁' σ₂' ε₂)) ⊢@{IProp GF}
      progCoupl e₁ σ₁ e₁' σ₁' ε Z := by
  iintro ⟨#H1F, Hcnt⟩
  classical
  -- Y: ε₂ when R ρ₁ σ₂' ∧ ε₂ ≤ 1, else 1.
  let Y : (Cfg rT) → (State rT) → ENNReal := fun ρ₁ σ₂' =>
    if R ρ₁ σ₂' ∧ ε₂ ≤ 1 then ε₂ else 1
  have HY_bnd : ∀ ρ₁ σ₂', Y ρ₁ σ₂' ≤ 1 := fun ρ₁ σ₂' => by
    simp only [Y]; split_ifs with h; exacts [h.2, _root_.le_refl _]
  have HY_exp : ∀ (h₁ h₂ : (Cfg rT) → ENNReal),
      (∀ a, h₁ a ≤ 1) → (∀ b, h₂ b ≤ 1) →
      (∀ a b, h₁ a ≤ h₂ b + Y a b.state) →
      (∫⁻ a, h₁ a ∂(primStep ⟨e₁, σ₁⟩)) ≤
        (∫⁻ b, h₂ b ∂(μ₁'.bind (fun σ => MeasureTheory.Measure.dirac ⟨e₁', σ⟩))) + ε := by
    intro h₁ h₂ Hh₁ Hh₂ Hh₁h₂
    by_cases hε₂ : ε₂ ≤ 1
    · -- Apply Hcpl (AddCoupl ε₁ R) with (h₁, (h₂ ∘ ⟨e₁', ·⟩) + ε₂ ⊓ 1).
      let h₃ : (State rT) → ENNReal := fun σ => (h₂ ⟨e₁', σ⟩ + ε₂) ⊓ 1
      have Hh₃ : ∀ σ, h₃ σ ≤ 1 := fun _ => inf_le_right
      have Hh₁h₃ : ∀ a b, R a b → h₁ a ≤ h₃ b + 0 := by
        intro a b HR
        rw [add_zero]
        simp only [h₃, le_inf_iff]
        refine ⟨?_, Hh₁ a⟩
        have := Hh₁h₂ a ⟨e₁', b⟩
        simp only [Y, if_pos (And.intro HR hε₂)] at this
        exact this
      have HAdd : (∫⁻ a, h₁ a ∂(primStep ⟨e₁, σ₁⟩)) ≤
          (∫⁻ b, h₃ b ∂μ₁') + ε₁ := by
        have := Hcpl ⟨h₁, Measurable.of_discrete, Hh₁⟩ ⟨h₃, Measurable.of_discrete, Hh₃⟩
          (fun {a b} (hab : R a b) => by
            have := Hh₁h₃ a b hab
            rw [add_zero] at this
            exact this)
        simpa using this
      have hμ₁_mass : μ₁' .univ = 1 := Erasable.mass Heras
      calc (∫⁻ a, h₁ a ∂(primStep ⟨e₁, σ₁⟩))
          ≤ (∫⁻ b, h₃ b ∂μ₁') + ε₁ := HAdd
        _ ≤ (∫⁻ σ, (h₂ ⟨e₁', σ⟩ + ε₂) ∂μ₁') + ε₁ := by
              gcongr with b; simp only [h₃]; exact inf_le_left
        _ = (∫⁻ σ, h₂ ⟨e₁', σ⟩ ∂μ₁') + ε₂ * μ₁' .univ + ε₁ := by
              rw [MeasureTheory.lintegral_add_right _ measurable_const,
                  MeasureTheory.lintegral_const, mul_comm]
        _ = (∫⁻ σ, h₂ ⟨e₁', σ⟩ ∂μ₁') + ε₂ + ε₁ := by rw [hμ₁_mass, mul_one]
        _ ≤ (∫⁻ σ, h₂ ⟨e₁', σ⟩ ∂μ₁') + ε := by
              rw [add_assoc, add_comm ε₂ ε₁]; gcongr
        _ = (∫⁻ b, h₂ b ∂(μ₁'.bind (fun σ => MeasureTheory.Measure.dirac ⟨e₁', σ⟩))) + ε := by
              congr 1
              rw [MeasureTheory.Measure.bind_dirac_eq_map _ Measurable.of_discrete,
                  MeasureTheory.lintegral_map Measurable.of_discrete Measurable.of_discrete]
    · have hε₂_gt : 1 ≤ ε₂ := (_root_.not_le.mp hε₂).le
      have hε₂_le_ε : ε₂ ≤ ε := _root_.le_trans (by exact _root_.le_add_self) Hε
      calc (∫⁻ a, h₁ a ∂(primStep ⟨e₁, σ₁⟩))
          ≤ ∫⁻ _, 1 ∂(primStep ⟨e₁, σ₁⟩) := MeasureTheory.lintegral_mono Hh₁
        _ = (primStep ⟨e₁, σ₁⟩) .univ := by simp
        _ ≤ 1 := primStep_univ_le_one _
        _ ≤ ε₂ := hε₂_gt
        _ ≤ ε := hε₂_le_ε
        _ ≤ _ := _root_.le_add_self
  iapply (progCoupl_step_l_erasable_adv (Hred := Hred) (Heras := Heras)
    (X₂ := Y) HY_bnd HY_exp)
  isplitr
  · iintro !> %e₂ %σ₂ %e₂' %σ₂'; iexact H1F
  iintro %e₂ %σ₂ %σ₂'
  simp only [Y]
  split_ifs with h
  · iapply Hcnt $$ %e₂ %σ₂ %σ₂'
    ipure_intro; exact h.1
  · imodintro
    iexact H1F

/-- `prog_coupl_step_l_dret` — LHS-only step with spec staying at exactly
`(e₁', σ₁')` (RHS is `dirac σ₁'`). Specialization of `_step_l_erasable`. -/
theorem progCoupl_step_l_dret {e₁ : (Exp rT)} {σ₁ : (State rT)} {e₁' : (Exp rT)} {σ₁' : (State rT)}
    {ε₁ ε₂ ε : ENNReal} {R : (Cfg rT) → (State rT) → Prop}
    {Z : (Exp rT) → (State rT) → (Exp rT) → (State rT) → ENNReal → IProp GF}
    (Hε : ε₁ + ε₂ ≤ ε)
    (Hred : Reducible e₁ σ₁)
    (Hcpl : AddCoupl ε₁ {p : (Cfg rT) × (State rT) | R p.1 p.2}
              (primStep ⟨e₁, σ₁⟩) (MeasureTheory.Measure.dirac σ₁')) :
    iprop((□ ∀ e₂ σ₂ e₂' σ₂', Z e₂ σ₂ e₂' σ₂' 1) ∗
          (∀ (e₂ : (Exp rT)) (σ₂ : (State rT)),
            (⌜R ⟨e₂, σ₂⟩ σ₁'⌝) -∗ |={∅}=>
              Z e₂ σ₂ e₁' σ₁' ε₂)) ⊢@{IProp GF}
      progCoupl e₁ σ₁ e₁' σ₁' ε Z := by
  iintro ⟨#H1F, H⟩
  classical
  -- Use pos_R to force σ₂' = σ₁' in the relation (since dirac σ₁' is supported
  -- only at σ₁').
  have Hpos := AddCoupl.pos_R Hcpl
  -- Hpos : AddCoupl ε₁ {p | R p.1 p.2 ∧ (primStep ⟨e₁,σ₁⟩) {p.1} ≠ 0 ∧
  --                              (dirac σ₁') {p.2} ≠ 0} ...
  -- The last condition forces p.2 = σ₁'.
  -- Redefine the relation to include "σ₂' = σ₁'":
  have HcplR : AddCoupl ε₁ {p : (Cfg rT) × (State rT) | R p.1 p.2 ∧ p.2 = σ₁'}
      (primStep ⟨e₁, σ₁⟩) (MeasureTheory.Measure.dirac σ₁') := by
    refine AddCoupl.mono_rel ?_ Hpos
    rintro ⟨ρ, σ⟩ ⟨HR, _, hσ⟩
    refine ⟨HR, ?_⟩
    -- hσ : dirac σ₁' {σ} ≠ 0 → σ = σ₁'
    by_contra hne
    apply hσ
    rw [MeasureTheory.Measure.dirac_apply' _ MeasurableSet.of_discrete]
    simp [Ne.symm hne]
  iapply (progCoupl_step_l_erasable (μ₁' := MeasureTheory.Measure.dirac σ₁')
    (Hε := Hε) (Hred := Hred)
    (R := fun ρ σ => R ρ σ ∧ σ = σ₁') HcplR (Erasable.dret σ₁'))
  isplitr
  · iintro !> %e₂ %σ₂ %e₂' %σ₂'; iexact H1F
  iintro %e₂ %σ₂ %σ₂' %HR'
  obtain ⟨HR, rfl⟩ := HR'
  iapply H $$ %e₂ %σ₂ %HR

/-- `prog_coupl_step_l` — pure LHS-step, any positive-measure primStep
successor lets us land. Mirrors Rocq's `prog_coupl_step_l`. -/
theorem progCoupl_step_l {e₁ : (Exp rT)} {σ₁ : (State rT)} {e₁' : (Exp rT)} {σ₁' : (State rT)}
    {ε : ENNReal} {Z : (Exp rT) → (State rT) → (Exp rT) → (State rT) → ENNReal → IProp GF}
    (Hred : Reducible e₁ σ₁) :
    iprop((□ ∀ e₂ σ₂ e₂' σ₂', Z e₂ σ₂ e₂' σ₂' 1) ∗
          (∀ (e₂ : (Exp rT)) (σ₂ : (State rT)),
            (⌜0 < primStep ⟨e₁, σ₁⟩ {⟨e₂, σ₂⟩}⌝) -∗ |={∅}=>
              Z e₂ σ₂ e₁' σ₁' ε)) ⊢@{IProp GF}
      progCoupl e₁ σ₁ e₁' σ₁' ε Z := by
  iintro ⟨#H1F, H⟩
  classical
  -- Build AddCoupl 0 R (primStep ⟨e₁,σ₁⟩) (dirac σ₁') via pos_R, where
  -- R ρ₁ _ := 0 < primStep {ρ₁}.
  have hprob_lhs : (primStep ⟨e₁, σ₁⟩) .univ = 1 := by
    haveI := prim_step_mass ⟨e₁, σ₁⟩ Hred
    exact MeasureTheory.IsProbabilityMeasure.measure_univ
  have hprob_rhs : (MeasureTheory.Measure.dirac σ₁' : MeasureTheory.Measure (State rT)) .univ = 1 := by
    simp
  have Htrivial : AddCoupl 0 Set.univ (primStep ⟨e₁, σ₁⟩)
      (MeasureTheory.Measure.dirac σ₁') :=
    RelCoupl.exact (RelCoupl.trivial hprob_lhs hprob_rhs)
  have Hpos := AddCoupl.pos_R Htrivial
  have Hε : (0 : ENNReal) + ε ≤ ε := by rw [zero_add]
  have HcplR : AddCoupl 0 {p : (Cfg rT) × (State rT) | (fun ρ _ => 0 < primStep ⟨e₁, σ₁⟩ {ρ}) p.1 p.2}
      (primStep ⟨e₁, σ₁⟩) (MeasureTheory.Measure.dirac σ₁') := by
    refine AddCoupl.mono_rel ?_ Hpos
    rintro ⟨ρ, σ⟩ ⟨_, hρ, _⟩
    exact pos_iff_ne_zero.mpr hρ
  iapply (progCoupl_step_l_dret (ε₁ := 0) (ε₂ := ε)
    (R := fun ρ _ => 0 < primStep ⟨e₁, σ₁⟩ {ρ})
    (Hε := Hε) (Hred := Hred) HcplR)
  isplitr
  · iintro !> %e₂ %σ₂ %e₂' %σ₂'; iexact H1F
  iintro %e₂ %σ₂ %Hpos'
  iapply H $$ %e₂ %σ₂ %Hpos'

/-! ## WP — outer OFE instances and `IntoVal`-style value intros -/

/-- General value introduction: from `e.toVal? = some v` and `|={E}=> Φ v`,
conclude `wp E e Φ`. -/
theorem wp_value_fupd_of_toVal {E : CoPset} {e : (Exp rT)} {v : (Val rT)}
    {Φ : (Val rT) → IProp GF} (h : e.toVal? = some v) :
    iprop(|={E}=> Φ v) ⊢@{IProp GF} wp E e Φ := by
  rw [← Exp.ofVal_of_toVal_some h]
  exact wp_value_fupd

/-- `wp` is non-expansive in its post. Proof mirrors Rocq's `wp_ne`:
strong induction on OFE distance `n`, `wp_unfold` on both sides, structural
walk through `wpPre` (same shape as `wpPre_contractive`), and IH at `m < n`
under the `▷` in the non-value branch. -/
theorem wp_ne_aux {E : CoPset} {e : (Exp rT)} {Φ Ψ : (Val rT) → IProp GF} {n : Nat}
    (HΦ : ∀ v, Φ v ≡{n}≡ Ψ v) : wp (GF := GF) E e Φ ≡{n}≡ wp E e Ψ := by
  induction n using Nat.strong_induction_on generalizing e Φ Ψ with
  | _ n IH =>
    have heq1 : wp (GF := GF) E e Φ ≡{n}≡ wpPre wp E e Φ :=
      OFE.equiv_dist.mp wp_unfold n
    have heq2 : wp (GF := GF) E e Ψ ≡{n}≡ wpPre wp E e Ψ :=
      OFE.equiv_dist.mp wp_unfold n
    refine heq1.trans (OFE.Dist.trans ?_ heq2.symm)
    -- Goal: wpPre wp E e Φ ≡{n}≡ wpPre wp E e Ψ. Structural walk.
    refine forall_ne fun σ₁ => ?_
    refine forall_ne fun e₁' => ?_
    refine forall_ne fun σ₁' => ?_
    refine forall_ne fun ε₁ => ?_
    refine wand_ne.ne (.of_eq rfl) ?_
    refine BIFUpdate.ne.ne ?_
    refine least_fixpoint_ne_outer (fun Ψ' s => ?_) (.of_eq rfl)
    refine or_ne.ne (.of_eq rfl) ?_
    refine or_ne.ne ?_ (.of_eq rfl)
    cases htv : e.toVal? with
    | some v =>
      refine BIFUpdate.ne.ne ?_
      refine sep_ne.ne (.of_eq rfl) ?_
      refine sep_ne.ne (.of_eq rfl) ?_
      refine sep_ne.ne (.of_eq rfl) ?_
      exact HΦ v
    | none =>
      refine progCoupl_ne fun e₃ σ₃ e₃' σ₃' ε₃ => ?_
      apply Contractive.distLater_dist (f := later)
      intro m Hm
      refine specCoupl_ne fun σ₄ ρ'' ε₄ => ?_
      refine BIFUpdate.ne.ne ?_
      refine sep_ne.ne (.of_eq rfl) ?_
      refine sep_ne.ne (.of_eq rfl) ?_
      refine sep_ne.ne (.of_eq rfl) ?_
      exact IH m Hm (fun v => OFE.Dist.lt (HΦ v) Hm)

instance wp_ne {E : CoPset} {e : (Exp rT)} :
    NonExpansive ((wp (GF := GF)) E e) where
  ne _ _ _ H := wp_ne_aux H

-- TODO: `wp_contractive` — `wp` is `Contractive` in its post when the head
-- is *not* a value. Needs structural `wp_unfold` walk under the
-- `e.toVal? = none` branch; dual to `wpPre_contractive` restricted to `none`.

/-! ## WP — structural lemmas (deferred, need more infra or Löb) -/

/-- The Löb-induction statement for `wp_bind`. -/
noncomputable abbrev wpBindStmt (K : (Ectx rT)) : IProp GF :=
  iprop(∀ (E : CoPset) (e : (Exp rT)) (Φ : (Val rT) → IProp GF),
    wp E e (fun v => wp E (K.fill (Exp.ofVal v)) Φ) -∗ wp E (K.fill e) Φ)

/-- `wp_bind` specialized to ProbLang's concrete `(Ectx rT)`.

Proved via Löb induction: under `loeb_wand`, we case-split on `e.toVal?`.
* Value case (`some v`): `e = ofVal v`, so `K.fill e = K.fill (ofVal v)`.
  After `fupd_specCoupl`, unfold the inner `wp E (K.fill (ofVal v)) Φ` directly.
* Non-value case: lift the inner `progCoupl` from `e` to `K.fill e` via
  `progCoupl_ctx_bind`, then rewrite the inner `wp E e₃ (λ v => wp E (K.fill (ofVal v)) Φ)`
  to `wp E (K.fill e₃) Φ` using the IH under `▷`. -/
theorem wp_bind {K : (Ectx rT)} {E : CoPset} {e : (Exp rT)} {Φ : (Val rT) → IProp GF} :
    wp E e (fun v => wp E (K.fill (Exp.ofVal v)) Φ) ⊢@{IProp GF}
      wp E (K.fill e) Φ := by
  have Hloeb : ⊢@{IProp GF} wpBindStmt (GF := GF) K := by
    iapply loeb_wand
    iintro !>
    iintro IH
    iintro %E' %e' %Φ' HW
    iapply wp_unfold
    unfold wpPre
    iintro %σ₁ %e₁' %σ₁' %ε₁ ⟨Hσ, Hs, Hε⟩
    ihave HW' := (BI.equiv_iff.mp wp_unfold).1 $$ HW
    ispecialize HW' $$ %σ₁ %e₁' %σ₁' %ε₁ [Hσ Hs Hε]
    · isplitl [Hσ]; · iassumption
      isplitl [Hs] <;> iassumption
    imod HW'
    imodintro
    iapply specCoupl_bind (E1 := ∅) (E2 := ∅) Std.LawfulSet.subset_refl
    isplitr [HW']
    swap
    · iexact HW'
    iintro %σ₂ %ρ₂ %ε₂ HBody
    -- HBody is the inner match at e'.toVal?.
    cases htv : e'.toVal? with
    | some v =>
      -- HBody : |={∅, E'}=> stateInterp (rT := rT) σ₂ ∗ specInterp ρ₂ ∗ errInterp (rT := rT) ε₂ ∗
      --                      wp E' (K.fill (ofVal v)) Φ'
      -- Note: e' = ofVal v, so K.fill e' = K.fill (ofVal v). The outer goal's
      -- match is on (K.fill e').toVal? = (K.fill (ofVal v)).toVal?.
      iapply fupd_specCoupl
      have heq : e' = Exp.ofVal v := (Exp.ofVal_of_toVal_some htv).symm
      rw [heq]
      imod HBody with ⟨Hσ', Hs', Hε', HInner⟩
      ihave HInner' := (BI.equiv_iff.mp wp_unfold).1 $$ HInner
      ispecialize HInner' $$ %σ₂ %ρ₂.expr %ρ₂.state %ε₂ [Hσ' Hs' Hε']
      · isplitl [Hσ']; · iassumption
        isplitl [Hs'] <;> iassumption
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
      -- Reduce the outer match using hKfillnone.
      -- Goal: specCoupl ∅ σ₂ ρ₂.expr ρ₂.state ε₂
      --         (match (K.fill e').toVal? with | some v => ... | none => progCoupl (K.fill e') ...).
      iapply specCoupl_ret
      simp only [hKfillnone]
      -- Goal: progCoupl (K.fill e') σ₂ ρ₂.expr ρ₂.state ε₂
      --         (fun e₃ σ₃ e₃' σ₃' ε₃ => ▷ specCoupl ∅ σ₃ e₃' σ₃' ε₃
      --           (fun σ₄ ρ'' ε₄ => |={∅, E'}=>
      --             stateInterp (rT := rT) σ₄ ∗ specInterp ρ'' ∗ errInterp (rT := rT) ε₄ ∗ wp E' e₃ Φ'))
      --
      -- HBody reduces via htv to:
      -- progCoupl e' σ₂ ρ₂.expr ρ₂.state ε₂
      --   (fun e₃ σ₃ e₃' σ₃' ε₃ => ▷ specCoupl ∅ σ₃ e₃' σ₃' ε₃
      --     (fun σ₄ ρ'' ε₄ => |={∅, E'}=>
      --       stateInterp (rT := rT) σ₄ ∗ specInterp ρ'' ∗ errInterp (rT := rT) ε₄ ∗
      --         wp E' e₃ (fun v => wp E' (K.fill (ofVal v)) Φ')))
      --
      -- Need to: (1) use progCoupl_ctx_bind to lift e' → K.fill e',
      --          (2) rewrite inner wp E' e₃ (...) to wp E' (K.fill e₃) Φ' using IH.
      -- Do (2) first via progCoupl_mono, then (1) via progCoupl_ctx_bind.
      iapply (progCoupl_ctx_bind (K := K) (e₁ := e') (Z := fun e₃ σ₃ e₃' σ₃' ε₃ =>
        iprop(▷ specCoupl ∅ σ₃ e₃' σ₃' ε₃ (fun σ₄ ρ'' ε₄ =>
          iprop(|={∅, E'}=>
            stateInterp (rT := rT) σ₄ ∗ SpecUpdateGS.specInterp (rT := rT) ρ'' ∗ errInterp (rT := rT) ε₄ ∗
              wp E' e₃ Φ')))) hv)
      isplitr
      · -- Catch-all: Z at ε = 1 via specCoupl_err_ge_1.
        iintro !> %e₃ %σ₃ %e₃' %σ₃'
        iintro !>
        iapply (specCoupl_err_ge_1 (hε := _root_.le_refl _))
      -- Continuation: transform HBody's inner wp via IH.
      iapply (progCoupl_mono (Z₁ := fun e₃ σ₃ e₃' σ₃' ε₃ =>
        iprop(▷ specCoupl ∅ σ₃ e₃' σ₃' ε₃ (fun σ₄ ρ'' ε₄ =>
          iprop(|={∅, E'}=>
            stateInterp (rT := rT) σ₄ ∗ SpecUpdateGS.specInterp (rT := rT) ρ'' ∗ errInterp (rT := rT) ε₄ ∗
              wp E' e₃ (fun v => wp E' (K.fill (Exp.ofVal v)) Φ'))))))
      isplitr [HBody]
      swap
      · iexact HBody
      iintro %e₃ %σ₃ %e₃' %σ₃' %ε₃ HLater
      iintro !>
      iapply specCoupl_mono_spatial
      isplitr [HLater]
      swap
      · iexact HLater
      iintro %σ₄ %ρ₄ %ε₄ HF
      imod HF with ⟨Hσ', Hs', Hε', HwpInner⟩
      imodintro
      isplitl [Hσ']; · iassumption
      isplitl [Hs']; · iassumption
      isplitl [Hε']; · iassumption
      -- Apply IH: wp E' e₃ (fun v => wp E' (K.fill (ofVal v)) Φ') -∗ wp E' (K.fill e₃) Φ'.
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
theorem specUpdate_wp {E : CoPset} {e : (Exp rT)} {Φ : (Val rT) → IProp GF} :
    specUpdate rT E (wp E e Φ) ⊢@{IProp GF} wp E e Φ := by
  unfold specUpdate
  iintro HS
  iapply wp_unfold
  unfold wpPre
  iintro %σ₁ %e₁' %σ₁' %ε₁ ⟨Hσ, Hs, Hε⟩
  ispecialize HS $$ %(⟨e₁', σ₁'⟩ : (Cfg rT)) Hs
  imod HS with ⟨%ρ', %n, %Hstep, Hs', HW⟩
  -- ρ' = ⟨e₂', σ₂'⟩ for some e₂', σ₂'. Need to destructure.
  cases ρ' with
  | mk e₂' σ₂' =>
    -- Hstep : pexecN n ⟨e₁', σ₁'⟩ = dirac ⟨e₂', σ₂'⟩
    -- HW : wp E e Φ
    ihave HW' := (BI.equiv_iff.mp wp_unfold).1 $$ HW
    ispecialize HW' $$ %σ₁ %e₂' %σ₂' %ε₁ [Hσ Hs' Hε]
    · isplitl [Hσ]; · iassumption
      isplitl [Hs'] <;> iassumption
    imod HW'
    imodintro
    iapply specCoupl_steps_det Hstep
    iexact HW'

/-- Löb-induction statement for `wp_specUpdate`. -/
noncomputable abbrev wpSpecUpdateStmt : IProp GF :=
  iprop(∀ (E : CoPset) (e : (Exp rT)) (Φ : (Val rT) → IProp GF),
    wp E e (fun v => specUpdate rT E (Φ v)) -∗ wp E e Φ)

/-- Dually to `specUpdate_wp`, a `specUpdate` in the postcondition absorbs
into `wp`. Löb induction matching the Rocq proof. -/
theorem wp_specUpdate {E : CoPset} {e : (Exp rT)} {Φ : (Val rT) → IProp GF} :
    wp E e (fun v => specUpdate rT E (Φ v)) ⊢@{IProp GF} wp E e Φ := by
  have Hloeb : ⊢@{IProp GF} wpSpecUpdateStmt (rT := rT) (GF := GF) := by
    iapply loeb_wand
    iintro !>
    iintro IH
    iintro %E' %e' %Φ' HW
    iapply wp_unfold
    unfold wpPre
    iintro %σ₁ %e₁' %σ₁' %ε₁ ⟨Hσ, Hs, Hε⟩
    ihave HW' := (BI.equiv_iff.mp wp_unfold).1 $$ HW
    ispecialize HW' $$ %σ₁ %e₁' %σ₁' %ε₁ [Hσ Hs Hε]
    · isplitl [Hσ]; · iassumption
      isplitl [Hs] <;> iassumption
    imod HW'
    imodintro
    iapply specCoupl_bind (E1 := ∅) (E2 := ∅) Std.LawfulSet.subset_refl
    isplitr [HW']
    swap
    · iexact HW'
    iintro %σ₂ %ρ₂ %ε₂ HBody
    cases htv : e'.toVal? with
    | some v =>
      -- HBody : |={∅, E'}=> stateInterp (rT := rT) σ₂ ∗ specInterp ρ₂ ∗ errInterp (rT := rT) ε₂ ∗
      --                      specUpdate rT E' (Φ' v).
      -- Goal: specCoupl ∅ σ₂ ρ₂.expr ρ₂.state ε₂ (match some v with ...)
      --     = specCoupl ∅ σ₂ ... (fun σ' ρ' ε' => |={∅, E'}=> ... ∗ Φ' v).
      -- Strategy: use `fupd_specCoupl` to introduce `|={∅}=> goal`, then absorb
      -- HBody under that. Then open ∅ via BIFUpdate.subset, close via Hclose.
      iapply fupd_specCoupl
      imod HBody with ⟨Hσ', Hs', Hε', HUpd⟩
      ispecialize HUpd $$ %ρ₂ Hs'
      imod HUpd with ⟨%ρ₃, %n, %Hstep, Hs'', HΦv⟩
      cases ρ₃ with
      | mk e₃' σ₃' =>
        -- Now in mask E' (from HBody) with the outer `|={∅}=>` still open.
        -- Close back to ∅ via a new introduction.
        imod (BIFUpdate.subset (E1 := E') (E2 := ∅) Std.LawfulSet.empty_subset)
          with Hclose
        imodintro
        iapply specCoupl_steps_det Hstep
        iapply specCoupl_ret
        imod Hclose
        imodintro
        isplitl [Hσ']; · iassumption
        isplitl [Hs'']; · iassumption
        isplitl [Hε'] <;> iassumption
    | none =>
      iapply specCoupl_ret
      iapply (progCoupl_mono (Z₁ := fun e₃ σ₃ e₃' σ₃' ε₃ =>
        iprop(▷ specCoupl ∅ σ₃ e₃' σ₃' ε₃ (fun σ₄ ρ'' ε₄ =>
          iprop(|={∅, E'}=>
            stateInterp (rT := rT) σ₄ ∗ SpecUpdateGS.specInterp (rT := rT) ρ'' ∗ errInterp (rT := rT) ε₄ ∗
              wp E' e₃ (fun v => specUpdate rT E' (Φ' v)))))))
      isplitr [HBody]
      swap
      · iexact HBody
      iintro %e₃ %σ₃ %e₃' %σ₃' %ε₃ HLater
      iintro !>
      iapply specCoupl_mono_spatial
      isplitr [HLater]
      swap
      · iexact HLater
      iintro %σ₄ %ρ₄ %ε₄ HF
      imod HF with ⟨Hσ', Hs', Hε', HwpInner⟩
      imodintro
      isplitl [Hσ']; · iassumption
      isplitl [Hs']; · iassumption
      isplitl [Hε']; · iassumption
      iapply IH $$ %E' %e₃ %Φ' HwpInner
  iapply Hloeb $$ %E %e %Φ

/-! ## WP — derived framing lemmas (all from `wp_strong_mono'`) -/

/-- Löb invariant for `wp_frame_l`. -/
noncomputable abbrev wpFrameLStmt : IProp GF :=
  iprop(∀ (E : CoPset) (e : (Exp rT)) (R : IProp GF) (Φ : (Val rT) → IProp GF),
    R -∗ wp E e Φ -∗ wp E e (fun v => iprop(R ∗ Φ v)))

/-- Left-frame: a spatial `R` can be carried through a `wp`. Proved via Löb
induction directly — `wp_wand` isn't usable because it requires a persistent
wand that can't capture the spatial `R`. -/
theorem wp_frame_l {E : CoPset} {e : (Exp rT)} {R : IProp GF} {Φ : (Val rT) → IProp GF} :
    iprop(R ∗ wp E e Φ) ⊢@{IProp GF} wp E e (fun v => iprop(R ∗ Φ v)) := by
  have Hloeb : ⊢@{IProp GF} wpFrameLStmt (rT := rT) (GF := GF) := by
    iapply loeb_wand
    iintro !>
    iintro IH
    iintro %E' %e' %R' %Φ'
    iintro HR HW
    iapply wp_unfold
    unfold wpPre
    iintro %σ₁ %e₁' %σ₁' %ε₁ ⟨Hσ, Hs, Hε⟩
    ihave HW' := (BI.equiv_iff.mp wp_unfold).1 $$ HW
    ispecialize HW' $$ %σ₁ %e₁' %σ₁' %ε₁ [Hσ Hs Hε]
    · isplitl [Hσ]; · iassumption
      isplitl [Hs] <;> iassumption
    imod HW'
    imodintro
    iapply specCoupl_mono_spatial
    isplitr [HW']
    swap
    · iexact HW'
    iintro %σ₂ %ρ₂ %ε₂ HBody
    cases htv : e'.toVal? with
    | some v =>
      -- HBody : (match e'.toVal? = some v → |={∅, E'}=> ...)
      imod HBody with ⟨Hσ', Hs', Hε', HΦv⟩
      simp only []
      imodintro
      iframe
    | none =>
      iapply progCoupl_mono
      isplitr [HBody]
      swap
      · iexact HBody
      iintro %e₃ %σ₃ %e₃' %σ₃' %ε₃ HLater
      iintro !>
      iapply specCoupl_mono_spatial
      isplitr [HLater]
      swap
      · iexact HLater
      iintro %σ₄ %ρ₄ %ε₄ HFinal
      imod HFinal with ⟨Hσ', Hs', Hε', HwpInner⟩
      imodintro
      iframe
      iapply IH $$ %E' %e₃ %R' %Φ' HR HwpInner
  iintro ⟨HR, HW⟩
  iapply Hloeb $$ %E %e %R %Φ HR HW

/-- Right-frame: symmetric variant, derived from `wp_frame_l` + `wp_wand`. -/
theorem wp_frame_r {E : CoPset} {e : (Exp rT)} {R : IProp GF} {Φ : (Val rT) → IProp GF} :
    iprop(wp E e Φ ∗ R) ⊢@{IProp GF} wp E e (fun v => iprop(Φ v ∗ R)) := by
  iintro ⟨HW, HR⟩
  iapply (wp_wand (Φ := fun v => iprop(R ∗ Φ v)) (Ψ := fun v => iprop(Φ v ∗ R)))
  isplitl [HW HR]
  · iapply (wp_frame_l (R := R) (Φ := Φ))
    isplitl [HR]; · iassumption
    iexact HW
  iintro !> %v ⟨HRv, HΦv⟩
  isplitl [HΦv]; · iassumption
  iassumption

-- `wp_frame_step_l` and `wp_frame_step_r` are proved below, after
-- `wp_step_fupd` (which they depend on).

/-- Frame-wand: if `wp`'s post consumes `R` to produce `Φ`, and we hold `R`
spatially outside, we can discharge `R` to conclude `wp` at `Φ`. -/
theorem wp_frame_wand {E : CoPset} {e : (Exp rT)} {R : IProp GF} {Φ : (Val rT) → IProp GF} :
    iprop(R ∗ wp E e (fun v => iprop(R -∗ Φ v))) ⊢@{IProp GF} wp E e Φ := by
  iintro ⟨HR, HW⟩
  iapply (wp_wand (Φ := fun v => iprop(R ∗ (R -∗ Φ v))) (Ψ := Φ))
  isplitl [HR HW]
  · iapply (wp_frame_l (R := R) (Φ := fun v => iprop(R -∗ Φ v)))
    isplitl [HR]; · iassumption
    iexact HW
  iintro !> %v ⟨HRv, HW'⟩
  iapply HW' $$ HRv

/-- `wp_step_fupd` — step-indexed fupd insertion. The `|={E1}[E2]▷=> P`
token delivers `P` after one step, which the inner wp's post consumes. -/
theorem wp_step_fupd {E1 E2 : CoPset} {e : (Exp rT)} {P : IProp GF} {Φ : (Val rT) → IProp GF}
    (HE : E2 ⊆ E1) (hv : e.toVal? = none) :
    iprop((|={E1, E2}=> ▷ |={E2, E1}=> P) ∗ wp E2 e (fun v => iprop(P -∗ Φ v))) ⊢@{IProp GF}
      wp E1 e Φ := by
  iintro ⟨HR, HW⟩
  iapply wp_unfold
  unfold wpPre
  iintro %σ₁ %e₁' %σ₁' %ε₁ ⟨Hσ, Hs, Hε⟩
  ihave HW' := (BI.equiv_iff.mp wp_unfold).1 $$ HW
  imod HR with HR
  ispecialize HW' $$ %σ₁ %e₁' %σ₁' %ε₁ [Hσ Hs Hε]
  · isplitl [Hσ]; · iassumption
    isplitl [Hs] <;> iassumption
  imod HW' with HW'
  imodintro
  iapply specCoupl_mono_spatial
  isplitr [HW']
  swap
  · iexact HW'
  iintro %σ₂ %ρ₂ %ε₂ HBody
  simp only [hv]
  iapply progCoupl_mono
  isplitr [HBody]
  swap
  · iexact HBody
  iintro %e₃ %σ₃ %e₃' %σ₃' %ε₃ HLater
  iintro !>
  iapply specCoupl_mono_spatial
  isplitr [HLater]
  swap
  · iexact HLater
  iintro %σ₄ %ρ₄ %ε₄ HFinal
  imod HFinal with ⟨Hσ', Hs', Hε', HwpInner⟩
  imod HR with HR
  imodintro
  isplitl [Hσ']; · iassumption
  isplitl [Hs']; · iassumption
  isplitl [Hε']; · iassumption
  iapply wp_mask_mono HE
  iapply (wp_wand (Φ := fun v => iprop(P ∗ (P -∗ Φ v))) (Ψ := Φ))
  isplitl [HwpInner HR]
  · iapply (wp_frame_l (R := P) (Φ := fun v => iprop(P -∗ Φ v)))
    isplitl [HR]; · iassumption
    iexact HwpInner
  iintro !> %v ⟨HP, HWand⟩
  iapply HWand $$ HP

/-- Step-indexed framing (left variant). Use `wp_step_fupd` with post
`R -∗ R ∗ Φ v`, via `wp_wand` to tack on the wand. -/
theorem wp_frame_step_l {E1 E2 : CoPset} {e : (Exp rT)} {R : IProp GF} {Φ : (Val rT) → IProp GF}
    (HE : E2 ⊆ E1) (hv : e.toVal? = none) :
    iprop((|={E1, E2}=> ▷ |={E2, E1}=> R) ∗ wp E2 e Φ) ⊢@{IProp GF}
      wp E1 e (fun v => iprop(R ∗ Φ v)) := by
  iintro ⟨HR, HW⟩
  iapply (wp_step_fupd (Φ := fun v => iprop(R ∗ Φ v)) HE hv)
  isplitl [HR]; · iassumption
  iapply (wp_wand (Φ := Φ) (Ψ := fun v => iprop(R -∗ R ∗ Φ v)))
  isplitl [HW]; · iassumption
  iintro !> %v HΦ HR'
  isplitl [HR']; · iassumption
  iassumption

/-- Step-indexed framing (right variant). -/
theorem wp_frame_step_r {E1 E2 : CoPset} {e : (Exp rT)} {R : IProp GF} {Φ : (Val rT) → IProp GF}
    (HE : E2 ⊆ E1) (hv : e.toVal? = none) :
    iprop(wp E2 e Φ ∗ (|={E1, E2}=> ▷ |={E2, E1}=> R)) ⊢@{IProp GF}
      wp E1 e (fun v => iprop(Φ v ∗ R)) := by
  iintro ⟨HW, HR⟩
  iapply (wp_step_fupd (Φ := fun v => iprop(Φ v ∗ R)) HE hv)
  isplitl [HR]; · iassumption
  iapply (wp_wand (Φ := Φ) (Ψ := fun v => iprop(R -∗ Φ v ∗ R)))
  isplitl [HW]; · iassumption
  iintro !> %v HΦ HR'
  isplitl [HΦ]; · iassumption
  iassumption

/-- `◇`-absorption: `◇ (wp E e Φ) ⊢ wp E e Φ`. Goes via
`◇ wp ⊢ ◇ (|={E}=> wp) ⊢ |={E}=> wp ⊢ wp`. -/
instance isExcept0_wp {E : CoPset} {e : (Exp rT)} {Φ : (Val rT) → IProp GF} :
    IsExcept0 (wp (GF := GF) E e Φ) where
  is_except0 := (except0_mono fupd_intro).trans (BIFUpdate.except0.trans fupd_wp)

/-- `iMod` on basic-update: given `|==> P`, absorb via `bupd ⊆ fupd`. -/
instance elimModal_bupd_wp {p : Bool} {E : CoPset} {e : (Exp rT)} {P : IProp GF}
    {Φ : (Val rT) → IProp GF} :
    ElimModal True p false iprop(|==> P) P (wp E e Φ) (wp E e Φ) where
  elim_modal _ := (sep_mono_l intuitionisticallyIf_elim).trans <|
    (sep_mono_l BIUpdateFUpdate.fupd_of_bupd).trans <|
    fupd_frame_r.trans <| (BIFUpdate.mono wand_elim_r).trans fupd_wp

/-- `iMod` on fancy-update at the same mask. -/
instance elimModal_fupd_wp {p : Bool} {E : CoPset} {e : (Exp rT)} {P : IProp GF}
    {Φ : (Val rT) → IProp GF} :
    ElimModal True p false iprop(|={E}=> P) P (wp E e Φ) (wp E e Φ) where
  elim_modal _ := (sep_mono_l intuitionisticallyIf_elim).trans <|
    fupd_frame_r.trans <| (BIFUpdate.mono wand_elim_r).trans fupd_wp

/-- `iMod` on `specUpdate` hypotheses absorbing into a `wp`. -/
instance elimModal_specUpdate_wp {E : CoPset} {e : (Exp rT)} {P : IProp GF}
    {Φ : (Val rT) → IProp GF} :
    ElimModal True false false (specUpdate rT E P) P (wp E e Φ) (wp E e Φ) where
  elim_modal _ := by
    simp only [Bool.false_eq_true, ↓reduceIte, intuitionisticallyIf]
    iintro ⟨HP, Hcnt⟩
    iapply specUpdate_wp
    iintro %ρ Hρ
    ispecialize HP $$ %ρ Hρ
    imod HP with ⟨%ρ', %n, %Hstep, Hρ', HPv⟩
    imodintro
    iexists ρ', n
    isplitr; · ipure_intro; exact Hstep
    isplitl [Hρ']; · iassumption
    iapply Hcnt $$ HPv

/-- `iMod` on `specUpdateN` hypotheses absorbing into a `wp`. -/
instance elimModal_specUpdateN_wp {n : Nat} {E : CoPset} {e : (Exp rT)} {P : IProp GF}
    {Φ : (Val rT) → IProp GF} :
    ElimModal True false false (specUpdateN rT n E P) P (wp E e Φ) (wp E e Φ) where
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
    isplitr; · ipure_intro; exact Hstep
    isplitl [Hρ']; · iassumption
    iapply Hcnt $$ HPv

/-! ## Lifting lemmas (ports `clutch/theories/approxis/lifting.v`)

Translate the operational semantics rules into WP rules. These sit directly
on top of `wp_unfold` + the `specCoupl` / `progCoupl` modalities. -/

/-- `wp_lift_step_couple` — the most general lifting lemma.
Directly restates `wp_unfold` so callers don't have to unfold `wpPre`. -/
theorem wp_lift_step_couple {E : CoPset} {e₁ : (Exp rT)} {Φ : (Val rT) → IProp GF} :
    iprop(∀ (σ₁ : (State rT)) (e₁' : (Exp rT)) (σ₁' : (State rT)) (ε₁ : ENNReal),
      (stateInterp (rT := rT) σ₁ ∗ SpecUpdateGS.specInterp (rT := rT) ⟨e₁', σ₁'⟩ ∗ errInterp (rT := rT) ε₁) -∗
        |={E, ∅}=> specCoupl ∅ σ₁ e₁' σ₁' ε₁ (fun σ₂ ρ' ε₂ =>
          match e₁.toVal? with
          | some v => iprop(|={∅, E}=>
              stateInterp (rT := rT) σ₂ ∗ SpecUpdateGS.specInterp (rT := rT) ρ' ∗ errInterp (rT := rT) ε₂ ∗ Φ v)
          | none => progCoupl e₁ σ₂ ρ'.expr ρ'.state ε₂ (fun e₃ σ₃ e₃' σ₃' ε₃ =>
              iprop(▷ specCoupl ∅ σ₃ e₃' σ₃' ε₃ (fun σ₄ ρ'' ε₄ =>
                iprop(|={∅, E}=>
                  stateInterp (rT := rT) σ₄ ∗ SpecUpdateGS.specInterp (rT := rT) ρ'' ∗ errInterp (rT := rT) ε₄ ∗
                    wp E e₃ Φ)))))) ⊢@{IProp GF}
      wp E e₁ Φ := by
  iintro H
  iapply wp_unfold
  unfold wpPre
  iexact H

/-- `wp_lift_step_spec_couple` — only spec-side coupling, no LHS step.
After the spec-coupling we must re-establish `wp E e₁ Φ`. -/
theorem wp_lift_step_spec_couple {E : CoPset} {e₁ : (Exp rT)} {Φ : (Val rT) → IProp GF} :
    iprop(∀ (σ₁ : (State rT)) (e₁' : (Exp rT)) (σ₁' : (State rT)) (ε₁ : ENNReal),
      (stateInterp (rT := rT) σ₁ ∗ SpecUpdateGS.specInterp (rT := rT) ⟨e₁', σ₁'⟩ ∗ errInterp (rT := rT) ε₁) -∗
        |={E, ∅}=> specCoupl ∅ σ₁ e₁' σ₁' ε₁ (fun σ₂ ρ' ε₂ =>
          iprop(|={∅, E}=>
            stateInterp (rT := rT) σ₂ ∗ SpecUpdateGS.specInterp (rT := rT) ρ' ∗ errInterp (rT := rT) ε₂ ∗
              wp E e₁ Φ))) ⊢@{IProp GF}
      wp E e₁ Φ := by
  iintro H
  iapply wp_lift_step_couple
  iintro %σ₁ %e₁' %σ₁' %ε₁ ⟨Hσ, Hs, Hε⟩
  ispecialize H $$ %σ₁ %e₁' %σ₁' %ε₁ [Hσ Hs Hε]
  · isplitl [Hσ]; · iassumption
    isplitl [Hs] <;> iassumption
  imod H
  imodintro
  iapply specCoupl_bind (E1 := ∅) (E2 := ∅) Std.LawfulSet.subset_refl
  isplitr [H]
  swap
  · iexact H
  iintro %σ₂ %ρ₂ %ε₂ HInner
  iapply fupd_specCoupl
  imod HInner with ⟨Hσ', Hs', Hε', HW⟩
  ihave HW' := (BI.equiv_iff.mp wp_unfold).1 $$ HW
  ispecialize HW' $$ %σ₂ %ρ₂.expr %ρ₂.state %ε₂ [Hσ' Hs' Hε']
  · isplitl [Hσ']; · iassumption
    isplitl [Hs'] <;> iassumption
  imod HW'
  imodintro
  iexact HW'

/-- `wp_lift_step_prog_couple` — one program step against any `progCoupl`,
no spec-only coupling prefix. Requires `e₁` is not a value. -/
theorem wp_lift_step_prog_couple {E : CoPset} {e₁ : (Exp rT)} {Φ : (Val rT) → IProp GF}
    (Hv : e₁.toVal? = none) :
    iprop(∀ (σ₁ : (State rT)) (e₁' : (Exp rT)) (σ₁' : (State rT)) (ε₁ : ENNReal),
      (stateInterp (rT := rT) σ₁ ∗ SpecUpdateGS.specInterp (rT := rT) ⟨e₁', σ₁'⟩ ∗ errInterp (rT := rT) ε₁) -∗
        |={E, ∅}=> progCoupl e₁ σ₁ e₁' σ₁' ε₁ (fun e₂ σ₂ e₂' σ₂' ε₂ =>
          iprop(▷ |={∅, E}=>
            stateInterp (rT := rT) σ₂ ∗ SpecUpdateGS.specInterp (rT := rT) ⟨e₂', σ₂'⟩ ∗ errInterp (rT := rT) ε₂ ∗
              wp E e₂ Φ))) ⊢@{IProp GF}
      wp E e₁ Φ := by
  iintro H
  iapply wp_lift_step_couple
  iintro %σ₁ %e₁' %σ₁' %ε₁ ⟨Hσ, Hs, Hε⟩
  ispecialize H $$ %σ₁ %e₁' %σ₁' %ε₁ [Hσ Hs Hε]
  · isplitl [Hσ]; · iassumption
    isplitl [Hs] <;> iassumption
  imod H
  imodintro
  iapply specCoupl_ret
  simp only [Hv]
  iapply (progCoupl_mono (Z₁ := fun e₂ σ₂ e₂' σ₂' ε₂ =>
    iprop(▷ |={∅, E}=>
      stateInterp (rT := rT) σ₂ ∗ SpecUpdateGS.specInterp (rT := rT) ⟨e₂', σ₂'⟩ ∗ errInterp (rT := rT) ε₂ ∗
        wp E e₂ Φ)))
  isplitr [H]
  swap
  · iexact H
  iintro %e₂ %σ₂ %e₂' %σ₂' %ε₂ HL
  iintro !>
  iapply specCoupl_ret
  iexact HL

/-- `wp_lift_step_later` — single LHS step, no spec-side coupling, results
under a later. Uses `progCoupl_step_l` through `wp_lift_step_couple`. -/
theorem wp_lift_step_later {E : CoPset} {e₁ : (Exp rT)} {Φ : (Val rT) → IProp GF}
    (Hv : e₁.toVal? = none) :
    iprop(∀ (σ₁ : (State rT)), stateInterp (rT := rT) σ₁ -∗ |={E, ∅}=>
      (⌜Reducible e₁ σ₁⌝) ∗
      ∀ (e₂ : (Exp rT)) (σ₂ : (State rT)),
        (⌜0 < primStep ⟨e₁, σ₁⟩ {⟨e₂, σ₂⟩}⌝) -∗ |={∅}=> iprop(▷ |={∅, E}=>
          stateInterp (rT := rT) σ₂ ∗ wp E e₂ Φ)) ⊢@{IProp GF}
      wp E e₁ Φ := by
  iintro H
  iapply wp_lift_step_couple
  iintro %σ₁ %e₁' %σ₁' %ε₁ ⟨Hσ, Hs, Hε⟩
  ispecialize H $$ %σ₁ [Hσ]
  · iassumption
  imod H with ⟨%Hred, H⟩
  imodintro
  iapply specCoupl_ret
  simp only [Hv]
  iapply (progCoupl_step_l (Z := fun e₃ σ₃ e₃' σ₃' ε₃ =>
    iprop(▷ specCoupl ∅ σ₃ e₃' σ₃' ε₃ (fun σ₄ ρ'' ε₄ =>
      iprop(|={∅, E}=>
        stateInterp (rT := rT) σ₄ ∗ SpecUpdateGS.specInterp (rT := rT) ρ'' ∗ errInterp (rT := rT) ε₄ ∗
          wp E e₃ Φ)))) Hred)
  isplitr
  · iintro !> %e₃ %σ₃ %e₃' %σ₃'
    iintro !>
    iapply (specCoupl_err_ge_1 (_root_.le_refl _))
  iintro %e₂ %σ₂ %Hstep
  ispecialize H $$ %e₂ %σ₂ %Hstep
  imod H
  imodintro
  iintro !>
  iapply specCoupl_ret
  imod H with ⟨Hσ', HwpNew⟩
  imodintro
  isplitl [Hσ']; · iassumption
  isplitl [Hs]; · iassumption
  isplitl [Hε]; · iassumption
  iassumption

/-- `wp_lift_step` — like `wp_lift_step_later` but with the `▷` flipped inside. -/
theorem wp_lift_step {E : CoPset} {e₁ : (Exp rT)} {Φ : (Val rT) → IProp GF}
    (Hv : e₁.toVal? = none) :
    iprop(∀ (σ₁ : (State rT)), stateInterp (rT := rT) σ₁ -∗ |={E, ∅}=>
      (⌜Reducible e₁ σ₁⌝) ∗
      ▷ ∀ (e₂ : (Exp rT)) (σ₂ : (State rT)),
        (⌜0 < primStep ⟨e₁, σ₁⟩ {⟨e₂, σ₂⟩}⌝) -∗ |={∅, E}=>
          stateInterp (rT := rT) σ₂ ∗ wp E e₂ Φ) ⊢@{IProp GF}
      wp E e₁ Φ := by
  iintro H
  iapply wp_lift_step_later Hv
  iintro %σ₁ Hσ
  ispecialize H $$ %σ₁ [Hσ]
  · iassumption
  imod H with ⟨%Hred, H⟩
  imodintro
  isplitr; · ipure_intro; exact Hred
  iintro %e₂ %σ₂ %Hstep
  imodintro
  iintro !>
  iapply H $$ %e₂ %σ₂ %Hstep

/-- `wp_lift_prim_steps_coupl` — coupling between LHS and RHS primStep. -/
theorem wp_lift_prim_steps_coupl {E : CoPset} {e₁ : (Exp rT)} {Φ : (Val rT) → IProp GF}
    (Hv : e₁.toVal? = none) :
    iprop(∀ (σ₁ : (State rT)) (e₁' : (Exp rT)) (σ₁' : (State rT)) (ε : ENNReal),
      (stateInterp (rT := rT) σ₁ ∗ SpecUpdateGS.specInterp (rT := rT) ⟨e₁', σ₁'⟩ ∗ errInterp (rT := rT) ε) -∗
        |={E, ∅}=>
        ∃ (R : (Cfg rT) → (Cfg rT) → Prop) (ε₁ ε₂ : ENNReal),
          (⌜ε₁ + ε₂ ≤ ε⌝) ∗
          (⌜Reducible e₁ σ₁⌝) ∗
          (⌜Reducible e₁' σ₁'⌝) ∗
          (⌜AddCoupl ε₁ {p : (Cfg rT) × (Cfg rT) | R p.1 p.2}
              (primStep ⟨e₁, σ₁⟩) (primStep ⟨e₁', σ₁'⟩)⌝) ∗
          (∀ (e₂ : (Exp rT)) (σ₂ : (State rT)) (e₂' : (Exp rT)) (σ₂' : (State rT)),
            (⌜R ⟨e₂, σ₂⟩ ⟨e₂', σ₂'⟩⌝) -∗ |={∅}=> iprop(▷ |={∅, E}=>
              stateInterp (rT := rT) σ₂ ∗ SpecUpdateGS.specInterp (rT := rT) ⟨e₂', σ₂'⟩ ∗
                errInterp (rT := rT) ε₂ ∗ wp E e₂ Φ))) ⊢@{IProp GF}
      wp E e₁ Φ := by
  iintro H
  iapply wp_lift_step_couple
  iintro %σ₁ %e₁' %σ₁' %ε ⟨Hσ, Hs, Hε⟩
  ispecialize H $$ %σ₁ %e₁' %σ₁' %ε [Hσ Hs Hε]
  · isplitl [Hσ]; · iassumption
    isplitl [Hs] <;> iassumption
  imod H with ⟨%R, %ε₁, %ε₂, %Hεsum, %Hred, %Hred', %Hcpl, H⟩
  imodintro
  iapply specCoupl_ret
  simp only [Hv]
  iapply (progCoupl_steps (Z := fun e₃ σ₃ e₃' σ₃' ε₃ =>
    iprop(▷ specCoupl ∅ σ₃ e₃' σ₃' ε₃ (fun σ₄ ρ'' ε₄ =>
      iprop(|={∅, E}=>
        stateInterp (rT := rT) σ₄ ∗ SpecUpdateGS.specInterp (rT := rT) ρ'' ∗ errInterp (rT := rT) ε₄ ∗
          wp E e₃ Φ)))) Hεsum Hred Hred' Hcpl)
  isplitr
  · iintro !> %e₃ %σ₃ %e₃' %σ₃'
    iintro !>
    iapply (specCoupl_err_ge_1 (_root_.le_refl _))
  iintro %e₂ %σ₂ %e₂' %σ₂' %HR
  ispecialize H $$ %e₂ %σ₂ %e₂' %σ₂' %HR
  imod H
  imodintro
  iintro !>
  iapply specCoupl_ret
  imod H with ⟨Hσ', Hs', Hε', Hwp'⟩
  imodintro
  isplitl [Hσ']; · iassumption
  isplitl [Hs']; · iassumption
  isplitl [Hε']; · iassumption
  iassumption

/-- `wp_lift_prim_step_l_dret` — LHS step, RHS dirac (no spec step). -/
theorem wp_lift_prim_step_l_dret {E : CoPset} {e₁ : (Exp rT)} {Φ : (Val rT) → IProp GF}
    (Hv : e₁.toVal? = none) :
    iprop(∀ (σ₁ : (State rT)) (e₁' : (Exp rT)) (σ₁' : (State rT)) (ε : ENNReal),
      (stateInterp (rT := rT) σ₁ ∗ SpecUpdateGS.specInterp (rT := rT) ⟨e₁', σ₁'⟩ ∗ errInterp (rT := rT) ε) -∗
        |={E, ∅}=>
        ∃ (R : (Cfg rT) → (State rT) → Prop) (ε₁ ε₂ : ENNReal),
          (⌜ε₁ + ε₂ ≤ ε⌝) ∗
          (⌜Reducible e₁ σ₁⌝) ∗
          (⌜AddCoupl ε₁ {p : (Cfg rT) × (State rT) | R p.1 p.2}
              (primStep ⟨e₁, σ₁⟩) (MeasureTheory.Measure.dirac σ₁')⌝) ∗
          (∀ (e₂ : (Exp rT)) (σ₂ : (State rT)),
            (⌜R ⟨e₂, σ₂⟩ σ₁'⌝) -∗ |={∅}=> iprop(▷ |={∅, E}=>
              stateInterp (rT := rT) σ₂ ∗ SpecUpdateGS.specInterp (rT := rT) ⟨e₁', σ₁'⟩ ∗
                errInterp (rT := rT) ε₂ ∗ wp E e₂ Φ))) ⊢@{IProp GF}
      wp E e₁ Φ := by
  iintro H
  iapply wp_lift_step_couple
  iintro %σ₁ %e₁' %σ₁' %ε ⟨Hσ, Hs, Hε⟩
  ispecialize H $$ %σ₁ %e₁' %σ₁' %ε [Hσ Hs Hε]
  · isplitl [Hσ]; · iassumption
    isplitl [Hs] <;> iassumption
  imod H with ⟨%R, %ε₁, %ε₂, %Hεsum, %Hred, %Hcpl, H⟩
  imodintro
  iapply specCoupl_ret
  simp only [Hv]
  iapply (progCoupl_step_l_dret (Z := fun e₃ σ₃ e₃' σ₃' ε₃ =>
    iprop(▷ specCoupl ∅ σ₃ e₃' σ₃' ε₃ (fun σ₄ ρ'' ε₄ =>
      iprop(|={∅, E}=>
        stateInterp (rT := rT) σ₄ ∗ SpecUpdateGS.specInterp (rT := rT) ρ'' ∗ errInterp (rT := rT) ε₄ ∗
          wp E e₃ Φ)))) Hεsum Hred Hcpl)
  isplitr
  · iintro !> %e₃ %σ₃ %e₃' %σ₃'
    iintro !>
    iapply (specCoupl_err_ge_1 (_root_.le_refl _))
  iintro %e₂ %σ₂ %HR
  ispecialize H $$ %e₂ %σ₂ %HR
  imod H
  imodintro
  iintro !>
  iapply specCoupl_ret
  imod H with ⟨Hσ', Hs', Hε', Hwp'⟩
  imodintro
  isplitl [Hσ']; · iassumption
  isplitl [Hs']; · iassumption
  isplitl [Hε']; · iassumption
  iassumption

/-- `wp_lift_prim_step_l_erasable` — LHS step, RHS erasable distribution. -/
theorem wp_lift_prim_step_l_erasable {E : CoPset} {e₁ : (Exp rT)} {Φ : (Val rT) → IProp GF}
    (Hv : e₁.toVal? = none) :
    iprop(∀ (σ₁ : (State rT)) (e₁' : (Exp rT)) (σ₁' : (State rT)) (ε : ENNReal),
      (stateInterp (rT := rT) σ₁ ∗ SpecUpdateGS.specInterp (rT := rT) ⟨e₁', σ₁'⟩ ∗ errInterp (rT := rT) ε) -∗
        |={E, ∅}=>
        ∃ (R : (Cfg rT) → (State rT) → Prop) (μ₁' : MeasureTheory.Measure (State rT))
          (ε₁ ε₂ : ENNReal),
          (⌜ε₁ + ε₂ ≤ ε⌝) ∗
          (⌜Reducible e₁ σ₁⌝) ∗
          (⌜Erasable μ₁' σ₁'⌝) ∗
          (⌜AddCoupl ε₁ {p : (Cfg rT) × (State rT) | R p.1 p.2}
              (primStep ⟨e₁, σ₁⟩) μ₁'⌝) ∗
          (∀ (e₂ : (Exp rT)) (σ₂ : (State rT)) (σ₂' : (State rT)),
            (⌜R ⟨e₂, σ₂⟩ σ₂'⌝) -∗ |={∅}=> iprop(▷ |={∅, E}=>
              stateInterp (rT := rT) σ₂ ∗ SpecUpdateGS.specInterp (rT := rT) ⟨e₁', σ₂'⟩ ∗
                errInterp (rT := rT) ε₂ ∗ wp E e₂ Φ))) ⊢@{IProp GF}
      wp E e₁ Φ := by
  iintro H
  iapply wp_lift_step_couple
  iintro %σ₁ %e₁' %σ₁' %ε ⟨Hσ, Hs, Hε⟩
  ispecialize H $$ %σ₁ %e₁' %σ₁' %ε [Hσ Hs Hε]
  · isplitl [Hσ]; · iassumption
    isplitl [Hs] <;> iassumption
  imod H with ⟨%R, %μ₁', %ε₁, %ε₂, %Hεsum, %Hred, %Heras, %Hcpl, H⟩
  imodintro
  iapply specCoupl_ret
  simp only [Hv]
  iapply (progCoupl_step_l_erasable (Z := fun e₃ σ₃ e₃' σ₃' ε₃ =>
    iprop(▷ specCoupl ∅ σ₃ e₃' σ₃' ε₃ (fun σ₄ ρ'' ε₄ =>
      iprop(|={∅, E}=>
        stateInterp (rT := rT) σ₄ ∗ SpecUpdateGS.specInterp (rT := rT) ρ'' ∗ errInterp (rT := rT) ε₄ ∗
          wp E e₃ Φ)))) Hεsum Hred Hcpl Heras)
  isplitr
  · iintro !> %e₃ %σ₃ %e₃' %σ₃'
    iintro !>
    iapply (specCoupl_err_ge_1 (_root_.le_refl _))
  iintro %e₂ %σ₂ %σ₂' %HR
  ispecialize H $$ %e₂ %σ₂ %σ₂' %HR
  imod H
  imodintro
  iintro !>
  iapply specCoupl_ret
  imod H with ⟨Hσ', Hs', Hε', Hwp'⟩
  imodintro
  isplitl [Hσ']; · iassumption
  isplitl [Hs']; · iassumption
  isplitl [Hε']; · iassumption
  iassumption

/-- `wp_lift_pure_step` — pure LHS step (deterministic state, always reducible). -/
theorem wp_lift_pure_step {E E' : CoPset} {e₁ : (Exp rT)} {Φ : (Val rT) → IProp GF}
    (Hsafe : ∀ σ₁, Reducible e₁ σ₁)
    (Hstep : ∀ σ₁ e₂ σ₂, 0 < primStep ⟨e₁, σ₁⟩ {⟨e₂, σ₂⟩} → σ₂ = σ₁) :
    iprop(|={E}[E']▷=> ∀ (e₂ : (Exp rT)) (σ : (State rT)),
      (⌜0 < primStep ⟨e₁, σ⟩ {⟨e₂, σ⟩}⌝) -∗ wp E e₂ Φ) ⊢@{IProp GF}
      wp E e₁ Φ := by
  iintro H
  have Hv : e₁.toVal? = none := by
    rcases htv : e₁.toVal? with _ | v
    · rfl
    · exfalso
      have : e₁.isValue := Exp.toVal?_isValue htv
      obtain ⟨ρ, hρ⟩ := Hsafe default
      exact val_stuck hρ this
  iapply wp_lift_step Hv
  iintro %σ₁ Hσ
  -- H : |={E,E'}=> ▷ |={E',E}=> ∀ e₂ σ, ⌜...⌝ -∗ wp E e₂ Φ
  -- Goal : |={E,∅}=> ⌜Reducible⌝ ∗ ▷ ∀ e₂ σ₂, ⌜...⌝ -∗ |={∅,E}=> stateInterp (rT := rT) σ₂ ∗ wp E e₂ Φ
  imod H
  -- Now H at mask E'; goal at mask E'
  imod (BIFUpdate.subset (E1 := E') (E2 := ∅) Std.LawfulSet.empty_subset)
    with Hclose
  imodintro
  isplitr; · ipure_intro; exact Hsafe σ₁
  iintro !>
  iintro %e₂ %σ₂ %Hpstep
  have hσ : σ₂ = σ₁ := Hstep σ₁ e₂ σ₂ Hpstep
  imod Hclose
  imod H
  imodintro
  isplitl [Hσ]; · rw [← hσ]; iassumption
  have Hpstep' : 0 < primStep ⟨e₁, σ₂⟩ {⟨e₂, σ₂⟩} := hσ ▸ Hpstep
  iapply H $$ %e₂ %σ₂ %Hpstep'

/-- `wp_lift_atomic_step_fupd` — atomic step with mask-shifting fupd. -/
theorem wp_lift_atomic_step_fupd {E1 E2 : CoPset} {e₁ : (Exp rT)} {Φ : (Val rT) → IProp GF}
    (Hv : e₁.toVal? = none) :
    iprop(∀ (σ₁ : (State rT)), stateInterp (rT := rT) σ₁ -∗ |={E1}=>
      (⌜Reducible e₁ σ₁⌝) ∗
      ∀ (e₂ : (Exp rT)) (σ₂ : (State rT)),
        (⌜0 < primStep ⟨e₁, σ₁⟩ {⟨e₂, σ₂⟩}⌝) -∗ |={E1}[E2]▷=>
          stateInterp (rT := rT) σ₂ ∗
          (match e₂.toVal? with | some v => Φ v | none => iprop(False))) ⊢@{IProp GF}
      wp E1 e₁ Φ := by
  iintro H
  iapply wp_lift_step_later Hv
  iintro %σ₁ Hσ
  ispecialize H $$ %σ₁ [Hσ]
  · iassumption
  imod H with ⟨%Hred, H⟩
  imod (BIFUpdate.subset (E1 := E1) (E2 := ∅) Std.LawfulSet.empty_subset)
    with Hclose
  imodintro
  isplitr; · ipure_intro; exact Hred
  iintro %e₂ %σ₂ %Hpstep
  imod Hclose
  ispecialize H $$ %e₂ %σ₂ %Hpstep
  -- H : |={E1,E2}=> ▷ |={E2,E1}=> stateInterp (rT := rT) σ₂ ∗ (match ...)
  imod H
  -- H at E2; goal at E1
  imod (BIFUpdate.subset (E1 := E2) (E2 := ∅) Std.LawfulSet.empty_subset)
    with Hclose
  imodintro
  iintro !>
  imod Hclose
  cases htv : e₂.toVal? with
  | some v =>
    imod H with ⟨Hσ', HΦ⟩
    imodintro
    isplitl [Hσ']; · iassumption
    iapply wp_value_of_toVal htv
    iexact HΦ
  | none =>
    imod H with ⟨Hσ', HΦ⟩
    iexfalso
    iexact HΦ

/-- `wp_lift_atomic_step` — atomic step without mask shift on the inner step. -/
theorem wp_lift_atomic_step {E : CoPset} {e₁ : (Exp rT)} {Φ : (Val rT) → IProp GF}
    (Hv : e₁.toVal? = none) :
    iprop(∀ (σ₁ : (State rT)), stateInterp (rT := rT) σ₁ -∗ |={E}=>
      (⌜Reducible e₁ σ₁⌝) ∗
      ▷ ∀ (e₂ : (Exp rT)) (σ₂ : (State rT)),
        (⌜0 < primStep ⟨e₁, σ₁⟩ {⟨e₂, σ₂⟩}⌝) -∗ |={E}=>
          stateInterp (rT := rT) σ₂ ∗
          (match e₂.toVal? with | some v => Φ v | none => iprop(False))) ⊢@{IProp GF}
      wp E e₁ Φ := by
  iintro H
  iapply wp_lift_atomic_step_fupd (E2 := E) Hv
  iintro %σ₁ Hσ
  ispecialize H $$ %σ₁ [Hσ]
  · iassumption
  imod H with ⟨%Hred, H⟩
  imodintro
  isplitr; · ipure_intro; exact Hred
  iintro %e₂ %σ₂ %Hpstep
  imodintro
  iintro !>
  iapply H $$ %e₂ %σ₂ %Hpstep

/-- `wp_lift_pure_det_step` — pure deterministic step. -/
theorem wp_lift_pure_det_step {E E' : CoPset} {e₁ e₂ : (Exp rT)} {Φ : (Val rT) → IProp GF}
    (Hsafe : ∀ σ₁, Reducible e₁ σ₁)
    (Hdet : ∀ σ₁ e₂' σ₂, 0 < primStep ⟨e₁, σ₁⟩ {⟨e₂', σ₂⟩} → σ₂ = σ₁ ∧ e₂' = e₂) :
    iprop(|={E}[E']▷=> wp E e₂ Φ) ⊢@{IProp GF} wp E e₁ Φ := by
  iintro H
  iapply wp_lift_pure_step (Hsafe := Hsafe)
    (Hstep := fun σ₁ e₂' σ₂ hp => (Hdet σ₁ e₂' σ₂ hp).1)
  imod H
  imodintro
  iintro !>
  imod H
  imodintro
  iintro %e₂' %σ %Hpstep
  obtain ⟨_, heq⟩ := Hdet σ e₂' σ Hpstep
  subst heq
  iexact H

end ApproxisWpGS

/-- Helper: if `PureStep e₁ e₂` and `0 < primStep ⟨e₁,σ⟩ {⟨e₂',σ₂⟩}`, then
`σ₂ = σ ∧ e₂' = e₂`. -/
theorem PureStep.prim_step_det {e₁ e₂ : (Exp rT)} (h : PureStep e₁ e₂)
    {σ : (State rT)} {e₂' : (Exp rT)} {σ₂ : (State rT)}
    (hp : 0 < primStep ⟨e₁, σ⟩ {⟨e₂', σ₂⟩}) :
    σ₂ = σ ∧ e₂' = e₂ := by
  classical
  haveI : MeasureTheory.IsProbabilityMeasure (primStep ⟨e₁, σ⟩) :=
    prim_step_mass _ ⟨⟨e₂, σ⟩, h.det σ ▸ zero_lt_one⟩
  have hmass := h.det σ
  -- {⟨e₂,σ⟩} has full mass 1, so its complement has mass 0.
  have h0 : (primStep ⟨e₁, σ⟩) ({⟨e₂, σ⟩}ᶜ : Set (Cfg rT)) = 0 := by
    have := MeasureTheory.prob_compl_eq_one_sub MeasurableSet.of_discrete
      (μ := primStep ⟨e₁, σ⟩) (s := {⟨e₂, σ⟩})
    rw [this, hmass, tsub_self]
  by_contra hne
  have hne' : (⟨e₂', σ₂⟩ : (Cfg rT)) ≠ ⟨e₂, σ⟩ := by
    rintro ⟨⟩; exact hne ⟨rfl, rfl⟩
  have hzero : (primStep ⟨e₁, σ⟩) {⟨e₂', σ₂⟩} = 0 := by
    apply _root_.le_antisymm _ (zero_le _)
    rw [← h0]
    exact MeasureTheory.measure_mono (fun x hx => by
      simp only [Set.mem_singleton_iff] at hx
      subst hx; exact hne')
  exact absurd hp (by rw [hzero]; exact _root_.lt_irrefl _)

namespace ApproxisWpGS
variable {GF : BundledGFunctors} [ApproxisWpGS (rT := rT) GF]

/-- `wp_pure_step_one` — single `PureStep` lifting. Single-step specialization of
Rocq's `wp_pure_step_later` (with n = 1), directly consumable downstream. -/
theorem wp_pure_step_one {E : CoPset} {e₁ e₂ : (Exp rT)} {Φ : (Val rT) → IProp GF}
    (Hstep : PureStep e₁ e₂) :
    iprop(▷ wp E e₂ Φ) ⊢@{IProp GF} wp E e₁ Φ := by
  iintro H
  have Hdet : ∀ σ₁ e₂' σ₂, 0 < primStep ⟨e₁, σ₁⟩ {⟨e₂', σ₂⟩} → σ₂ = σ₁ ∧ e₂' = e₂ :=
    fun σ e₂' σ₂ hp => Hstep.prim_step_det hp
  iapply (wp_lift_pure_det_step (E' := E) (e₂ := e₂) Hstep.safe Hdet)
  imodintro; iintro !>; imodintro; iexact H

/-- `wp_pure_step_fupd` — `PureExec` step lifting (n-step `step_fupd` form).

The `Nat.repeat` is left as-is in the statement; callers unfold via
`simp only [Nat.repeat]` after `iapply`. -/
theorem wp_pure_step_fupd {E E' : CoPset} {e₁ e₂ : (Exp rT)} {φ : Prop} {n : Nat}
    {Φ : (Val rT) → IProp GF}
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
    have Hdet : ∀ σ₁ e₂' σ₂, 0 < primStep ⟨e₁, σ₁⟩ {⟨e₂', σ₂⟩} → σ₂ = σ₁ ∧ e₂' = c :=
      fun σ e₂' σ₂ hp => Hstep.prim_step_det hp
    iapply (wp_lift_pure_det_step (e₂ := c) Hstep.safe Hdet)
    imod H; imodintro; iintro !>; imod H; imodintro
    iapply (IH Hrest)
    iexact H

/-- `wp_pure_step_later` — `PureExec` step lifting (n-step `▷` form).

Proven via `wp_pure_step_fupd` by converting `▷^n` to `(|={E}[E]▷=>)^n` with
a trivial mask-preserving step-fupd per layer. -/
theorem wp_pure_step_later {E : CoPset} {e₁ e₂ : (Exp rT)} {φ : Prop} {n : Nat}
    {Φ : (Val rT) → IProp GF}
    [Hex : PureExec φ n e₁ e₂] (Hφ : φ) :
    Nat.repeat (fun Q : IProp GF => iprop(▷ Q)) n (wp E e₂ Φ) ⊢@{IProp GF}
      wp E e₁ Φ := by
  refine BI.Entails.trans ?_ (wp_pure_step_fupd (E := E) (E' := E)
    (e₁ := e₁) (e₂ := e₂) (n := n) (Hex := Hex) Hφ)
  -- Pointwise: `▷ Q ⊢ |={E}[E]▷=> Q`.
  induction n with
  | zero =>
    simp only [Nat.repeat]
    exact BI.BIBase.Entails.rfl
  | succ n ih =>
    simp only [Nat.repeat]
    refine (BI.later_mono ih).trans ?_
    -- `▷ |={E}[E]▷=>^[n] wp ⊢ |={E}[E]▷=> |={E}[E]▷=>^[n] wp`
    -- using `fupd_intro_mask` on both outer masks (mask E = E, trivial).
    iintro H
    imodintro; iintro !>; imodintro; iexact H

/-! ## Step-fupdN helpers (`|={E}[E']▷=>^[n] _`)

Utility lemmas for navigating `Nat.repeat`-encoded stacked step-fupds. Used by
adequacy. -/

/-- Introduce `n` layers of step-fupd trivially. -/
theorem stepFupdN_intro {E E' : CoPset} (HE : E' ⊆ E) (n : Nat) {P : IProp GF} :
    P ⊢@{IProp GF} iprop(|={E}[E']▷=>^[n] P) := by
  induction n with
  | zero => simp only [Nat.repeat]; exact BI.BIBase.Entails.rfl
  | succ n ih =>
    simp only [Nat.repeat]
    iintro H
    imod (BIFUpdate.subset (E1 := E) (E2 := E') HE) with Hclose
    imodintro
    iintro !>
    imod Hclose
    imodintro
    iapply ih
    iexact H

/-- Monotonicity of step-fupdN in its body. -/
theorem stepFupdN_mono {E E' : CoPset} {n : Nat} {P Q : IProp GF}
    (HPQ : P ⊢@{IProp GF} Q) :
    iprop(|={E}[E']▷=>^[n] P) ⊢@{IProp GF} iprop(|={E}[E']▷=>^[n] Q) := by
  induction n with
  | zero => simp only [Nat.repeat]; exact HPQ
  | succ n ih =>
    simp only [Nat.repeat]
    iintro H
    imod H; imodintro
    iintro !>
    imod H; imodintro
    iapply ih
    iexact H

/-! ## (Ectx rT)-lifting lemmas (ports `clutch/theories/approxis/ectx_lifting.v`)

Specialize `Lifting` to head-step semantics using `headStep`/`Reducible.of_head`.
-/

/-- `wp_lift_head_step_prog_couple` — head-step specialization. -/
theorem wp_lift_head_step_prog_couple {E : CoPset} {e₁ : (Exp rT)} {Φ : (Val rT) → IProp GF}
    (Hv : e₁.toVal? = none) :
    iprop(∀ (σ₁ : (State rT)) (e₁' : (Exp rT)) (σ₁' : (State rT)) (ε₁ : ENNReal),
      (stateInterp (rT := rT) σ₁ ∗ SpecUpdateGS.specInterp (rT := rT) ⟨e₁', σ₁'⟩ ∗ errInterp (rT := rT) ε₁) -∗
        |={E, ∅}=> (⌜∃ ρ : (Cfg rT), 0 < headStep ⟨e₁, σ₁⟩ {ρ}⌝) ∗
        progCoupl e₁ σ₁ e₁' σ₁' ε₁ (fun e₂ σ₂ e₂' σ₂' ε₂ =>
          iprop(▷ |={∅, E}=>
            stateInterp (rT := rT) σ₂ ∗ SpecUpdateGS.specInterp (rT := rT) ⟨e₂', σ₂'⟩ ∗ errInterp (rT := rT) ε₂ ∗
              wp E e₂ Φ))) ⊢@{IProp GF}
      wp E e₁ Φ := by
  iintro H
  iapply wp_lift_step_prog_couple Hv
  iintro %σ₁ %e₁' %σ₁' %ε₁ ⟨Hσ, Hs, Hε⟩
  ispecialize H $$ %σ₁ %e₁' %σ₁' %ε₁ [Hσ Hs Hε]
  · isplitl [Hσ]; · iassumption
    isplitl [Hs] <;> iassumption
  imod H with ⟨%_Hhred, H⟩
  imodintro
  iexact H

/-- `wp_lift_head_step` — head-step lifting (no spec coupling). -/
theorem wp_lift_head_step {E : CoPset} {e₁ : (Exp rT)} {Φ : (Val rT) → IProp GF}
    (Hv : e₁.toVal? = none) :
    iprop(∀ (σ₁ : (State rT)), stateInterp (rT := rT) σ₁ -∗ |={E, ∅}=>
      (⌜∃ ρ : (Cfg rT), 0 < headStep ⟨e₁, σ₁⟩ {ρ}⌝) ∗
      ▷ ∀ (e₂ : (Exp rT)) (σ₂ : (State rT)),
        (⌜0 < headStep ⟨e₁, σ₁⟩ {⟨e₂, σ₂⟩}⌝) -∗ |={∅, E}=>
          stateInterp (rT := rT) σ₂ ∗ wp E e₂ Φ) ⊢@{IProp GF}
      wp E e₁ Φ := by
  iintro H
  iapply wp_lift_step Hv
  iintro %σ₁ Hσ
  ispecialize H $$ %σ₁ [Hσ]
  · iassumption
  imod H with ⟨%Hhred, H⟩
  imodintro
  isplitr; · ipure_intro; exact Reducible.of_head Hhred
  iintro !>
  iintro %e₂ %σ₂ %Hpstep
  -- primStep positive + head-reducible ⇒ headStep positive at same successor
  have hpos : 0 < headStep ⟨e₁, σ₁⟩ {⟨e₂, σ₂⟩} := by
    have heq : primStep ⟨e₁, σ₁⟩ = headStep ⟨e₁, σ₁⟩ := primStep_eq_headStep Hhred
    exact heq ▸ Hpstep
  iapply H $$ %e₂ %σ₂ %hpos

/-- `wp_lift_atomic_head_step_fupd` — atomic head-step with mask shift. -/
theorem wp_lift_atomic_head_step_fupd {E1 E2 : CoPset} {e₁ : (Exp rT)} {Φ : (Val rT) → IProp GF}
    (Hv : e₁.toVal? = none) :
    iprop(∀ (σ₁ : (State rT)), stateInterp (rT := rT) σ₁ -∗ |={E1}=>
      (⌜∃ ρ : (Cfg rT), 0 < headStep ⟨e₁, σ₁⟩ {ρ}⌝) ∗
      ∀ (e₂ : (Exp rT)) (σ₂ : (State rT)),
        (⌜0 < headStep ⟨e₁, σ₁⟩ {⟨e₂, σ₂⟩}⌝) -∗ |={E1}[E2]▷=>
          stateInterp (rT := rT) σ₂ ∗
          (match e₂.toVal? with | some v => Φ v | none => iprop(False))) ⊢@{IProp GF}
      wp E1 e₁ Φ := by
  iintro H
  iapply wp_lift_atomic_step_fupd Hv
  iintro %σ₁ Hσ
  ispecialize H $$ %σ₁ [Hσ]
  · iassumption
  imod H with ⟨%Hhred, H⟩
  imodintro
  isplitr; · ipure_intro; exact Reducible.of_head Hhred
  iintro %e₂ %σ₂ %Hpstep
  have hpos : 0 < headStep ⟨e₁, σ₁⟩ {⟨e₂, σ₂⟩} := by
    have heq : primStep ⟨e₁, σ₁⟩ = headStep ⟨e₁, σ₁⟩ := primStep_eq_headStep Hhred
    exact heq ▸ Hpstep
  iapply H $$ %e₂ %σ₂ %hpos

/-- `wp_lift_atomic_head_step` — atomic head-step without mask shift. -/
theorem wp_lift_atomic_head_step {E : CoPset} {e₁ : (Exp rT)} {Φ : (Val rT) → IProp GF}
    (Hv : e₁.toVal? = none) :
    iprop(∀ (σ₁ : (State rT)), stateInterp (rT := rT) σ₁ -∗ |={E}=>
      (⌜∃ ρ : (Cfg rT), 0 < headStep ⟨e₁, σ₁⟩ {ρ}⌝) ∗
      ▷ ∀ (e₂ : (Exp rT)) (σ₂ : (State rT)),
        (⌜0 < headStep ⟨e₁, σ₁⟩ {⟨e₂, σ₂⟩}⌝) -∗ |={E}=>
          stateInterp (rT := rT) σ₂ ∗
          (match e₂.toVal? with | some v => Φ v | none => iprop(False))) ⊢@{IProp GF}
      wp E e₁ Φ := by
  iintro H
  iapply wp_lift_atomic_step Hv
  iintro %σ₁ Hσ
  ispecialize H $$ %σ₁ [Hσ]
  · iassumption
  imod H with ⟨%Hhred, H⟩
  imodintro
  isplitr; · ipure_intro; exact Reducible.of_head Hhred
  iintro !>
  iintro %e₂ %σ₂ %Hpstep
  have hpos : 0 < headStep ⟨e₁, σ₁⟩ {⟨e₂, σ₂⟩} := by
    have heq : primStep ⟨e₁, σ₁⟩ = headStep ⟨e₁, σ₁⟩ := primStep_eq_headStep Hhred
    exact heq ▸ Hpstep
  iapply H $$ %e₂ %σ₂ %hpos

/-- `wp_lift_pure_det_head_step` — pure deterministic head step. -/
theorem wp_lift_pure_det_head_step {E E' : CoPset} {e₁ e₂ : (Exp rT)} {Φ : (Val rT) → IProp GF}
    (_Hv : e₁.toVal? = none)
    (Hsafe : ∀ σ₁, ∃ ρ : (Cfg rT), 0 < headStep ⟨e₁, σ₁⟩ {ρ})
    (Hdet : ∀ σ₁ e₂' σ₂, 0 < headStep ⟨e₁, σ₁⟩ {⟨e₂', σ₂⟩} → σ₂ = σ₁ ∧ e₂' = e₂) :
    iprop(|={E}[E']▷=> wp E e₂ Φ) ⊢@{IProp GF} wp E e₁ Φ := by
  iapply wp_lift_pure_det_step (Hsafe := fun σ => Reducible.of_head (Hsafe σ))
  intros σ e₂' σ₂ hp
  have heq : primStep ⟨e₁, σ⟩ = headStep ⟨e₁, σ⟩ := primStep_eq_headStep (Hsafe σ)
  exact Hdet σ e₂' σ₂ (heq ▸ hp)

/-- `wp_lift_pure_det_head_step'` — `▷`-form of `wp_lift_pure_det_head_step`. -/
theorem wp_lift_pure_det_head_step' {E : CoPset} {e₁ e₂ : (Exp rT)} {Φ : (Val rT) → IProp GF}
    (Hv : e₁.toVal? = none)
    (Hsafe : ∀ σ₁, ∃ ρ : (Cfg rT), 0 < headStep ⟨e₁, σ₁⟩ {ρ})
    (Hdet : ∀ σ₁ e₂' σ₂, 0 < headStep ⟨e₁, σ₁⟩ {⟨e₂', σ₂⟩} → σ₂ = σ₁ ∧ e₂' = e₂) :
    iprop(▷ wp E e₂ Φ) ⊢@{IProp GF} wp E e₁ Φ := by
  iintro H
  iapply (wp_lift_pure_det_head_step (E' := E) Hv Hsafe Hdet)
  imodintro; iintro !>; imodintro
  iexact H

end ApproxisWpGS

end ProbLang
