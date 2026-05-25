module

public import Metrology.TotalEris.Weakestpre
public import Iris.BI.Lib.Fixpoint
public import Iris.ProofMode.Classes
public import Iris.ProofMode.InstancesUpdates

@[expose] public section

open Std Iris Iris.Std Iris.BI Iris.ProofMode OFE COFE ProbLang
open scoped ENNReal

namespace ProbLang
namespace TotalEris
namespace ErisWpGS

variable {GF : BundledGFunctors} [ErisWpGS GF]

/-! # `tgl_wp` — total-correctness weakest precondition

Port of `clutch/theories/eris/total_weakestpre.v`.

The total WP differs from `pgl_wp` in *one place* — there is no `▷` (later)
modality in the recursive call. This makes the recursion non-guarded and
forces us to use `bi_least_fixpoint` rather than the OFE guarded fixpoint.
The total-WP semantics is: with probability at least `1 - ε`, `e` terminates
in a value satisfying `Φ`.

To use `bi_least_fixpoint`, we uncurry the `(E, e, Φ)` arguments into a
single state type. -/

/-- Discrete OFE on `Exp` — needed so that the induction principle
`tglWp_ind_simple` can require `NonExpansive Q` for `Q : Exp → IProp GF`.
Also installed for `CoPset`. -/
instance : COFE Exp := COFE.ofDiscrete _ Eq_Equivalence
instance : OFE.Discrete Exp := ⟨id⟩
instance : OFE.Leibniz Exp := ⟨id⟩


/-- Packed fixpoint state for `tgl_wp`: an `(E, e)` pair.

We *fix* the postcondition `Φ` as an outer parameter rather than including
it in the fixpoint state. This is valid because the recursive call inside
`tglWpPre` uses the *same* `Φ` (only `E` and `e` change). The payoff is
that `TglWpState` is now Leibniz-discrete, which lets `BIMonoPred`'s
`mono_pred_ne` close by reflection.

The price is that non-expansiveness in `Φ` becomes an *outer* statement
about the function `Φ ↦ tglWp E e Φ`, proved separately. -/
abbrev TglWpState : Type _ := CoPset × Exp

instance : COFE TglWpState := COFE.ofDiscrete _ Eq_Equivalence
instance : OFE.Discrete TglWpState := ⟨id⟩
instance : OFE.Leibniz TglWpState := ⟨id⟩

/-- One unfolding of `tgl_wp`. Identical to `pglWpPre` *except* the
recursive call is **not** under `▷`. The body is again written in the
"always-quantify, match-inside" form so the Iris-Lean structural-walk
lemmas work without bumping `maxHeartbeats`. -/
abbrev tglWpPre
    (wp : CoPset → Exp → (Val → IProp GF) → IProp GF)
    (E : CoPset) (e₁ : Exp) (Φ : Val → IProp GF) : IProp GF :=
  iprop(∀ (σ₁ : State) (ε₁ : ENNReal),
    (stateInterp σ₁ ∗ errInterp ε₁) -∗
      match e₁.toVal? with
      | some v => iprop(|={E}=>
          stateInterp σ₁ ∗ errInterp ε₁ ∗ Φ v)
      | none => iprop(|={E, ∅}=>
          glm e₁ σ₁ ε₁ (fun ρ ε₂ =>
            iprop(|={∅, E}=>
              stateInterp ρ.state ∗ errInterp ε₂ ∗ wp E ρ.expr Φ))))

/-- Uncurried form of `tglWpPre` at a fixed postcondition `Φ`. -/
abbrev tglWpPreFixed (Φ : Val → IProp GF)
    (wp : TglWpState → IProp GF) : TglWpState → IProp GF :=
  fun ⟨E, e⟩ => tglWpPre (fun E' e' _ => wp ⟨E', e'⟩) E e Φ

/-- The pre-functor at a fixed `Φ` is monotone. -/
instance tglWpPreFixed_mono {Φ : Val → IProp GF} :
    BIMonoPred (tglWpPreFixed (GF := GF) Φ) where
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
      iapply glm_mono_pred
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

/-- The Eris total weakest precondition. -/
@[reducible, expose]
noncomputable def tglWp (E : CoPset) (e : Exp) (Φ : Val → IProp GF) : IProp GF :=
  bi_least_fixpoint (tglWpPreFixed (GF := GF) Φ) ⟨E, e⟩

/-- Fixpoint unfolding for `tglWp`. -/
theorem tglWp_unfold {E : CoPset} {e : Exp} {Φ : Val → IProp GF} :
    tglWp (GF := GF) E e Φ ≡ tglWpPre (tglWp (GF := GF)) E e Φ :=
  least_fixpoint_unfold _

/-- Specialised unfolding at a *value* expression: the `match` reduces by
`Exp.toVal?_ofVal`, eliminating the recursive call and exposing the post
`Φ v` directly. This is the Lean term-level equality used to derive value
extraction without an Iris-side rewrite. -/
theorem tglWp_unfold_value {E : CoPset} {v : Val} {Φ : Val → IProp GF} :
    tglWp E (Exp.ofVal v) Φ ≡
      iprop(∀ (σ : State) (ε : ENNReal),
        (stateInterp σ ∗ errInterp ε) -∗
          |={E}=> stateInterp σ ∗ errInterp ε ∗ Φ v) := by
  refine .trans tglWp_unfold ?_
  unfold tglWpPre
  rw [Exp.toVal?_ofVal]

/-- Specialised unfolding at a *non-value* expression: the `match` reduces by
the hypothesis `Hv : e.toVal? = none`, exposing the `glm`-step body directly.
Dual to `tglWp_unfold_value`. -/
theorem tglWp_unfold_step {E : CoPset} {e : Exp} {Φ : Val → IProp GF}
    (Hv : e.toVal? = none) :
    tglWp E e Φ ≡
      iprop(∀ (σ : State) (ε : ENNReal),
        (stateInterp σ ∗ errInterp ε) -∗
          |={E, ∅}=> glm e σ ε (fun ρ ε₂ =>
            iprop(|={∅, E}=>
              stateInterp ρ.state ∗ errInterp ε₂ ∗ tglWp E ρ.expr Φ))) := by
  refine .trans tglWp_unfold ?_
  unfold tglWpPre
  rw [Hv]

/-- Lean-level equality for `tglWpPre` at a value (reduces the inner `match`).
Used by clients (e.g. `tglWp_bind`) that need to cast an iris hypothesis of
type `tglWpPre wp E (ofVal v) Φ` to the reduced body form without an
iris-side rewrite. -/
theorem tglWpPre_eq_value {wp : CoPset → Exp → (Val → IProp GF) → IProp GF}
    {E : CoPset} {v : Val} {Φ : Val → IProp GF} :
    tglWpPre wp E (Exp.ofVal v) Φ =
      iprop(∀ (σ : State) (ε : ENNReal),
        (stateInterp σ ∗ errInterp ε) -∗
          |={E}=> stateInterp σ ∗ errInterp ε ∗ Φ v) := by
  unfold tglWpPre; rw [Exp.toVal?_ofVal]

/-- Lean-level equality for `tglWpPre` at a non-value (dual of `tglWpPre_eq_value`). -/
theorem tglWpPre_eq_step {wp : CoPset → Exp → (Val → IProp GF) → IProp GF}
    {E : CoPset} {e : Exp} {Φ : Val → IProp GF} (Hv : e.toVal? = none) :
    tglWpPre wp E e Φ =
      iprop(∀ (σ : State) (ε : ENNReal),
        (stateInterp σ ∗ errInterp ε) -∗
          |={E, ∅}=> glm e σ ε (fun ρ ε₂ =>
            iprop(|={∅, E}=>
              stateInterp ρ.state ∗ errInterp ε₂ ∗ wp E ρ.expr Φ))) := by
  unfold tglWpPre; rw [Hv]

/-! ## Value rules -/

/-- Value introduction (fupd-flavored). -/
theorem tglWp_value_fupd {E : CoPset} {v : Val} {Φ : Val → IProp GF} :
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

/-- Plain value introduction. -/
theorem tglWp_value {E : CoPset} {v : Val} {Φ : Val → IProp GF} :
    Φ v ⊢@{IProp GF} tglWp E (Exp.ofVal v) Φ := by
  iintro HΦ
  iapply tglWp_value_fupd
  imodintro
  iexact HΦ

/-- General value form. -/
theorem tglWp_value_of_toVal {E : CoPset} {e : Exp} {v : Val}
    {Φ : Val → IProp GF} (h : e.toVal? = some v) :
    Φ v ⊢@{IProp GF} tglWp E e Φ := by
  rw [← Exp.ofVal_of_toVal_some h]
  exact tglWp_value

/-- General fupd-value form: the fupd variant of `tglWp_value_of_toVal`. -/
theorem tglWp_value_fupd_of_toVal {E : CoPset} {e : Exp} {v : Val}
    {Φ : Val → IProp GF} (h : e.toVal? = some v) :
    iprop(|={E}=> Φ v) ⊢@{IProp GF} tglWp E e Φ := by
  rw [← Exp.ofVal_of_toVal_some h]
  exact tglWp_value_fupd

/-- Extract a value-WP's post under state interp. The state-monadic dual of
`tglWp_value_fupd`: with `stateInterp σ` and `errInterp ε` available, the
value-WP `tglWp E (ofVal v) Φ` produces `|={E}=> stateInterp σ ∗ errInterp ε ∗ Φ v`.

Useful for examples that need to "execute" a value-WP after its preceding
primitive step (which yielded fresh state/err interps). -/
theorem tglWp_value_inv_with_state {E : CoPset} {v : Val} {σ : State}
    {ε : ENNReal} {Φ : Val → IProp GF} :
    iprop(tglWp E (Exp.ofVal v) Φ ∗ stateInterp σ ∗ errInterp ε) ⊢@{IProp GF}
      iprop(|={E}=> stateInterp σ ∗ errInterp ε ∗ Φ v) := by
  iintro ⟨HW, Hσ, Hε⟩
  ihave HW' := (BI.equiv_iff.mp tglWp_unfold_value).1 $$ HW
  iapply HW' $$ %σ %ε
  isplitl [Hσ]; · iexact Hσ
  iexact Hε

/-! ## Induction principle -/

/-- *Simple* fixpoint induction for `tglWp`.

To prove `Q e'` from `tglWp E e Φ`, it suffices to exhibit a per-`e'`
predicate `Q` (NonExpansive in `e'`) that closes under one unfolding of
`tglWpPre` at the *induction-hypothesis* shape `(_, e', _) ↦ Q e'`.

This is the analogue of Rocq's `tgl_wp_ind_simple` (specialised to a
single-mask, fixed-`Φ` use). The outer `E` is threaded as an iris-level
`⌜E' = E⌝` premise on the induction predicate so that `least_fixpoint_iter`
(which quantifies over arbitrary fixpoint-state seeds) still goes through. -/
theorem tglWp_ind_simple {E : CoPset} {e : Exp} {Φ : Val → IProp GF}
    (Q : Exp → IProp GF) [NonExpansive Q] :
    iprop(□ (∀ e',
      tglWpPre (fun _ e'' _ => Q e'') E e' Φ -∗ Q e')) ⊢@{IProp GF}
        (tglWp E e Φ -∗ Q e) := by
  iintro #HInd HW
  -- Lift Q to the fixpoint state, threading `E' = E` as a pure premise.
  -- `letI` (not `have`) so the `NonExpansive` instance is visible to typeclass
  -- synthesis at the `least_fixpoint_iter` call below.
  letI Q' : TglWpState → IProp GF :=
    fun s => iprop(⌜s.1 = E⌝ -∗ Q s.2)
  letI : NonExpansive Q' := nonExpansive_of_discrete_leibniz Q'
  -- Prove `Q' ⟨E, e⟩` from `HW`, then apply to `⌜E = E⌝` to extract `Q e`.
  ihave HQ' : iprop(Q' ⟨E, e⟩) $$ [HW]
  · -- Goal: `Q' ⟨E, e⟩` with spatial context `HW : tglWp E e Φ`.
    -- `least_fixpoint_iter`'s conclusion `Q' x` unifies with the goal at
    -- `x := ⟨E, e⟩`. iapply leaves two subgoals: the inductive step and
    -- `bi_least_fixpoint (tglWpPreFixed Φ) ⟨E, e⟩` (= `tglWp E e Φ` by defeq).
    iapply least_fixpoint_iter (F := tglWpPreFixed Φ) (Φ := Q')
    swap
    · iexact HW
    -- Discharge the induction step: `□ ∀ y, tglWpPreFixed Φ Q' y -∗ Q' y`.
    iintro !> %s HF
    rcases s with ⟨E', e'⟩
    iintro %hEeq
    subst hEeq
    iapply HInd
    -- `tglWpPreFixed Φ Q' ⟨E, e'⟩` is defeq to `tglWpPre (fun E'' e'' _ => Q' ⟨E'', e''⟩) E e' Φ`
    -- (both are `abbrev`s). Enter the `∀ σ ε, ...` body.
    iintro %σ %ε ⟨Hσ, Hε⟩
    ispecialize HF $$ %σ %ε [Hσ Hε]
    · isplitl [Hσ]; · iexact Hσ
      iexact Hε
    cases htv : e'.toVal? with
    | some v => iexact HF
    | none =>
      imod HF with HG
      imodintro
      iapply glm_mono_pred
      isplitr [HG]
      swap
      · iexact HG
      iintro !> %ρ %ε' HC
      imod HC with ⟨Hσ', Hε', HW⟩
      imodintro
      isplitl [Hσ']; · iexact Hσ'
      isplitl [Hε']; · iexact Hε'
      -- HW : Q' ⟨E, ρ.expr⟩ = ⌜E = E⌝ -∗ Q ρ.expr. Discharge with rfl.
      iapply HW; ipure_intro; rfl
  iapply HQ'; ipure_intro; rfl

/-! ## Derived structural rules -/

/-- Strong monotonicity at a fixed mask under a *spatial* `fupd` wand. Rocq:
`tgl_wp_strong_mono` (with `E1 = E2`). Uses `glm_strong_mono` (spatial) to
walk the non-value case, and the standard "carry the wand through the
fixpoint via `Q`" trick to make `tglWp_ind_simple` accept a spatial wand. -/
theorem tglWp_strong_mono {E : CoPset} {e : Exp}
    {Φ Ψ : Val → IProp GF} :
    iprop(tglWp E e Φ ∗ (∀ v, Φ v ={E}=∗ Ψ v)) ⊢@{IProp GF} tglWp E e Ψ := by
  iintro ⟨HW, Hwand⟩
  -- `Q e' := ∀ Ψ', (∀ v, Φ v ={E}=∗ Ψ' v) -∗ tglWp E e' Ψ'`. Each iteration of
  -- the IH receives a fresh wand from its own `Q`-argument, so the spatial
  -- accounting of the outer `Hwand` is consumed only once (at the final apply).
  letI Q : Exp → IProp GF := fun e' => iprop(
    ∀ (Ψ' : Val → IProp GF), (∀ v, Φ v ={E}=∗ Ψ' v) -∗ tglWp E e' Ψ')
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
      -- HF body's continuation calls `Q ρ.expr`. Goal's calls `tglWp E ρ.expr Ψ'`.
      -- Lift via `glm_strong_mono` with the per-ρ wand `Q ρ.expr -∗ tglWp E ρ.expr Ψ'`.
      imod HF with HG
      imodintro
      iapply glm_strong_mono
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

/-- Spatial wand variant of strong-mono — directly absorbs the no-fupd wand
into the `={E}=∗` form expected by `tglWp_strong_mono`. -/
theorem tglWp_wand {E : CoPset} {e : Exp} {Φ Ψ : Val → IProp GF} :
    iprop(tglWp E e Φ ∗ (∀ v, Φ v -∗ Ψ v)) ⊢@{IProp GF} tglWp E e Ψ := by
  iintro ⟨HW, HΦΨ⟩
  iapply tglWp_strong_mono
  isplitl [HW]; · iexact HW
  iintro %v HΦv
  imodintro
  iapply HΦΨ; iexact HΦv

/-- Wand-on-the-left curry: take the WP after the wand. -/
theorem tglWp_wand_l {E : CoPset} {e : Exp} {Φ Ψ : Val → IProp GF} :
    iprop((∀ v, Φ v -∗ Ψ v) ∗ tglWp E e Φ) ⊢@{IProp GF} tglWp E e Ψ := by
  iintro ⟨HΦΨ, HW⟩
  iapply tglWp_wand
  isplitl [HW]; · iexact HW
  iexact HΦΨ

/-- Absorb a leading `|={E}=>` into the WP. Rocq: `fupd_tgl_wp`. -/
theorem fupd_tglWp {E : CoPset} {e : Exp} {Φ : Val → IProp GF} :
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

/-- Absorb a `fupd` from the post-condition. Rocq: `tgl_wp_fupd`. -/
theorem tglWp_fupd {E : CoPset} {e : Exp} {Φ : Val → IProp GF} :
    tglWp E e (fun v => iprop(|={E}=> Φ v)) ⊢@{IProp GF} tglWp E e Φ := by
  iintro HW
  iapply tglWp_strong_mono
    (Φ := fun v => iprop(|={E}=> Φ v)) (Ψ := Φ)
  isplitl [HW]; · iexact HW
  iintro %v HΦfupd
  imod HΦfupd
  imodintro
  iexact HΦfupd

/-- Frame a (spatial) resource on the left into a `tglWp`. Rocq:
`tgl_wp_frame_l`. -/
theorem tglWp_frame_l {E : CoPset} {e : Exp} {R : IProp GF}
    {Φ : Val → IProp GF} :
    iprop(R ∗ tglWp E e Φ) ⊢@{IProp GF} tglWp E e (fun v => iprop(R ∗ Φ v)) := by
  iintro ⟨HR, HW⟩
  iapply tglWp_wand
  isplitl [HW]; · iexact HW
  iintro %v HΦv
  isplitr [HΦv]; swap
  · iexact HΦv
  iexact HR

/-- Frame a (spatial) resource on the right into a `tglWp`. Rocq:
`tgl_wp_frame_r`. -/
theorem tglWp_frame_r {E : CoPset} {e : Exp} {R : IProp GF}
    {Φ : Val → IProp GF} :
    iprop(tglWp E e Φ ∗ R) ⊢@{IProp GF} tglWp E e (fun v => iprop(Φ v ∗ R)) := by
  iintro ⟨HW, HR⟩
  iapply tglWp_wand
  isplitl [HW]; · iexact HW
  iintro %v HΦv
  isplitl [HΦv]
  · iexact HΦv
  iexact HR

/-- Spatial-frame variant where the framed resource is *also* in the post.
`R ∗ WP e {fun v => R -∗ Φ v} ⊢ WP e {Φ}`. Useful when a spatial resource
needs to survive the step and then be re-consumed in the post.
Rocq: `wp_frame_wand` (Approxis port). -/
theorem tglWp_frame_wand {E : CoPset} {e : Exp} {R : IProp GF}
    {Φ : Val → IProp GF} :
    iprop(R ∗ tglWp E e (fun v => iprop(R -∗ Φ v))) ⊢@{IProp GF} tglWp E e Φ := by
  iintro ⟨HR, HW⟩
  iapply (tglWp_wand (Φ := fun v => iprop(R ∗ (R -∗ Φ v))) (Ψ := Φ))
  isplitl [HR HW]
  · iapply (tglWp_frame_l (R := R) (Φ := fun v => iprop(R -∗ Φ v)))
    isplitl [HR]; · iassumption
    iexact HW
  iintro %v ⟨HRv, HW'⟩
  iapply HW' $$ HRv

/-- Pointwise post-strengthening for `tglWp`. Rocq: `tgl_wp_mono` (specialised
to a fixed mask). -/
theorem tglWp_mono {E : CoPset} {e : Exp} {Φ Ψ : Val → IProp GF}
    (HΦ : ∀ v, Φ v ⊢@{IProp GF} Ψ v) :
    tglWp E e Φ ⊢@{IProp GF} tglWp E e Ψ := by
  iintro HW
  -- `Q e' := tglWp E e' Ψ` is non-expansive because `Exp` is a discrete OFE
  -- (`OFE.Leibniz Exp`), so any function out of `Exp` is automatically NE.
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
    -- Both HF and the goal have the same `|={E,∅}=> glm ...` shape with `tglWp E ρ.expr Ψ`
    -- in the continuation; no transformation needed.
    iexact HF

/-! ## Bind -/

/-- Full evaluation-context bind for `tglWp`. Rocq: `tgl_wp_bind`.

Uses `tglWp_ind_simple` with `Q e' := tglWp E (K.fill e') Φ`. Per-iteration
value/step sub-cases use the per-branch `tglWpPre_eq_value`/`tglWpPre_eq_step`
Lean equalities, applied via `Eq.mpr` term-level cast (which works because
the equalities are between definitionally-equal `IProp GF` terms — the only
thing the inner `match` does is depend on `e'.toVal?`). -/
theorem tglWp_bind {K : Ectx} {E : CoPset} {e : Exp} {Φ : Val → IProp GF} :
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
    ihave HF_red : iprop(∀ (σ : State) (ε : ENNReal),
        (stateInterp σ ∗ errInterp ε) -∗
          |={E}=> stateInterp σ ∗ errInterp ε ∗ tglWp E (K.fill (Exp.ofVal v)) Φ)
      $$ [HF]
    · rw [← heqV]; iexact HF
    -- Goal: tglWp E (K.fill (ofVal v)) Φ. Reduce via the per-branch unfold and
    -- discharge using HF_red's contents (state-bridged via imod).
    cases hKtv : (K.fill (Exp.ofVal v)).toVal? with
    | some v' =>
      have heq' : K.fill (Exp.ofVal v) = Exp.ofVal v' :=
        (Exp.ofVal_of_toVal_some hKtv).symm
      have key : tglWp E (K.fill (Exp.ofVal v)) Φ ≡
                 iprop(∀ (σ' : State) (ε' : ENNReal),
                   (stateInterp σ' ∗ errInterp ε') -∗
                     |={E}=> stateInterp σ' ∗ errInterp ε' ∗ Φ v') := by
        rw [heq']; exact tglWp_unfold_value
      iapply (BI.equiv_iff.mp key).2
      iintro %σ %ε ⟨Hσ, Hε⟩
      ispecialize HF_red $$ %σ %ε [Hσ Hε]
      · isplitl [Hσ]; · iexact Hσ
        iexact Hε
      imod HF_red with ⟨Hσ', Hε', HInner⟩
      have key2 : tglWp E (K.fill (Exp.ofVal v)) Φ ≡
                  iprop(∀ (σ'' : State) (ε'' : ENNReal),
                    (stateInterp σ'' ∗ errInterp ε'') -∗
                      |={E}=> stateInterp σ'' ∗ errInterp ε'' ∗ Φ v') := by
        rw [heq']; exact tglWp_unfold_value
      ihave HInner' := (BI.equiv_iff.mp key2).1 $$ HInner
      iapply HInner' $$ %σ %ε
      isplitl [Hσ']; · iexact Hσ'
      iexact Hε'
    | none =>
      iapply (BI.equiv_iff.mp (tglWp_unfold_step hKtv)).2
      iintro %σ %ε ⟨Hσ, Hε⟩
      ispecialize HF_red $$ %σ %ε [Hσ Hε]
      · isplitl [Hσ]; · iexact Hσ
        iexact Hε
      imod HF_red with ⟨Hσ', Hε', HInner⟩
      ihave HInner' := (BI.equiv_iff.mp (tglWp_unfold_step hKtv)).1 $$ HInner
      iapply HInner' $$ %σ %ε
      isplitl [Hσ']; · iexact Hσ'
      iexact Hε'
  | none =>
    have hKtv : (K.fill e').toVal? = none :=
      Exp.toVal?_eq_none.mpr fun hKv =>
        (Exp.toVal?_eq_none.mp htv) (Ectx.fill_isValue hKv)
    have heqS := tglWpPre_eq_step (wp := fun _ e'' _ => tglWp E (K.fill e'') Φ)
                  (E := E) (e := e')
                  (Φ := fun w => tglWp E (K.fill (Exp.ofVal w)) Φ) htv
    ihave HF_red : iprop(∀ (σ : State) (ε : ENNReal),
        (stateInterp σ ∗ errInterp ε) -∗
          |={E, ∅}=> glm e' σ ε (fun ρ ε₂ =>
            iprop(|={∅, E}=>
              stateInterp ρ.state ∗ errInterp ε₂ ∗ tglWp E (K.fill ρ.expr) Φ)))
      $$ [HF]
    · rw [← heqS]; iexact HF
    have key : tglWp E (K.fill e') Φ ≡
               iprop(∀ (σ' : State) (ε' : ENNReal),
                 (stateInterp σ' ∗ errInterp ε') -∗
                   |={E, ∅}=> glm (K.fill e') σ' ε' (fun ρ ε₂ =>
                     iprop(|={∅, E}=>
                       stateInterp ρ.state ∗ errInterp ε₂ ∗ tglWp E ρ.expr Φ))) :=
      tglWp_unfold_step hKtv
    iapply (BI.equiv_iff.mp key).2
    iintro %σ %ε ⟨Hσ, Hε⟩
    ispecialize HF_red $$ %σ %ε [Hσ Hε]
    · isplitl [Hσ]; · iexact Hσ
      iexact Hε
    imod HF_red
    imodintro
    iapply (glm_bind (K := K) (e := e') (σ := σ) (ε := ε)
            (Z := fun ρ ε₂ => iprop(|={∅, E}=>
              stateInterp ρ.state ∗ errInterp ε₂ ∗ tglWp E ρ.expr Φ)))
    iexact HF_red

/-- Value-only specialization of `tglWp_bind`. When the inner expression has
already reduced to a value, the bind collapses to executing the outer
continuation. Uses `tglWp_unfold_value` to extract the post, then
`tglWp_unfold_{value,step}` to discharge the outer-WP body (avoiding
iris-hyp rewrites on the inner match). -/
theorem tglWp_bind_value {K : Ectx} {E : CoPset} {v : Val} {Φ : Val → IProp GF} :
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
    -- `K.fill (ofVal v) = ofVal v'`; carry the equality through to instantiate
    -- `tglWp_unfold_value` at the right shape.
    have heq : K.fill (Exp.ofVal v) = Exp.ofVal v' := (Exp.ofVal_of_toVal_some htv).symm
    have key : tglWp E (K.fill (Exp.ofVal v)) Φ ≡
               iprop(∀ (σ' : State) (ε' : ENNReal),
                 (stateInterp σ' ∗ errInterp ε') -∗
                   |={E}=> stateInterp σ' ∗ errInterp ε' ∗ Φ v') := by
      rw [heq]; exact tglWp_unfold_value
    imod HW' with ⟨Hσ', Hε', HInner⟩
    ihave HInner' := (BI.equiv_iff.mp key).1 $$ HInner
    iapply HInner' $$ %σ %ε
    isplitl [Hσ']; · iexact Hσ'
    iexact Hε'
  | none =>
    -- `(K.fill (ofVal v)).toVal? = none`; use the step-form unfold.
    imod HW' with ⟨Hσ', Hε', HInner⟩
    ihave HInner' := (BI.equiv_iff.mp (tglWp_unfold_step htv)).1 $$ HInner
    iapply HInner' $$ %σ %ε
    isplitl [Hσ']; · iexact Hσ'
    iexact Hε'

end ErisWpGS
end TotalEris
end ProbLang
