module

public import Metrology.ProbLang.Exec

@[expose] public section

/-!
# Erasable and rewritable distributions

Port of `theories/common/erasable.v` from Clutch.

A distribution `μ` on states is *erasable at `σ`* if, for every expression `e`
and every step count `m`, sampling from `μ` and then running `execN m` is
equivalent to running `execN m` from `σ` directly. Intuitively: observing `μ`
instead of `σ` as the initial state does not change the termination
distribution at any finite step budget.

This is the core notion used in Clutch's `erasure.v` (lazy/eager sampling
equivalence) and in the tape-coupling rules of `coupling_rules.v`. The
language-parametric version is specialized here to ProbLang.

**Caveat on strength.** Clutch's `erasable` is phrased over `distr val`
(val-projected `exec`), so it collapses tape differences at final values.
Our `Erasable` is phrased over `Measure Cfg` (unprojected), so it is
strictly stronger: a `dret σ` distribution satisfies it, but a
`tapePresample σ α`-style distribution does **not** (presampling genuinely
changes the final tape content). The `tapePresample` theorems in
`Erasure.lean` are therefore expressed as **couplings** (using `AddCoupl`
with an expression-projection relation), not as erasability witnesses.

We also port the companion notion of *rewritable*: a configuration
distribution `μ` is rewritable at `ρ` when `limExec ρ = μ >>= limExec`.
-/

namespace ProbLang


variable {rT : Type _} [ProbLangℝ rT]

open MeasureTheory Measure

/-! ## Erasable -/

/-- A state distribution `μ` is *erasable at `σ`* if, for every expression
`e` and every finite step budget `m`, binding `μ` into `execN m ⟨e, ·⟩`
produces the same measure as running `execN m` directly from `σ`. -/
def Erasable (μ : Measure (State rT)) (σ : State rT) : Prop :=
  ∀ (e : Exp rT) (m : Nat),
    μ.bind (fun σ' => execN m ⟨e, σ'⟩) = execN m ⟨e, σ⟩

/-- Two measures on `Cfg` are equal iff they agree on every singleton.
Uses `⊤`-measurable space + countability of `Cfg` via `tsum` over
singletons. -/
theorem Cfg.measure_ext_singletons [Countable rT] [MeasurableSingletonClass rT]
    {μ ν : Measure (Cfg rT)}
    (h : ∀ c : Cfg rT, μ {c} = ν {c}) : μ = ν := by
  refine Measure.ext fun S _ => ?_
  -- Decompose `S` as a countable disjoint union of singletons indexed
  -- by the subtype `↑S`, then evaluate the union via `measure_iUnion`.
  have hSeq : (⋃ c : S, ({(c : Cfg rT)} : Set (Cfg rT))) = S := by
    ext c; simp
  have hdecomp : ∀ μ' : Measure (Cfg rT),
      μ' S = ∑' c : S, μ' ({(c : Cfg rT)} : Set (Cfg rT)) := by
    intro μ'
    conv_lhs => rw [← hSeq]
    exact measure_iUnion
      (f := fun c : S => ({c.val} : Set (Cfg rT)))
      (fun i j hij => Set.disjoint_singleton.mpr fun heq => hij (Subtype.ext heq))
      (fun _ => .of_discrete)
  rw [hdecomp μ, hdecomp ν]
  exact tsum_congr (fun c => h c)

namespace Erasable

/-- The dirac distribution at `σ` is erasable at `σ`. The bind collapses
to a single evaluation at `σ`, after which the projection is trivially
equal. -/
@[discrete] -- dret'
theorem dret [Countable rT] [MeasurableSingletonClass rT]
    (σ : State rT) : Erasable (Measure.dirac σ) σ := by
  intro e m
  rw [Measure.dirac_bind (f := fun σ' => execN m ⟨e, σ'⟩) Measurable.of_discrete]

theorem dret' (σ : State rT) : Erasable (Measure.dirac σ) σ := by
  intro e m
  rw [Measure.dirac_bind (f := fun σ' => execN m ⟨e, σ'⟩) (by measurability)]

theorem dbind'
    {μ₁ : Measure (State rT)} {μ₂ : State rT → Measure (State rT)} {σ : State rT}
    (h₁ : Erasable μ₁ σ) (h₂ : ∀ σ', Erasable (μ₂ σ') σ') (hm₂ : AEMeasurable μ₂ μ₁) :
    Erasable (μ₁.bind μ₂) σ := by
  intro e m
  rw [Measure.bind_bind hm₂ (Measurable.aemeasurable (by measurability))]
  conv_lhs =>
    rw [show (fun σ' => (μ₂ σ').bind (fun σ'' => execN m ⟨e, σ''⟩))
            = (fun σ' => execN m ⟨e, σ'⟩) from by
          funext σ'; exact h₂ σ' e m]
  exact h₁ e m

theorem lim_exec'
    {μ : Measure (State rT)} {σ : State rT} (h : Erasable μ σ) (e : Exp rT) :
    μ.bind (fun σ' => limExec ⟨e, σ'⟩) = limExec ⟨e, σ⟩ := by
  ext S HS
  rw [bind_apply HS (by measurability)]
  simp_rw [limExec_apply _ HS]
  rw [lintegral_iSup (fun n => ?G1) ?G2]
  case G1 =>
    exact (Measure.measurable_coe HS).comp ((execN_measurable n).comp (by measurability))
  case G2 =>
    exact fun n m hnm a => execN_mono hnm ⟨e, a⟩ S
  suffices hbind : ∀ n, ∫⁻ σ', (execN n ⟨e, σ'⟩) S ∂μ = (execN n ⟨e, σ⟩) S by
    simp [hbind]
  intro n
  have hμ : (μ.bind fun σ' ↦ execN n ⟨e, σ'⟩) S = (execN n ⟨e, σ⟩) S := congrArg (· S) (h e n)
  rw [← hμ, bind_apply HS (by measurability)]

@[discrete] -- lim_exec'
theorem lim_exec [Countable rT] [MeasurableSingletonClass rT]
    {μ : Measure (State rT)} {σ : State rT} (h : Erasable μ σ) (e : Exp rT) :
    μ.bind (fun σ' => limExec ⟨e, σ'⟩) = limExec ⟨e, σ⟩ :=
  lim_exec' h e

theorem dret_final {μ : Measure (State rT)} {σ : State rT} {e : Exp rT} (hv : IsVal e)
    (h : Erasable μ σ) :
    μ.bind (fun σ' => Measure.dirac (⟨e, σ'⟩ : Cfg rT)) =
      Measure.dirac (⟨e, σ⟩ : Cfg rT) := by
  -- `execN 1 ⟨e, σ'⟩ = dirac ⟨e, σ'⟩` for values (isValue is on the `Cfg.expr`
  -- component, which unifies with `e` definitionally).
  have hstep : ∀ σ' : State rT,
      execN 1 (⟨e, σ'⟩ : Cfg rT) = Measure.dirac (⟨e, σ'⟩ : Cfg rT) := by
    intro σ'
    exact execN_succ_isValue (ρ := ⟨e, σ'⟩) hv.toIsValue 0
  calc μ.bind (fun σ' => Measure.dirac (⟨e, σ'⟩ : Cfg rT))
      = μ.bind (fun σ' => execN 1 ⟨e, σ'⟩) := by simp only [hstep]
    _ = execN 1 ⟨e, σ⟩ := h e 1
    _ = Measure.dirac ⟨e, σ⟩ := hstep σ

theorem pexecN_lim_exec
    {μ : Measure (State rT)} {σ : State rT}
    (h : Erasable μ σ) (n : Nat) (e : Exp rT) :
    (μ.bind (fun σ' => pexecN n ⟨e, σ'⟩)).bind limExec = limExec ⟨e, σ⟩ := by
  rw [Measure.bind_bind
        (Measurable.aemeasurable (by measurability))
        (Measurable.aemeasurable (by measurability))]
  conv_lhs =>
    rw [show (fun σ' => (pexecN n ⟨e, σ'⟩).bind limExec)
           = (fun σ' => limExec ⟨e, σ'⟩) from by
         funext σ'; exact (limExec_pexecN n ⟨e, σ'⟩).symm]
  exact h.lim_exec' e

theorem mass
    {μ : Measure (State rT)} {σ : State rT} (h : Erasable μ σ) :
    μ Set.univ = 1 := by
  have hv : IsVal (Exp.lit (rT := rT) .unit) := .lit
  have hstep : ∀ σ' : State rT,
      execN 1 ((⟨.lit .unit, σ'⟩ : Cfg rT)) = Measure.dirac (⟨.lit .unit, σ'⟩ : Cfg rT) :=
    fun σ' => execN_succ_isValue (ρ := ⟨.lit .unit, σ'⟩) hv.toIsValue 0
  have h1 := h (.lit .unit) 1
  have hboth := congrArg (fun ν => ν (Set.univ : Set (Cfg rT))) h1
  simp only at hboth
  rw [hstep σ] at hboth
  rw [Measure.dirac_apply' _ .univ] at hboth
  simp at hboth
  rw [bind_apply .univ (Measurable.aemeasurable (by measurability))] at hboth
  simp_rw [hstep] at hboth
  simp_rw [Measure.dirac_apply' _ .univ] at hboth
  simp at hboth
  exact hboth


/-- A two-branch erasable combinator: dispatching on a measurable Boolean
function through a total distribution yields an erasable combination. -/
theorem dbind_predicate [Countable rT] [MeasurableSingletonClass rT]
    {A : Type*} [MeasurableSpace A] [DiscreteMeasurableSpace A]
    {μ : Measure A} {μ₁ μ₂ : Measure (State rT)} {σ : State rT} {f : A → Bool}
    (hμ : μ Set.univ = 1) (h₁ : Erasable μ₁ σ) (h₂ : Erasable μ₂ σ) :
    Erasable (μ.bind (fun a => if f a then μ₁ else μ₂)) σ := by
  intro e m
  rw [Measure.bind_bind
        (Measurable.aemeasurable .of_discrete)
        (Measurable.aemeasurable .of_discrete)]
  have hker : ∀ a : A,
      (if f a then μ₁ else μ₂).bind (fun σ' => execN m ⟨e, σ'⟩) = execN m ⟨e, σ⟩ := by
    intro a
    split
    · exact h₁ e m
    · exact h₂ e m
  conv_lhs => rw [show (fun a => (if f a then μ₁ else μ₂).bind
                    (fun σ' => execN m ⟨e, σ'⟩))
                = (fun _ => execN m ⟨e, σ⟩) from by funext a; exact hker a]
  -- Now we have `μ.bind (fun _ => execN m ⟨e, σ⟩) = execN m ⟨e, σ⟩`.
  -- Evaluate both sides on every set: LHS reduces to `μ Set.univ * (RHS S) = 1 * (RHS S)`.
  refine Measure.ext fun S _ => ?_
  rw [bind_apply MeasurableSet.of_discrete Measurable.of_discrete.aemeasurable,
      lintegral_const, hμ, mul_one]

end Erasable

/-! ## Rewritable -/

/-- A configuration distribution `μ` is *rewritable at `ρ`* if running
`limExec` on `ρ` is equivalent to sampling from `μ` and then running
`limExec` on the sampled configuration. -/
def Rewritable (ρ : Cfg rT) (μ : Measure (Cfg rT)) : Prop :=
  limExec ρ = μ.bind limExec

namespace Rewritable

/-- Dirac rewritability: `limExec ρ = dirac ρ >>= limExec`. -/
theorem dret [Countable rT] [MeasurableSingletonClass rT]
    (ρ : Cfg rT) : Rewritable ρ (Measure.dirac ρ) := by
  show limExec ρ = (Measure.dirac ρ).bind limExec
  rw [Measure.dirac_bind Measurable.of_discrete]

/-- Every finite unfolding `pexecN m ρ` is rewritable at `ρ`. -/
theorem ofPexecN [Countable rT] [MeasurableSingletonClass rT]
    (ρ : Cfg rT) (m : Nat) : Rewritable ρ (ProbLang.pexecN m ρ) :=
  limExec_pexecN m ρ

/-- Erasability on the state component lifts to rewritability on the
configuration: if `μ` is erasable at `ρ.state`, then binding `ρ.expr`
onto samples from `μ` gives a rewritable `Cfg`-distribution. -/
theorem of_erasable [Countable rT] [MeasurableSingletonClass rT]
    {ρ : Cfg rT} {μ : Measure (State rT)} (h : Erasable μ ρ.state) :
    Rewritable ρ (μ.bind (fun σ => Measure.dirac (⟨ρ.expr, σ⟩ : Cfg rT))) := by
  show limExec ρ
      = (μ.bind (fun σ => Measure.dirac (⟨ρ.expr, σ⟩ : Cfg rT))).bind limExec
  rw [Measure.bind_bind
        (Measurable.aemeasurable .of_discrete)
        (Measurable.aemeasurable .of_discrete)]
  have hker : (fun σ : State rT => (Measure.dirac (⟨ρ.expr, σ⟩ : Cfg rT)).bind limExec)
       = (fun σ : State rT => limExec ⟨ρ.expr, σ⟩) := by
    funext σ
    rw [Measure.dirac_bind (f := limExec) Measurable.of_discrete]
  rw [hker, h.lim_exec ρ.expr]

/-- Erasability combined with `pexecN`: push `μ` in on the state side,
then unfold `pexecN m` inside. -/
theorem of_erasable_pexecN [Countable rT] [MeasurableSingletonClass rT]
    {ρ : Cfg rT} {μ : Measure (State rT)} (m : Nat)
    (h : Erasable μ ρ.state) :
    Rewritable ρ (μ.bind (fun σ => pexecN m ⟨ρ.expr, σ⟩)) := by
  show limExec ρ = (μ.bind (fun σ => pexecN m ⟨ρ.expr, σ⟩)).bind limExec
  rw [Measure.bind_bind
        (Measurable.aemeasurable .of_discrete)
        (Measurable.aemeasurable .of_discrete)]
  have : (fun σ => (pexecN m ⟨ρ.expr, σ⟩).bind limExec)
       = (fun σ => limExec ⟨ρ.expr, σ⟩) := by
    funext σ; exact (limExec_pexecN m ⟨ρ.expr, σ⟩).symm
  rw [this, h.lim_exec ρ.expr]

/-! ### Countability-free variants

These mirror the `@[discrete]` lemmas above but route through the
countability-free `limExec.measurable` and `Erasable.lim_exec'` instead of
`Measurable.of_discrete` / `Erasable.lim_exec`, so they hold for a diffuse `rT`. -/

/-- Dirac rewritability, countability-free: `limExec ρ = dirac ρ >>= limExec`. -/
theorem dret' (ρ : Cfg rT) : Rewritable ρ (Measure.dirac ρ) := by
  show limExec ρ = (Measure.dirac ρ).bind limExec
  rw [Measure.dirac_bind (f := limExec) limExec.measurable]

/-- Every finite unfolding `pexecN m ρ` is rewritable at `ρ`, countability-free. -/
theorem ofPexecN' (ρ : Cfg rT) (m : Nat) : Rewritable ρ (ProbLang.pexecN m ρ) :=
  limExec_pexecN m ρ

/-- Erasability on the state component lifts to rewritability, countability-free. -/
theorem of_erasable' {ρ : Cfg rT} {μ : Measure (State rT)} (h : Erasable μ ρ.state) :
    Rewritable ρ (μ.bind (fun σ => Measure.dirac (⟨ρ.expr, σ⟩ : Cfg rT))) := by
  show limExec ρ
      = (μ.bind (fun σ => Measure.dirac (⟨ρ.expr, σ⟩ : Cfg rT))).bind limExec
  rw [Measure.bind_bind
        (Measurable.aemeasurable (by measurability))
        (Measurable.aemeasurable limExec.measurable)]
  have hker : (fun σ : State rT => (Measure.dirac (⟨ρ.expr, σ⟩ : Cfg rT)).bind limExec)
       = (fun σ : State rT => limExec ⟨ρ.expr, σ⟩) := by
    funext σ
    rw [Measure.dirac_bind (f := limExec) limExec.measurable]
  rw [hker, h.lim_exec' ρ.expr]

/-- Erasability combined with `pexecN`, countability-free. -/
theorem of_erasable_pexecN' {ρ : Cfg rT} {μ : Measure (State rT)} (m : Nat)
    (h : Erasable μ ρ.state) :
    Rewritable ρ (μ.bind (fun σ => pexecN m ⟨ρ.expr, σ⟩)) := by
  show limExec ρ = (μ.bind (fun σ => pexecN m ⟨ρ.expr, σ⟩)).bind limExec
  rw [Measure.bind_bind
        (Measurable.aemeasurable (by measurability))
        (Measurable.aemeasurable limExec.measurable)]
  have : (fun σ => (pexecN m ⟨ρ.expr, σ⟩).bind limExec)
       = (fun σ => limExec ⟨ρ.expr, σ⟩) := by
    funext σ; exact (limExec_pexecN m ⟨ρ.expr, σ⟩).symm
  rw [this, h.lim_exec' ρ.expr]

end Rewritable

/-- Turn a state-erasable `μ` plus an expression `e` into the `Cfg`-valued
distribution that pairs `e` with each sample. Mirrors Clutch's
`rewritable_of_erasable`. -/
noncomputable def rewritableOfErasable (μ : Measure (State rT)) (e : Exp rT) : Measure (Cfg rT) :=
  μ.bind (fun σ => Measure.dirac ⟨e, σ⟩)

end ProbLang
