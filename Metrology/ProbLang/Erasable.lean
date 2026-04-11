import Metrology.ProbLang.Exec

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

We also port the companion notion of *rewritable*: a configuration
distribution `μ` is rewritable at `ρ` when `limExec ρ = μ >>= limExec`.
-/

namespace ProbLang

open MeasureTheory Measure

/-! ## Erasable -/

/-- A state distribution `μ` is *erasable at `σ`* if, for every expression
`e` and every finite step budget `m`, binding `μ` into `execN m ⟨e, ·⟩`
produces the same measure as running `execN m` directly from `σ`. -/
def Erasable (μ : Measure State) (σ : State) : Prop :=
  ∀ (e : Exp) (m : Nat),
    μ.bind (fun σ' => execN m ⟨e, σ'⟩) = execN m ⟨e, σ⟩

/-- Two measures on `Cfg` are equal iff they agree on every singleton.
Uses `⊤`-measurable space + countability of `Cfg` via `tsum` over
singletons. -/
theorem Cfg.measure_ext_singletons {μ ν : Measure Cfg}
    (h : ∀ c : Cfg, μ {c} = ν {c}) : μ = ν := by
  refine Measure.ext fun S _ => ?_
  -- Decompose `S` as a countable disjoint union of singletons indexed
  -- by the subtype `↑S`, then evaluate the union via `measure_iUnion`.
  have hSeq : (⋃ c : S, ({(c : Cfg)} : Set Cfg)) = S := by
    ext c; simp
  have hdecomp : ∀ μ' : Measure Cfg,
      μ' S = ∑' c : S, μ' ({(c : Cfg)} : Set Cfg) := by
    intro μ'
    conv_lhs => rw [← hSeq]
    exact measure_iUnion
      (f := fun c : S => ({c.val} : Set Cfg))
      (fun i j hij => Set.disjoint_singleton.mpr fun heq => hij (Subtype.ext heq))
      (fun _ => .of_discrete)
  rw [hdecomp μ, hdecomp ν]
  exact tsum_congr (fun c => h c)

namespace Erasable

/-- The dirac distribution at `σ` is erasable at `σ`. -/
theorem dret (σ : State) : Erasable (Measure.dirac σ) σ := by
  intro e m
  rw [Measure.dirac_bind (f := fun σ' => execN m ⟨e, σ'⟩) Measurable.of_discrete]

/-- Erasable distributions compose under `bind`. If `μ₁` is erasable at `σ`
and `μ₂ σ'` is erasable at `σ'` for every `σ'` in the support of `μ₁`,
then `μ₁ >>= μ₂` is erasable at `σ`.

Clutch's proof has a support-conditional hypothesis (`μ₁ σ' > 0`). For
measures we strengthen it to an unconditional hypothesis; the
conditional form follows because any kernel can be modified on a null
set without changing the bind. -/
theorem dbind {μ₁ : Measure State} {μ₂ : State → Measure State} {σ : State}
    (h₁ : Erasable μ₁ σ) (h₂ : ∀ σ', Erasable (μ₂ σ') σ') :
    Erasable (μ₁.bind μ₂) σ := by
  intro e m
  rw [Measure.bind_bind
        (Measurable.aemeasurable .of_discrete)
        (Measurable.aemeasurable .of_discrete)]
  conv_lhs =>
    rw [show (fun σ' => (μ₂ σ').bind (fun σ'' => execN m ⟨e, σ''⟩))
            = (fun σ' => execN m ⟨e, σ'⟩) from by
          funext σ'; exact h₂ σ' e m]
  exact h₁ e m

/-! ### The load-bearing lemma: erasability lifts through `limExec`.

We prove `μ.bind (limExec ⟨e, ·⟩) = limExec ⟨e, σ⟩` by `Measure.ext` +
singleton decomposition, using monotone convergence (`lintegral_iSup`) to
swap the `iSup` in `limExec` with the outer `lintegral` from `bind_apply`.
The trickiest step — that the `iSup` of measures agrees pointwise on sets
with the pointwise `iSup` — is avoided by going through singletons
(where `limExec_apply` already supplies the needed equation) and then
decomposing arbitrary sets via `⋃ c ∈ S, {c}`, mirroring `limExec_univ`.
-/

/-- The main consequence: if `μ` is erasable at `σ`, then we can push `μ`
through `limExec` on any expression `e`.

Proof sketch: both sides of the equation are measures on `Cfg` determined
by their values on singletons. On a singleton `{c}`, both reduce via
`limExec_apply` to an iSup of `execN n _ {c}` values. The hypothesis `h e n`,
applied at `{c}`, gives exactly what we need to collapse the outer
`lintegral` to a constant `(execN n ⟨e, σ⟩) {c}`, and then `limExec_apply`
reassembles the RHS. Monotone convergence (`lintegral_iSup`) handles the
swap between `lintegral` and `iSup`. -/
theorem lim_exec {μ : Measure State} {σ : State} (h : Erasable μ σ) (e : Exp) :
    μ.bind (fun σ' => limExec ⟨e, σ'⟩) = limExec ⟨e, σ⟩ := by
  refine Cfg.measure_ext_singletons fun c => ?_
  -- LHS: apply `bind_apply`, then unfold `limExec` at singleton via `limExec_apply`.
  rw [bind_apply MeasurableSet.of_discrete Measurable.of_discrete.aemeasurable]
  simp_rw [limExec_apply]
  -- Swap `lintegral` with `iSup`: monotone convergence.
  rw [lintegral_iSup
        (fun _ => Measurable.of_discrete)
        (fun i j hij σ' => execN_mono_singleton hij ⟨e, σ'⟩ _)]
  -- Each `∫⁻ σ', (execN n ⟨e,σ'⟩) {c} ∂μ` equals `(execN n ⟨e,σ⟩) {c}`
  -- by the erasability hypothesis applied at `{c}`.
  have hbind : ∀ n,
      ∫⁻ σ', (execN n ⟨e, σ'⟩) {c} ∂μ = (execN n ⟨e, σ⟩) {c} := by
    intro n
    have hμ := congrArg (fun ν => ν ({c} : Set Cfg)) (h e n)
    simpa [bind_apply MeasurableSet.of_discrete
             Measurable.of_discrete.aemeasurable] using hμ
  simp only [hbind, ← limExec_apply]

/-- `dret v = μ >>= (λ _, dret v)` when `e` is already a value. This is
the specialization of `Erasable.lim_exec` to the value case. -/
theorem dret_final {μ : Measure State} {σ : State} {e : Exp} (hv : IsVal e)
    (h : Erasable μ σ) :
    μ.bind (fun σ' => Measure.dirac (⟨e, σ'⟩ : Cfg)) =
      Measure.dirac (⟨e, σ⟩ : Cfg) := by
  -- `execN 1 ⟨e, σ'⟩ = dirac ⟨e, σ'⟩` for values (isValue is on the `Cfg.expr`
  -- component, which unifies with `e` definitionally).
  have hstep : ∀ σ' : State,
      execN 1 (⟨e, σ'⟩ : Cfg) = Measure.dirac (⟨e, σ'⟩ : Cfg) := by
    intro σ'
    exact execN_succ_isValue (ρ := ⟨e, σ'⟩) hv.toIsValue 0
  calc μ.bind (fun σ' => Measure.dirac (⟨e, σ'⟩ : Cfg))
      = μ.bind (fun σ' => execN 1 ⟨e, σ'⟩) := by simp only [hstep]
    _ = execN 1 ⟨e, σ⟩ := h e 1
    _ = Measure.dirac ⟨e, σ⟩ := hstep σ

/-- Push an erasable distribution through `pexecN n` then `limExec`. -/
theorem pexecN_lim_exec {μ : Measure State} {σ : State}
    (h : Erasable μ σ) (n : Nat) (e : Exp) :
    (μ.bind (fun σ' => pexecN n ⟨e, σ'⟩)).bind limExec = limExec ⟨e, σ⟩ := by
  rw [Measure.bind_bind
        (Measurable.aemeasurable .of_discrete)
        (Measurable.aemeasurable .of_discrete)]
  conv_lhs =>
    rw [show (fun σ' => (pexecN n ⟨e, σ'⟩).bind limExec)
           = (fun σ' => limExec ⟨e, σ'⟩) from by
         funext σ'; exact (limExec_pexecN n ⟨e, σ'⟩).symm]
  exact h.lim_exec e

/-- An erasable distribution has total mass 1, provided the language has at
least one value (we use `.lit .unit`). -/
theorem mass {μ : Measure State} {σ : State} (h : Erasable μ σ) :
    μ Set.univ = 1 := by
  -- Specialize `h` to the unit literal (always a value) and 1 step.
  have hv : IsVal (Exp.lit .unit) := .lit
  have hstep : ∀ σ' : State,
      execN 1 ((⟨.lit .unit, σ'⟩ : Cfg)) = Measure.dirac (⟨.lit .unit, σ'⟩ : Cfg) :=
    fun σ' => execN_succ_isValue (ρ := ⟨.lit .unit, σ'⟩) hv.toIsValue 0
  have h1 := h (.lit .unit) 1
  -- Take `Set.univ`-mass of both sides of `h1`.
  have hboth := congrArg (fun ν => ν (Set.univ : Set Cfg)) h1
  simp only at hboth
  -- RHS mass: `(execN 1 _) univ = (dirac _) univ = 1`.
  rw [hstep σ] at hboth
  rw [Measure.dirac_apply' _ MeasurableSet.of_discrete] at hboth
  simp at hboth
  -- LHS mass: collapses to `μ Set.univ` via `bind_apply` + `hstep`.
  rw [bind_apply MeasurableSet.of_discrete
        Measurable.of_discrete.aemeasurable] at hboth
  simp_rw [hstep] at hboth
  simp_rw [Measure.dirac_apply' _ MeasurableSet.of_discrete] at hboth
  simp at hboth
  exact hboth

/-- A two-branch erasable combinator: dispatching on a measurable Boolean
function through a total distribution yields an erasable combination. -/
theorem dbind_predicate {A : Type*} [MeasurableSpace A] [DiscreteMeasurableSpace A]
    {μ : Measure A} {μ₁ μ₂ : Measure State} {σ : State} {f : A → Bool}
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
def Rewritable (ρ : Cfg) (μ : Measure Cfg) : Prop :=
  limExec ρ = μ.bind limExec

namespace Rewritable

/-- Dirac rewritability: `limExec ρ = dirac ρ >>= limExec`. -/
theorem dret (ρ : Cfg) : Rewritable ρ (Measure.dirac ρ) := by
  show limExec ρ = (Measure.dirac ρ).bind limExec
  rw [Measure.dirac_bind Measurable.of_discrete]

/-- Every finite unfolding `pexecN m ρ` is rewritable at `ρ`. -/
theorem ofPexecN (ρ : Cfg) (m : Nat) : Rewritable ρ (ProbLang.pexecN m ρ) :=
  limExec_pexecN m ρ

/-- Erasability on the state component lifts to rewritability on the
configuration: if `μ` is erasable at `ρ.state`, then binding `ρ.expr`
onto samples from `μ` gives a rewritable `Cfg`-distribution. -/
theorem of_erasable {ρ : Cfg} {μ : Measure State} (h : Erasable μ ρ.state) :
    Rewritable ρ (μ.bind (fun σ => Measure.dirac (⟨ρ.expr, σ⟩ : Cfg))) := by
  show limExec ρ
      = (μ.bind (fun σ => Measure.dirac (⟨ρ.expr, σ⟩ : Cfg))).bind limExec
  rw [Measure.bind_bind
        (Measurable.aemeasurable .of_discrete)
        (Measurable.aemeasurable .of_discrete)]
  have hker : (fun σ : State => (Measure.dirac (⟨ρ.expr, σ⟩ : Cfg)).bind limExec)
       = (fun σ : State => limExec ⟨ρ.expr, σ⟩) := by
    funext σ
    rw [Measure.dirac_bind (f := limExec) Measurable.of_discrete]
  rw [hker, h.lim_exec ρ.expr]

/-- Erasability combined with `pexecN`: push `μ` in on the state side,
then unfold `pexecN m` inside. -/
theorem of_erasable_pexecN {ρ : Cfg} {μ : Measure State} (m : Nat)
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

end Rewritable

/-- Turn a state-erasable `μ` plus an expression `e` into the `Cfg`-valued
distribution that pairs `e` with each sample. Mirrors Clutch's
`rewritable_of_erasable`. -/
noncomputable def rewritableOfErasable (μ : Measure State) (e : Exp) : Measure Cfg :=
  μ.bind (fun σ => Measure.dirac ⟨e, σ⟩)

end ProbLang
