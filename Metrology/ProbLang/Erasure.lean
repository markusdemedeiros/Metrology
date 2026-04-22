import Metrology.ProbLang.Erasable
import Metrology.ProbLang.Metatheory

/-!
# Erasure: presampling on tapes is invisible

Port of `theories/prob_lang/erasure.v` from Clutch, reformulated to avoid
introducing a language-level `state_step` primitive.

The headline theorem `execN_tape_presample_expr_eq` says: appending a
uniformly-sampled value onto an *existing* tape `α` of `σ` does not change
`execN m ⟨e, σ⟩` *at the expression level* (i.e. after projecting the
post-configuration by `(·.expr)`). Equivalently, the local "uniform
presample" distribution `tapePresample σ α` on `State` is `ErasableExpr`
at `σ`.

The full-`Cfg` version is false (presample genuinely changes the final tape
content), but the projected version is exactly what the adequacy layer
observes. All `state_step`-specialized corollaries of Clutch's `erasure.v`
are dropped in favor of the general `ErasableExpr` wrappers, which take an
arbitrary `μ : Measure State` and do the lifting. Clients construct
`tapePresample` themselves and invoke `ErasableExpr.tapePresample` to get
the witness.
-/

namespace ProbLang

open MeasureTheory Measure

/-! ## Local uniform-presample distribution

These are file-local helpers used to *state* erasure, without adding any
new primitives to the language. In particular, `tapePresample σ α` is
**not** a language-level transition: it is just the `Measure State`
obtained by "uniformly appending onto an existing tape `α`". Clients of
erasure construct it when invoking the `ARcoupl` wrappers below.
-/

/-- The uniform distribution on indices `{ z : Int // 0 ≤ z ∧ z < N }`.
If `N ≤ 0`, the subtype is empty and we return the zero measure; the
relevant erasure lemmas only apply to existing tapes, which always have a
positive bound. -/
noncomputable def tapeIndexUniform (N : Int) :
    Measure { z : Int // 0 ≤ z ∧ z < N } :=
  if h : (Finset.Ico 0 N).Nonempty then
    -- Map the uniform distribution on `Finset.Ico 0 N` into the subtype.
    (PMF.uniformOfFinset (Finset.Ico 0 N) h).toMeasure.map
      (fun z =>
        if hz : 0 ≤ z ∧ z < N then ⟨z, hz⟩
        else ⟨0, by
          -- Unreachable for `z` in the support, but we need a
          -- `{ z // 0 ≤ z ∧ z < N }` to make the function total. If
          -- `N ≤ 0` this branch is dead on the left already.
          rcases h with ⟨w, hw⟩
          simp [Finset.mem_Ico] at hw
          exact ⟨le_refl _, by omega⟩⟩)
  else 0

/-- The local "uniform presample on tape `α`" distribution on `State`.
Given an existing tape `α` of bound `N` with current content `bs`, this
returns the `State`-measure obtained by sampling `n ∈ [0, N)` uniformly
and appending `n` to the tape. This is the analogue of Clutch's
`state_step σ α`, localized to this file so as not to pollute the
language-level semantics. If the tape `α` is absent, we return `0`. -/
noncomputable def tapePresample (σ : State) (α : Loc) : Measure State :=
  match σ.tapes[α]? with
  | none => 0
  | some ⟨N, bs⟩ =>
      (tapeIndexUniform N).bind (fun n =>
        Measure.dirac (σ.update_tapes (·.insert α ⟨N, bs ++ [n]⟩)))

/-- `tapeIndexUniform N` is a probability measure when `0 < N`. -/
theorem tapeIndexUniform_univ_eq_one {N : Int} (hN : 0 < N) :
    (tapeIndexUniform N) Set.univ = 1 := by
  unfold tapeIndexUniform
  have hNonempty : (Finset.Ico 0 N).Nonempty := by
    refine ⟨0, Finset.mem_Ico.mpr ⟨le_refl _, hN⟩⟩
  rw [dif_pos hNonempty]
  haveI : IsProbabilityMeasure
      (PMF.uniformOfFinset (Finset.Ico 0 N) hNonempty).toMeasure :=
    PMF.toMeasure.isProbabilityMeasure _
  rw [Measure.map_apply Measurable.of_discrete MeasurableSet.univ]
  simp only [Set.preimage_univ, measure_univ]

/-- `tapePresample σ α` is a probability measure when `α` is an existing
tape with positive bound. -/
theorem tapePresample_univ_eq_one {σ : State} {α : Loc} {t : Tape}
    (h : σ.tapes[α]? = some t) (hN : 0 < t.bound) :
    (tapePresample σ α) Set.univ = 1 := by
  obtain ⟨N, bs⟩ := t
  simp only [tapePresample, h]
  rw [Measure.bind_apply MeasurableSet.univ
        Measurable.of_discrete.aemeasurable]
  simp_rw [Measure.dirac_apply' _ MeasurableSet.univ, Set.indicator_univ,
    Pi.one_apply, lintegral_one]
  exact tapeIndexUniform_univ_eq_one hN


/-! ## Bind-map distributivity (local helper)

A small helper used throughout this file: `.map` distributes over `.bind`.
Both arguments are over `Measure`-types with `⊤` measurable spaces, so
all measurability side conditions are `.of_discrete`. -/
theorem Measure.bind_map_comm {α β γ : Type*}
    [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    [DiscreteMeasurableSpace α] [DiscreteMeasurableSpace β]
    [DiscreteMeasurableSpace γ]
    (μ : Measure α) (k : α → Measure β) (f : β → γ) :
    (μ.bind k).map f = μ.bind (fun a => (k a).map f) := by
  refine Measure.ext fun S hS => ?_
  rw [Measure.map_apply .of_discrete hS,
      Measure.bind_apply (by exact .of_discrete) Measurable.of_discrete.aemeasurable,
      Measure.bind_apply hS Measurable.of_discrete.aemeasurable]
  simp_rw [Measure.map_apply .of_discrete hS]

/-! ## Tape persistence through a prim step

Before the core induction, we note that tape `α` is never *deleted* by a
`primStep`: it either stays untouched (in all heap/arith/ctl cases) or is
modified in a way that preserves its bound (in the `.rand α` case, which
consumes one sample from the head but leaves the rest in place). The
precise fact we need: for every `ρ` in the support of `primStep ⟨e, σ⟩`,
`ρ.state.tapes[α]?` is `some t'` for some `t'` with the same bound as `t`.
We package this as an a.e. statement for use in the induction step. -/

/-- Tape persistence through a single prim step (support form): if
`σ.tapes[α]? = some t`, then every `ρ` with `primStep ⟨e, σ⟩ {ρ} > 0` has
`ρ.state.tapes[α]?` equal to `some t'` for some `t'` with `t'.bound = t.bound`.

This is a case analysis on `headStep`, but cleaner than the full commutation
because we only track the bound, not the full tape content. -/
theorem primStep_tape_persists_support
    {σ : State} {α : Loc} {e : Exp} {t : Tape} {ρ : Cfg}
    (h : σ.tapes[α]? = some t)
    (hρ : 0 < primStep ⟨e, σ⟩ {ρ}) :
    ∃ t' : Tape, ρ.state.tapes[α]? = some t' ∧ t'.bound = t.bound := by
  obtain ⟨e₂, σ₂⟩ := ρ
  -- Destructure primStep via `prim_step_iff` to get head-step support witness.
  obtain ⟨K, e₁', e₂', _hfill1, _hfill2, hhs⟩ := prim_step_iff.mp hρ
  rw [headStep_support_iff] at hhs
  -- Case-split on the `HeadStepSupport` constructor; in each case,
  -- determine what happens to tape α.
  cases hhs with
  | BetaLamS =>
    exact ⟨t, h, rfl⟩
  | BetaFixS =>
    exact ⟨t, h, rfl⟩
  | UnOpS =>
    exact ⟨t, h, rfl⟩
  | BinOpS =>
    exact ⟨t, h, rfl⟩
  | IfTrueS =>
    exact ⟨t, h, rfl⟩
  | IfFalseS =>
    exact ⟨t, h, rfl⟩
  | FstS =>
    exact ⟨t, h, rfl⟩
  | SndS =>
    exact ⟨t, h, rfl⟩
  | CaseLS =>
    exact ⟨t, h, rfl⟩
  | CaseRS =>
    exact ⟨t, h, rfl⟩
  | AllocS _ _ hσ' =>
    -- Heap alloc: σ₂ = update_heap σ ..., tapes unchanged.
    subst hσ'
    exact ⟨t, by simp [State.update_heap, h], rfl⟩
  | LoadS =>
    exact ⟨t, h, rfl⟩
  | StoreS _ _ hσ' =>
    subst hσ'
    exact ⟨t, by simp [State.update_heap, h], rfl⟩
  | RandNoTapeS =>
    exact ⟨t, h, rfl⟩
  | TapeS hℓ hσ' =>
    -- Tape allocation at fresh location ℓ. We need ℓ ≠ α so α survives.
    -- By `State.fresh_loc_upd_some` / `upd_diff_tape_tot`.
    subst hσ' hℓ
    have hne : σ.tapes.fresh ≠ α := Std.ExtTreeMap.elem_fresh_ne h
    refine ⟨t, ?_, rfl⟩
    exact State.upd_diff_tape_tot (hne.symm) |>.trans h
  | RandTapeS _hz hα' _hN _hv hσ' =>
    -- Rand read from a tape (call it β). Case-split on whether β = α.
    -- `RandTapeS` introduces six auto-implicits (in order): β, N, nn, ns, v, z.
    -- Bind all six by name so reordering/adding an implicit to the
    -- constructor signature produces a loud error here instead of a silent
    -- shift in meaning.
    subst hσ'
    rename_i β N _ns _v _z
    by_cases hαβ : α = β
    · -- Same tape: consumes head, leaves tail `ns✝`. Bound = N, unchanged.
      subst hαβ
      rw [hα'] at h
      have ht := Option.some.inj h
      subst ht
      refine ⟨_, State.upd_tape_some _ _ _, rfl⟩
    · refine ⟨t, ?_, rfl⟩
      have hne : α ≠ β := hαβ
      rw [show (σ.update_tapes fun x => x.insert β _).tapes[α]? = σ.tapes[α]?
          from State.upd_diff_tape_tot hne]
      exact h
  | RandTapeEmptyS _ _ _ _ _ hσ' =>
    subst hσ'
    exact ⟨t, h, rfl⟩
  | RandTapeOtherS _ _ _ _ _ hσ' =>
    subst hσ'
    exact ⟨t, h, rfl⟩
  | ScrutSuccessS =>
    exact ⟨t, h, rfl⟩
  | ScrutFailureS =>
    exact ⟨t, h, rfl⟩

/-- Tape persistence, a.e. form: the set of `ρ`s where tape `α` is either
absent or has a different bound from `t` has measure 0 under `primStep ⟨e, σ⟩`.
Derived from the support form via the fact that singletons outside the
support have measure 0 (every discrete measure). -/
theorem primStep_tape_persists
    {σ : State} {α : Loc} {e : Exp} {t : Tape}
    (h : σ.tapes[α]? = some t) :
    ∀ᵐ ρ ∂(primStep ⟨e, σ⟩),
      ∃ t' : Tape, ρ.state.tapes[α]? = some t' ∧ t'.bound = t.bound := by
  -- Use `MeasureTheory.ae_iff` (the filter-level form).
  refine (MeasureTheory.ae_iff).mpr ?_
  rw [show {ρ : Cfg | ¬ ∃ t' : Tape, ρ.state.tapes[α]? = some t' ∧ t'.bound = t.bound}
        = ⋃ ρ ∈ {ρ : Cfg | ¬ ∃ t' : Tape, ρ.state.tapes[α]? = some t' ∧ t'.bound = t.bound},
            ({ρ} : Set Cfg) from by ext; simp]
  refine (measure_biUnion_null_iff (Set.to_countable _)).mpr ?_
  intro ρ hρ
  by_contra hne
  rw [← ne_eq, ← pos_iff_ne_zero] at hne
  exact hρ (primStep_tape_persists_support h hne)

/-! ## Structural properties of `tapePresample`

Lemmas characterizing what `tapePresample σ α` preserves or commutes with.
These feed the main induction: the heap and non-`α` tapes are a.e.
unchanged, and heap/tape updates commute with presampling. -/

/-- **Pointwise-support sufficient condition for a.e. statements on
`tapePresample σ α`.** Every state in the support of `tapePresample σ α`
with `σ.tapes[α]? = some ⟨N, bs⟩` has the form
`σ.update_tapes (·.insert α ⟨N, bs ++ [n]⟩)` for some sampled `n`. Proving
a property `P` holds a.e. on `tapePresample σ α` therefore reduces to
checking it at every such update — bypassing the `bind`/`lintegral`/
`indicator` scaffolding. -/
theorem tapePresample_ae {σ : State} {α : Loc} {N : Int}
    {bs : List { z : Int // 0 ≤ z ∧ z < N }} (h : σ.tapes[α]? = some ⟨N, bs⟩)
    {P : State → Prop}
    (hP : ∀ n, P (σ.update_tapes (·.insert α ⟨N, bs ++ [n]⟩))) :
    ∀ᵐ σ' ∂(tapePresample σ α), P σ' := by
  refine MeasureTheory.ae_iff.mpr ?_
  simp only [tapePresample, h]
  rw [Measure.bind_apply MeasurableSet.of_discrete
        Measurable.of_discrete.aemeasurable]
  refine (lintegral_eq_zero_iff Measurable.of_discrete).mpr ?_
  refine MeasureTheory.ae_of_all _ fun n => ?_
  show (Measure.dirac (σ.update_tapes (·.insert α ⟨N, bs ++ [n]⟩)))
        {a | ¬P a} = 0
  rw [Measure.dirac_apply' _ MeasurableSet.of_discrete,
      Set.indicator_of_notMem]
  simp only [Set.mem_setOf_eq, not_not]
  exact hP n

/-- `tapePresample σ α` is heap-preserving: every state in its support has
the same heap as `σ`. -/
theorem tapePresample_heap_eq {σ : State} {α : Loc} :
    ∀ᵐ σ' ∂(tapePresample σ α), σ'.heap = σ.heap := by
  cases hsome : σ.tapes[α]? with
  | none =>
    refine MeasureTheory.ae_iff.mpr ?_
    simp [tapePresample, hsome]
  | some t =>
    obtain ⟨N, bs⟩ := t
    exact tapePresample_ae hsome fun _ => by simp [State.update_tapes]

/-- `tapePresample σ α` only touches tape `α`: for any other location
`α_lbl ≠ α`, the lookup at `α_lbl` is a.e. unchanged. -/
theorem tapePresample_tape_ne_ae {σ : State} {α α_lbl : Loc} {t : Tape}
    (h : σ.tapes[α]? = some t) (hne : α_lbl ≠ α) :
    ∀ᵐ σ' ∂(tapePresample σ α), σ'.tapes[α_lbl]? = σ.tapes[α_lbl]? := by
  obtain ⟨N, bs⟩ := t
  exact tapePresample_ae h fun _ => State.upd_diff_tape_tot hne

/-- **Heap-pull helper for tape-presample binds.**

If a kernel `k` only inspects the heap of its state argument (passed
explicitly as the first argument), binding it through `tapePresample σ α`
is equivalent to binding it with the heap fixed to `σ.heap`. This is
because `tapePresample σ α` only modifies tapes — every state in its
support has heap equal to `σ.heap`.

Used to dispatch the heap-touching cases (load, store, alloc) of
`headStep_tapePresample_comm` cleanly, without running into Lean's
instance-resolution issues on `σ'.heap[ℓ]?` lookups inside anonymous
lambdas. -/
theorem tapePresample_bind_pull_heap
    {σ : State} {α : Loc}
    (k : Std.ExtTreeMap Loc Val compare → State → Measure Cfg) :
    (tapePresample σ α).bind (fun σ' => k σ'.heap σ') =
      (tapePresample σ α).bind (fun σ' => k σ.heap σ') := by
  -- Both sides equal each other a.e. on tapePresample because every state
  -- in its support has heap = σ.heap.
  unfold tapePresample
  cases hsome : σ.tapes[α]? with
  | none =>
    show ((0 : Measure State).bind _) = _
    rw [Measure.bind_zero_left, Measure.bind_zero_left]
  | some t =>
    -- Both binds reduce to (tapeIndexUniform t.bound).bind (fun n => ...)
    -- and pointwise the inner kernel evaluates to the same thing because
    -- (σ.update_tapes ...).heap = σ.heap.
    rw [Measure.bind_bind
          Measurable.of_discrete.aemeasurable
          Measurable.of_discrete.aemeasurable,
        Measure.bind_bind
          Measurable.of_discrete.aemeasurable
          Measurable.of_discrete.aemeasurable]
    congr 1
    funext n'
    rw [Measure.dirac_bind (f := _) Measurable.of_discrete,
        Measure.dirac_bind (f := _) Measurable.of_discrete]
    -- Both sides: k (σ'.heap) σ' = k σ.heap σ' where σ' = σ.update_tapes ...
    -- The two are equal because σ'.heap = σ.heap.
    show k (σ.update_tapes _).heap _ = k σ.heap _
    simp [State.update_tapes]

/-- Heap updates commute with tape presampling. Specifically:
`tapePresample (σ.update_heap f) α = (tapePresample σ α).map (·.update_heap f)`. -/
theorem tapePresample_update_heap_comm
    {σ : State} {α : Loc} (f : Std.ExtTreeMap Loc Val compare → Std.ExtTreeMap Loc Val compare) :
    tapePresample (σ.update_heap f) α =
      (tapePresample σ α).map (·.update_heap f) := by
  unfold tapePresample
  -- (σ.update_heap f).tapes[α]? = σ.tapes[α]?
  have htapes : (σ.update_heap f).tapes[α]? = σ.tapes[α]? := by
    simp [State.update_heap]
  rw [htapes]
  cases hsome : σ.tapes[α]? with
  | none =>
    show (0 : Measure State) = _
    rw [Measure.map_zero]
  | some t =>
    obtain ⟨N, bs⟩ := t
    simp only
    -- Both sides are (tapeIndexUniform N).bind (...)
    rw [Measure.bind_map_comm]
    congr 1
    funext n'
    rw [Measure.map_dirac (f := (·.update_heap f))
          (σ.update_tapes (·.insert α ⟨N, bs ++ [n']⟩))]
    -- (σ.update_heap f).update_tapes _ = (σ.update_tapes _).update_heap f
    simp [State.update_tapes, State.update_heap]

/-- Tape updates at keys other than `α` commute with tape presampling.
`tapePresample (σ.update_tapes f) α = (tapePresample σ α).map (·.update_tapes f)`,
provided `f` only modifies keys other than `α` in the sense that
`(σ.update_tapes f).tapes[α]? = σ.tapes[α]?` and the update/insert commute. -/
theorem tapePresample_update_tapes_ne_comm
    {σ : State} {α β : Loc} {v : Tape} (hne : β ≠ α) :
    tapePresample (σ.update_tapes (·.insert β v)) α =
      (tapePresample σ α).map (·.update_tapes (·.insert β v)) := by
  unfold tapePresample
  have htapes : (σ.update_tapes (·.insert β v)).tapes[α]? = σ.tapes[α]? :=
    State.upd_diff_tape_tot (Ne.symm hne)
  rw [htapes]
  cases hsome : σ.tapes[α]? with
  | none =>
    show (0 : Measure State) = _
    rw [Measure.map_zero]
  | some t =>
    obtain ⟨N, bs⟩ := t
    simp only
    rw [Measure.bind_map_comm]
    congr 1
    funext n'
    rw [show Measure.dirac ((σ.update_tapes (·.insert β v)).update_tapes
            (·.insert α ⟨N, bs ++ [n']⟩))
        = (Measure.dirac (σ.update_tapes (·.insert α ⟨N, bs ++ [n']⟩))).map
            (·.update_tapes (·.insert β v)) from by
      rw [Measure.map_dirac]; congr 1; exact State.upd_diff_tape_comm (Ne.symm hne)]

/-- Lintegral over `tapePresample σ α` unfolds to a lintegral over
`tapeIndexUniform N` against the presampled-state integrand. Combines the
unfolding of `tapePresample` with `lintegral_bind` + `lintegral_dirac'` so
call sites don't re-do the same 3-line scaffold. -/
theorem tapePresample_lintegral
    {σ : State} {α : Loc} {N : Int}
    {bs : List { z : Int // 0 ≤ z ∧ z < N }}
    (h : σ.tapes[α]? = some ⟨N, bs⟩) (f : State → ENNReal) :
    ∫⁻ σ', f σ' ∂tapePresample σ α
      = ∫⁻ n, f (σ.update_tapes (·.insert α ⟨N, bs ++ [n]⟩)) ∂tapeIndexUniform N := by
  simp only [tapePresample, h]
  rw [lintegral_bind Measurable.of_discrete.aemeasurable
        Measurable.of_discrete.aemeasurable]
  simp_rw [lintegral_dirac' _ Measurable.of_discrete]

/-- Lintegral form of `tapePresample_update_heap_comm`: integrating a
state-dependent integrand `f` against `tapePresample σ α` after a heap
update is the same as integrating `f` against `tapePresample` on the
updated state. Combines `lintegral_map` with `tapePresample_update_heap_comm`
so call sites skip the intermediate `.map` form. -/
theorem tapePresample_lintegral_update_heap
    {σ : State} {α : Loc}
    (g : Std.ExtTreeMap Loc Val compare → Std.ExtTreeMap Loc Val compare)
    (f : State → ENNReal) :
    ∫⁻ σ', f (σ'.update_heap g) ∂tapePresample σ α
      = ∫⁻ τ, f τ ∂tapePresample (σ.update_heap g) α := by
  rw [tapePresample_update_heap_comm,
      lintegral_map Measurable.of_discrete Measurable.of_discrete]

/-- Lintegral form of `tapePresample_update_tapes_ne_comm`. -/
theorem tapePresample_lintegral_update_tapes_ne
    {σ : State} {α β : Loc} {v : Tape} (hne : β ≠ α)
    (f : State → ENNReal) :
    ∫⁻ σ', f (σ'.update_tapes (·.insert β v)) ∂tapePresample σ α
      = ∫⁻ τ, f τ ∂tapePresample (σ.update_tapes (·.insert β v)) α := by
  rw [tapePresample_update_tapes_ne_comm hne,
      lintegral_map Measurable.of_discrete Measurable.of_discrete]

/-- `Cfg.uniform` as a bind over a PMF measure, with explicit state fiber. -/
theorem Cfg.uniform_eq_bind {z : Int} {σ : State} (hz : 0 < z) :
    Cfg.uniform z σ =
      ((PMF.uniformOfFinset (Finset.Ico 0 z)
            (Finset.nonempty_Ico.mpr hz)).toMeasure).bind
        (fun n => Measure.dirac (⟨.lit (.int n), σ⟩ : Cfg)) := by
  unfold Cfg.uniform Int.isPos Option.unwrapM
  rw [dif_pos hz]
  rw [Measure.bind_dirac_eq_map _ Measurable.of_discrete]

/-- **Commutation helper for `rand.plain` and `rand.tape.*`**.

Presampling onto tape `α` commutes with `Cfg.uniform z σ` in the sense
that pulling `tapePresample` outside the `Cfg.uniform` bind (on the RHS
as a per-post-state presample) gives back the original `tapePresample`-
then-`Cfg.uniform` composition. This is the only non-trivial headStep
case where the head-step result is a `Cfg.uniform` measure. -/
theorem tapePresample_bind_cfgUniform_comm
    {σ : State} {α : Loc} (z : Int) :
    (tapePresample σ α).bind (fun σ' => Cfg.uniform z σ') =
      (Cfg.uniform z σ).bind (fun ρ' =>
        (tapePresample ρ'.state α).bind
          (fun σ'' => Measure.dirac (⟨ρ'.expr, σ''⟩ : Cfg))) := by
  by_cases hz : 0 < z
  · -- Both sides reduce to a double bind over (tapePresample σ α) and
    -- the uniform int PMF; they agree by Fubini / bind-swap.
    -- Rewrite Cfg.uniform using the bind form.
    have huniform_σ := Cfg.uniform_eq_bind (σ := σ) hz
    -- LHS: push Cfg.uniform to the bind form at each σ'.
    have hLHS : (tapePresample σ α).bind (fun σ' => Cfg.uniform z σ') =
        (tapePresample σ α).bind (fun σ' =>
          ((PMF.uniformOfFinset (Finset.Ico 0 z)
                (Finset.nonempty_Ico.mpr hz)).toMeasure).bind
              (fun n => Measure.dirac (⟨.lit (.int n), σ'⟩ : Cfg))) := by
      congr 1; funext σ'; exact Cfg.uniform_eq_bind (σ := σ') hz
    rw [hLHS, huniform_σ]
    -- RHS: apply bind_bind and dirac_bind to collapse.
    rw [Measure.bind_bind
          Measurable.of_discrete.aemeasurable
          Measurable.of_discrete.aemeasurable]
    simp_rw [Measure.dirac_bind
              (f := fun ρ' : Cfg => (tapePresample ρ'.state α).bind
                (fun σ'' => Measure.dirac (⟨ρ'.expr, σ''⟩ : Cfg)))
              Measurable.of_discrete]
    -- Now both sides are:
    -- LHS: (tapePresample σ α).bind (fun σ' => PMF.bind (fun n => dirac ⟨lit (int n), σ'⟩))
    -- RHS: PMF.bind (fun n => (tapePresample σ α).bind (fun σ'' => dirac ⟨lit (int n), σ''⟩))
    -- Swap via lintegral_lintegral_swap.
    refine Measure.ext fun S hS => ?_
    rw [Measure.bind_apply hS Measurable.of_discrete.aemeasurable,
        Measure.bind_apply hS Measurable.of_discrete.aemeasurable]
    -- Rewrite each inner bind via lintegral_bind.
    have hLlint : ∀ σ' : State,
        ((((PMF.uniformOfFinset (Finset.Ico 0 z)
              (Finset.nonempty_Ico.mpr hz)).toMeasure).bind
                (fun n => Measure.dirac (⟨.lit (.int n), σ'⟩ : Cfg))) S) =
        ∫⁻ n, (Measure.dirac (⟨.lit (.int n), σ'⟩ : Cfg)) S
          ∂((PMF.uniformOfFinset (Finset.Ico 0 z)
              (Finset.nonempty_Ico.mpr hz)).toMeasure) := by
      intro σ'
      exact Measure.bind_apply hS Measurable.of_discrete.aemeasurable
    have hRlint : ∀ n : Int,
        ((tapePresample σ α).bind
            (fun σ'' => Measure.dirac (⟨.lit (.int n), σ''⟩ : Cfg))) S =
        ∫⁻ σ'', (Measure.dirac (⟨.lit (.int n), σ''⟩ : Cfg)) S
          ∂(tapePresample σ α) := by
      intro n
      exact Measure.bind_apply hS Measurable.of_discrete.aemeasurable
    simp_rw [hLlint, hRlint]
    -- Apply lintegral_lintegral_swap: outer is tapePresample σ α (SFinite
    -- since IsProbabilityMeasure), inner is the PMF measure.
    exact lintegral_lintegral_swap
      (μ := tapePresample σ α)
      (ν := ((PMF.uniformOfFinset (Finset.Ico 0 z)
              (Finset.nonempty_Ico.mpr hz)).toMeasure))
      (f := fun σ' n => (Measure.dirac (⟨.lit (.int n), σ'⟩ : Cfg)) S)
      Measurable.of_discrete.aemeasurable
  · -- Both sides reduce to 0.
    have hCfg0' : ∀ σ' : State, Cfg.uniform z σ' = 0 :=
      fun σ' => Cfg.uniform_eq_zero_iff.mpr hz
    simp_rw [hCfg0', Measure.bind_zero_left, Measure.bind_zero_right']

/-! ## Core: presampling is invisible to `execN` at the expression level

The honest statement — the one we can actually prove in our port — is that
*after projecting to the expression component*, presampling is invisible.
The strict full-`Cfg` version is false: `tapePresample` genuinely changes
the final tape content, so configurations ending in the same expression
but different states distinguish the two measures. But the expression
component is all the adequacy layer observes, so the projected equation
is exactly the right downstream notion.

This is Clutch's `prim_coupl_upd_tapes_dom` almost verbatim: Clutch states
it as an `Rcoupl` under `eq` on the `dmap (λ x, x.1)` projection, which is
the same thing. -/

/-- Inserting the same tape value at an existing key is the identity on `State`. -/
theorem State.update_tapes_insert_id {σ : State} {α : Loc} {t : Tape}
    (h : σ.tapes[α]? = some t) :
    σ.update_tapes (·.insert α t) = σ :=
  State.update_tapes_no_change h

/-- Mapping `tapeIndexUniform N` through the Cfg embedding `a ↦ ⟨lit (int ↑a), σ⟩`
gives `Cfg.uniform N σ`. Both are the uniform distribution on
`{⟨lit (int n), σ⟩ | n ∈ [0, N)}`. -/
theorem tapeIndexUniform_lintegral_eq_cfg_uniform
    {N : Int} (hN : 0 < N) (σ : State)
    (f : Cfg → ENNReal) :
    ∫⁻ (a : { z : Int // 0 ≤ z ∧ z < N }),
        f ⟨.lit (.int ↑a), σ⟩ ∂tapeIndexUniform N
      = ∫⁻ (ρ : Cfg), f ρ ∂Cfg.uniform N σ := by
  -- Unfold both definitions to PMF.uniformOfFinset level
  unfold tapeIndexUniform Cfg.uniform Int.isPos Option.unwrapM
  have hNonempty : (Finset.Ico 0 N).Nonempty := ⟨0, Finset.mem_Ico.mpr ⟨le_refl _, hN⟩⟩
  rw [dif_pos hNonempty, dif_pos hN]
  simp only
  -- Now both sides are lintegrals over `Measure.map` of the same PMF.toMeasure
  -- LHS: ∫⁻ a, f ⟨lit (int ↑a), σ⟩ ∂(pmf.toMeasure.map (subtypeEmbed))
  -- RHS: ∫⁻ ρ, f ρ ∂(pmf.toMeasure.map (cfgEmbed))
  -- Use lintegral_map on both sides to push through the map
  have hm_sub : Measurable (fun z : Int => if hz : 0 ≤ z ∧ z < N then (⟨z, hz⟩ : {z // 0 ≤ z ∧ z < N}) else ⟨0, ⟨le_refl _, by omega⟩⟩) := Measurable.of_discrete
  have hm_cfg : Measurable (fun x : Int => (⟨Exp.lit (BaseLit.int x), σ⟩ : Cfg)) := Measurable.of_discrete
  -- Both sides are lintegrals over Measure.map of the same PMF.toMeasure.
  -- Strategy: rewrite both to lintegrals over the base PMF.toMeasure on ℤ using lintegral_map,
  -- then show the integrands agree on the PMF support.
  have hm_f_sub : Measurable (fun (a : {z // 0 ≤ z ∧ z < N}) => f ⟨.lit (.int ↑a), σ⟩) :=
    Measurable.of_discrete
  have hm_f_cfg : Measurable f := Measurable.of_discrete
  -- Both sides integrate f over a uniform measure on {⟨lit(int n), σ⟩ | n ∈ Ico 0 N}.
  -- Step 1: Push both lintegrals through the Measure.map using lintegral_map
  rw [lintegral_map hm_f_sub hm_sub, lintegral_map hm_f_cfg hm_cfg]
  -- Both are: ∫⁻ a:ℤ, ... ∂pmf.toMeasure
  -- Step 2: Show integrands agree a.e. on pmf.toMeasure
  -- The PMF support is Ico 0 N. On support, dite takes the then-branch.
  apply lintegral_congr_ae
  -- Use PMF.ae_iff: ∀ᵐ a ∂pmf.toMeasure, P a ↔ ∀ a ∈ support, P a
  rw [Filter.eventuallyEq_iff_exists_mem]
  use (PMF.uniformOfFinset (Finset.Ico 0 N) hNonempty).support
  constructor
  · -- support ∈ ae(pmf.toMeasure): complement has measure 0
    rw [mem_ae_iff]
    rw [(PMF.uniformOfFinset (Finset.Ico 0 N) hNonempty).toMeasure_apply_eq_zero_iff (MeasurableSet.of_discrete)]
    exact disjoint_compl_right
  · intro a ha
    have hmem : a ∈ Finset.Ico 0 N := by
      rwa [PMF.mem_support_uniformOfFinset_iff] at ha
    have hab : 0 ≤ a ∧ a < N := Finset.mem_Ico.mp hmem
    simp [dif_pos hab]

/-! ## Case-closing helpers for the main erasure induction

Two reusable helpers factored out of `execN_tape_presample_expr_eq`. Each
closes one flavor of head-step case (state-preserving dirac, resp.
`Cfg.uniform`) given a pointwise IH specialized through `K.fillCfg`
(`ih_fill`). Keeping them top-level means the main induction can dispatch
cases by `exact`/`refine` rather than redefining the helpers inside every
attempt at the proof, and any future changes to the case-closing shape are
localized here. -/

/-- Helper for state-preserving dirac head-step cases: if
`headStep ⟨e_h, σ'⟩ = dirac ⟨e', σ'⟩` for all `σ'`, the goal reduces to a
single `ih_fill` application. -/
theorem erasure_det_close
    {m : Nat} {K : Ectx} {S : Set Exp} {σ : State} {α : Loc} {t : Tape}
    (h : σ.tapes[α]? = some t) (hN : 0 < t.bound)
    (ih_fill : ∀ (e' : Exp) (σ' : State) (t' : Tape),
      σ'.tapes[α]? = some t' → 0 < t'.bound →
      ∫⁻ σ'', ((execN m ∘ K.fillCfg) ⟨e', σ''⟩) ((fun x => x.expr) ⁻¹' S)
          ∂tapePresample σ' α
        = ((execN m ∘ K.fillCfg) ⟨e', σ'⟩) ((fun x => x.expr) ⁻¹' S))
    (e_h e' : Exp)
    (hs : ∀ σ' : State, headStep (⟨e_h, σ'⟩ : Cfg) = Measure.dirac ⟨e', σ'⟩) :
    ∫⁻ σ', ∫⁻ ρ, ((execN m ∘ K.fillCfg) ρ) ((fun x => x.expr) ⁻¹' S)
              ∂headStep ⟨e_h, σ'⟩ ∂tapePresample σ α
      = ∫⁻ ρ, ((execN m ∘ K.fillCfg) ρ) ((fun x => x.expr) ⁻¹' S)
          ∂headStep ⟨e_h, σ⟩ := by
  simp_rw [hs, lintegral_dirac' _ Measurable.of_discrete]
  exact ih_fill _ σ t h hN

/-- Helper for `Cfg.uniform` head-step cases. Given that
`headStep ⟨e_h, σ'⟩ = Cfg.uniform z_r σ'` a.e. on `tapePresample σ α` and at
`σ` itself, the goal collapses via Fubini + `ih_fill` at each sampled
index. -/
theorem erasure_uniform_close
    {m : Nat} {K : Ectx} {S : Set Exp} {σ : State} {α : Loc} {t : Tape}
    (h : σ.tapes[α]? = some t) (hN : 0 < t.bound)
    (ih_fill : ∀ (e' : Exp) (σ' : State) (t' : Tape),
      σ'.tapes[α]? = some t' → 0 < t'.bound →
      ∫⁻ σ'', ((execN m ∘ K.fillCfg) ⟨e', σ''⟩) ((fun x => x.expr) ⁻¹' S)
          ∂tapePresample σ' α
        = ((execN m ∘ K.fillCfg) ⟨e', σ'⟩) ((fun x => x.expr) ⁻¹' S))
    (e_h : Exp) (z_r : Int) (hz : 0 < z_r)
    (hstep_ae : ∀ᵐ σ' ∂(tapePresample σ α),
        headStep (⟨e_h, σ'⟩ : Cfg) = Cfg.uniform z_r σ')
    (hstep_σ : headStep (⟨e_h, σ⟩ : Cfg) = Cfg.uniform z_r σ) :
    ∫⁻ σ', ∫⁻ ρ, ((execN m ∘ K.fillCfg) ρ) ((fun x => x.expr) ⁻¹' S)
              ∂headStep ⟨e_h, σ'⟩ ∂tapePresample σ α
      = ∫⁻ ρ, ((execN m ∘ K.fillCfg) ρ) ((fun x => x.expr) ⁻¹' S)
          ∂headStep ⟨e_h, σ⟩ := by
  haveI : IsProbabilityMeasure (tapePresample σ α) :=
    ⟨tapePresample_univ_eq_one h hN⟩
  have hNonempty : (Finset.Ico (0 : Int) z_r).Nonempty := Finset.nonempty_Ico.mpr hz
  set pmf := PMF.uniformOfFinset (Finset.Ico (0 : Int) z_r) hNonempty
  have hunif : ∀ σ₀ : State, Cfg.uniform z_r σ₀ =
      pmf.toMeasure.map (fun n : Int => (⟨.lit (.int n), σ₀⟩ : Cfg)) := fun σ₀ => by
    unfold Cfg.uniform Int.isPos Option.unwrapM; rw [dif_pos hz]
  calc ∫⁻ σ', ∫⁻ ρ, ((execN m ∘ K.fillCfg) ρ) ((fun x => x.expr) ⁻¹' S)
                ∂headStep ⟨e_h, σ'⟩ ∂tapePresample σ α
      = ∫⁻ σ', ∫⁻ ρ, ((execN m ∘ K.fillCfg) ρ) ((fun x => x.expr) ⁻¹' S)
                ∂Cfg.uniform z_r σ' ∂tapePresample σ α := by
        refine lintegral_congr_ae ?_
        filter_upwards [hstep_ae] with σ' hs; rw [hs]
    _ = ∫⁻ ρ, ((execN m ∘ K.fillCfg) ρ) ((fun x => x.expr) ⁻¹' S)
          ∂Cfg.uniform z_r σ := by
        simp_rw [hunif, lintegral_map Measurable.of_discrete Measurable.of_discrete]
        rw [lintegral_lintegral_swap (f := fun σ' n =>
              ((execN m ∘ K.fillCfg) ⟨.lit (.int n), σ'⟩) ((fun x => x.expr) ⁻¹' S))
            Measurable.of_discrete.aemeasurable]
        congr 1; funext n; exact ih_fill _ σ t h hN
    _ = ∫⁻ ρ, ((execN m ∘ K.fillCfg) ρ) ((fun x => x.expr) ⁻¹' S)
          ∂headStep ⟨e_h, σ⟩ := by rw [hstep_σ]

/-! ### Per-head-step case closers

One lemma per non-trivial `HeadStepSupport` constructor whose closure does
more than a single `det_close_state_pres` / `uniform_close` call. Every
helper has the same goal shape — the post-`K.fillCfg` double integral
equals the single integral at `σ` — and takes `h`, `hN`, `ih_fill` as
hypotheses. Adding or renaming fields of a constructor now only forces
updates to one helper at a time. -/

/-- Common IH shape threaded through every head-step case. Having a named
abbreviation cuts the verbose repetition in case-helper signatures. -/
abbrev ErasureIHFill (m : Nat) (K : Ectx) (S : Set Exp) (α : Loc) : Prop :=
  ∀ (e' : Exp) (σ' : State) (t' : Tape),
    σ'.tapes[α]? = some t' → 0 < t'.bound →
    ∫⁻ σ'', ((execN m ∘ K.fillCfg) ⟨e', σ''⟩) ((fun x => x.expr) ⁻¹' S)
        ∂tapePresample σ' α
      = ((execN m ∘ K.fillCfg) ⟨e', σ'⟩) ((fun x => x.expr) ⁻¹' S)

/-- `load ℓ` case. `headStep` only depends on `σ'.heap`, which
`tapePresample` preserves a.e., so both sides reduce to a single
`ih_fill` at the looked-up value. -/
theorem erasure_load_close
    {m : Nat} {K : Ectx} {S : Set Exp} {σ : State} {α ℓ : Loc} {t : Tape} {v : Val}
    (h : σ.tapes[α]? = some t) (hN : 0 < t.bound)
    (ih_fill : ErasureIHFill m K S α)
    (hlookup : σ.heap[ℓ]? = some v) :
    ∫⁻ σ', ∫⁻ ρ, ((execN m ∘ K.fillCfg) ρ) ((fun x => x.expr) ⁻¹' S)
              ∂headStep ⟨.load (.lit (.loc ℓ)), σ'⟩ ∂tapePresample σ α
      = ∫⁻ ρ, ((execN m ∘ K.fillCfg) ρ) ((fun x => x.expr) ⁻¹' S)
          ∂headStep ⟨.load (.lit (.loc ℓ)), σ⟩ := by
  have hload : ∀ (σ₀ : State), σ₀.heap = σ.heap →
      headStep (⟨.load (.lit (.loc ℓ)), σ₀⟩ : Cfg) = Measure.dirac ⟨.ofVal v, σ₀⟩ := by
    intro σ₀ hh
    change (match σ₀.heap[ℓ]? with
              | none => (0 : Measure Cfg) | some v => Measure.dirac ⟨.ofVal v, σ₀⟩) = _
    rw [hh, hlookup]
  calc ∫⁻ σ', ∫⁻ ρ, ((execN m ∘ K.fillCfg) ρ) ((fun x => x.expr) ⁻¹' S)
                ∂headStep ⟨.load (.lit (.loc ℓ)), σ'⟩ ∂tapePresample σ α
      = ∫⁻ σ', ((execN m ∘ K.fillCfg) ⟨.ofVal v, σ'⟩)
                ((fun x => x.expr) ⁻¹' S) ∂tapePresample σ α := by
        refine lintegral_congr_ae ?_
        filter_upwards [tapePresample_heap_eq (σ := σ) (α := α)] with σ' hheap
        rw [hload σ' hheap, lintegral_dirac' _ Measurable.of_discrete]
    _ = ((execN m ∘ K.fillCfg) ⟨.ofVal v, σ⟩) ((fun x => x.expr) ⁻¹' S) :=
        ih_fill _ σ t h hN
    _ = ∫⁻ ρ, ((execN m ∘ K.fillCfg) ρ) ((fun x => x.expr) ⁻¹' S)
          ∂headStep ⟨.load (.lit (.loc ℓ)), σ⟩ := by
        rw [hload σ rfl, lintegral_dirac' _ Measurable.of_discrete]

/-- `alloc ed` case. Heap-preservation under `tapePresample` gives
`σ'.heap.fresh = σ.heap.fresh`, and then `tapePresample_update_heap_comm`
pushes the fresh-cell insert through the presample. -/
theorem erasure_alloc_close
    {m : Nat} {K : Ectx} {S : Set Exp} {σ : State} {α : Loc} {t : Tape} {ed : Exp}
    (h : σ.tapes[α]? = some t) (hN : 0 < t.bound)
    (ih_fill : ErasureIHFill m K S α) :
    ∫⁻ σ', ∫⁻ ρ, ((execN m ∘ K.fillCfg) ρ) ((fun x => x.expr) ⁻¹' S)
              ∂headStep ⟨.alloc ed, σ'⟩ ∂tapePresample σ α
      = ∫⁻ ρ, ((execN m ∘ K.fillCfg) ρ) ((fun x => x.expr) ⁻¹' S)
          ∂headStep ⟨.alloc ed, σ⟩ := by
  have halloc : ∀ (σ₀ : State), σ₀.heap = σ.heap →
      headStep (⟨.alloc ed, σ₀⟩ : Cfg) =
        ed.asValM fun vd =>
          let ℓ := σ.heap.fresh
          Measure.dirac ⟨.lit (.loc ℓ), σ₀.update_heap fun hp => hp.insert ℓ vd⟩ := by
    intro σ₀ hh
    show Exp.asValM ed (fun vd => let ℓ := σ₀.heap.fresh; _) = _
    rw [hh]
  calc ∫⁻ σ', ∫⁻ ρ, ((execN m ∘ K.fillCfg) ρ) ((fun x => x.expr) ⁻¹' S)
                ∂headStep ⟨.alloc ed, σ'⟩ ∂tapePresample σ α
      = ∫⁻ σ', ∫⁻ ρ, ((execN m ∘ K.fillCfg) ρ) ((fun x => x.expr) ⁻¹' S)
                ∂(ed.asValM fun vd => let ℓ := σ.heap.fresh;
                    Measure.dirac ⟨.lit (.loc ℓ), σ'.update_heap fun hp => hp.insert ℓ vd⟩)
                ∂tapePresample σ α := by
        refine lintegral_congr_ae ?_
        filter_upwards [tapePresample_heap_eq (σ := σ) (α := α)] with σ' hheap
        rw [halloc σ' hheap]
    _ = ∫⁻ ρ, ((execN m ∘ K.fillCfg) ρ) ((fun x => x.expr) ⁻¹' S)
          ∂headStep ⟨.alloc ed, σ⟩ := by
        cases hcheck : ed.toVal? with
        | none =>
          simp only [Exp.asValM, hcheck, lintegral_zero_measure]
          rw [halloc σ rfl]; simp [Exp.asValM, hcheck, lintegral_zero_measure]
        | some vd =>
          simp only [Exp.asValM, hcheck]
          simp_rw [lintegral_dirac' _ Measurable.of_discrete]
          set f_heap : Std.ExtTreeMap Loc Val compare → Std.ExtTreeMap Loc Val compare :=
            (fun hp => hp.insert σ.heap.fresh vd)
          have htape_upd : (σ.update_heap f_heap).tapes[α]? = some t := by
            simp [State.update_heap, h]
          rw [tapePresample_lintegral_update_heap (f := fun τ =>
                ((execN m ∘ K.fillCfg) ⟨.lit (.loc σ.heap.fresh), τ⟩)
                  ((fun x => x.expr) ⁻¹' S)),
              ih_fill _ (σ.update_heap f_heap) t htape_upd hN,
              halloc σ rfl]
          simp [Exp.asValM, hcheck, lintegral_dirac' _ Measurable.of_discrete, f_heap]

/-- `store ℓ ev` case. Dispatches on whether `ev` is a value and whether
the heap lookup succeeds; the live branch mirrors `erasure_alloc_close`. -/
theorem erasure_store_close
    {m : Nat} {K : Ectx} {S : Set Exp} {σ : State} {α ℓ : Loc} {t : Tape} {ev : Exp}
    (h : σ.tapes[α]? = some t) (hN : 0 < t.bound)
    (ih_fill : ErasureIHFill m K S α) :
    ∫⁻ σ', ∫⁻ ρ, ((execN m ∘ K.fillCfg) ρ) ((fun x => x.expr) ⁻¹' S)
              ∂headStep ⟨.store (.lit (.loc ℓ)) ev, σ'⟩ ∂tapePresample σ α
      = ∫⁻ ρ, ((execN m ∘ K.fillCfg) ρ) ((fun x => x.expr) ⁻¹' S)
          ∂headStep ⟨.store (.lit (.loc ℓ)) ev, σ⟩ := by
  have hstore : ∀ (σ₀ : State), σ₀.heap = σ.heap →
      headStep (⟨.store (.lit (.loc ℓ)) ev, σ₀⟩ : Cfg) =
        ev.asValM fun v =>
          match σ.heap[ℓ]? with
          | none => (0 : Measure Cfg)
          | some _ => Measure.dirac ⟨.lit .unit, σ₀.update_heap fun hp => hp.insert ℓ v⟩ := by
    intro σ₀ hh
    show Exp.asValM ev (fun v => match σ₀.heap[ℓ]? with | none => _ | some _ => _) = _
    rw [hh]
  -- Shared closer for the two "zero" branches (ev not a value; heap miss):
  -- `headStep = 0` at every heap-equivalent `σ₀`, so both sides vanish.
  have zero_branch : ∀ (_hz : ∀ (σ₀ : State), σ₀.heap = σ.heap →
      headStep (⟨.store (.lit (.loc ℓ)) ev, σ₀⟩ : Cfg) = 0),
      ∫⁻ σ', ∫⁻ ρ, ((execN m ∘ K.fillCfg) ρ) ((fun x => x.expr) ⁻¹' S)
              ∂headStep ⟨.store (.lit (.loc ℓ)) ev, σ'⟩ ∂tapePresample σ α
        = ∫⁻ ρ, ((execN m ∘ K.fillCfg) ρ) ((fun x => x.expr) ⁻¹' S)
            ∂headStep ⟨.store (.lit (.loc ℓ)) ev, σ⟩ := fun hz => by
    rw [hz σ rfl, lintegral_zero_measure]
    refine (lintegral_eq_zero_iff Measurable.of_discrete).mpr ?_
    filter_upwards [tapePresample_heap_eq (σ := σ) (α := α)] with σ' hheap
    rw [hz σ' hheap]; exact lintegral_zero_measure _
  cases hcheck : ev.toVal? with
  | none =>
    exact zero_branch fun σ₀ hh => by
      rw [hstore σ₀ hh]; simp [Exp.asValM, hcheck]
  | some v =>
    cases hlook : σ.heap[ℓ]? with
    | none =>
      exact zero_branch fun σ₀ hh => by
        rw [hstore σ₀ hh]; simp [Exp.asValM, hcheck, hlook]
    | some w =>
      set f_heap : Std.ExtTreeMap Loc Val compare → Std.ExtTreeMap Loc Val compare :=
        (fun hp => hp.insert ℓ v)
      calc ∫⁻ σ', ∫⁻ ρ, ((execN m ∘ K.fillCfg) ρ) ((fun x => x.expr) ⁻¹' S)
                    ∂headStep ⟨.store (.lit (.loc ℓ)) ev, σ'⟩ ∂tapePresample σ α
          = ∫⁻ σ', ((execN m ∘ K.fillCfg) ⟨.lit .unit, σ'.update_heap f_heap⟩)
                      ((fun x => x.expr) ⁻¹' S) ∂tapePresample σ α := by
            refine lintegral_congr_ae ?_
            filter_upwards [tapePresample_heap_eq (σ := σ) (α := α)] with σ' hheap
            rw [hstore σ' hheap]
            simp only [Exp.asValM, hcheck, hlook, lintegral_dirac' _ Measurable.of_discrete]
            simp only [f_heap]
        _ = ∫⁻ ρ, ((execN m ∘ K.fillCfg) ρ) ((fun x => x.expr) ⁻¹' S)
              ∂headStep ⟨.store (.lit (.loc ℓ)) ev, σ⟩ := by
            have htape_upd : (σ.update_heap f_heap).tapes[α]? = some t := by
              simp [State.update_heap, h]
            rw [tapePresample_lintegral_update_heap (f := fun τ =>
                  ((execN m ∘ K.fillCfg) ⟨.lit .unit, τ⟩) ((fun x => x.expr) ⁻¹' S)),
                ih_fill _ (σ.update_heap f_heap) t htape_upd hN,
                hstore σ rfl]
            simp [Exp.asValM, hcheck, hlook, lintegral_dirac' _ Measurable.of_discrete, f_heap]

/-- `tape z` case. Presample never touches a fresh location, so
`σ'.tapes.fresh = σ.tapes.fresh` a.e.; the fresh-tape insert then commutes
with `tapePresample` via `tapePresample_update_tapes_ne_comm`. -/
theorem erasure_tape_close
    {m : Nat} {K : Ectx} {S : Set Exp} {σ : State} {α : Loc} {t : Tape} {z : Int}
    (h : σ.tapes[α]? = some t) (hN : 0 < t.bound)
    (ih_fill : ErasureIHFill m K S α) :
    ∫⁻ σ', ∫⁻ ρ, ((execN m ∘ K.fillCfg) ρ) ((fun x => x.expr) ⁻¹' S)
              ∂headStep ⟨.tape (.lit (.int z)), σ'⟩ ∂tapePresample σ α
      = ∫⁻ ρ, ((execN m ∘ K.fillCfg) ρ) ((fun x => x.expr) ⁻¹' S)
          ∂headStep ⟨.tape (.lit (.int z)), σ⟩ := by
  have hne : σ.tapes.fresh ≠ α := Std.ExtTreeMap.elem_fresh_ne h
  have hfresh_eq : ∀ᵐ σ' ∂(tapePresample σ α), σ'.tapes.fresh = σ.tapes.fresh := by
    obtain ⟨N, bs⟩ := t
    exact tapePresample_ae h fun _ => State.fresh_loc_upd_some h
  have htape_rw : ∀ (σ₀ : State), σ₀.tapes.fresh = σ.tapes.fresh →
      headStep (⟨.tape (.lit (.int z)), σ₀⟩ : Cfg) =
        Measure.dirac ⟨.lit (.lbl σ.tapes.fresh),
          σ₀.update_tapes (·.insert σ.tapes.fresh (Tape.empty z))⟩ := by
    intro σ₀ hfr; simp only [headStep, hfr]
  calc ∫⁻ σ', ∫⁻ ρ, ((execN m ∘ K.fillCfg) ρ) ((fun x => x.expr) ⁻¹' S)
                ∂headStep ⟨.tape (.lit (.int z)), σ'⟩ ∂tapePresample σ α
      = ∫⁻ σ', ((execN m ∘ K.fillCfg)
            ⟨.lit (.lbl σ.tapes.fresh),
             σ'.update_tapes (·.insert σ.tapes.fresh (Tape.empty z))⟩)
                  ((fun x => x.expr) ⁻¹' S) ∂tapePresample σ α := by
        refine lintegral_congr_ae ?_
        filter_upwards [hfresh_eq] with σ' hfr
        rw [htape_rw σ' hfr, lintegral_dirac' _ Measurable.of_discrete]
    _ = ∫⁻ ρ, ((execN m ∘ K.fillCfg) ρ) ((fun x => x.expr) ⁻¹' S)
          ∂headStep ⟨.tape (.lit (.int z)), σ⟩ := by
        have htape_upd :
            (σ.update_tapes (·.insert σ.tapes.fresh (Tape.empty z))).tapes[α]?
              = some t := by
          rw [State.upd_diff_tape_tot (Ne.symm hne)]; exact h
        rw [tapePresample_lintegral_update_tapes_ne hne (f := fun τ =>
              ((execN m ∘ K.fillCfg) ⟨.lit (.lbl σ.tapes.fresh), τ⟩)
                ((fun x => x.expr) ⁻¹' S)),
            ih_fill _ (σ.update_tapes (·.insert σ.tapes.fresh (Tape.empty z)))
              t htape_upd hN,
            htape_rw σ rfl, lintegral_dirac' _ Measurable.of_discrete]

/-- Zero-head-step case. `headStep ⟨e_red, σ⟩ = 0` propagates a.e. over
`tapePresample σ α` via `State.head_step_dzero_upd_tapes`, collapsing both
sides to `0`. -/
theorem erasure_zero_close
    {m : Nat} {K : Ectx} {S : Set Exp} {σ : State} {α : Loc} {t : Tape} {e_red : Exp}
    (h : σ.tapes[α]? = some t) (_hN : 0 < t.bound)
    (hzero : headStep ⟨e_red, σ⟩ = 0) :
    ∫⁻ σ', ∫⁻ ρ, ((execN m ∘ K.fillCfg) ρ) ((fun x => x.expr) ⁻¹' S)
              ∂headStep ⟨e_red, σ'⟩ ∂tapePresample σ α
      = ∫⁻ ρ, ((execN m ∘ K.fillCfg) ρ) ((fun x => x.expr) ⁻¹' S)
          ∂headStep ⟨e_red, σ⟩ := by
  have hzero_ae : ∀ᵐ σ' ∂(tapePresample σ α), headStep ⟨e_red, σ'⟩ = 0 := by
    obtain ⟨N, bs⟩ := t
    exact tapePresample_ae h fun _ => State.head_step_dzero_upd_tapes h hzero
  rw [hzero, lintegral_zero_measure]
  calc ∫⁻ σ', ∫⁻ ρ, ((execN m ∘ K.fillCfg) ρ) ((fun x => x.expr) ⁻¹' S)
                ∂headStep ⟨e_red, σ'⟩ ∂tapePresample σ α
      = ∫⁻ _, (0 : ENNReal) ∂tapePresample σ α := by
        refine lintegral_congr_ae ?_
        filter_upwards [hzero_ae] with σ' h0
        rw [h0, lintegral_zero_measure]
    _ = 0 := lintegral_zero

/-- **Main theorem (Clutch `prim_coupl_upd_tapes_dom`, projected form).**
Appending a uniformly-sampled value onto an existing tape `α` of `σ` with
positive bound is invisible to `execN m ⟨e, σ⟩` **at the expression level**.

That is, projecting `execN m` by `(·.expr)` gives a measure on expressions
that is unaffected by presampling onto tape `α`.

The positivity hypothesis `0 < t.bound` is essential: `tapePresample σ α`
is the zero measure when the tape bound is nonpositive, so without it
the LHS would collapse to `0` while the RHS may be nonzero. -/
theorem execN_tape_presample_expr_eq
    {σ : State} {α : Loc} {e : Exp} {m : Nat} {t : Tape}
    (h : σ.tapes[α]? = some t) (hN : 0 < t.bound) :
    ((tapePresample σ α).bind (fun σ' => execN m ⟨e, σ'⟩)).map (·.expr) =
      (execN m ⟨e, σ⟩).map (·.expr) := by
  -- Induction on `m`, generalized over `e`, `σ`, `t` so the IH applies at
  -- the post-step state (which may hold different tape content but retains
  -- tape `α` with the same bound, via tape-bound persistence).
  induction m generalizing e σ t with
  | zero =>
    -- `execN 0 _ = 0`, so both sides project to the zero measure.
    show ((tapePresample σ α).bind (fun _ => (0 : Measure Cfg))).map (·.expr) =
         ((0 : Measure Cfg)).map (·.expr)
    refine Measure.ext fun S hS => ?_
    rw [Measure.map_apply Measurable.of_discrete hS,
        Measure.map_apply Measurable.of_discrete hS,
        Measure.bind_apply (by exact .of_discrete) Measurable.of_discrete.aemeasurable]
    simp only [Measure.coe_zero, Pi.zero_apply, lintegral_zero]
  | succ m ih =>
    by_cases hv : e.isValue
    · -- Value case. `execN (m+1) ⟨e, σ'⟩ = dirac ⟨e, σ'⟩`, so after projecting
      -- by `(·.expr)` both sides become `dirac e` (using that `tapePresample`
      -- is a probability measure).
      have hstep : ∀ σ' : State,
          execN (m + 1) ⟨e, σ'⟩ = Measure.dirac ⟨e, σ'⟩ := fun σ' =>
        execN_succ_isValue (ρ := ⟨e, σ'⟩) hv m
      simp_rw [hstep]
      rw [Measure.bind_map_comm]
      -- Explicit pointwise kernel equality avoids `simp_rw` metavariable issues.
      have hker : (fun σ' : State => Measure.map (·.expr) (Measure.dirac (⟨e, σ'⟩ : Cfg)))
          = (fun _ => Measure.dirac e) := by
        funext σ'
        rw [Measure.map_dirac (f := fun c : Cfg => c.expr) (⟨e, σ'⟩ : Cfg)]
      rw [hker, Measure.map_dirac (f := fun c : Cfg => c.expr) (⟨e, σ⟩ : Cfg)]
      refine Measure.ext fun S hS => ?_
      rw [Measure.bind_apply hS Measurable.of_discrete.aemeasurable,
          lintegral_const, tapePresample_univ_eq_one h hN, mul_one]
    · -- Non-value case. Unfold `execN (m+1)` to `primStep ≫= execN m`,
      -- decompose `primStep` into `headStep` at the redex, and dispatch by
      -- `det_or_prob_or_zero`. The K.fillCfg, map-bind shuffling, and
      -- integral-form reshaping done below are mechanical setup; the
      -- substance lives in the three case helpers (`det_close_state_pres`,
      -- `uniform_close`, and the bespoke handling of each rand/heap case).
      have hstep : ∀ σ' : State,
          execN (m + 1) ⟨e, σ'⟩ = (primStep ⟨e, σ'⟩).bind (execN m) :=
        fun σ' => execN_succ_not_isValue (ρ := ⟨e, σ'⟩) hv m
      simp_rw [hstep]
      set K := e.decomp.1
      set e_red := e.decomp.2
      have hprim : ∀ σ' : State,
          primStep ⟨e, σ'⟩ = (headStep ⟨e_red, σ'⟩).map K.fillCfg := by
        intro σ'; simp only [primStep, e_red, K]
      simp_rw [hprim, Measure.bind_map .of_discrete .of_discrete]
      refine Measure.ext fun S hS => ?_
      rw [Measure.map_apply Measurable.of_discrete hS,
          Measure.map_apply Measurable.of_discrete hS]
      rw [Measure.bind_apply (Measurable.of_discrete hS) Measurable.of_discrete.aemeasurable]
      simp_rw [Measure.bind_apply (Measurable.of_discrete hS) Measurable.of_discrete.aemeasurable]
      -- Reshape the IH (`.map (·.expr)` form) into the pointwise integral
      -- form used by the case helpers below.
      have ih_pointwise : ∀ (e' : Exp) (σ' : State) (t' : Tape),
          σ'.tapes[α]? = some t' → 0 < t'.bound →
          ∫⁻ σ'', (execN m ⟨e', σ''⟩) ((fun x => x.expr) ⁻¹' S) ∂tapePresample σ' α
            = (execN m ⟨e', σ'⟩) ((fun x => x.expr) ⁻¹' S) := by
        intro e' σ' t' ht' hN'
        have hih : ((tapePresample σ' α).bind (fun σ'' => execN m ⟨e', σ''⟩)).map (·.expr)
                  = (execN m ⟨e', σ'⟩).map (·.expr) := ih ht' hN'
        have hval : ((tapePresample σ' α).bind (fun σ'' => execN m ⟨e', σ''⟩)).map (·.expr) S
                  = (execN m ⟨e', σ'⟩).map (·.expr) S := by rw [hih]
        rw [Measure.map_apply Measurable.of_discrete hS,
            Measure.map_apply Measurable.of_discrete hS,
            Measure.bind_apply (Measurable.of_discrete hS) Measurable.of_discrete.aemeasurable] at hval
        exact hval
      -- Specialization composing `ih_pointwise` with `K.fill`, matching the
      -- shape of the post-`K.fillCfg` integrand.
      have ih_fill : ∀ (e' : Exp) (σ' : State) (t' : Tape),
          σ'.tapes[α]? = some t' → 0 < t'.bound →
          ∫⁻ σ'', ((execN m ∘ K.fillCfg) ⟨e', σ''⟩) ((fun x => x.expr) ⁻¹' S)
              ∂tapePresample σ' α
            = ((execN m ∘ K.fillCfg) ⟨e', σ'⟩) ((fun x => x.expr) ⁻¹' S) := by
        intro e' σ' t' ht' hN'
        simp only [Function.comp]
        exact ih_pointwise (K.fill e') σ' t' ht' hN'
      -- Case-closing helpers are hoisted to top-level as `erasure_det_close`
      -- and `erasure_uniform_close`; local names here just pin the
      -- `ih_fill`/`h`/`hN` environment.
      have det_close_state_pres := fun e_h e' hs =>
        erasure_det_close (m := m) (K := K) (S := S) h hN ih_fill e_h e' hs
      have uniform_close := fun e_h z_r hz hstep_ae hstep_σ =>
        erasure_uniform_close (m := m) (K := K) (S := S) h hN ih_fill
          e_h z_r hz hstep_ae hstep_σ
      -- Case-split on headStep using det_or_prob_or_zero.
      rcases det_or_prob_or_zero e_red σ with hdet | hprob | hzero
      · -- Deterministic case: headStep produces a dirac. Each constructor
        -- provides `∀ σ', headStep ⟨e_h, σ'⟩ = dirac ⟨e', σ'⟩` for some `e'`,
        -- and `det_close_state_pres` closes the goal.
        clear_value e_red K
        cases hdet with
        | betaLam hv2 =>
          rename_i e1 e2
          refine det_close_state_pres _ (Exp.open' e1 e2) fun σ' => ?_
          exact Exp.isValM_some hv2
        | betaFix hv2 =>
          rename_i e1 e2
          refine det_close_state_pres _ (Exp.app (Exp.open' e1 (.fix e1)) e2) fun σ' => ?_
          exact Exp.isValM_some hv2
        | unop hv heval =>
          rename_i op e_u e'
          refine det_close_state_pres _ e' fun σ' => ?_
          show Exp.isValM e_u (ProbLang.Option.unwrapM _ (op.eval e_u)) = _
          rw [Exp.isValM_some hv, heval]; rfl
        | binop hv1 hv2 heval =>
          rename_i op e1 e2 e'
          refine det_close_state_pres _ e' fun σ' => ?_
          show Exp.isValM e1 (Exp.isValM e2 (ProbLang.Option.unwrapM _ (op.eval e1 e2))) = _
          rw [Exp.isValM_some hv2, Exp.isValM_some hv1, heval]; rfl
        | ifTrue =>
          rename_i et ef
          exact det_close_state_pres _ et fun _ => rfl
        | ifFalse =>
          rename_i et ef
          exact det_close_state_pres _ ef fun _ => rfl
        | fst hv1 hv2 =>
          rename_i e1 e2
          refine det_close_state_pres _ e1 fun σ' => ?_
          show Exp.isValM e1 (Exp.isValM e2 (Measure.dirac _)) = _
          rw [Exp.isValM_some hv2, Exp.isValM_some hv1]
        | snd hv1 hv2 =>
          rename_i e1 e2
          refine det_close_state_pres _ e2 fun σ' => ?_
          show Exp.isValM e1 (Exp.isValM e2 (Measure.dirac _)) = _
          rw [Exp.isValM_some hv2, Exp.isValM_some hv1]
        | caseL hv =>
          rename_i e_c el er
          refine det_close_state_pres _ (el.app e_c) fun σ' => ?_
          exact Exp.isValM_some hv
        | caseR hv =>
          rename_i e_c el er
          refine det_close_state_pres _ (er.app e_c) fun σ' => ?_
          exact Exp.isValM_some hv
        | scrutSuccess hv hmatch =>
          rename_i e_s p bindings
          refine det_close_state_pres _ (.inl bindings) fun σ' => ?_
          show Exp.isValM e_s (match Pat.tryMatch p e_s with | some b => _ | none => _) = _
          rw [Exp.isValM_some hv, hmatch]
        | scrutFailure hv hmatch =>
          rename_i e_s p
          refine det_close_state_pres _ (.inr (.lit .unit)) fun σ' => ?_
          show Exp.isValM e_s (match Pat.tryMatch p e_s with | some b => _ | none => _) = _
          rw [Exp.isValM_some hv, hmatch]
        | load hlook =>
          rename_i ℓ v
          exact erasure_load_close (v := v) h hN ih_fill hlook
        | alloc hv =>
          rename_i ed
          exact erasure_alloc_close (ed := ed) h hN ih_fill
        | store hv hsome =>
          rename_i ℓ ev
          exact erasure_store_close (ℓ := ℓ) (ev := ev) h hN ih_fill
        | tape =>
          rename_i z
          exact erasure_tape_close (z := z) h hN ih_fill
      · -- Probabilistic case: `headStep` is either `Cfg.uniform` (non-tape
        -- or "other-tape" rand) or a tape-popping dirac (same-tape rand).
        clear_value e_red K
        cases hprob with
        | randNoTape hz =>
          rename_i z_r
          exact uniform_close _ z_r hz
            (MeasureTheory.ae_of_all _ fun _ => rfl) rfl
        | @randTape z_r α_lbl _ N_b nn ns hz htapes hzN =>
          subst hzN
          by_cases hαeq : α = α_lbl
          · -- Same tape: `headStep` pops `nn`. After unfolding both sides,
            -- the post-state measure matches `tapePresample σ_popped α`,
            -- so `ih_fill` at `σ_popped` closes via `convert`.
            subst hαeq
            have ht_eq : t = ⟨z_r, nn :: ns⟩ := by
              rw [h] at htapes; exact Option.some.inj htapes
            subst ht_eq
            -- Reduce RHS.
            have hrhs : headStep ⟨.rand (.lit (.int z_r)) (.lit (.lbl α)), σ⟩ =
                Measure.dirac ⟨.lit (.int nn),
                  σ.update_tapes (·.insert α ⟨z_r, ns⟩)⟩ := by
              simp [headStep, htapes]
            rw [hrhs, lintegral_dirac' _ Measurable.of_discrete,
                tapePresample_lintegral h]
            have hstep_upd : ∀ n' : { z : Int // 0 ≤ z ∧ z < z_r },
                headStep ⟨.rand (.lit (.int z_r)) (.lit (.lbl α)),
                  σ.update_tapes (·.insert α ⟨z_r, (nn :: ns) ++ [↑n']⟩)⟩ =
                Measure.dirac ⟨.lit (.int ↑nn),
                  σ.update_tapes (·.insert α ⟨z_r, ns ++ [↑n']⟩)⟩ := by
              intro ⟨n', hn'⟩
              simp only [headStep, State.upd_tape_some, List.cons_append, ↓reduceIte]
              rw [State.update_tapes_twice]
            simp_rw [hstep_upd, lintegral_dirac' _ Measurable.of_discrete]
            -- Fold the residual integral back into `tapePresample σ_popped α`.
            have htape_popped : (σ.update_tapes (·.insert α ⟨z_r, ns⟩)).tapes[α]? =
                some ⟨z_r, ns⟩ := State.upd_tape_some _ _ _
            convert
              ih_fill (.lit (.int ↑nn)) (σ.update_tapes (·.insert α ⟨z_r, ns⟩))
                ⟨z_r, ns⟩ htape_popped hN using 1
            rw [tapePresample_lintegral htape_popped]
            simp_rw [State.update_tapes_twice]
          · -- α_lbl ≠ α: tapePresample doesn't affect tape α_lbl.
            have hstep_rw : ∀ (σ₀ : State), σ₀.tapes[α_lbl]? = some ⟨z_r, nn :: ns⟩ →
                headStep (⟨.rand (.lit (.int z_r)) (.lit (.lbl α_lbl)), σ₀⟩ : Cfg) =
                  Measure.dirac ⟨.lit (.int nn),
                    σ₀.update_tapes (·.insert α_lbl ⟨z_r, ns⟩)⟩ := by
              intro σ₀ ht'; simp [headStep, ht']
            have htapes_pres : ∀ᵐ σ' ∂(tapePresample σ α),
                σ'.tapes[α_lbl]? = some ⟨z_r, nn :: ns⟩ := by
              filter_upwards [tapePresample_tape_ne_ae h (Ne.symm hαeq)] with σ' heq
              exact heq.trans htapes
            calc ∫⁻ σ', ∫⁻ ρ, ((execN m ∘ K.fillCfg) ρ) ((fun x => x.expr) ⁻¹' S)
                          ∂headStep ⟨.rand (.lit (.int z_r)) (.lit (.lbl α_lbl)), σ'⟩
                          ∂tapePresample σ α
                = ∫⁻ σ', ((execN m ∘ K.fillCfg)
                      ⟨.lit (.int nn), σ'.update_tapes (·.insert α_lbl ⟨z_r, ns⟩)⟩)
                        ((fun x => x.expr) ⁻¹' S) ∂tapePresample σ α := by
                  refine lintegral_congr_ae ?_
                  filter_upwards [htapes_pres] with σ' ht'
                  rw [hstep_rw σ' ht', lintegral_dirac' _ Measurable.of_discrete]
              _ = ∫⁻ ρ, ((execN m ∘ K.fillCfg) ρ) ((fun x => x.expr) ⁻¹' S)
                    ∂headStep ⟨.rand (.lit (.int z_r)) (.lit (.lbl α_lbl)), σ⟩ := by
                  have htape_upd :
                      (σ.update_tapes (·.insert α_lbl ⟨z_r, ns⟩)).tapes[α]?
                        = some t := by
                    rw [State.upd_diff_tape_tot hαeq]; exact h
                  rw [tapePresample_lintegral_update_tapes_ne (Ne.symm hαeq)
                        (f := fun τ =>
                          ((execN m ∘ K.fillCfg) ⟨.lit (.int nn), τ⟩)
                            ((fun x => x.expr) ⁻¹' S)),
                      ih_fill _ (σ.update_tapes (·.insert α_lbl ⟨z_r, ns⟩))
                        t htape_upd hN,
                      hstep_rw σ htapes, lintegral_dirac' _ Measurable.of_discrete]
        | @randTapeEmpty z_r α_lbl _ N_b hz htapes hzN =>
          subst hzN
          by_cases hαeq : α = α_lbl
          · -- Empty same tape: each presample `n'` yields a tape `[n']` that
            -- `headStep` then consumes, leaving the tape empty again. So LHS
            -- reduces to a tapeIndex-uniform integral over `σ`, which matches
            -- RHS = `Cfg.uniform z_r σ` via
            -- `tapeIndexUniform_lintegral_eq_cfg_uniform`.
            subst hαeq
            have ht_eq : t = ⟨z_r, []⟩ := by
              rw [h] at htapes; exact Option.some.inj htapes
            subst ht_eq
            have hrhs : headStep ⟨.rand (.lit (.int z_r)) (.lit (.lbl α)), σ⟩ =
                Cfg.uniform z_r σ := by simp [headStep, htapes]
            rw [hrhs, tapePresample_lintegral h]
            have hstep_upd : ∀ n' : { z : Int // 0 ≤ z ∧ z < z_r },
                headStep ⟨.rand (.lit (.int z_r)) (.lit (.lbl α)),
                  σ.update_tapes (·.insert α ⟨z_r, [n']⟩)⟩ =
                Measure.dirac ⟨.lit (.int ↑n'),
                  σ.update_tapes (·.insert α ⟨z_r, []⟩)⟩ := by
              intro ⟨n', hn'⟩
              simp only [headStep, State.upd_tape_some, ↓reduceIte]
              rw [State.update_tapes_twice]
            simp only [List.nil_append]
            simp_rw [hstep_upd, lintegral_dirac' _ Measurable.of_discrete]
            -- `σ.update_tapes(insert α ⟨z_r, []⟩) = σ` since the tape was
            -- already `⟨z_r, []⟩`; then the LHS and RHS are two encodings of
            -- the same uniform integral over indices in `[0, z_r)`.
            rw [State.update_tapes_insert_id htapes]
            exact tapeIndexUniform_lintegral_eq_cfg_uniform hz σ
              (fun ρ => ((execN m ∘ K.fillCfg) ρ) ((fun x => x.expr) ⁻¹' S))
          · -- Different tape: lookup preserved a.e., so `headStep` stays
            -- `Cfg.uniform z_r σ'` and `uniform_close` closes the goal.
            have hstep_σ : headStep (⟨.rand (.lit (.int z_r)) (.lit (.lbl α_lbl)), σ⟩ : Cfg)
                = Cfg.uniform z_r σ := by simp [headStep, htapes]
            refine uniform_close _ z_r hz ?_ hstep_σ
            filter_upwards [tapePresample_tape_ne_ae h (Ne.symm hαeq)] with σ' htape_eq
            simp [headStep, htape_eq.trans htapes]
        | @randTapeOther z_r α_lbl _ N_b L hz htapes hzN =>
          -- `z_r ≠ N_b`, so headStep falls through to `Cfg.uniform z_r σ'`.
          -- For `α_lbl = α`, tapePresample appends to α but preserves bound
          -- `N_b`; for `α_lbl ≠ α`, the lookup is unchanged.
          -- Helper: when tape at `α_lbl` has bound `≠ z_r`, headStep is uniform.
          have hrand_uniform : ∀ (σ₀ : State) {M : Int} {ns : List _},
              σ₀.tapes[α_lbl]? = some ⟨M, ns⟩ → M ≠ z_r →
              headStep (⟨.rand (.lit (.int z_r)) (.lit (.lbl α_lbl)), σ₀⟩ : Cfg)
                = Cfg.uniform z_r σ₀ := by
            intro σ₀ M ns ht hne
            show (match σ₀.tapes[α_lbl]? with | none => _ | some ⟨M, _⟩ => _) = _
            rw [ht]; simp only; rw [if_neg hne]
          refine uniform_close _ z_r hz ?_ (hrand_uniform σ htapes (Ne.symm hzN))
          obtain ⟨N, bs⟩ := t
          by_cases hαeq : α = α_lbl
          · -- Same tape: presample appends, bound stays `N = N_b`.
            subst hαeq
            have hNN : N_b = N :=
              congrArg Tape.bound (Option.some.inj (htapes.symm.trans h))
            refine tapePresample_ae h fun n => ?_
            have hlook : (σ.update_tapes (·.insert α ⟨N, bs ++ [n]⟩)).tapes[α]?
                = some ⟨N, bs ++ [n]⟩ := by simp [State.update_tapes]
            exact hrand_uniform _ hlook (fun h => hzN (hNN ▸ h.symm))
          · -- Different tape: lookup preserved.
            filter_upwards [tapePresample_tape_ne_ae h (Ne.symm hαeq)] with σ' htape_eq
            exact hrand_uniform _ (htape_eq.trans htapes) (Ne.symm hzN)
      · -- Zero case handled by `erasure_zero_close`.
        exact erasure_zero_close (e_red := e_red) h hN hzero

/-! ## Iterated and limit variants -/

/-- `n`-fold presample iterator on a single tape `α`. Used to state
`execN_iterM_tape_presample_expr_eq` below: the anonymous `Nat.rec` in
Clutch's `erasure.v` tape-batching statement is definitionally equal to
this `Nat.rec`-free variant. -/
noncomputable def tapePresampleIter (α : Loc) (σ : State) : Nat → Measure State
  | 0 => Measure.dirac σ
  | n + 1 => (tapePresampleIter α σ n).bind (fun σ' => tapePresample σ' α)

/-- Tape-bound persistence under `tapePresampleIter`: every state in the
support retains tape `α` with the same bound as the initial `σ`. -/
theorem tapePresampleIter_tape_bound_ae {σ : State} {α : Loc} {t : Tape}
    (h : σ.tapes[α]? = some t) (n : Nat) :
    ∀ᵐ σ' ∂(tapePresampleIter α σ n),
      ∃ t' : Tape, σ'.tapes[α]? = some t' ∧ t'.bound = t.bound := by
  induction n with
  | zero =>
    -- `tapePresampleIter α σ 0 = dirac σ`; the a.e. statement on a dirac
    -- reduces to the property at the dirac point.
    show ∀ᵐ σ' ∂(Measure.dirac σ), _
    rw [MeasureTheory.ae_iff, Measure.dirac_apply' _ MeasurableSet.of_discrete,
        Set.indicator_of_notMem]
    simp only [Set.mem_setOf_eq, not_not]
    exact ⟨t, h, rfl⟩
  | succ k ihk =>
    rw [tapePresampleIter, MeasureTheory.ae_iff,
        Measure.bind_apply MeasurableSet.of_discrete
          Measurable.of_discrete.aemeasurable]
    refine (lintegral_eq_zero_iff Measurable.of_discrete).mpr ?_
    filter_upwards [ihk] with σ'' ⟨t'', ht'', hbound⟩
    -- Under `tapePresample σ'' α`, every post-state has tape α with the
    -- same bound as `t''` (just one extra presample appended).
    show tapePresample σ'' α _ = 0
    obtain ⟨Nb, bs⟩ := t''
    refine MeasureTheory.ae_iff.mp (tapePresample_ae ht'' fun n' => ?_)
    exact ⟨⟨Nb, bs ++ [n']⟩, by simp [State.update_tapes], hbound⟩

/-- Iterated-presample variant of `execN_tape_presample_expr_eq`:
`n`-fold presampling onto tape `α` is invisible to `execN m ⟨e, ·⟩` at the
expression level, provided the initial tape exists and has positive bound. -/
theorem execN_tapePresampleIter_expr_eq
    {σ : State} {α : Loc} {e : Exp} {m : Nat} {t : Tape} (n : Nat)
    (h : σ.tapes[α]? = some t) (hN : 0 < t.bound) :
    ((tapePresampleIter α σ n).bind (fun σ' => execN m ⟨e, σ'⟩)).map (·.expr) =
      (execN m ⟨e, σ⟩).map (·.expr) := by
  induction n generalizing σ with
  | zero =>
    -- `tapePresampleIter α σ 0 = dirac σ`, so LHS collapses to `execN m ⟨e, σ⟩`.
    show ((Measure.dirac σ).bind (fun σ' => execN m ⟨e, σ'⟩)).map (·.expr) = _
    rw [Measure.dirac_bind (f := _) Measurable.of_discrete]
  | succ k ih =>
    -- Unfold the outer step and push `map` through `bind`.
    show ((((tapePresampleIter α σ k).bind (fun σ' => tapePresample σ' α)).bind
            (fun σ' => execN m ⟨e, σ'⟩)).map (·.expr)) = _
    rw [Measure.bind_bind
          Measurable.of_discrete.aemeasurable
          Measurable.of_discrete.aemeasurable,
        Measure.bind_map_comm]
    -- Reduce pointwise: at each σ₁ in the support of `iter k`, apply
    -- `execN_tape_presample_expr_eq` (using tape-bound persistence) and
    -- close via the IH.
    refine Measure.ext fun S hS => ?_
    rw [Measure.bind_apply hS Measurable.of_discrete.aemeasurable]
    calc ∫⁻ σ₁, ((tapePresample σ₁ α).bind (fun σ' => execN m ⟨e, σ'⟩)).map (·.expr) S
            ∂(tapePresampleIter α σ k)
        = ∫⁻ σ₁, (execN m ⟨e, σ₁⟩).map (·.expr) S ∂(tapePresampleIter α σ k) := by
          refine lintegral_congr_ae ?_
          filter_upwards [tapePresampleIter_tape_bound_ae h k]
            with σ₁ ⟨t', ht', hbound⟩
          rw [execN_tape_presample_expr_eq ht' (hbound ▸ hN)]
      _ = ((tapePresampleIter α σ k).bind (fun σ' => execN m ⟨e, σ'⟩)).map (·.expr) S := by
          rw [Measure.map_apply Measurable.of_discrete hS,
              Measure.bind_apply (Measurable.of_discrete hS)
                Measurable.of_discrete.aemeasurable]
          simp_rw [Measure.map_apply Measurable.of_discrete hS]
      _ = (execN m ⟨e, σ⟩).map (·.expr) S := by
          rw [ih h, Measure.map_apply Measurable.of_discrete hS]

theorem execN_iterM_tape_presample_expr_eq
    {σ : State} {α : Loc} {e : Exp} {m : Nat} {t : Tape} (n : Nat)
    (h : σ.tapes[α]? = some t) (hN : 0 < t.bound) :
    (((Nat.rec (motive := fun _ => Measure State)
                (Measure.dirac σ)
                (fun _ μ => μ.bind (fun σ' => tapePresample σ' α))) n).bind
       (fun σ' => execN m ⟨e, σ'⟩)).map (·.expr) =
      (execN m ⟨e, σ⟩).map (·.expr) := by
  -- The anonymous `Nat.rec` is definitionally equal to `tapePresampleIter`.
  have hiter_eq : (Nat.rec (motive := fun _ => Measure State)
                    (Measure.dirac σ)
                    (fun _ μ => μ.bind (fun σ' => tapePresample σ' α))) n
                = tapePresampleIter α σ n := by
    induction n with
    | zero => rfl
    | succ k ih => show _ = (tapePresampleIter α σ k).bind _; rw [← ih]
  rw [hiter_eq]
  exact execN_tapePresampleIter_expr_eq n h hN

/-- **Clutch `limprim_coupl_step_limprim` / `lim_exec_eq_erasure`, projected form.**
Binding `tapePresample σ α` into `limExec ⟨e, ·⟩` is equal to `limExec ⟨e, σ⟩`
at the expression level. Derived from `execN_tape_presample_expr_eq` by
monotone convergence via `lintegral_limExec`. -/
theorem limExec_tape_presample_expr_eq
    {σ : State} {α : Loc} {t : Tape} {e : Exp}
    (h : σ.tapes[α]? = some t) (hN : 0 < t.bound) :
    ((tapePresample σ α).bind (fun σ' => limExec ⟨e, σ'⟩)).map (·.expr) =
      (limExec ⟨e, σ⟩).map (·.expr) := by
  -- We replay the `ErasableExpr.lim_exec` proof inline with
  -- `execN_tape_presample_expr_eq` as the per-n hypothesis.
  refine Measure.ext fun S hS => ?_
  rw [Measure.map_apply Measurable.of_discrete hS,
      Measure.map_apply Measurable.of_discrete hS,
      Measure.bind_apply (Measurable.of_discrete hS)
        Measurable.of_discrete.aemeasurable]
  have hind : ∀ ρ : Cfg,
      limExec ρ ((·.expr) ⁻¹' S)
        = ∫⁻ x, (((·.expr) ⁻¹' S) : Set Cfg).indicator 1 x ∂(limExec ρ) := by
    intro ρ
    rw [lintegral_indicator_one (Measurable.of_discrete hS)]
  simp_rw [hind]
  simp_rw [lintegral_limExec]
  rw [lintegral_iSup (fun _ => Measurable.of_discrete)
        (fun i j hij σ' =>
          lintegral_mono' (execN_mono hij ⟨e, σ'⟩) (le_refl _))]
  refine iSup_congr fun n => ?_
  have hn := execN_tape_presample_expr_eq (e := e) (m := n) h hN
  have hval : ((tapePresample σ α).bind (fun σ' => execN n ⟨e, σ'⟩)).map (·.expr) S
            = (execN n ⟨e, σ⟩).map (·.expr) S := by
    rw [hn]
  rw [Measure.map_apply Measurable.of_discrete hS,
      Measure.map_apply Measurable.of_discrete hS,
      Measure.bind_apply (Measurable.of_discrete hS)
        Measurable.of_discrete.aemeasurable] at hval
  rw [show (∫⁻ x, (((·.expr) ⁻¹' S) : Set Cfg).indicator 1 x ∂(execN n ⟨e, σ⟩))
        = (execN n ⟨e, σ⟩) ((·.expr) ⁻¹' S)
      from lintegral_indicator_one (Measurable.of_discrete hS)]
  simp_rw [show ∀ σ' : State,
        (∫⁻ x, (((·.expr) ⁻¹' S) : Set Cfg).indicator 1 x ∂(execN n ⟨e, σ'⟩))
          = (execN n ⟨e, σ'⟩) ((·.expr) ⁻¹' S)
      from fun σ' => lintegral_indicator_one (Measurable.of_discrete hS)]
  exact hval

/-! ## `ErasableExpr`: the weak erasability notion

Clutch's `erasable` is defined over val-projected `exec`, so it implicitly
projects away state differences at final configurations. Our `Erasable`
(in `Erasable.lean`) is phrased over `Measure Cfg` and is therefore
strictly stronger — `dret σ` satisfies it, but `tapePresample σ α`
generally does not.

`ErasableExpr` is the projected notion: the distributions agree *after
projecting to the expression component*. This is the semantically correct
analogue of Clutch's `erasable` for our `Cfg`-valued operational semantics.
Both `dret`-style and `tapePresample`-style distributions satisfy it. -/
def ErasableExpr (μ : Measure State) (σ : State) : Prop :=
  ∀ (e : Exp) (m : Nat),
    (μ.bind (fun σ' => execN m ⟨e, σ'⟩)).map (·.expr) =
      (execN m ⟨e, σ⟩).map (·.expr)

namespace ErasableExpr

/-- Strict `Erasable` implies `ErasableExpr`. -/
theorem of_erasable {μ : Measure State} {σ : State} (h : Erasable μ σ) :
    ErasableExpr μ σ := by
  intro e m
  rw [h e m]

/-- Dirac distributions are `ErasableExpr`. -/
theorem dret (σ : State) : ErasableExpr (Measure.dirac σ) σ :=
  of_erasable (Erasable.dret σ)

/-- `tapePresample σ α` is `ErasableExpr`. This is the main theorem
`execN_tape_presample_expr_eq`, repackaged as an `ErasableExpr` witness. -/
theorem tapePresample {σ : State} {α : Loc} {t : Tape}
    (h : σ.tapes[α]? = some t) (hN : 0 < t.bound) :
    ErasableExpr (tapePresample σ α) σ := by
  intro e m
  exact execN_tape_presample_expr_eq h hN

/-- `ErasableExpr` is closed under `bind`. -/
theorem dbind {μ₁ : Measure State} {μ₂ : State → Measure State} {σ : State}
    (h₁ : ErasableExpr μ₁ σ) (h₂ : ∀ σ', ErasableExpr (μ₂ σ') σ') :
    ErasableExpr (μ₁.bind μ₂) σ := by
  intro e m
  -- Flatten the outer `(μ₁.bind μ₂).bind (execN m ⟨e, ·⟩)` into a
  -- double bind; apply `h₂` pointwise to each σ' in the inner kernel
  -- (at the projected level); then use `h₁` to finish.
  rw [Measure.bind_bind
        Measurable.of_discrete.aemeasurable
        Measurable.of_discrete.aemeasurable]
  -- Push the outer `.map (·.expr)` inside the bind.
  rw [Measure.bind_map_comm]
  -- Pointwise: for each σ', replace the inner bind+map with the IH.
  have hker : (fun σ' : State =>
      Measure.map (·.expr : Cfg → Exp)
        ((μ₂ σ').bind (fun σ'' => execN m ⟨e, σ''⟩)))
      = (fun σ' : State =>
          Measure.map (·.expr) (execN m ⟨e, σ'⟩)) := by
    funext σ'
    exact h₂ σ' e m
  rw [hker]
  -- Now the goal is: μ₁.bind (fun σ' => (execN m ⟨e, σ'⟩).map (·.expr)) =
  --                  (execN m ⟨e, σ⟩).map (·.expr).
  -- Pull the `.map` back out, then apply `h₁ e m`.
  rw [← Measure.bind_map_comm]
  exact h₁ e m

/-- `ErasableExpr` lifts through `limExec` at the expression-projection
level. This is the load-bearing corollary for the adequacy wrappers.

Proof via `lintegral_limExec`: we test both sides against the indicator of
`(·.expr) ⁻¹' S`, use the integral-vs-iSup equation `lintegral_limExec`,
and apply the `ErasableExpr` hypothesis pointwise at each `n`. -/
theorem lim_exec {μ : Measure State} {σ : State} (h : ErasableExpr μ σ)
    (e : Exp) :
    (μ.bind (fun σ' => limExec ⟨e, σ'⟩)).map (·.expr) =
      (limExec ⟨e, σ⟩).map (·.expr) := by
  refine Measure.ext fun S hS => ?_
  -- Rewrite both sides as `limExec ... (preimage S)`:
  rw [Measure.map_apply Measurable.of_discrete hS,
      Measure.map_apply Measurable.of_discrete hS,
      Measure.bind_apply (Measurable.of_discrete hS)
        Measurable.of_discrete.aemeasurable]
  -- Goal now:
  --   ∫⁻ σ', limExec ⟨e,σ'⟩ ((·.expr) ⁻¹' S) ∂μ
  --   = limExec ⟨e,σ⟩ ((·.expr) ⁻¹' S)
  -- Express each `limExec ρ A` as `∫⁻ x, indicator A 1 x ∂(limExec ρ)`:
  have hind : ∀ ρ : Cfg,
      limExec ρ ((·.expr) ⁻¹' S)
        = ∫⁻ x, (((·.expr) ⁻¹' S) : Set Cfg).indicator 1 x ∂(limExec ρ) := by
    intro ρ
    rw [lintegral_indicator_one (Measurable.of_discrete hS)]
  simp_rw [hind]
  -- Use `lintegral_limExec` on both sides (outer iSup swap).
  simp_rw [lintegral_limExec]
  -- Goal:
  --   ∫⁻ σ', (⨆ n, ∫⁻ x, indicator _ 1 x ∂(execN n ⟨e,σ'⟩)) ∂μ
  --   = ⨆ n, ∫⁻ x, indicator _ 1 x ∂(execN n ⟨e,σ⟩)
  -- Pull the outer iSup through the outer integral:
  rw [lintegral_iSup (fun _ => Measurable.of_discrete)
        (fun i j hij σ' =>
          lintegral_mono' (execN_mono hij ⟨e, σ'⟩) (le_refl _))]
  -- Now just pointwise equality at each n, via the `ErasableExpr` hypothesis.
  refine iSup_congr fun n => ?_
  -- For each n, apply h e n and evaluate at the set S. The hypothesis is
  -- about the projected measure on `Exp`.
  have hn := h e n
  have hval : (μ.bind (fun σ' => execN n ⟨e, σ'⟩)).map (·.expr) S
            = (execN n ⟨e, σ⟩).map (·.expr) S := by
    rw [hn]
  rw [Measure.map_apply Measurable.of_discrete hS,
      Measure.map_apply Measurable.of_discrete hS,
      Measure.bind_apply (Measurable.of_discrete hS)
        Measurable.of_discrete.aemeasurable] at hval
  -- Convert both sides' integrals from indicator form:
  rw [show (∫⁻ x, (((·.expr) ⁻¹' S) : Set Cfg).indicator 1 x ∂(execN n ⟨e, σ⟩))
        = (execN n ⟨e, σ⟩) ((·.expr) ⁻¹' S)
      from lintegral_indicator_one (Measurable.of_discrete hS)]
  simp_rw [show ∀ σ' : State,
        (∫⁻ x, (((·.expr) ⁻¹' S) : Set Cfg).indicator 1 x ∂(execN n ⟨e, σ'⟩))
          = (execN n ⟨e, σ'⟩) ((·.expr) ⁻¹' S)
      from fun σ' => lintegral_indicator_one (Measurable.of_discrete hS)]
  exact hval

end ErasableExpr

/-! ## ARcoupl wrappers

These are the Approxis-facing lemmas. They take `ErasableExpr` witnesses
(weaker than strict `Erasable`) and an `AddCoupl` on the underlying state
distributions, and lift to an `AddCoupl` on the `execN`/`limExec` images
**at the expression-projection level**.

The wrapper conclusions are phrased as `AddCoupl ε Φexp (μ.map (·.expr)) (ν.map (·.expr))`
rather than the unprojected `AddCoupl ε (ExprRel Φexp) μ ν`. The projected
form is semantically what the adequacy layer consumes (Clutch's `ARcoupl`
is already at the val-projected level), and it's the level at which our
`ErasableExpr` hypothesis naturally interacts with `AddCoupl.bind`. -/

/-- **Clutch `ARcoupl_erasure_erasable`, core version (projected form).**
Given an additive coupling between `ErasableExpr` distributions `μ₁` and
`μ₂`, and a coupling continuation on projected `execN n / limExec` under an
`Exp × Exp` relation, we lift to a coupling on
`(execN n ⟨e₁, σ₁⟩).map (·.expr) / (limExec ⟨e₁', σ₁'⟩).map (·.expr)`.
The error slacks add. -/
theorem AddCoupl_erasure_erasable
    {e₁ e₁' : Exp} {σ₁ σ₁' : State}
    {μ₁ μ₂ : Measure State} {R : Set (State × State)}
    {Φexp : Set (Exp × Exp)}
    {ε ε₁ ε₂ : ENNReal} {n : Nat}
    (hSum : ε₁ + ε₂ ≤ ε)
    (hμ₁mass : μ₁ Set.univ ≤ 1)
    (hCoupl : AddCoupl ε₁ R μ₁ μ₂)
    (hErase₁ : ErasableExpr μ₁ σ₁)
    (hErase₂ : ErasableExpr μ₂ σ₁')
    (hCont : ∀ σ₂ σ₂', R (σ₂, σ₂') →
        AddCoupl ε₂ Φexp
          ((execN n ⟨e₁, σ₂⟩).map (·.expr))
          ((limExec ⟨e₁', σ₂'⟩).map (·.expr))) :
    AddCoupl ε Φexp
      ((execN n ⟨e₁, σ₁⟩).map (·.expr))
      ((limExec ⟨e₁', σ₁'⟩).map (·.expr)) := by
  -- Rewrite both projected targets via the `ErasableExpr` hypotheses.
  rw [← hErase₁ e₁ n, ← hErase₂.lim_exec e₁']
  -- Push `.map (·.expr)` through both outer binds.
  rw [Measure.bind_map_comm, Measure.bind_map_comm]
  -- Sub-probability of the inner kernels (projected `execN n`).
  have hmassk : ∀ σ : State, (execN n ⟨e₁, σ⟩).map (·.expr) Set.univ ≤ 1 := by
    intro σ
    rw [Measure.map_apply Measurable.of_discrete MeasurableSet.univ]
    simpa using execN_univ_le_one n ⟨e₁, σ⟩
  -- Apply `AddCoupl.bind` to get the `(ε₁ + ε₂)`-slack coupling, then
  -- strengthen to `ε`-slack via `mono_grading`.
  have hBind := AddCoupl.bind
    (Hfm := Measurable.of_discrete) (Hgm := Measurable.of_discrete)
    (Hμₗ := hμ₁mass) (Hfsprob := hmassk)
    (Hcpl := hCoupl)
    (Hbind := fun {σ₂ σ₂'} (hR : R (σ₂, σ₂')) => hCont σ₂ σ₂' hR)
  exact AddCoupl.mono_grading hSum hBind

/-- **Clutch `ARcoupl_erasure_erasable_exp_rhs`, reformulated (projected form).**
RHS expected-value variant (advanced composition). The continuation's
slack `E₂` depends on the RHS sample, paid as additional slack on the LHS. -/
theorem AddCoupl_erasure_erasable_exp_rhs
    {e₁ e₁' : Exp} {σ₁ σ₁' : State}
    {μ₁ μ₁' : Measure State} {R : Set (State × Cfg)}
    {Φexp : Set (Exp × Exp)}
    {ε ε₁ ε₂ : ENNReal} {E₂ : Cfg → ENNReal} {n m : Nat}
    (hE₂meas : Measurable E₂)
    (hCoupl : AddCoupl ε₁ R μ₁
        (μ₁'.bind (fun σ₂' => pexecN m ⟨e₁', σ₂'⟩)))
    (hBoundSum : ∫⁻ ρ, E₂ ρ ∂(μ₁'.bind (fun σ₂' => pexecN m ⟨e₁', σ₂'⟩)) ≤ ε₂)
    (hEpsSum : ε₁ + ε₂ ≤ ε)
    (hErase₁ : ErasableExpr μ₁ σ₁)
    (hErase₁' : ErasableExpr μ₁' σ₁')
    (hCont : ∀ σ₂ ρ', R (σ₂, ρ') →
        AddCoupl (E₂ ρ') Φexp
          ((execN n ⟨e₁, σ₂⟩).map (·.expr))
          ((limExec ρ').map (·.expr))) :
    AddCoupl ε Φexp
      ((execN n ⟨e₁, σ₁⟩).map (·.expr))
      ((limExec ⟨e₁', σ₁'⟩).map (·.expr)) := by
  -- Rewrite both projected targets via the erasability hypotheses.
  -- LHS: `(execN n ⟨e₁, σ₁⟩).map (·.expr)` ← `(μ₁.bind (execN n ⟨e₁, ·⟩)).map (·.expr)`
  rw [← hErase₁ e₁ n]
  -- RHS: `(limExec ⟨e₁', σ₁'⟩).map (·.expr)` ← `(μ₁'.bind (limExec ⟨e₁', ·⟩)).map (·.expr)`
  rw [← hErase₁'.lim_exec e₁']
  -- Also fold `μ₁'.bind (pexecN m ⟨e₁', ·⟩).bind limExec` into
  -- `μ₁'.bind (limExec ⟨e₁', ·⟩)` using `limExec_pexecN`.
  -- But first we'll express the target in terms of the `pexecN m`-form
  -- so that `hCoupl` applies directly as the outer coupling.
  --
  -- Rewrite `μ₁'.bind (fun σ₂' => limExec ⟨e₁', σ₂'⟩)` to the double-bind form:
  --   = μ₁'.bind (fun σ₂' => (pexecN m ⟨e₁', σ₂'⟩).bind limExec)
  --   = (μ₁'.bind (pexecN m ⟨e₁', ·⟩)).bind limExec
  have hrw : (μ₁'.bind (fun σ₂' => limExec ⟨e₁', σ₂'⟩))
           = (μ₁'.bind (fun σ₂' => pexecN m ⟨e₁', σ₂'⟩)).bind limExec := by
    rw [Measure.bind_bind
          Measurable.of_discrete.aemeasurable
          Measurable.of_discrete.aemeasurable]
    congr 1
    funext σ₂'
    exact limExec_pexecN m ⟨e₁', σ₂'⟩
  rw [hrw]
  -- Push `.map (·.expr)` through both outer binds.
  rw [Measure.bind_map_comm, Measure.bind_map_comm]
  -- Sub-probability of the inner kernels (projected `execN n ⟨e₁, ·⟩`).
  have hmassk : ∀ σ : State, (execN n ⟨e₁, σ⟩).map (·.expr) Set.univ ≤ 1 := by
    intro σ
    rw [Measure.map_apply Measurable.of_discrete MeasurableSet.univ]
    simpa using execN_univ_le_one n ⟨e₁, σ⟩
  -- Apply `bind_adv` with outer `hCoupl` and inner `hCont`.
  have hBind := AddCoupl.bind_adv
    (Hfm := Measurable.of_discrete) (Hgm := Measurable.of_discrete)
    (HE₂m := hE₂meas)
    (Hfsprob := hmassk)
    (HE₂sum := hBoundSum)
    (Hcpl := hCoupl)
    (Hbind := fun {σ₂ ρ'} hR => hCont σ₂ ρ' hR)
  exact AddCoupl.mono_grading hEpsSum hBind

/-- **Clutch `ARcoupl_erasure_erasable_exp_lhs`, reformulated (projected form).**
LHS expected-value variant. Symmetric to `AddCoupl_erasure_erasable_exp_rhs`. -/
theorem AddCoupl_erasure_erasable_exp_lhs
    {e₁ e₁' : Exp} {σ₁ σ₁' : State}
    {μ₁' : Measure State} {R : Set (Cfg × State)}
    {Φexp : Set (Exp × Exp)}
    {ε ε₁ ε₂ : ENNReal} {E₂ : Cfg → ENNReal} {n : Nat}
    (hE₂meas : Measurable E₂)
    (hCoupl : AddCoupl ε₁ R (primStep ⟨e₁, σ₁⟩) μ₁')
    (hBoundSum : ∫⁻ ρ, E₂ ρ ∂(primStep ⟨e₁, σ₁⟩) ≤ ε₂)
    (hEpsSum : ε₁ + ε₂ ≤ ε)
    (hErase₁' : ErasableExpr μ₁' σ₁')
    (hCont : ∀ ρ σ₂', R (ρ, σ₂') →
        AddCoupl (E₂ ρ) Φexp
          ((execN n ρ).map (·.expr))
          ((limExec ⟨e₁', σ₂'⟩).map (·.expr))) :
    AddCoupl ε Φexp
      (((primStep ⟨e₁, σ₁⟩).bind (execN n)).map (·.expr))
      ((limExec ⟨e₁', σ₁'⟩).map (·.expr)) := by
  -- Rewrite the RHS via `hErase₁'`:
  --   `(limExec ⟨e₁', σ₁'⟩).map (·.expr) = (μ₁'.bind (limExec ⟨e₁', ·⟩)).map (·.expr)`.
  rw [← hErase₁'.lim_exec e₁']
  -- Push `.map (·.expr)` through both outer binds.
  rw [Measure.bind_map_comm, Measure.bind_map_comm]
  -- Sub-probability of inner `execN n ρ` projected kernels.
  have hmassk : ∀ ρ : Cfg, (execN n ρ).map (·.expr) Set.univ ≤ 1 := by
    intro ρ
    rw [Measure.map_apply Measurable.of_discrete MeasurableSet.univ]
    simpa using execN_univ_le_one n ρ
  -- Apply `bind_adv_lhs` (LHS-indexed variable slack).
  have hBind := AddCoupl.bind_adv_lhs
    (Hfm := Measurable.of_discrete) (Hgm := Measurable.of_discrete)
    (HE₂m := hE₂meas)
    (Hfsprob := hmassk)
    (HE₂sum := hBoundSum)
    (Hcpl := hCoupl)
    (Hbind := fun {ρ σ₂'} hR => hCont ρ σ₂' hR)
  exact AddCoupl.mono_grading hEpsSum hBind

/-- **Clutch `ARcoupl_erasure_erasable_exp_lhs_kanto`, reformulated (projected form).**

Kantorovich-style LHS variant. The slack `E₂ : Cfg → Cfg → ENNReal` depends
on both the LHS and RHS samples, and the wrapper takes a higher-order
test-function expectation-bound hypothesis (`hExp`): for every pair of
`[0,1]`-bounded measurable `h₁, h₂` with `h₁ ρ ≤ h₂ ρ' + E₂ ρ ρ'`,
`∫⁻ h₁ ∂(primStep ⟨e₁,σ₁⟩) ≤ ∫⁻ h₂ ∂(μ₁'.bind (pexecN m ⟨e₁', ·⟩)) + ε`.

The conclusion operates on the LHS *after* one `primStep` bind — i.e. on
`(primStep ⟨e₁,σ₁⟩ >>= execN n).map (·.expr)` — matching `execN (n+1)` for
non-value `e₁` via `execN_succ_not_isValue`. -/
theorem AddCoupl_erasure_erasable_exp_lhs_kanto
    {e₁ e₁' : Exp} {σ₁ σ₁' : State}
    {μ₁' : Measure State} {Φexp : Set (Exp × Exp)}
    {ε : ENNReal} {E₂ : Cfg → Cfg → ENNReal}
    {n m : Nat}
    (hErase₁' : ErasableExpr μ₁' σ₁')
    (hExp : ∀ (h₁ h₂ : Cfg → ENNReal),
        (∀ ρ, h₁ ρ ≤ 1) → (∀ ρ, h₂ ρ ≤ 1) →
        (∀ ρ ρ', h₁ ρ ≤ h₂ ρ' + E₂ ρ ρ') →
        ∫⁻ ρ, h₁ ρ ∂(primStep ⟨e₁, σ₁⟩) ≤
          ∫⁻ ρ', h₂ ρ' ∂(μ₁'.bind (fun σ => pexecN m ⟨e₁', σ⟩)) + ε)
    (hCont : ∀ ρ ρ',
        AddCoupl (E₂ ρ ρ') Φexp
          ((execN n ρ).map (·.expr))
          ((limExec ρ').map (·.expr))) :
    AddCoupl ε Φexp
      (((primStep ⟨e₁, σ₁⟩).bind (execN n)).map (·.expr))
      ((limExec ⟨e₁', σ₁'⟩).map (·.expr)) := by
  -- Rewrite RHS via `hErase₁'` (erasability) and `limExec_pexecN` (pexec-limExec).
  --   (limExec ⟨e₁', σ₁'⟩).map (·.expr)
  --   = (μ₁'.bind (limExec ⟨e₁', ·⟩)).map (·.expr)                (hErase)
  --   = (μ₁'.bind (fun σ => (pexecN m ⟨e₁',σ⟩).bind limExec)).map (·.expr)  (limExec_pexecN)
  --   = ((μ₁'.bind (pexecN m ⟨e₁', ·⟩)).bind limExec).map (·.expr)           (bind_bind)
  rw [← hErase₁'.lim_exec e₁']
  have hrw : (μ₁'.bind (fun σ => limExec ⟨e₁', σ⟩))
           = (μ₁'.bind (fun σ => pexecN m ⟨e₁', σ⟩)).bind limExec := by
    rw [Measure.bind_bind
          Measurable.of_discrete.aemeasurable
          Measurable.of_discrete.aemeasurable]
    congr 1
    funext σ
    exact limExec_pexecN m ⟨e₁', σ⟩
  rw [hrw]
  -- Push `.map (·.expr)` through both outer binds.
  rw [Measure.bind_map_comm, Measure.bind_map_comm]
  -- Subprobability of inner kernels.
  have hmassk_L : ∀ ρ : Cfg, (execN n ρ).map (·.expr) Set.univ ≤ 1 := by
    intro ρ
    rw [Measure.map_apply Measurable.of_discrete MeasurableSet.univ]
    simpa using execN_univ_le_one n ρ
  have hmassk_R : ∀ ρ' : Cfg, (limExec ρ').map (·.expr) Set.univ ≤ 1 := by
    intro ρ'
    rw [Measure.map_apply Measurable.of_discrete MeasurableSet.univ]
    simpa using limExec_leq_mass (r := 1) (fun n => execN_univ_le_one n ρ')
  -- Apply `bind_adv_kanto`. Test-function measurability is automatic on Cfg
  -- (discrete space) via `Measurable.of_discrete`.
  exact AddCoupl.bind_adv_kanto
    (Hfm := Measurable.of_discrete) (Hgm := Measurable.of_discrete)
    (Hfsprob := hmassk_L) (Hgsprob := hmassk_R)
    (Hexp := fun h₁ h₂ _ _ => hExp h₁ h₂)
    (Hcont := hCont)

end ProbLang
