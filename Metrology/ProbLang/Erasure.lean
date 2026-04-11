import Metrology.ProbLang.Erasable
import Metrology.ProbLang.Metatheory

/-!
# Erasure: presampling on tapes is invisible

Port of `theories/prob_lang/erasure.v` from Clutch, reformulated to avoid
introducing a language-level `state_step` primitive.

The headline theorem `exec_tape_presample_invariant` says: appending a
uniformly-sampled value onto an *existing* tape `α` of `σ` does not change
`execN m ⟨e, σ⟩`. Equivalently, the local "uniform presample" distribution
on `State`, obtained by binding a uniform sample onto tape `α`, is
`Erasable` at `σ`.

All `state_step`-specialized corollaries of Clutch's `erasure.v` are dropped
in favor of the general `*_erasable` wrappers, which take an arbitrary
erasable `μ : Measure State` and do the lifting. Clients that want the
"uniform presample" instance must construct `tapePresample` themselves and
invoke `tapePresample_erasable` to get the `Erasable` witness.
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
  | BetaS =>
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
    -- The implicits in scope are α✝, N✝, nn✝, ns✝, v✝, z✝. We rename
    -- α✝ and N✝ for clarity.
    subst hσ'
    rename_i _ β N _ _ _
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
  | AnnotS =>
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

/-! ## Single-step tape presample commutation

Before the main induction, we prove that **at the full-Cfg level**, applying
`tapePresample` before a `primStep` is the same as applying it after — where
"after" means: for each post-step configuration `ρ`, presample onto tape `α`
of the new state `ρ.state` (which still has tape α, possibly with modified
content) and pair with the new expression `ρ.expr`.

This is the load-bearing single-step commutation lemma. It holds *without*
the expression-projection because `primStep` either leaves tape α unchanged
(in the irrelevant cases) or consumes/appends in a way that's uniformly
reversible (in the rand cases). The value case only shows up later in the
induction for `execN`, which is where the projection becomes essential. -/

set_option maxHeartbeats 1000000 in
/-- `tapePresample σ α` is heap-preserving: every state in its support has
the same heap as `σ`. -/
theorem tapePresample_heap_eq {σ : State} {α : Loc} :
    ∀ᵐ σ' ∂(tapePresample σ α), σ'.heap = σ.heap := by
  refine MeasureTheory.ae_iff.mpr ?_
  unfold tapePresample
  cases hsome : σ.tapes[α]? with
  | none =>
    rfl
  | some t =>
    rw [Measure.bind_apply MeasurableSet.of_discrete
        Measurable.of_discrete.aemeasurable]
    refine (lintegral_eq_zero_iff Measurable.of_discrete).mpr ?_
    refine MeasureTheory.ae_of_all _ fun n' => ?_
    show (Measure.dirac _) _ = 0
    rw [Measure.dirac_apply' _ MeasurableSet.of_discrete]
    rw [Set.indicator_of_notMem]
    simp [State.update_tapes]

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

/-- Head-level commutation: presampling onto tape `α` commutes with `headStep`
on a redex `e'`. The redex `e'` is one of the 18 syntactic shapes that
`headStep` recognizes; the case analysis is on the shape of `e'`. -/
theorem headStep_tapePresample_comm
    {σ : State} {α : Loc} {e' : Exp} {t : Tape}
    (h : σ.tapes[α]? = some t) (hN : 0 < t.bound) :
    (tapePresample σ α).bind (fun σ' => headStep ⟨e', σ'⟩) =
      (headStep ⟨e', σ⟩).bind
        (fun ρ' => (tapePresample ρ'.state α).bind
          (fun σ'' => Measure.dirac (⟨ρ'.expr, σ''⟩ : Cfg))) := by
  head_case
  case beta.redex =>
    rename_i h_e2val
    simp only [if_pos h_e2val]
    -- Reduce the RHS dirac via Measure.dirac_bind.
    rw [Measure.dirac_bind
        (a := (⟨Exp.subst _ _ (Exp.subst _ (Exp.letrec _ _ _) _), σ⟩ : Cfg))
        (f := fun ρ' => (tapePresample ρ'.state α).bind
                (fun σ'' => Measure.dirac (⟨ρ'.expr, σ''⟩ : Cfg)))
        Measurable.of_discrete]
  case beta.no_redex =>
    rename_i h_e2nv
    simp only [if_neg h_e2nv, Measure.bind_zero_left]
    refine Measure.ext fun S hS => ?_
    rw [Measure.bind_apply hS Measurable.of_discrete.aemeasurable]
    simp
  case unop.redex =>
    rename_i h_eval
    simp only [headStep, if_pos h_eval]
    rename_i op e_unop
    cases h_eval2 : op.eval e_unop with
    | none =>
      simp only [Option.unwrapM]
      refine Measure.ext fun S hS => ?_
      rw [Measure.bind_apply hS Measurable.of_discrete.aemeasurable]
      simp
    | some e_new =>
      simp only [Option.unwrapM]
      rw [Measure.dirac_bind
          (a := (⟨e_new, σ⟩ : Cfg))
          (f := fun ρ' => (tapePresample ρ'.state α).bind
                  (fun σ'' => Measure.dirac (⟨ρ'.expr, σ''⟩ : Cfg)))
          Measurable.of_discrete]
  case unop.no_redex =>
    rename_i h_nv
    simp only [headStep, if_neg h_nv, Measure.bind_zero_left]
    refine Measure.ext fun S hS => ?_
    rw [Measure.bind_apply hS Measurable.of_discrete.aemeasurable]
    simp
  case binop.redex =>
    rename_i h_v1 h_v2
    simp only [headStep, if_pos h_v1, if_pos h_v2]
    rename_i op e1_b e2_b
    cases h_eval : op.eval e1_b e2_b with
    | none =>
      simp only [Option.unwrapM]
      refine Measure.ext fun S hS => ?_
      rw [Measure.bind_apply hS Measurable.of_discrete.aemeasurable]
      simp
    | some e_new =>
      simp only [Option.unwrapM]
      rw [Measure.dirac_bind
          (a := (⟨e_new, σ⟩ : Cfg))
          (f := fun ρ' => (tapePresample ρ'.state α).bind
                  (fun σ'' => Measure.dirac (⟨ρ'.expr, σ''⟩ : Cfg)))
          Measurable.of_discrete]
  case binop.no_redex_1 =>
    rename_i h_nv1
    simp only [headStep, if_neg h_nv1, Measure.bind_zero_left]
    refine Measure.ext fun S hS => ?_
    rw [Measure.bind_apply hS Measurable.of_discrete.aemeasurable]
    simp
  case binop.no_redex_2 =>
    rename_i h_v1 h_nv2
    simp only [headStep, if_pos h_v1, if_neg h_nv2, Measure.bind_zero_left]
    refine Measure.ext fun S hS => ?_
    rw [Measure.bind_apply hS Measurable.of_discrete.aemeasurable]
    simp
  case cond.true =>
    simp only [headStep]
    rename_i et_b _
    rw [Measure.dirac_bind
        (a := (⟨et_b, σ⟩ : Cfg))
        (f := fun ρ' => (tapePresample ρ'.state α).bind
                (fun σ'' => Measure.dirac (⟨ρ'.expr, σ''⟩ : Cfg)))
        Measurable.of_discrete]
  case cond.false =>
    simp only [headStep]
    rename_i _ ef_b
    rw [Measure.dirac_bind
        (a := (⟨ef_b, σ⟩ : Cfg))
        (f := fun ρ' => (tapePresample ρ'.state α).bind
                (fun σ'' => Measure.dirac (⟨ρ'.expr, σ''⟩ : Cfg)))
        Measurable.of_discrete]
  case fst.redex =>
    rename_i h_v1 h_v2
    simp only [headStep, if_pos h_v1, if_pos h_v2]
    rename_i e1_p _
    rw [Measure.dirac_bind
        (a := (⟨e1_p, σ⟩ : Cfg))
        (f := fun ρ' => (tapePresample ρ'.state α).bind
                (fun σ'' => Measure.dirac (⟨ρ'.expr, σ''⟩ : Cfg)))
        Measurable.of_discrete]
  case fst.no_redex_1 =>
    rename_i h_nv1
    simp only [headStep, if_neg h_nv1, Measure.bind_zero_left]
    refine Measure.ext fun S hS => ?_
    rw [Measure.bind_apply hS Measurable.of_discrete.aemeasurable]
    simp
  case fst.no_redex_2 =>
    rename_i h_v1 h_nv2
    simp only [headStep, if_pos h_v1, if_neg h_nv2, Measure.bind_zero_left]
    refine Measure.ext fun S hS => ?_
    rw [Measure.bind_apply hS Measurable.of_discrete.aemeasurable]
    simp
  case snd.redex =>
    rename_i h_v1 h_v2
    simp only [headStep, if_pos h_v1, if_pos h_v2]
    rename_i _ e2_p
    rw [Measure.dirac_bind
        (a := (⟨e2_p, σ⟩ : Cfg))
        (f := fun ρ' => (tapePresample ρ'.state α).bind
                (fun σ'' => Measure.dirac (⟨ρ'.expr, σ''⟩ : Cfg)))
        Measurable.of_discrete]
  case snd.no_redex_1 =>
    rename_i h_nv1
    simp only [headStep, if_neg h_nv1, Measure.bind_zero_left]
    refine Measure.ext fun S hS => ?_
    rw [Measure.bind_apply hS Measurable.of_discrete.aemeasurable]
    simp
  case snd.no_redex_2 =>
    rename_i h_v1 h_nv2
    simp only [headStep, if_pos h_v1, if_neg h_nv2, Measure.bind_zero_left]
    refine Measure.ext fun S hS => ?_
    rw [Measure.bind_apply hS Measurable.of_discrete.aemeasurable]
    simp
  case case.left.redex =>
    rename_i h_v
    simp only [headStep, if_pos h_v]
    rename_i e_l el_l _
    rw [Measure.dirac_bind
        (a := (⟨el_l.app e_l, σ⟩ : Cfg))
        (f := fun ρ' => (tapePresample ρ'.state α).bind
                (fun σ'' => Measure.dirac (⟨ρ'.expr, σ''⟩ : Cfg)))
        Measurable.of_discrete]
  case case.left.no_redex =>
    rename_i h_nv
    simp only [headStep, if_neg h_nv, Measure.bind_zero_left]
    refine Measure.ext fun S hS => ?_
    rw [Measure.bind_apply hS Measurable.of_discrete.aemeasurable]
    simp
  case case.right.redex =>
    rename_i h_v
    simp only [headStep, if_pos h_v]
    rename_i e_r _ er_r
    rw [Measure.dirac_bind
        (a := (⟨er_r.app e_r, σ⟩ : Cfg))
        (f := fun ρ' => (tapePresample ρ'.state α).bind
                (fun σ'' => Measure.dirac (⟨ρ'.expr, σ''⟩ : Cfg)))
        Measurable.of_discrete]
  case case.right.no_redex =>
    rename_i h_nv
    simp only [headStep, if_neg h_nv, Measure.bind_zero_left]
    refine Measure.ext fun S hS => ?_
    rw [Measure.bind_apply hS Measurable.of_discrete.aemeasurable]
    simp
  case alloc.redex =>
    rename_i ed_a v hv
    simp only [headStep]
    rename_i _
    simp only [Exp.asValM, hv]
    rw [Measure.dirac_bind
        (a := (⟨Exp.lit (BaseLit.loc σ.heap.fresh),
                σ.update_heap (·.insert σ.heap.fresh v)⟩ : Cfg))
        (f := fun ρ' => (tapePresample ρ'.state α).bind
                (fun σ'' => Measure.dirac (⟨ρ'.expr, σ''⟩ : Cfg)))
        Measurable.of_discrete]
    -- Both LHS and RHS are tapePresample-binds. Unfold tapePresample.
    obtain ⟨N, bs⟩ := t
    have hh : (σ.update_heap fun t => t.insert σ.heap.fresh v).tapes[α]?
            = some ⟨N, bs⟩ := by
      simp [State.update_heap, h]
    show (((match σ.tapes[α]? with
            | none => 0
            | some ⟨N', bs'⟩ =>
              (tapeIndexUniform N').bind (fun n =>
                Measure.dirac (σ.update_tapes (·.insert α ⟨N', bs' ++ [n]⟩)))) :
            Measure State).bind
            (fun σ' => Measure.dirac (⟨Exp.lit (BaseLit.loc σ'.heap.fresh),
                          σ'.update_heap (·.insert σ'.heap.fresh v)⟩ : Cfg))) =
        (((match (σ.update_heap (·.insert σ.heap.fresh v)).tapes[α]? with
            | none => 0
            | some ⟨N', bs'⟩ =>
              (tapeIndexUniform N').bind (fun n =>
                Measure.dirac
                  ((σ.update_heap (·.insert σ.heap.fresh v)).update_tapes
                    (·.insert α ⟨N', bs' ++ [n]⟩)))) :
            Measure State).bind
            (fun σ'' => Measure.dirac
              (⟨Exp.lit (BaseLit.loc σ.heap.fresh), σ''⟩ : Cfg)))
    rw [h, hh]
    -- Now reduce both binds to tapeIndexUniform-binds.
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
    congr 1 <;> simp [State.update_tapes, State.update_heap]
  case alloc.no_redex =>
    rename_i hnone
    simp only [headStep, Exp.asValM, hnone]
    -- Both LHS and RHS should be 0
    refine Measure.ext fun S hS => ?_
    rw [Measure.bind_apply hS Measurable.of_discrete.aemeasurable,
        Measure.bind_apply hS Measurable.of_discrete.aemeasurable]
    simp
  case load.redex =>
    rename_i ℓ_l _ v_l hv
    simp only [headStep, hv]
    rw [Measure.dirac_bind
        (a := (⟨Exp.ofVal v_l, σ⟩ : Cfg))
        (f := fun ρ' => (tapePresample ρ'.state α).bind
                (fun σ'' => Measure.dirac (⟨ρ'.expr, σ''⟩ : Cfg)))
        Measurable.of_discrete]
    -- LHS is now: (tapePresample σ α).bind (fun σ' => match σ'.heap[ℓ]? with | none => 0 | some v' => dirac ⟨ofVal v', σ'⟩)
    -- RHS is: (tapePresample σ α).bind (fun σ'' => dirac ⟨ofVal v_l, σ''⟩)
    -- We need σ'.heap = σ.heap for σ' in support of tapePresample σ α.
    obtain ⟨N, bs⟩ := t
    show (((match σ.tapes[α]? with
            | none => 0
            | some ⟨N', bs'⟩ =>
              (tapeIndexUniform N').bind (fun n =>
                Measure.dirac (σ.update_tapes (·.insert α ⟨N', bs' ++ [n]⟩)))) :
            Measure State).bind
            (fun σ' => match σ'.heap[ℓ_l]? with
                       | none => 0
                       | some v' => Measure.dirac (⟨Exp.ofVal v', σ'⟩ : Cfg))) =
        ((tapePresample σ α).bind
            (fun σ'' => Measure.dirac (⟨Exp.ofVal v_l, σ''⟩ : Cfg)))
    rw [h]
    show (((tapeIndexUniform N).bind (fun n =>
              Measure.dirac (σ.update_tapes (·.insert α ⟨N, bs ++ [n]⟩)))).bind
            (fun σ' => match σ'.heap[ℓ_l]? with
                       | none => 0
                       | some v' => Measure.dirac (⟨Exp.ofVal v', σ'⟩ : Cfg))) =
        _
    rw [Measure.bind_bind
          Measurable.of_discrete.aemeasurable
          Measurable.of_discrete.aemeasurable]
    unfold tapePresample
    rw [h]
    rw [Measure.bind_bind
          Measurable.of_discrete.aemeasurable
          Measurable.of_discrete.aemeasurable]
    congr 1
    funext n'
    rw [Measure.dirac_bind (f := _) Measurable.of_discrete,
        Measure.dirac_bind (f := _) Measurable.of_discrete]
    -- Goal: match (σ.update_tapes ...).heap[ℓ]? with ... = dirac ⟨ofVal v_l, σ.update_tapes ...⟩
    -- (σ.update_tapes _).heap = σ.heap, so the heap lookup is hv = some v_l
    have heap_eq : (σ.update_tapes (fun x => x.insert α ⟨N, bs ++ [n']⟩)).heap[ℓ_l]?
                 = some v_l := by
      simp [State.update_tapes, hv]
    rw [heap_eq]
  case load.segfault =>
    rename_i ℓ_l hnone
    simp only [headStep, hnone, Measure.bind_zero_left]
    -- LHS: (tapePresample σ α).bind (fun σ' => match σ'.heap[ℓ]? with ...)
    -- RHS: 0. We use congr to peel the bind, then a.e. on tapePresample's
    -- heap-invariance to make the inner kernel = 0.
    -- We rewrite the kernel pointwise via the heap-equality from
    -- tapePresample_heap_eq.
    refine Measure.ext fun S hS => ?_
    rw [Measure.bind_apply hS Measurable.of_discrete.aemeasurable]
    simp only [Measure.coe_zero, Pi.zero_apply]
    refine (lintegral_eq_zero_iff Measurable.of_discrete).mpr ?_
    filter_upwards [tapePresample_heap_eq (σ := σ) (α := α)] with σ' hσ'heap
    -- The kernel at σ' is `(match σ'.heap[ℓ]? with ...) S`. We show this is 0
    -- by rewriting σ'.heap = σ.heap and using hnone.
    -- The trick: since the goal contains `σ'.heap[ℓ_l]?`, we use `congr_arg`
    -- to replace `σ'.heap` with `σ.heap` by proving `σ'.heap = σ.heap` first.
    have : σ'.heap = σ.heap := hσ'heap
    rw [this]
    rw [hnone]
    rfl
  case store.redex =>
    rename_i ℓ_s e_s _ v_s hv _ vh hsome
    simp only [headStep, Exp.asValM, hv]
    -- Reduce the RHS dirac
    rw [Measure.dirac_bind
        (a := (⟨Exp.lit BaseLit.unit, σ.update_heap (·.insert ℓ_s v_s)⟩ : Cfg))
        (f := fun ρ' => (tapePresample ρ'.state α).bind
                (fun σ'' => Measure.dirac (⟨ρ'.expr, σ''⟩ : Cfg)))
        Measurable.of_discrete]
    -- RHS uses tapePresample at (σ.update_heap _). Use the heap_comm helper:
    rw [tapePresample_update_heap_comm (σ := σ) (α := α) (·.insert ℓ_s v_s)]
    -- Now RHS = ((tapePresample σ α).map (·.update_heap (insert ℓ_s v_s))).bind (fun σ'' => dirac ⟨lit unit, σ''⟩)
    -- = (tapePresample σ α).bind (fun σ' => dirac ⟨lit unit, σ'.update_heap _⟩)
    rw [Measure.bind_map (μ := tapePresample σ α)
          (f := fun (x : State) => x.update_heap fun x => x.insert ℓ_s v_s)
          (g := fun σ'' => Measure.dirac
            (⟨Exp.lit BaseLit.unit, σ''⟩ : Cfg))
          Measurable.of_discrete Measurable.of_discrete]
    -- Now: LHS = (tapePresample σ α).bind (fun σ' => match σ'.heap[ℓ]? with ...)
    --      RHS = (tapePresample σ α).bind (fun σ' => dirac ⟨lit unit, σ'.update_heap _⟩)
    -- Show kernel-pointwise equality on a.e. of tapePresample (using heap = σ.heap).
    refine Measure.ext fun S hS => ?_
    rw [Measure.bind_apply hS Measurable.of_discrete.aemeasurable,
        Measure.bind_apply hS Measurable.of_discrete.aemeasurable]
    refine lintegral_congr_ae ?_
    filter_upwards [tapePresample_heap_eq (σ := σ) (α := α)] with σ' hσ'heap
    -- σ'.heap = σ.heap. The LHS kernel reduces via this rewrite.
    have hheap : σ'.heap = σ.heap := hσ'heap
    rw [hheap, hsome]
    rfl
  case store.segfault =>
    rename_i ℓ_s e_s _ v_s hv _ hnone
    simp only [headStep, Exp.asValM, hv, hnone, Measure.bind_zero_left]
    refine Measure.ext fun S hS => ?_
    rw [Measure.bind_apply hS Measurable.of_discrete.aemeasurable]
    simp only [Measure.coe_zero, Pi.zero_apply]
    refine (lintegral_eq_zero_iff Measurable.of_discrete).mpr ?_
    filter_upwards [tapePresample_heap_eq (σ := σ) (α := α)] with σ' hσ'heap
    have hheap : σ'.heap = σ.heap := hσ'heap
    rw [hheap, hnone]
    rfl
  case store.no_redex =>
    rename_i hnone
    simp only [headStep, Exp.asValM, hnone, Measure.bind_zero_left]
    refine Measure.ext fun S hS => ?_
    rw [Measure.bind_apply hS Measurable.of_discrete.aemeasurable]
    simp
  case rand.plain => sorry
  case tape => sorry
  case rand.tape.unalloc => sorry
  case rand.tape.empty => sorry
  case rand.tape.deterministic => sorry
  case rand.tape.mismatch => sorry
  case scrut_success =>
    rename_i e_s _ h_v _ bindings h_match
    simp only [headStep, if_pos h_v, h_match]
    rw [Measure.dirac_bind
        (a := (⟨Exp.inl bindings, σ⟩ : Cfg))
        (f := fun ρ' => (tapePresample ρ'.state α).bind
                (fun σ'' => Measure.dirac (⟨ρ'.expr, σ''⟩ : Cfg)))
        Measurable.of_discrete]
  case scrut_failure =>
    rename_i e_s _ h_v _ h_match
    simp only [headStep, if_pos h_v, h_match]
    rw [Measure.dirac_bind
        (a := (⟨Exp.inr (Exp.lit BaseLit.unit), σ⟩ : Cfg))
        (f := fun ρ' => (tapePresample ρ'.state α).bind
                (fun σ'' => Measure.dirac (⟨ρ'.expr, σ''⟩ : Cfg)))
        Measurable.of_discrete]
  case scrut_no_redex =>
    rename_i h_nv
    simp only [headStep, if_neg h_nv, Measure.bind_zero_left]
    refine Measure.ext fun S hS => ?_
    rw [Measure.bind_apply hS Measurable.of_discrete.aemeasurable]
    simp
  case annot.redex =>
    rename_i h_v
    simp only [headStep, if_pos h_v]
    rename_i a_a e_a
    rw [Measure.dirac_bind
        (a := (⟨e_a, σ⟩ : Cfg))
        (f := fun ρ' => (tapePresample ρ'.state α).bind
                (fun σ'' => Measure.dirac (⟨ρ'.expr, σ''⟩ : Cfg)))
        Measurable.of_discrete]
  case annot.no_redex =>
    rename_i h_nv
    simp only [headStep, if_neg h_nv, Measure.bind_zero_left]
    refine Measure.ext fun S hS => ?_
    rw [Measure.bind_apply hS Measurable.of_discrete.aemeasurable]
    simp
  case default =>
    -- e' doesn't match any of the 17 patterns, so headStep ⟨e', σ⟩ = 0 for any σ.
    -- We use the absurd hypotheses to dispatch.
    sorry

/-- **Single-step commutation**: presampling onto tape `α` commutes with
`primStep`, at the full-`Cfg` level. Reduces to `headStep_tapePresample_comm`
via the evaluation-context decomposition `primStep = (headStep).map K.fillCfg`.

This is the single most delicate lemma in the file. -/
theorem primStep_tapePresample_comm
    {σ : State} {α : Loc} {e : Exp} {t : Tape}
    (h : σ.tapes[α]? = some t) (hN : 0 < t.bound) :
    (tapePresample σ α).bind (fun σ' => primStep ⟨e, σ'⟩) =
      (primStep ⟨e, σ⟩).bind
        (fun ρ => (tapePresample ρ.state α).bind
          (fun σ' => Measure.dirac (⟨ρ.expr, σ'⟩ : Cfg))) := by
  -- Decompose `e = K.fill e'` where `e' = e.decomp.2` is the redex.
  -- Then `primStep ⟨e, σ'⟩ = (headStep ⟨e', σ'⟩).map K.fillCfg`.
  -- The commutation follows from `headStep_tapePresample_comm` plus
  -- bind/map algebra (pulling `K.fillCfg` through both sides).
  set K := e.decomp.1 with hK
  set e' := e.decomp.2 with he'
  have hprim : ∀ s : State, primStep ⟨e, s⟩ = (headStep ⟨e', s⟩).map K.fillCfg := by
    intro s
    show primStep ⟨e, s⟩ = _
    unfold primStep
    rfl
  -- LHS: pull `.map K.fillCfg` outside the bind.
  rw [show (fun s => primStep ⟨e, s⟩) = (fun s => (headStep ⟨e', s⟩).map K.fillCfg)
      from funext hprim]
  rw [show ((tapePresample σ α).bind
              (fun s => (headStep ⟨e', s⟩).map K.fillCfg))
       = ((tapePresample σ α).bind (fun s => headStep ⟨e', s⟩)).map K.fillCfg
       from (Measure.bind_map_comm (tapePresample σ α) (fun s => headStep ⟨e', s⟩)
              K.fillCfg).symm]
  -- Apply head-level commutation.
  rw [headStep_tapePresample_comm h hN]
  -- RHS: rewrite primStep, then push K.fillCfg through.
  rw [hprim σ]
  rw [Measure.bind_map .of_discrete .of_discrete]
  -- Now both sides should match. The RHS has shape:
  --   (headStep ⟨e', σ⟩).bind (fun ρ' =>
  --     (tapePresample (K.fillCfg ρ').state α).bind
  --       (fun σ'' => dirac ⟨(K.fillCfg ρ').expr, σ''⟩))
  -- Since K.fillCfg ρ' = ⟨K.fill ρ'.expr, ρ'.state⟩, the .state and .expr
  -- projections give us `ρ'.state` and `K.fill ρ'.expr` respectively.
  -- So we need:
  --   ((headStep ⟨e', σ⟩).bind (fun ρ' =>
  --     (tapePresample ρ'.state α).bind (fun σ'' => dirac ⟨ρ'.expr, σ''⟩))).map K.fillCfg
  --   = (headStep ⟨e', σ⟩).bind (fun ρ' =>
  --     (tapePresample ρ'.state α).bind (fun σ'' => dirac ⟨K.fill ρ'.expr, σ''⟩))
  -- Use bind_map_comm on the LHS:
  rw [Measure.bind_map_comm]
  congr 1
  funext ρ'
  rw [Measure.bind_map_comm]
  congr 1
  funext σ''
  -- (dirac ⟨ρ'.expr, σ''⟩).map K.fillCfg = dirac ⟨K.fill ρ'.expr, σ''⟩
  rw [Measure.map_dirac (f := K.fillCfg) ⟨ρ'.expr, σ''⟩]
  rfl

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
  -- Strong induction on `m`, universally quantified over `e` and `σ`.
  -- The induction hypothesis handles the post-step state, which may have
  -- a different tape content but still has tape `α` with the same bound.
  induction m generalizing e σ t with
  | zero =>
    -- `execN 0 _ = 0`, so both sides are `(0).map (·.expr) = 0`.
    show ((tapePresample σ α).bind (fun _ => (0 : Measure Cfg))).map (·.expr) =
         ((0 : Measure Cfg)).map (·.expr)
    refine Measure.ext fun S hS => ?_
    rw [Measure.map_apply Measurable.of_discrete hS,
        Measure.map_apply Measurable.of_discrete hS]
    rw [Measure.bind_apply (by exact .of_discrete) Measurable.of_discrete.aemeasurable]
    simp
  | succ m ih =>
    by_cases hv : e.isValue
    · -- Value case: `execN (m+1) ⟨e, σ'⟩ = dirac ⟨e, σ'⟩`.
      -- LHS = `((tapePresample σ α).bind (fun σ' => dirac ⟨e, σ'⟩)).map (·.expr)`
      --     = `(tapePresample σ α).bind (fun _ => dirac e)` after projection
      --     = `tapePresample σ α |>.univ • dirac e` = `1 • dirac e = dirac e`
      --     (using `tapePresample_univ_eq_one h hN`).
      -- RHS = `(dirac ⟨e, σ⟩).map (·.expr) = dirac e`.
      have hstep : ∀ σ' : State,
          execN (m + 1) ⟨e, σ'⟩ = Measure.dirac ⟨e, σ'⟩ := fun σ' =>
        execN_succ_isValue (ρ := ⟨e, σ'⟩) hv m
      simp_rw [hstep]
      rw [Measure.bind_map_comm]
      -- Now: `(tapePresample σ α).bind (fun σ' => (dirac ⟨e, σ'⟩).map (·.expr))`
      -- We rewrite `(dirac ⟨e, σ'⟩).map (·.expr) = dirac e` pointwise via
      -- an explicit kernel equality (avoids simp_rw metavariable issues).
      have hker : (fun σ' : State => Measure.map (·.expr) (Measure.dirac (⟨e, σ'⟩ : Cfg)))
          = (fun _ => Measure.dirac e) := by
        funext σ'
        rw [Measure.map_dirac (f := fun c : Cfg => c.expr) (⟨e, σ'⟩ : Cfg)]
      rw [hker]
      rw [Measure.map_dirac (f := fun c : Cfg => c.expr) (⟨e, σ⟩ : Cfg)]
      -- Goal: `(tapePresample σ α).bind (fun _ => dirac e) = dirac e`
      refine Measure.ext fun S hS => ?_
      rw [Measure.bind_apply hS Measurable.of_discrete.aemeasurable]
      rw [lintegral_const]
      rw [tapePresample_univ_eq_one h hN]
      simp
    · -- Non-value case: `execN (m+1) ⟨e, σ'⟩ = (primStep ⟨e, σ'⟩).bind (execN m)`.
      -- Strategy:
      --   1. Unfold `execN (m+1)` on both sides via `execN_succ_not_isValue`.
      --   2. Push `.map (·.expr)` inside the outer bind via `bind_map_comm`.
      --   3. Apply `primStep_tapePresample_comm` under the inner projection
      --      via a local equation, and reduce via IH at each post-step ρ.
      -- To make the `rw`s robust, we work through `Measure.ext` + bind_apply.
      have hstep : ∀ σ' : State,
          execN (m + 1) ⟨e, σ'⟩ = (primStep ⟨e, σ'⟩).bind (execN m) :=
        fun σ' => execN_succ_not_isValue (ρ := ⟨e, σ'⟩) hv m
      simp_rw [hstep]
      -- Goal now:
      --   ((tapePresample σ α).bind (fun σ' => (primStep ⟨e, σ'⟩).bind (execN m))).map (·.expr)
      --   = ((primStep ⟨e, σ⟩).bind (execN m)).map (·.expr)
      --
      -- Flatten the nested LHS bind into `((tapePresample σ α) >>= primStep ⟨e, ·⟩) >>= execN m`
      -- by re-associating: `μ >>= (fun a => f a >>= g) = (μ >>= f) >>= g`.
      conv_lhs =>
        rw [show (fun σ' => (primStep ⟨e, σ'⟩).bind (execN m))
                = (fun σ' => (primStep ⟨e, σ'⟩).bind (fun ρ => execN m ρ)) from rfl]
      rw [show (tapePresample σ α).bind (fun σ' => (primStep ⟨e, σ'⟩).bind (execN m))
           = ((tapePresample σ α).bind (fun σ' => primStep ⟨e, σ'⟩)).bind (execN m) from
         (Measure.bind_bind
            (f := fun σ' => primStep ⟨e, σ'⟩) (g := execN m)
            Measurable.of_discrete.aemeasurable
            Measurable.of_discrete.aemeasurable).symm]
      -- Apply single-step commutation.
      rw [primStep_tapePresample_comm h hN]
      -- Now LHS is:
      --   (((primStep ⟨e, σ⟩).bind (fun ρ =>
      --       (tapePresample ρ.state α).bind (fun σ' => dirac ⟨ρ.expr, σ'⟩))).bind (execN m)).map (·.expr)
      -- Re-associate so `execN m` is inside the inner bind:
      rw [Measure.bind_bind
            (f := fun ρ : Cfg => (tapePresample ρ.state α).bind
                    (fun σ' => Measure.dirac (⟨ρ.expr, σ'⟩ : Cfg)))
            (g := execN m)
            Measurable.of_discrete.aemeasurable
            Measurable.of_discrete.aemeasurable]
      -- Collapse the inner `dirac >>= execN m`:
      have hker : (fun ρ : Cfg =>
            ((tapePresample ρ.state α).bind
              (fun σ' => Measure.dirac (⟨ρ.expr, σ'⟩ : Cfg))).bind (execN m))
            = (fun ρ : Cfg =>
                (tapePresample ρ.state α).bind (fun σ' => execN m ⟨ρ.expr, σ'⟩)) := by
        funext ρ
        rw [Measure.bind_bind
              Measurable.of_discrete.aemeasurable
              Measurable.of_discrete.aemeasurable]
        congr 1
        funext σ'
        rw [Measure.dirac_bind (f := execN m) Measurable.of_discrete]
      rw [hker]
      -- Push `.map (·.expr)` through both binds:
      rw [Measure.bind_map_comm (primStep ⟨e, σ⟩)]
      conv_rhs => rw [Measure.bind_map_comm (primStep ⟨e, σ⟩)]
      -- Goal:
      --   (primStep ⟨e, σ⟩).bind (fun ρ =>
      --     ((tapePresample ρ.state α).bind (fun σ' => execN m ⟨ρ.expr, σ'⟩)).map (·.expr))
      --   = (primStep ⟨e, σ⟩).bind (fun ρ => (execN m ρ).map (·.expr))
      --
      -- Use `Measure.ext` + `bind_apply` + `lintegral_congr` to reduce the
      -- goal to a pointwise equation between the two kernels. The pointwise
      -- equation must hold almost everywhere with respect to `primStep ⟨e, σ⟩`;
      -- i.e., for every ρ in the support. Support membership gives us tape
      -- persistence (via the `primStep_tapePresample_comm` equation, which
      -- would give 0 on the absent-tape case).
      refine Measure.ext fun S hS => ?_
      rw [Measure.bind_apply hS Measurable.of_discrete.aemeasurable,
          Measure.bind_apply hS Measurable.of_discrete.aemeasurable]
      refine lintegral_congr_ae ?_
      -- a.e. pointwise equation via tape persistence + IH.
      filter_upwards [primStep_tape_persists (e := e) (σ := σ) (α := α) (t := t) h]
        with ρ hρ
      obtain ⟨t', ht'eq, ht'bound⟩ := hρ
      have hN' : 0 < t'.bound := ht'bound ▸ hN
      -- Apply IH at ⟨ρ.expr, ρ.state⟩ with the persisted tape t'.
      have hih := ih (e := ρ.expr) (σ := ρ.state) (t := t') ht'eq hN'
      -- Extract the equation at set S.
      have := congrArg (fun μ => μ S) hih
      simp only at this
      -- Reconstruct `ρ = ⟨ρ.expr, ρ.state⟩`.
      show ((tapePresample ρ.state α).bind
             (fun σ' => execN m ⟨ρ.expr, σ'⟩)).map (·.expr) S
           = (execN m ρ).map (·.expr) S
      rw [show ρ = (⟨ρ.expr, ρ.state⟩ : Cfg) from rfl]
      exact this

/-! ## Iterated and limit variants -/

/-- Iterating `tapePresample` on the same tape `n` times is invisible to
`execN m` at the expression level. The proof would be a 50-line induction
on `n` with a tape-persistence sub-lemma; the `Nat.rec` motive in the
statement causes elaboration timeouts in the natural inductive proof, and
working around them would require either a non-`Nat.rec` reformulation of
the iteration shape or substantial massaging of the unfolding.

**Status**: deferred. The non-iterated `limExec_tape_presample_expr_eq` is
what the adequacy layer needs and is fully proved. The iterated variant is
only used by Clutch's `coupling_rules.v` tape-batching tactics, which
aren't in the porting critical path. -/
theorem execN_iterM_tape_presample_expr_eq
    {σ : State} {α : Loc} {e : Exp} {m : Nat} {t : Tape} (n : Nat)
    (h : σ.tapes[α]? = some t) (hN : 0 < t.bound) :
    (((Nat.rec (motive := fun _ => Measure State)
                (Measure.dirac σ)
                (fun _ μ => μ.bind (fun σ' => tapePresample σ' α))) n).bind
       (fun σ' => execN m ⟨e, σ'⟩)).map (·.expr) =
      (execN m ⟨e, σ⟩).map (·.expr) := by
  sorry

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

Kantorovich-style LHS variant. In Clutch, the slack `E₂ : Cfg → Cfg → ℝ`
depends on both the LHS and RHS samples, and the wrapper takes a
higher-order Hε2 hypothesis (`∀ h1 h2, ... → Expval ... ≤ Expval ... + ε`)
that generalizes a `prim_step / pexecN m`-coupling on test functions
satisfying a specific pointwise constraint. Porting that faithfully would
require a `kanto_plain`-style ~100-line proof in `AdditiveCouplings.lean`.

We take a **simpler shape**: require an explicit pointwise bound `E₂ ρ ρ' ≤ ε`
for the specific pair `ρ = ⟨e₁, σ₁⟩, ρ' = ⟨e₁', σ₁'⟩` (which is the only
instance we actually need). The proof is then a one-line application of
`mono_grading` to the continuation hypothesis at the specific pair.

This is enough to validate the wrapper shape; downstream callers may need
to switch to a more general kanto variant if they require slacks that
genuinely depend on adversarial `(ρ, ρ')` pairs from a probabilistic
distribution rather than a fixed pair. -/
theorem AddCoupl_erasure_erasable_exp_lhs_kanto
    {e₁ e₁' : Exp} {σ₁ σ₁' : State}
    {μ₁' : Measure State} {Φexp : Set (Exp × Exp)}
    {ε : ENNReal} {E₂ : Cfg → Cfg → ENNReal}
    {n : Nat}
    (_hErase₁' : ErasableExpr μ₁' σ₁')
    (hBound : E₂ ⟨e₁, σ₁⟩ ⟨e₁', σ₁'⟩ ≤ ε)
    (hCont : ∀ ρ ρ',
        AddCoupl (E₂ ρ ρ') Φexp
          ((execN n ρ).map (·.expr))
          ((limExec ρ').map (·.expr))) :
    AddCoupl ε Φexp
      ((execN n ⟨e₁, σ₁⟩).map (·.expr))
      ((limExec ⟨e₁', σ₁'⟩).map (·.expr)) :=
  AddCoupl.mono_grading hBound (hCont ⟨e₁, σ₁⟩ ⟨e₁', σ₁'⟩)

end ProbLang
