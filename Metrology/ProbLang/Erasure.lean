module

public import Metrology.ProbLang.Erasable
public import Metrology.ProbLang.Metatheory

@[expose] public section

/-!
# Erasure: presampling on tapes is invisible

Port of `theories/prob_lang/erasure.v` from Clutch, reformulated to avoid
introducing a language-level `state_step` primitive.

The headline theorem `execN_tape_presample_expr_eq` says: appending a
uniformly-sampled value onto an *existing* tape `α` of `σ` does not change
`execN m ⟨e, σ⟩` *at the expression level* (i.e. after projecting the
post-configuration by `(·.expr)`). Equivalently, the local "uniform
presample" distribution `tapePresample σ α` on `(State rT)` is `ErasableExpr`
at `σ`.

The full-`(Cfg rT)` version is false (presample genuinely changes the final tape
content), but the projected version is exactly what the adequacy layer
observes. All `state_step`-specialized corollaries of Clutch's `erasure.v`
are dropped in favor of the general `ErasableExpr` wrappers, which take an
arbitrary `μ : Measure (State rT)` and do the lifting. Clients construct
`tapePresample` themselves and invoke `ErasableExpr.tapePresample` to get
the witness.
-/

namespace ProbLang


variable {rT : Type _} [ProbLangℝ rT]

open MeasureTheory Measure

/-! ## Local uniform-presample distribution

These are file-local helpers used to *state* erasure, without adding any
new primitives to the language. In particular, `tapePresample σ α` is
**not** a language-level transition: it is just the `Measure (State rT)`
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

/-- List of all currently allocated tape addresses in `σ`. Rocq:
`get_active σ`. Used by the state-step disjunct of `glm` to enumerate
the tapes that may be presampled at a given step. -/
def getActive (σ : (State rT)) : List Loc := σ.tapes.keys

omit [ProbLangℝ rT] in
theorem getActive_mem_iff {σ : (State rT)} {α : Loc} :
    α ∈ getActive σ ↔ α ∈ σ.tapes := by
  unfold getActive
  exact Std.ExtTreeMap.mem_keys

/-- The local "uniform presample on tape `α`" distribution on `(State rT)`.
Given an existing tape `α` of bound `N` with current content `bs`, this
returns the `(State rT)`-measure obtained by sampling `n ∈ [0, N)` uniformly
and appending `n` to the tape. This is the analogue of Clutch's
`state_step σ α`, localized to this file so as not to pollute the
language-level semantics. If the tape `α` is absent, we return `0`. -/
noncomputable def tapePresample (σ : (State rT)) (α : Loc) : Measure (State rT) :=
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
omit [ProbLangℝ rT] in
tape with positive bound. -/
theorem tapePresample_univ_eq_one {σ : (State rT)} {α : Loc} {t : Tape}
    (h : σ.tapes[α]? = some t) (hN : 0 < t.bound) :
    (tapePresample σ α) Set.univ = 1 := by
  obtain ⟨N, bs⟩ := t
  simp only [tapePresample, h]
  rw [Measure.bind_apply MeasurableSet.univ
        Measurable.of_discrete.aemeasurable]
  simp_rw [Measure.dirac_apply' _ MeasurableSet.univ, Set.indicator_univ,
    Pi.one_apply, lintegral_one]
  exact tapeIndexUniform_univ_eq_one hN

/-- `tapeIndexUniform N` is s-finite (it is either a probability measure or `0`). -/
instance tapeIndexUniform.instSFinite {N : Int} : SFinite (tapeIndexUniform N) := by
  unfold tapeIndexUniform
  split
  · infer_instance
  · infer_instance

/-- **Kernel measurability of `tapePresample`** (countability-free).

`fun σ => tapePresample σ α` is measurable in the state. Discreteness of
`rT` previously made this `.of_discrete`; here we prove it directly via the
parameterized-pushforward machinery `Measure.measurable_map_uncurry`, the same
tool used for `Cfg.uniform.measurable`. The `match` on the (countable, discrete)
`Option Tape` lookup is dispatched by `measurable_from_prod_countable_right`. -/
theorem tapePresample.measurable {α : Loc} :
    Measurable (fun σ : State rT => tapePresample σ α) := by
  -- Body as a function of `(σ, optTape)`, with `optTape = σ.tapes[α]?` plugged in last.
  let leaf : State rT × Option Tape → Measure (State rT) :=
    fun p =>
      match p.2 with
      | none => 0
      | some ⟨N, bs⟩ =>
        (tapeIndexUniform N).bind
          (fun n => Measure.dirac (p.1.update_tapes (·.insert α ⟨N, bs ++ [n]⟩)))
  have hleaf : Measurable leaf := by
    have hflat : Measurable (fun q : Option Tape × State rT => leaf (q.2, q.1)) := by
      apply measurable_from_prod_countable_right
      intro optTape
      show Measurable (fun σ : State rT => leaf (σ, optTape))
      cases optTape with
      | none => exact measurable_const
      | some t =>
        obtain ⟨N, bs⟩ := t
        show Measurable (fun σ : State rT =>
          (tapeIndexUniform N).bind
            (fun n => Measure.dirac (σ.update_tapes (·.insert α ⟨N, bs ++ [n]⟩))))
        -- bind of a dirac kernel is a pushforward.
        have hconv : (fun σ : State rT =>
            (tapeIndexUniform N).bind
              (fun n => Measure.dirac (σ.update_tapes (·.insert α ⟨N, bs ++ [n]⟩))))
            = (fun σ : State rT =>
              (tapeIndexUniform N).map
                (fun n => σ.update_tapes (·.insert α ⟨N, bs ++ [n]⟩))) := by
          funext σ; exact Measure.bind_dirac_eq_map _ Measurable.of_discrete
        rw [hconv]
        -- Parameterized pushforward: `h (σ, n) = σ.update_tapes ...`, constant source kernel.
        have hval : Measurable
            (fun p : State rT × {z : Int // 0 ≤ z ∧ z < N} =>
              (⟨N, bs ++ [p.2]⟩ : Tape)) :=
          (Measurable.of_discrete (f := fun n : {z : Int // 0 ≤ z ∧ z < N} =>
            (⟨N, bs ++ [n]⟩ : Tape))).comp measurable_snd
        have hh : Measurable
            (fun p : State rT × {z : Int // 0 ≤ z ∧ z < N} =>
              p.1.update_tapes (·.insert α ⟨N, bs ++ [p.2]⟩)) :=
          State.measurable_mk_param (State.measurable_heap.comp measurable_fst)
            ((Measurable.locHeap_insert α).comp
              ((State.measurable_tapes.comp measurable_fst).prodMk hval))
        have hk : Measurable (fun _ : State rT => tapeIndexUniform N) := measurable_const
        have hSF : ProbabilityTheory.IsSFiniteKernel
            (ProbabilityTheory.Kernel.mk (fun _ : State rT => tapeIndexUniform N) hk) := by
          have : ProbabilityTheory.Kernel.mk (fun _ : State rT => tapeIndexUniform N) hk
              = ProbabilityTheory.Kernel.const (State rT) (tapeIndexUniform N) := rfl
          rw [this]; infer_instance
        exact @Measure.measurable_map_uncurry (State rT) {z : Int // 0 ≤ z ∧ z < N}
          (State rT) _ _ _ _ hh (fun _ => tapeIndexUniform N) hk hSF
    exact hflat.comp ((measurable_snd).prodMk measurable_fst)
  have hproj : Measurable (fun σ : State rT => (σ, σ.tapes[α]?)) :=
    measurable_id.prodMk ((LocHeap.measurable_getElem? α).comp State.measurable_tapes)
  show Measurable (fun σ : State rT => leaf (σ, σ.tapes[α]?))
  exact hleaf.comp hproj

/-- `tapeIndexUniform N` has total mass at most `1` (it is a probability
measure or `0`). -/
theorem tapeIndexUniform_univ_le_one {N : Int} :
    (tapeIndexUniform N) Set.univ ≤ 1 := by
  unfold tapeIndexUniform
  split
  · rename_i h
    haveI : IsProbabilityMeasure
        (PMF.uniformOfFinset (Finset.Ico 0 N) h).toMeasure :=
      PMF.toMeasure.isProbabilityMeasure _
    rw [Measure.map_apply Measurable.of_discrete MeasurableSet.univ]
    simp
  · simp

/-- `tapePresample σ α` has total mass at most `1` for every state. -/
theorem tapePresample_univ_le_one {σ : (State rT)} {α : Loc} :
    (tapePresample σ α) Set.univ ≤ 1 := by
  cases hsome : σ.tapes[α]? with
  | none => simp [tapePresample, hsome]
  | some t =>
    obtain ⟨N, bs⟩ := t
    simp only [tapePresample, hsome]
    rw [Measure.bind_apply MeasurableSet.univ Measurable.of_discrete.aemeasurable]
    calc ∫⁻ n, (Measure.dirac (σ.update_tapes (·.insert α ⟨N, bs ++ [n]⟩)) : Measure (State rT)) Set.univ
            ∂(tapeIndexUniform N)
        = ∫⁻ _, 1 ∂(tapeIndexUniform N) := by
          simp_rw [Measure.dirac_apply' _ MeasurableSet.univ, Set.indicator_univ, Pi.one_apply]
      _ = (tapeIndexUniform N) Set.univ := by rw [lintegral_one]
      _ ≤ 1 := tapeIndexUniform_univ_le_one

/-- **Kernel-measurability of a `tapePresample`-then-`dirac` bind.**

For a jointly-measurable post-state builder `g`, the kernel
`fun ρ => (tapePresample ρ.state α).bind (fun σ'' => dirac (g ρ σ''))` is
measurable in `ρ`. This is the countability-free replacement for the
`.of_discrete` kernel measurability used throughout the erasure proofs;
it relies on `tapePresample.measurable` and the mass bound
`tapePresample_univ_le_one` (which makes the source an `IsFiniteKernel`). -/
theorem tapePresample_bind_dirac_measurable {α : Loc}
    {g : (Cfg rT) → (State rT) → (Cfg rT)}
    (hg : Measurable (fun p : (Cfg rT) × (State rT) => g p.1 p.2)) :
    Measurable (fun ρ : (Cfg rT) =>
      (tapePresample ρ.state α).bind (fun σ'' => Measure.dirac (g ρ σ''))) := by
  have hconv : (fun ρ : (Cfg rT) =>
        (tapePresample ρ.state α).bind (fun σ'' => Measure.dirac (g ρ σ'')))
      = (fun ρ : (Cfg rT) => (tapePresample ρ.state α).map (fun σ'' => g ρ σ'')) := by
    funext ρ
    exact Measure.bind_dirac_eq_map _ (hg.comp (measurable_const.prodMk measurable_id))
  rw [hconv]
  have hk : Measurable (fun ρ : (Cfg rT) => tapePresample ρ.state α) :=
    tapePresample.measurable.comp Cfg.measurable_state
  haveI hFin : ProbabilityTheory.IsFiniteKernel
      (ProbabilityTheory.Kernel.mk (fun ρ : (Cfg rT) => tapePresample ρ.state α) hk) :=
    ⟨1, ENNReal.one_lt_top, fun _ => tapePresample_univ_le_one⟩
  exact Measure.measurable_map_uncurry hg hk


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

/-- Countability-free variant of `Measure.bind_map_comm`: pushing a map
through a bind, requiring explicit measurability of the kernel and the map
function rather than a discrete measurable space. -/
theorem Measure.bind_map_comm' {α β γ : Type*}
    [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    (μ : Measure α) (k : α → Measure β) (f : β → γ)
    (hk : AEMeasurable k μ) (hf : Measurable f) :
    (μ.bind k).map f = μ.bind (fun a => (k a).map f) := by
  have hkmap : AEMeasurable (fun a => (k a).map f) μ :=
    (Measure.measurable_map f hf).comp_aemeasurable hk
  refine Measure.ext fun S hS => ?_
  rw [Measure.map_apply hf hS,
      Measure.bind_apply (hf hS) hk,
      Measure.bind_apply hS hkmap]
  simp_rw [Measure.map_apply hf hS]

/-- Countability-free variant of `Measure.bind_map`: binding through a
pushforward, requiring explicit measurability rather than a discrete
measurable space. -/
theorem Measure.bind_map' {α β γ : Type*}
    [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    {μ : Measure α} {f : α → β} {g : β → Measure γ}
    (hf : Measurable f) (hg : Measurable g) :
    (μ.map f).bind g = μ.bind (g ∘ f) := by
  rw [Measure.bind, Measure.bind, Measure.map_map hg hf]

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
theorem primStep_tape_persists_support [ProbLangℝ rT]
    {σ : (State rT)} {αloc : Loc} {e : (Exp rT)} {t : Tape} {ρ : (Cfg rT)}
    (h : σ.tapes[αloc]? = some t)
    (hρ : Possible ρ (primStep ⟨e, σ⟩)) :
    ∃ t' : Tape, ρ.state.tapes[αloc]? = some t' ∧ t'.bound = t.bound := by
  obtain ⟨e₂, σ₂⟩ := ρ
  obtain ⟨K, e₁', e₂', _hfill1, _hfill2, hhs⟩ := prim_step_iff.mp hρ
  replace hhs := Possible.headStepSupport hhs
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
    have hne : σ.tapes.fresh ≠ αloc := Std.ExtTreeMap.elem_fresh_ne h
    refine ⟨t, ?_, rfl⟩
    exact State.upd_diff_tape_tot (hne.symm) |>.trans h
  | @RandTapeS β _ _ _ _ _ _ _ hα' _hN _hv hσ' =>
    subst hσ'
    by_cases hαβ : αloc = β
    · subst hαβ
      rw [hα'] at h
      have ht := Option.some.inj h
      subst ht
      refine ⟨_, State.upd_tape_some _ _ _, rfl⟩
    · refine ⟨t, ?_, rfl⟩
      rw [show (σ.update_tapes fun x => x.insert β _).tapes[αloc]? = σ.tapes[αloc]?
          from State.upd_diff_tape_tot hαβ]
      exact h
  | RandTapeEmptyS _ _ _ _ _ hσ' =>
    subst hσ'
    exact ⟨t, h, rfl⟩
  | RandTapeOtherS _ _ _ _ _ hσ' =>
    subst hσ'
    exact ⟨t, h, rfl⟩
  | RandNonposS _ =>
    exact ⟨t, h, rfl⟩
  | RandTapeNonposEmptyS _ _ _ =>
    exact ⟨t, h, rfl⟩
  | RandTapeNonposOtherS _ _ _ =>
    exact ⟨t, h, rfl⟩
  | ScrutSuccessS =>
    exact ⟨t, h, rfl⟩
  | ScrutFailureS =>
    exact ⟨t, h, rfl⟩
  | UrandS =>
    -- Continuous sample leaves the state (hence all tapes) unchanged.
    exact ⟨t, h, rfl⟩

/-- Discrete (positivity-phrased) wrapper around `primStep_tape_persists_support`. -/
@[discrete]
theorem Discrete.primStep_tape_persists_support [Countable rT] [MeasurableSingletonClass rT]
    {σ : (State rT)} {αloc : Loc} {e : (Exp rT)} {t : Tape} {ρ : (Cfg rT)}
    (h : σ.tapes[αloc]? = some t)
    (hρ : 0 < primStep ⟨e, σ⟩ {ρ}) :
    ∃ t' : Tape, ρ.state.tapes[αloc]? = some t' ∧ t'.bound = t.bound :=
  ProbLang.primStep_tape_persists_support h (possible_iff_pos.mpr hρ)

/-- Tape persistence, a.e. form: the set of `ρ`s where tape `α` is either
absent or has a different bound from `t` has measure 0 under `primStep ⟨e, σ⟩`.
Derived from the support form via the fact that singletons outside the
support have measure 0 (every discrete measure). -/
theorem primStep_tape_persists [Countable rT] [MeasurableSingletonClass rT]
    {σ : (State rT)} {α : Loc} {e : (Exp rT)} {t : Tape}
    (h : σ.tapes[α]? = some t) :
    ∀ᵐ ρ ∂(primStep ⟨e, σ⟩),
      ∃ t' : Tape, ρ.state.tapes[α]? = some t' ∧ t'.bound = t.bound := by
  -- Use `MeasureTheory.ae_iff` (the filter-level form).
  refine (MeasureTheory.ae_iff).mpr ?_
  rw [show {ρ : (Cfg rT) | ¬ ∃ t' : Tape, ρ.state.tapes[α]? = some t' ∧ t'.bound = t.bound}
        = ⋃ ρ ∈ {ρ : (Cfg rT) | ¬ ∃ t' : Tape, ρ.state.tapes[α]? = some t' ∧ t'.bound = t.bound},
            ({ρ} : Set (Cfg rT)) from by ext; simp]
  refine (measure_biUnion_null_iff (Set.to_countable _)).mpr ?_
  intro ρ hρ
  by_contra hne
  rw [← ne_eq, ← pos_iff_ne_zero] at hne
  exact hρ (primStep_tape_persists_support h (possible_iff_pos.mpr hne))

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
omit [ProbLangℝ rT] in
`indicator` scaffolding. -/
theorem tapePresample_ae
    {σ : (State rT)} {α : Loc} {N : Int}
    {bs : List { z : Int // 0 ≤ z ∧ z < N }} (h : σ.tapes[α]? = some ⟨N, bs⟩)
    {P : (State rT) → Prop} (hPm : MeasurableSet {σ' | P σ'})
    (hP : ∀ n, P (σ.update_tapes (·.insert α ⟨N, bs ++ [n]⟩))) :
    ∀ᵐ σ' ∂(tapePresample σ α), P σ' := by
  refine MeasureTheory.ae_iff.mpr ?_
  have hPc : MeasurableSet {σ' : (State rT) | ¬ P σ'} := hPm.compl
  simp only [tapePresample, h]
  rw [Measure.bind_apply hPc Measurable.of_discrete.aemeasurable]
  refine (lintegral_eq_zero_iff Measurable.of_discrete).mpr ?_
  refine MeasureTheory.ae_of_all _ fun n => ?_
  show (Measure.dirac (σ.update_tapes (·.insert α ⟨N, bs ++ [n]⟩)))
        {a | ¬P a} = 0
  rw [Measure.dirac_apply' _ hPc, Set.indicator_of_notMem]
  simp only [Set.mem_setOf_eq, not_not]
  exact hP n

/-- Discrete wrapper around `tapePresample_ae` (supplies the predicate
measurability via `MeasurableSet.of_discrete`). -/
@[discrete]
theorem Discrete.tapePresample_ae [Countable rT] [MeasurableSingletonClass rT]
    {σ : (State rT)} {α : Loc} {N : Int}
    {bs : List { z : Int // 0 ≤ z ∧ z < N }} (h : σ.tapes[α]? = some ⟨N, bs⟩)
    {P : (State rT) → Prop}
    (hP : ∀ n, P (σ.update_tapes (·.insert α ⟨N, bs ++ [n]⟩))) :
    ∀ᵐ σ' ∂(tapePresample σ α), P σ' :=
  ProbLang.tapePresample_ae h MeasurableSet.of_discrete hP

/-- `tapePresample σ α` is heap-preserving: every state in its support has
the same heap as `σ`. -/
theorem tapePresample_heap_eq
    {σ : (State rT)} {α : Loc} :
    ∀ᵐ σ' ∂(tapePresample σ α), σ'.heap = σ.heap := by
  cases hsome : σ.tapes[α]? with
  | none =>
    refine MeasureTheory.ae_iff.mpr ?_
    simp [tapePresample, hsome]
  | some t =>
    obtain ⟨N, bs⟩ := t
    exact tapePresample_ae hsome (by measurability) fun _ => by simp [State.update_tapes]

@[discrete]
theorem Discrete.tapePresample_heap_eq [Countable rT] [MeasurableSingletonClass rT]
    {σ : (State rT)} {α : Loc} :
    ∀ᵐ σ' ∂(tapePresample σ α), σ'.heap = σ.heap :=
  ProbLang.tapePresample_heap_eq

/-- `tapePresample σ α` only touches tape `α`: for any other location
`α_lbl ≠ α`, the lookup at `α_lbl` is a.e. unchanged. -/
theorem tapePresample_tape_ne_ae
    {σ : (State rT)} {α α_lbl : Loc} {t : Tape}
    (h : σ.tapes[α]? = some t) (hne : α_lbl ≠ α) :
    ∀ᵐ σ' ∂(tapePresample σ α), σ'.tapes[α_lbl]? = σ.tapes[α_lbl]? := by
  obtain ⟨N, bs⟩ := t
  exact tapePresample_ae h (by measurability) fun _ => State.upd_diff_tape_tot hne

@[discrete]
theorem Discrete.tapePresample_tape_ne_ae [Countable rT] [MeasurableSingletonClass rT]
    {σ : (State rT)} {α α_lbl : Loc} {t : Tape}
    (h : σ.tapes[α]? = some t) (hne : α_lbl ≠ α) :
    ∀ᵐ σ' ∂(tapePresample σ α), σ'.tapes[α_lbl]? = σ.tapes[α_lbl]? :=
  ProbLang.tapePresample_tape_ne_ae h hne

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
theorem tapePresample_bind_pull_heap [Countable rT] [MeasurableSingletonClass rT]
    {σ : (State rT)} {α : Loc}
    (k : Std.ExtTreeMap Loc (Val rT) compare → (State rT) → Measure (Cfg rT)) :
    (tapePresample σ α).bind (fun σ' => k σ'.heap σ') =
      (tapePresample σ α).bind (fun σ' => k σ.heap σ') := by
  -- Both sides equal each other a.e. on tapePresample because every state
  -- in its support has heap = σ.heap.
  unfold tapePresample
  cases hsome : σ.tapes[α]? with
  | none =>
    show ((0 : Measure (State rT)).bind _) = _
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
`tapePresample (σ.update_heap f) α = (tapePresample σ α).map (·.update_heap f)`.

Countability-free: the bind is over the discrete sample type (an `Int`
subtype), so the kernel is measurable via `.of_discrete`; only the
`update_heap f` map requires the explicit measurability hypothesis `hf`. -/
theorem tapePresample_update_heap_comm
    {σ : (State rT)} {α : Loc} (f : Std.ExtTreeMap Loc (Val rT) compare → Std.ExtTreeMap Loc (Val rT) compare)
    (hf : Measurable f) :
    tapePresample (σ.update_heap f) α =
      (tapePresample σ α).map (·.update_heap f) := by
  have hmap : Measurable (fun σ' : State rT => σ'.update_heap f) :=
    State.measurable_iff.mpr ⟨hf.comp State.measurable_heap, State.measurable_tapes⟩
  unfold tapePresample
  -- (σ.update_heap f).tapes[α]? = σ.tapes[α]?
  have htapes : (σ.update_heap f).tapes[α]? = σ.tapes[α]? := by
    simp [State.update_heap]
  rw [htapes]
  cases hsome : σ.tapes[α]? with
  | none =>
    show (0 : Measure (State rT)) = _
    rw [Measure.map_zero]
  | some t =>
    obtain ⟨N, bs⟩ := t
    simp only
    -- Both sides are (tapeIndexUniform N).bind (...)
    have hker : AEMeasurable (fun n : {z : Int // 0 ≤ z ∧ z < N} =>
        (Measure.dirac (σ.update_tapes (·.insert α ⟨N, bs ++ [n]⟩)) : Measure (State rT)))
        (tapeIndexUniform N) :=
      (measurable_dirac.comp Measurable.of_discrete).aemeasurable
    rw [Measure.bind_map_comm' _ _ _ hker hmap]
    congr 1
    funext n'
    rw [Measure.map_dirac (f := (·.update_heap f)) (σ.update_tapes (·.insert α ⟨N, bs ++ [n']⟩))]
    -- (σ.update_heap f).update_tapes _ = (σ.update_tapes _).update_heap f
    simp [State.update_tapes, State.update_heap]

@[discrete]
theorem Discrete.tapePresample_update_heap_comm [Countable rT] [MeasurableSingletonClass rT]
    {σ : (State rT)} {α : Loc} (f : Std.ExtTreeMap Loc (Val rT) compare → Std.ExtTreeMap Loc (Val rT) compare) :
    tapePresample (σ.update_heap f) α =
      (tapePresample σ α).map (·.update_heap f) :=
  ProbLang.tapePresample_update_heap_comm f Measurable.of_discrete

/-- Tape updates at keys other than `α` commute with tape presampling.
`tapePresample (σ.update_tapes f) α = (tapePresample σ α).map (·.update_tapes f)`,
provided `f` only modifies keys other than `α` in the sense that
`(σ.update_tapes f).tapes[α]? = σ.tapes[α]?` and the update/insert commute. -/
theorem tapePresample_update_tapes_ne_comm
    {σ : (State rT)} {α β : Loc} {v : Tape} (hne : β ≠ α) :
    tapePresample (σ.update_tapes (·.insert β v)) α =
      (tapePresample σ α).map (·.update_tapes (·.insert β v)) := by
  have hins : Measurable (fun m : LocHeap Tape => m.insert β v) :=
    (Measurable.locHeap_insert β).comp (measurable_id.prodMk measurable_const)
  have hmap : Measurable (fun σ' : State rT => σ'.update_tapes (·.insert β v)) :=
    State.measurable_iff.mpr ⟨State.measurable_heap, hins.comp State.measurable_tapes⟩
  unfold tapePresample
  have htapes : (σ.update_tapes (·.insert β v)).tapes[α]? = σ.tapes[α]? :=
    State.upd_diff_tape_tot (Ne.symm hne)
  rw [htapes]
  cases hsome : σ.tapes[α]? with
  | none =>
    show (0 : Measure (State rT)) = _
    rw [Measure.map_zero]
  | some t =>
    obtain ⟨N, bs⟩ := t
    simp only
    have hker : AEMeasurable (fun n : {z : Int // 0 ≤ z ∧ z < N} =>
        (Measure.dirac (σ.update_tapes (·.insert α ⟨N, bs ++ [n]⟩)) : Measure (State rT)))
        (tapeIndexUniform N) :=
      (measurable_dirac.comp Measurable.of_discrete).aemeasurable
    rw [Measure.bind_map_comm' _ _ _ hker hmap]
    congr 1
    funext n'
    rw [show Measure.dirac ((σ.update_tapes (·.insert β v)).update_tapes
            (·.insert α ⟨N, bs ++ [n']⟩))
        = (Measure.dirac (σ.update_tapes (·.insert α ⟨N, bs ++ [n']⟩))).map
            (·.update_tapes (·.insert β v)) from by
      rw [Measure.map_dirac]; congr 1; exact State.upd_diff_tape_comm (Ne.symm hne)]

@[discrete]
theorem Discrete.tapePresample_update_tapes_ne_comm [Countable rT] [MeasurableSingletonClass rT]
    {σ : (State rT)} {α β : Loc} {v : Tape} (hne : β ≠ α) :
    tapePresample (σ.update_tapes (·.insert β v)) α =
      (tapePresample σ α).map (·.update_tapes (·.insert β v)) :=
  ProbLang.tapePresample_update_tapes_ne_comm hne

/-- Lintegral over `tapePresample σ α` unfolds to a lintegral over
`tapeIndexUniform N` against the presampled-state integrand. Combines the
unfolding of `tapePresample` with `lintegral_bind` + `lintegral_dirac'` so
omit [ProbLangℝ rT] in
call sites don't re-do the same 3-line scaffold. -/
theorem tapePresample_lintegral
    {σ : (State rT)} {α : Loc} {N : Int}
    {bs : List { z : Int // 0 ≤ z ∧ z < N }}
    (h : σ.tapes[α]? = some ⟨N, bs⟩) (f : (State rT) → ENNReal)
    (hf : Measurable f) :
    ∫⁻ σ', f σ' ∂tapePresample σ α
      = ∫⁻ n, f (σ.update_tapes (·.insert α ⟨N, bs ++ [n]⟩)) ∂tapeIndexUniform N := by
  simp only [tapePresample, h]
  have hker : AEMeasurable (fun n : {z : Int // 0 ≤ z ∧ z < N} =>
      (Measure.dirac (σ.update_tapes (·.insert α ⟨N, bs ++ [n]⟩)) : Measure (State rT)))
      (tapeIndexUniform N) :=
    (measurable_dirac.comp Measurable.of_discrete).aemeasurable
  rw [lintegral_bind hker hf.aemeasurable]
  simp_rw [lintegral_dirac]

@[discrete]
theorem Discrete.tapePresample_lintegral [Countable rT] [MeasurableSingletonClass rT]
    {σ : (State rT)} {α : Loc} {N : Int}
    {bs : List { z : Int // 0 ≤ z ∧ z < N }}
    (h : σ.tapes[α]? = some ⟨N, bs⟩) (f : (State rT) → ENNReal) :
    ∫⁻ σ', f σ' ∂tapePresample σ α
      = ∫⁻ n, f (σ.update_tapes (·.insert α ⟨N, bs ++ [n]⟩)) ∂tapeIndexUniform N :=
  ProbLang.tapePresample_lintegral h f Measurable.of_discrete

/-- Lintegral form of `tapePresample_update_heap_comm`: integrating a
state-dependent integrand `f` against `tapePresample σ α` after a heap
update is the same as integrating `f` against `tapePresample` on the
updated state. Combines `lintegral_map` with `tapePresample_update_heap_comm`
so call sites skip the intermediate `.map` form. -/
theorem tapePresample_lintegral_update_heap
    {σ : (State rT)} {α : Loc}
    (g : Std.ExtTreeMap Loc (Val rT) compare → Std.ExtTreeMap Loc (Val rT) compare)
    (hg : Measurable g)
    (f : (State rT) → ENNReal) (hf : Measurable f) :
    ∫⁻ σ', f (σ'.update_heap g) ∂tapePresample σ α
      = ∫⁻ τ, f τ ∂tapePresample (σ.update_heap g) α := by
  have hmap : Measurable (fun σ' : State rT => σ'.update_heap g) :=
    State.measurable_iff.mpr ⟨hg.comp State.measurable_heap, State.measurable_tapes⟩
  rw [tapePresample_update_heap_comm g hg,
      lintegral_map hf hmap]

@[discrete]
theorem Discrete.tapePresample_lintegral_update_heap [Countable rT] [MeasurableSingletonClass rT]
    {σ : (State rT)} {α : Loc}
    (g : Std.ExtTreeMap Loc (Val rT) compare → Std.ExtTreeMap Loc (Val rT) compare)
    (f : (State rT) → ENNReal) :
    ∫⁻ σ', f (σ'.update_heap g) ∂tapePresample σ α
      = ∫⁻ τ, f τ ∂tapePresample (σ.update_heap g) α :=
  ProbLang.tapePresample_lintegral_update_heap g Measurable.of_discrete f Measurable.of_discrete

/-- Lintegral form of `tapePresample_update_tapes_ne_comm`. -/
theorem tapePresample_lintegral_update_tapes_ne
    {σ : (State rT)} {α β : Loc} {v : Tape} (hne : β ≠ α)
    (f : (State rT) → ENNReal) (hf : Measurable f) :
    ∫⁻ σ', f (σ'.update_tapes (·.insert β v)) ∂tapePresample σ α
      = ∫⁻ τ, f τ ∂tapePresample (σ.update_tapes (·.insert β v)) α := by
  have hins : Measurable (fun m : LocHeap Tape => m.insert β v) :=
    (Measurable.locHeap_insert β).comp (measurable_id.prodMk measurable_const)
  have hmap : Measurable (fun σ' : State rT => σ'.update_tapes (·.insert β v)) :=
    State.measurable_iff.mpr ⟨State.measurable_heap, hins.comp State.measurable_tapes⟩
  rw [tapePresample_update_tapes_ne_comm hne,
      lintegral_map hf hmap]

@[discrete]
theorem Discrete.tapePresample_lintegral_update_tapes_ne [Countable rT] [MeasurableSingletonClass rT]
    {σ : (State rT)} {α β : Loc} {v : Tape} (hne : β ≠ α)
    (f : (State rT) → ENNReal) :
    ∫⁻ σ', f (σ'.update_tapes (·.insert β v)) ∂tapePresample σ α
      = ∫⁻ τ, f τ ∂tapePresample (σ.update_tapes (·.insert β v)) α :=
  ProbLang.tapePresample_lintegral_update_tapes_ne hne f Measurable.of_discrete

/-- `Cfg.uniform` as a bind over a PMF measure, with explicit state fiber. -/
theorem Cfg.uniform_eq_bind {z : Int} {σ : (State rT)} (hz : 0 < z) :
    Cfg.uniform z σ =
      ((PMF.uniformOfFinset (Finset.Ico 0 z)
            (Finset.nonempty_Ico.mpr hz)).toMeasure).bind
        (fun n => Measure.dirac (⟨.lit (.int n), σ⟩ : (Cfg rT))) := by
  unfold Cfg.uniform Int.isPos
  rw [dif_pos hz]
  rw [Measure.bind_dirac_eq_map _ Measurable.of_discrete]

/-- **Commutation helper for `rand.plain` and `rand.tape.*`**.

Presampling onto tape `α` commutes with `Cfg.uniform z σ` in the sense
that pulling `tapePresample` outside the `Cfg.uniform` bind (on the RHS
as a per-post-state presample) gives back the original `tapePresample`-
then-`Cfg.uniform` composition. This is the only non-trivial headStep
case where the head-step result is a `Cfg.uniform` measure. -/
theorem tapePresample_bind_cfgUniform_comm
    {σ : (State rT)} {α : Loc} (z : Int) :
    (tapePresample σ α).bind (fun σ' => Cfg.uniform z σ') =
      (Cfg.uniform z σ).bind (fun ρ' =>
        (tapePresample ρ'.state α).bind
          (fun σ'' => Measure.dirac (⟨ρ'.expr, σ''⟩ : (Cfg rT)))) := by
  -- Kernel measurability of `ρ' ↦ (tapePresample ρ'.state α).bind (dirac ∘ ⟨ρ'.expr, ·⟩)`.
  have hg2 : Measurable (fun p : (Cfg rT) × (State rT) => (⟨p.1.expr, p.2⟩ : (Cfg rT))) := by
    refine Cfg.measurable_mk.comp (Measurable.prodMk ?_ ?_)
    · exact Cfg.measurable_expr.comp measurable_fst
    · exact measurable_snd
  have hk2 : Measurable (fun ρ' : (Cfg rT) =>
      (tapePresample ρ'.state α).bind
        (fun σ'' => Measure.dirac (⟨ρ'.expr, σ''⟩ : (Cfg rT)))) :=
    tapePresample_bind_dirac_measurable (g := fun ρ' σ'' => ⟨ρ'.expr, σ''⟩) hg2
  by_cases hz : 0 < z
  · -- Both sides reduce to a double bind over (tapePresample σ α) and
    -- the uniform int PMF; they agree by Fubini / bind-swap.
    -- Rewrite Cfg.uniform using the bind form.
    have huniform_σ := Cfg.uniform_eq_bind (σ := σ) hz
    -- Kernel measurability of `σ' ↦ (PMF).bind (dirac ∘ ⟨lit n, ·⟩) = Cfg.uniform z σ'`.
    have hk_pmf : Measurable (fun σ' : (State rT) =>
        ((PMF.uniformOfFinset (Finset.Ico 0 z)
              (Finset.nonempty_Ico.mpr hz)).toMeasure).bind
            (fun n => Measure.dirac (⟨.lit (.int n), σ'⟩ : (Cfg rT)))) := by
      have hre : (fun σ' : (State rT) =>
          ((PMF.uniformOfFinset (Finset.Ico 0 z)
                (Finset.nonempty_Ico.mpr hz)).toMeasure).bind
              (fun n => Measure.dirac (⟨.lit (.int n), σ'⟩ : (Cfg rT))))
          = (fun σ' : (State rT) => Cfg.uniform z σ') := by
        funext σ'; exact (Cfg.uniform_eq_bind (σ := σ') hz).symm
      rw [hre]
      exact Cfg.uniform.measurable.comp (measurable_const.prodMk measurable_id)
    -- LHS: push Cfg.uniform to the bind form at each σ'.
    have hLHS : (tapePresample σ α).bind (fun σ' => Cfg.uniform z σ') =
        (tapePresample σ α).bind (fun σ' =>
          ((PMF.uniformOfFinset (Finset.Ico 0 z)
                (Finset.nonempty_Ico.mpr hz)).toMeasure).bind
              (fun n => Measure.dirac (⟨.lit (.int n), σ'⟩ : (Cfg rT)))) := by
      congr 1; funext σ'; exact Cfg.uniform_eq_bind (σ := σ') hz
    rw [hLHS, huniform_σ]
    -- RHS: apply bind_bind and dirac_bind to collapse.
    rw [Measure.bind_bind
          Measurable.of_discrete.aemeasurable
          hk2.aemeasurable]
    simp_rw [Measure.dirac_bind
              (f := fun ρ' : (Cfg rT) => (tapePresample ρ'.state α).bind
                (fun σ'' => Measure.dirac (⟨ρ'.expr, σ''⟩ : (Cfg rT))))
              hk2]
    -- Now both sides are:
    -- LHS: (tapePresample σ α).bind (fun σ' => PMF.bind (fun n => dirac ⟨lit (int n), σ'⟩))
    -- RHS: PMF.bind (fun n => (tapePresample σ α).bind (fun σ'' => dirac ⟨lit (int n), σ''⟩))
    -- Swap via lintegral_lintegral_swap.
    refine Measure.ext fun S hS => ?_
    rw [Measure.bind_apply hS hk_pmf.aemeasurable,
        Measure.bind_apply hS Measurable.of_discrete.aemeasurable]
    -- Rewrite each inner bind via lintegral_bind.
    have hLlint : ∀ σ' : (State rT),
        ((((PMF.uniformOfFinset (Finset.Ico 0 z)
              (Finset.nonempty_Ico.mpr hz)).toMeasure).bind
                (fun n => Measure.dirac (⟨.lit (.int n), σ'⟩ : (Cfg rT)))) S) =
        ∫⁻ n, (Measure.dirac (⟨.lit (.int n), σ'⟩ : (Cfg rT))) S
          ∂((PMF.uniformOfFinset (Finset.Ico 0 z)
              (Finset.nonempty_Ico.mpr hz)).toMeasure) := by
      intro σ'
      exact Measure.bind_apply hS Measurable.of_discrete.aemeasurable
    have hRlint : ∀ n : Int,
        ((tapePresample σ α).bind
            (fun σ'' => Measure.dirac (⟨.lit (.int n), σ''⟩ : (Cfg rT)))) S =
        ∫⁻ σ'', (Measure.dirac (⟨.lit (.int n), σ''⟩ : (Cfg rT))) S
          ∂(tapePresample σ α) := by
      intro n
      exact Measure.bind_apply hS
        (Cfg.measurable_dirac_mk (fe := fun _ => .lit (.int n)) measurable_const
          measurable_id).aemeasurable
    simp_rw [hLlint, hRlint]
    -- Apply lintegral_lintegral_swap: outer is tapePresample σ α (finite, hence
    -- SFinite), inner is the PMF measure.
    haveI : IsFiniteMeasure (tapePresample σ α) :=
      ⟨lt_of_le_of_lt tapePresample_univ_le_one ENNReal.one_lt_top⟩
    have hcfgbuild : Measurable (fun p : (State rT) × Int =>
        (⟨.lit (.int p.2), p.1⟩ : (Cfg rT))) :=
      Cfg.measurable_iff.mpr
        ⟨Exp.lit.measurable.comp (BaseLit.int.measurable.comp measurable_snd), measurable_fst⟩
    have hswapmeas : Measurable (Function.uncurry (fun (σ' : (State rT)) (n : Int) =>
        (Measure.dirac (⟨.lit (.int n), σ'⟩ : (Cfg rT))) S)) := by
      show Measurable (fun p : (State rT) × Int =>
        (Measure.dirac (⟨.lit (.int p.2), p.1⟩ : (Cfg rT))) S)
      exact ((Measure.measurable_coe hS).comp measurable_dirac).comp hcfgbuild
    exact lintegral_lintegral_swap
      (μ := tapePresample σ α)
      (ν := ((PMF.uniformOfFinset (Finset.Ico 0 z)
              (Finset.nonempty_Ico.mpr hz)).toMeasure))
      (f := fun σ' n => (Measure.dirac (⟨.lit (.int n), σ'⟩ : (Cfg rT))) S)
      hswapmeas.aemeasurable
  · -- Both sides: Cfg.uniform z σ' = dirac ⟨lit -1, σ'⟩ for nonpos z.
    have hCfg' : ∀ σ' : (State rT),
        Cfg.uniform z σ' = Measure.dirac (⟨.lit (.int (-1)), σ'⟩ : (Cfg rT)) :=
      fun σ' => Cfg.uniform_nonpos_eq hz
    simp_rw [hCfg']
    rw [Measure.dirac_bind
          (f := fun ρ' : (Cfg rT) => (tapePresample ρ'.state α).bind
            (fun σ'' => Measure.dirac (⟨ρ'.expr, σ''⟩ : (Cfg rT))))
          hk2]

@[discrete]
theorem Discrete.tapePresample_bind_cfgUniform_comm [Countable rT] [MeasurableSingletonClass rT]
    {σ : (State rT)} {α : Loc} (z : Int) :
    (tapePresample σ α).bind (fun σ' => Cfg.uniform z σ') =
      (Cfg.uniform z σ).bind (fun ρ' =>
        (tapePresample ρ'.state α).bind
          (fun σ'' => Measure.dirac (⟨ρ'.expr, σ''⟩ : (Cfg rT)))) :=
  ProbLang.tapePresample_bind_cfgUniform_comm z

/-! ## Core: presampling is invisible to `execN` at the expression level

The honest statement — the one we can actually prove in our port — is that
*after projecting to the expression component*, presampling is invisible.
The strict full-`(Cfg rT)` version is false: `tapePresample` genuinely changes
the final tape content, so configurations ending in the same expression
but different states distinguish the two measures. But the expression
component is all the adequacy layer observes, so the projected equation
is exactly the right downstream notion.

This is Clutch's `prim_coupl_upd_tapes_dom` almost verbatim: Clutch states
it as an `Rcoupl` under `eq` on the `dmap (λ x, x.1)` projection, which is
the same thing. -/

omit [ProbLangℝ rT] in
/-- Inserting the same tape value at an existing key is the identity on `(State rT)`. -/
theorem State.update_tapes_insert_id {σ : (State rT)} {α : Loc} {t : Tape}
    (h : σ.tapes[α]? = some t) :
    σ.update_tapes (·.insert α t) = σ :=
  State.update_tapes_no_change h

/-- Mapping `tapeIndexUniform N` through the (Cfg rT) embedding `a ↦ ⟨lit (int ↑a), σ⟩`
gives `Cfg.uniform N σ`. Both are the uniform distribution on
omit [ProbLangℝ rT] in
`{⟨lit (int n), σ⟩ | n ∈ [0, N)}`. -/
theorem tapeIndexUniform_lintegral_eq_cfg_uniform
    {N : Int} (hN : 0 < N) (σ : (State rT))
    (f : (Cfg rT) → ENNReal) (hf : Measurable f) :
    ∫⁻ (a : { z : Int // 0 ≤ z ∧ z < N }),
        f ⟨.lit (.int ↑a), σ⟩ ∂tapeIndexUniform N
      = ∫⁻ (ρ : (Cfg rT)), f ρ ∂Cfg.uniform N σ := by
  -- Unfold both definitions to PMF.uniformOfFinset level
  unfold tapeIndexUniform Cfg.uniform Int.isPos
  have hNonempty : (Finset.Ico 0 N).Nonempty := ⟨0, Finset.mem_Ico.mpr ⟨le_refl _, hN⟩⟩
  rw [dif_pos hNonempty, dif_pos hN]
  simp only
  -- Now both sides are lintegrals over `Measure.map` of the same PMF.toMeasure
  -- LHS: ∫⁻ a, f ⟨lit (int ↑a), σ⟩ ∂(pmf.toMeasure.map (subtypeEmbed))
  -- RHS: ∫⁻ ρ, f ρ ∂(pmf.toMeasure.map (cfgEmbed))
  -- Use lintegral_map on both sides to push through the map
  have hm_sub : Measurable (fun z : Int => if hz : 0 ≤ z ∧ z < N then (⟨z, hz⟩ : {z // 0 ≤ z ∧ z < N}) else ⟨0, ⟨le_refl _, by omega⟩⟩) := Measurable.of_discrete
  have hm_cfg : Measurable (fun x : Int => (⟨Exp.lit (BaseLit.int x), σ⟩ : (Cfg rT))) := Measurable.of_discrete
  -- Both sides are lintegrals over Measure.map of the same PMF.toMeasure.
  -- Strategy: rewrite both to lintegrals over the base PMF.toMeasure on ℤ using lintegral_map,
  -- then show the integrands agree on the PMF support.
  have hm_f_sub : Measurable (fun (a : {z // 0 ≤ z ∧ z < N}) => f ⟨.lit (.int ↑a), σ⟩) :=
    Measurable.of_discrete
  have hm_f_cfg : Measurable f := hf
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

@[discrete]
theorem Discrete.tapeIndexUniform_lintegral_eq_cfg_uniform [Countable rT] [MeasurableSingletonClass rT]
    {N : Int} (hN : 0 < N) (σ : (State rT))
    (f : (Cfg rT) → ENNReal) :
    ∫⁻ (a : { z : Int // 0 ≤ z ∧ z < N }),
        f ⟨.lit (.int ↑a), σ⟩ ∂tapeIndexUniform N
      = ∫⁻ (ρ : (Cfg rT)), f ρ ∂Cfg.uniform N σ :=
  ProbLang.tapeIndexUniform_lintegral_eq_cfg_uniform hN σ f Measurable.of_discrete

/-! ## Case-closing helpers for the main erasure induction

Two reusable helpers factored out of `execN_tape_presample_expr_eq`. Each
closes one flavor of head-step case (state-preserving dirac, resp.
`Cfg.uniform`) given a pointwise IH specialized through `K.fillCfg`
(`ih_fill`). Keeping them top-level means the main induction can dispatch
cases by `exact`/`refine` rather than redefining the helpers inside every
attempt at the proof, and any future changes to the case-closing shape are
localized here. -/

/-- Integrand measurability for the erasure case-closers: for measurable
`S`, the map `ρ ↦ (execN m (K.fillCfg ρ)) ((·.expr)⁻¹' S)` is measurable.
Countability-free (uses `execN_measurable`, `Ectx.fillCfg.measurable`,
`Cfg.measurable_expr`). -/
theorem erasure_integrand_measurable {m : Nat} {K : (Ectx rT)} {S : Set (Exp rT)}
    (hS : MeasurableSet S) :
    Measurable (fun ρ : (Cfg rT) =>
      ((execN m ∘ K.fillCfg) ρ) ((fun x => x.expr) ⁻¹' S)) :=
  ((Measure.measurable_coe (Cfg.measurable_expr hS)).comp
    (execN_measurable m)).comp (Ectx.fillCfg.measurable K)

/-- Helper for state-preserving dirac head-step cases: if
`headStep ⟨e_h, σ'⟩ = dirac ⟨e', σ'⟩` for all `σ'`, the goal reduces to a
single `ih_fill` application. -/
theorem erasure_det_close
    {m : Nat} {K : (Ectx rT)} {S : Set (Exp rT)} {σ : (State rT)} {α : Loc} {t : Tape}
    (h : σ.tapes[α]? = some t) (hN : 0 < t.bound)
    (ih_fill : ∀ (e' : (Exp rT)) (σ' : (State rT)) (t' : Tape),
      σ'.tapes[α]? = some t' → 0 < t'.bound →
      ∫⁻ σ'', ((execN m ∘ K.fillCfg) ⟨e', σ''⟩) ((fun x => x.expr) ⁻¹' S)
          ∂tapePresample σ' α
        = ((execN m ∘ K.fillCfg) ⟨e', σ'⟩) ((fun x => x.expr) ⁻¹' S))
    (e_h e' : (Exp rT))
    (hs : ∀ σ' : (State rT), headStep (⟨e_h, σ'⟩ : (Cfg rT)) = Measure.dirac ⟨e', σ'⟩) :
    ∫⁻ σ', ∫⁻ ρ, ((execN m ∘ K.fillCfg) ρ) ((fun x => x.expr) ⁻¹' S)
              ∂headStep ⟨e_h, σ'⟩ ∂tapePresample σ α
      = ∫⁻ ρ, ((execN m ∘ K.fillCfg) ρ) ((fun x => x.expr) ⁻¹' S)
          ∂headStep ⟨e_h, σ⟩ := by
  simp_rw [hs, lintegral_dirac]
  exact ih_fill _ σ t h hN

/-- Helper for state-preserving dirac head-step cases that hold ONLY a.e.
on `tapePresample σ α` (rather than for all `σ'`). Used by the new
nonpos-rand cases where headStep depends on tape state, which presample
preserves only on the support. -/
theorem erasure_det_close_ae
    {m : Nat} {K : (Ectx rT)} {S : Set (Exp rT)} {σ : (State rT)} {α : Loc} {t : Tape}
    (h : σ.tapes[α]? = some t) (hN : 0 < t.bound)
    (ih_fill : ∀ (e' : (Exp rT)) (σ' : (State rT)) (t' : Tape),
      σ'.tapes[α]? = some t' → 0 < t'.bound →
      ∫⁻ σ'', ((execN m ∘ K.fillCfg) ⟨e', σ''⟩) ((fun x => x.expr) ⁻¹' S)
          ∂tapePresample σ' α
        = ((execN m ∘ K.fillCfg) ⟨e', σ'⟩) ((fun x => x.expr) ⁻¹' S))
    (e_h e' : (Exp rT))
    (hs_ae : ∀ᵐ σ' ∂(tapePresample σ α),
        headStep (⟨e_h, σ'⟩ : (Cfg rT)) = Measure.dirac ⟨e', σ'⟩)
    (hs_σ : headStep (⟨e_h, σ⟩ : (Cfg rT)) = Measure.dirac ⟨e', σ⟩) :
    ∫⁻ σ', ∫⁻ ρ, ((execN m ∘ K.fillCfg) ρ) ((fun x => x.expr) ⁻¹' S)
              ∂headStep ⟨e_h, σ'⟩ ∂tapePresample σ α
      = ∫⁻ ρ, ((execN m ∘ K.fillCfg) ρ) ((fun x => x.expr) ⁻¹' S)
          ∂headStep ⟨e_h, σ⟩ := by
  haveI : IsProbabilityMeasure (tapePresample σ α) :=
    ⟨tapePresample_univ_eq_one h hN⟩
  rw [hs_σ, lintegral_dirac]
  calc ∫⁻ σ', ∫⁻ ρ, ((execN m ∘ K.fillCfg) ρ) ((fun x => x.expr) ⁻¹' S)
                ∂headStep ⟨e_h, σ'⟩ ∂tapePresample σ α
      = ∫⁻ σ', ((execN m ∘ K.fillCfg) ⟨e', σ'⟩) ((fun x => x.expr) ⁻¹' S)
          ∂tapePresample σ α := by
        refine lintegral_congr_ae ?_
        filter_upwards [hs_ae] with σ' hs
        rw [hs, lintegral_dirac]
    _ = ((execN m ∘ K.fillCfg) ⟨e', σ⟩) ((fun x => x.expr) ⁻¹' S) :=
          ih_fill _ σ t h hN

/-- Helper for `Cfg.uniform` head-step cases. Given that
`headStep ⟨e_h, σ'⟩ = Cfg.uniform z_r σ'` a.e. on `tapePresample σ α` and at
`σ` itself, the goal collapses via Fubini + `ih_fill` at each sampled
omit [MeasurableSingletonClass rT] in
index. -/
theorem erasure_uniform_close
    {m : Nat} {K : (Ectx rT)} {S : Set (Exp rT)} {σ : (State rT)} {α : Loc} {t : Tape}
    (hS : MeasurableSet S)
    (h : σ.tapes[α]? = some t) (hN : 0 < t.bound)
    (ih_fill : ∀ (e' : (Exp rT)) (σ' : (State rT)) (t' : Tape),
      σ'.tapes[α]? = some t' → 0 < t'.bound →
      ∫⁻ σ'', ((execN m ∘ K.fillCfg) ⟨e', σ''⟩) ((fun x => x.expr) ⁻¹' S)
          ∂tapePresample σ' α
        = ((execN m ∘ K.fillCfg) ⟨e', σ'⟩) ((fun x => x.expr) ⁻¹' S))
    (e_h : (Exp rT)) (z_r : Int) (hz : 0 < z_r)
    (hstep_ae : ∀ᵐ σ' ∂(tapePresample σ α),
        headStep (⟨e_h, σ'⟩ : (Cfg rT)) = Cfg.uniform z_r σ')
    (hstep_σ : headStep (⟨e_h, σ⟩ : (Cfg rT)) = Cfg.uniform z_r σ) :
    ∫⁻ σ', ∫⁻ ρ, ((execN m ∘ K.fillCfg) ρ) ((fun x => x.expr) ⁻¹' S)
              ∂headStep ⟨e_h, σ'⟩ ∂tapePresample σ α
      = ∫⁻ ρ, ((execN m ∘ K.fillCfg) ρ) ((fun x => x.expr) ⁻¹' S)
          ∂headStep ⟨e_h, σ⟩ := by
  haveI : IsProbabilityMeasure (tapePresample σ α) :=
    ⟨tapePresample_univ_eq_one h hN⟩
  have hNonempty : (Finset.Ico (0 : Int) z_r).Nonempty := Finset.nonempty_Ico.mpr hz
  set pmf := PMF.uniformOfFinset (Finset.Ico (0 : Int) z_r) hNonempty
  have hunif : ∀ σ₀ : (State rT), Cfg.uniform z_r σ₀ =
      pmf.toMeasure.map (fun n : Int => (⟨.lit (.int n), σ₀⟩ : (Cfg rT))) := fun σ₀ => by
    unfold Cfg.uniform Int.isPos; rw [dif_pos hz]
  calc ∫⁻ σ', ∫⁻ ρ, ((execN m ∘ K.fillCfg) ρ) ((fun x => x.expr) ⁻¹' S)
                ∂headStep ⟨e_h, σ'⟩ ∂tapePresample σ α
      = ∫⁻ σ', ∫⁻ ρ, ((execN m ∘ K.fillCfg) ρ) ((fun x => x.expr) ⁻¹' S)
                ∂Cfg.uniform z_r σ' ∂tapePresample σ α := by
        refine lintegral_congr_ae ?_
        filter_upwards [hstep_ae] with σ' hs; rw [hs]
    _ = ∫⁻ ρ, ((execN m ∘ K.fillCfg) ρ) ((fun x => x.expr) ⁻¹' S)
          ∂Cfg.uniform z_r σ := by
        have hcfgbuild : Measurable (fun p : (State rT) × Int =>
            (⟨.lit (.int p.2), p.1⟩ : (Cfg rT))) := by
          refine Cfg.measurable_mk.comp (Measurable.prodMk ?_ measurable_fst)
          exact Exp.lit.measurable.comp (BaseLit.int.measurable.comp measurable_snd)
        simp_rw [hunif,
          lintegral_map (erasure_integrand_measurable hS) Measurable.of_discrete]
        rw [lintegral_lintegral_swap (f := fun σ' n =>
              ((execN m ∘ K.fillCfg) ⟨.lit (.int n), σ'⟩) ((fun x => x.expr) ⁻¹' S))
            ((erasure_integrand_measurable hS).comp hcfgbuild).aemeasurable]
        congr 1; funext n; exact ih_fill _ σ t h hN
    _ = ∫⁻ ρ, ((execN m ∘ K.fillCfg) ρ) ((fun x => x.expr) ⁻¹' S)
          ∂headStep ⟨e_h, σ⟩ := by rw [hstep_σ]

/-- Continuous analogue of `erasure_uniform_close`: the `urand` head step pushes
`unifUnit` forward onto real-literal configs at the unchanged state. Tape
presampling commutes because `urand` ignores tapes. Same Tonelli-swap proof as
the discrete case, with `unifUnit` (a probability ⇒ s-finite measure) in place of
the finite PMF and genuine measurability of `r ↦ ⟨.lit (.real r), σ⟩`. -/
theorem erasure_uniformReal_close
    {m : Nat} {K : (Ectx rT)} {S : Set (Exp rT)} {σ : (State rT)} {α : Loc} {t : Tape}
    (hS : MeasurableSet S)
    (h : σ.tapes[α]? = some t) (hN : 0 < t.bound)
    (ih_fill : ∀ (e' : (Exp rT)) (σ' : (State rT)) (t' : Tape),
      σ'.tapes[α]? = some t' → 0 < t'.bound →
      ∫⁻ σ'', ((execN m ∘ K.fillCfg) ⟨e', σ''⟩) ((fun x => x.expr) ⁻¹' S)
          ∂tapePresample σ' α
        = ((execN m ∘ K.fillCfg) ⟨e', σ'⟩) ((fun x => x.expr) ⁻¹' S))
    (e_h : (Exp rT))
    (hstep_ae : ∀ᵐ σ' ∂(tapePresample σ α),
        headStep (⟨e_h, σ'⟩ : (Cfg rT)) = Cfg.uniformReal σ')
    (hstep_σ : headStep (⟨e_h, σ⟩ : (Cfg rT)) = Cfg.uniformReal σ) :
    ∫⁻ σ', ∫⁻ ρ, ((execN m ∘ K.fillCfg) ρ) ((fun x => x.expr) ⁻¹' S)
              ∂headStep ⟨e_h, σ'⟩ ∂tapePresample σ α
      = ∫⁻ ρ, ((execN m ∘ K.fillCfg) ρ) ((fun x => x.expr) ⁻¹' S)
          ∂headStep ⟨e_h, σ⟩ := by
  haveI : IsProbabilityMeasure (tapePresample σ α) :=
    ⟨tapePresample_univ_eq_one h hN⟩
  have hunif : ∀ σ₀ : (State rT), Cfg.uniformReal σ₀ =
      (ProbLangℝ.unifUnit (T := rT)).map (fun r : rT => (⟨.lit (.real r), σ₀⟩ : (Cfg rT))) :=
    fun _ => rfl
  calc ∫⁻ σ', ∫⁻ ρ, ((execN m ∘ K.fillCfg) ρ) ((fun x => x.expr) ⁻¹' S)
                ∂headStep ⟨e_h, σ'⟩ ∂tapePresample σ α
      = ∫⁻ σ', ∫⁻ ρ, ((execN m ∘ K.fillCfg) ρ) ((fun x => x.expr) ⁻¹' S)
                ∂Cfg.uniformReal σ' ∂tapePresample σ α := by
        refine lintegral_congr_ae ?_
        filter_upwards [hstep_ae] with σ' hs; rw [hs]
    _ = ∫⁻ ρ, ((execN m ∘ K.fillCfg) ρ) ((fun x => x.expr) ⁻¹' S)
          ∂Cfg.uniformReal σ := by
        have hcfgbuild : Measurable (fun p : (State rT) × rT =>
            (⟨.lit (.real p.2), p.1⟩ : (Cfg rT))) := by
          refine Cfg.measurable_mk.comp (Measurable.prodMk ?_ measurable_fst)
          exact Exp.lit.measurable.comp (BaseLit.real.measurable.comp measurable_snd)
        have hmap : ∀ σ₀ : State rT, Measurable (fun r : rT => (⟨.lit (.real r), σ₀⟩ : (Cfg rT))) :=
          fun σ₀ => Cfg.measurable_iff.mpr
            ⟨Exp.lit.measurable.comp BaseLit.real.measurable, measurable_const⟩
        simp_rw [hunif,
          lintegral_map (erasure_integrand_measurable hS) (hmap _)]
        rw [lintegral_lintegral_swap (f := fun σ' r =>
              ((execN m ∘ K.fillCfg) ⟨.lit (.real r), σ'⟩) ((fun x => x.expr) ⁻¹' S))
            ((erasure_integrand_measurable hS).comp hcfgbuild).aemeasurable]
        congr 1; funext r; exact ih_fill _ σ t h hN
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
abbrev ErasureIHFill (m : Nat) (K : (Ectx rT)) (S : Set (Exp rT)) (α : Loc) : Prop :=
  ∀ (e' : (Exp rT)) (σ' : (State rT)) (t' : Tape),
    σ'.tapes[α]? = some t' → 0 < t'.bound →
    ∫⁻ σ'', ((execN m ∘ K.fillCfg) ⟨e', σ''⟩) ((fun x => x.expr) ⁻¹' S)
        ∂tapePresample σ' α
      = ((execN m ∘ K.fillCfg) ⟨e', σ'⟩) ((fun x => x.expr) ⁻¹' S)

/-- `load ℓ` case. `headStep` only depends on `σ'.heap`, which
`tapePresample` preserves a.e., so both sides reduce to a single
`ih_fill` at the looked-up value. -/
theorem erasure_load_close
    {m : Nat} {K : (Ectx rT)} {S : Set (Exp rT)} {σ : (State rT)} {α ℓ : Loc} {t : Tape} {v : (Val rT)}
    (h : σ.tapes[α]? = some t) (hN : 0 < t.bound)
    (ih_fill : ErasureIHFill m K S α)
    (hlookup : σ.heap[ℓ]? = some v) :
    ∫⁻ σ', ∫⁻ ρ, ((execN m ∘ K.fillCfg) ρ) ((fun x => x.expr) ⁻¹' S)
              ∂headStep ⟨.load (.lit (.loc ℓ)), σ'⟩ ∂tapePresample σ α
      = ∫⁻ ρ, ((execN m ∘ K.fillCfg) ρ) ((fun x => x.expr) ⁻¹' S)
          ∂headStep ⟨.load (.lit (.loc ℓ)), σ⟩ := by
  have hload : ∀ (σ₀ : (State rT)), σ₀.heap = σ.heap →
      headStep (⟨.load (.lit (.loc ℓ)), σ₀⟩ : (Cfg rT)) = Measure.dirac ⟨.ofVal v, σ₀⟩ := by
    intro σ₀ hh
    change (match σ₀.heap[ℓ]? with
              | none => (0 : Measure (Cfg rT)) | some v => Measure.dirac ⟨.ofVal v, σ₀⟩) = _
    rw [hh, hlookup]
  calc ∫⁻ σ', ∫⁻ ρ, ((execN m ∘ K.fillCfg) ρ) ((fun x => x.expr) ⁻¹' S)
                ∂headStep ⟨.load (.lit (.loc ℓ)), σ'⟩ ∂tapePresample σ α
      = ∫⁻ σ', ((execN m ∘ K.fillCfg) ⟨.ofVal v, σ'⟩)
                ((fun x => x.expr) ⁻¹' S) ∂tapePresample σ α := by
        refine lintegral_congr_ae ?_
        filter_upwards [tapePresample_heap_eq (σ := σ) (α := α)] with σ' hheap
        rw [hload σ' hheap, lintegral_dirac]
    _ = ((execN m ∘ K.fillCfg) ⟨.ofVal v, σ⟩) ((fun x => x.expr) ⁻¹' S) :=
        ih_fill _ σ t h hN
    _ = ∫⁻ ρ, ((execN m ∘ K.fillCfg) ρ) ((fun x => x.expr) ⁻¹' S)
          ∂headStep ⟨.load (.lit (.loc ℓ)), σ⟩ := by
        rw [hload σ rfl, lintegral_dirac]

/-- `alloc ed` case. Heap-preservation under `tapePresample` gives
`σ'.heap.fresh = σ.heap.fresh`, and then `tapePresample_update_heap_comm`
pushes the fresh-cell insert through the presample. -/
theorem erasure_alloc_close
    {m : Nat} {K : (Ectx rT)} {S : Set (Exp rT)} {σ : (State rT)} {α : Loc} {t : Tape} {ed : (Exp rT)}
    (hS : MeasurableSet S)
    (h : σ.tapes[α]? = some t) (hN : 0 < t.bound)
    (ih_fill : ErasureIHFill m K S α) :
    ∫⁻ σ', ∫⁻ ρ, ((execN m ∘ K.fillCfg) ρ) ((fun x => x.expr) ⁻¹' S)
              ∂headStep ⟨.alloc ed, σ'⟩ ∂tapePresample σ α
      = ∫⁻ ρ, ((execN m ∘ K.fillCfg) ρ) ((fun x => x.expr) ⁻¹' S)
          ∂headStep ⟨.alloc ed, σ⟩ := by
  have halloc : ∀ (σ₀ : (State rT)), σ₀.heap = σ.heap →
      headStep (⟨.alloc ed, σ₀⟩ : (Cfg rT)) =
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
          simp_rw [lintegral_dirac]
          set f_heap : Std.ExtTreeMap Loc (Val rT) compare → Std.ExtTreeMap Loc (Val rT) compare :=
            (fun hp => hp.insert σ.heap.fresh vd)
          have htape_upd : (σ.update_heap f_heap).tapes[α]? = some t := by
            simp [State.update_heap, h]
          have hg_fheap : Measurable f_heap :=
            (Measurable.locHeap_insert σ.heap.fresh).comp (measurable_id.prodMk measurable_const)
          have hf_int : Measurable (fun τ : (State rT) =>
              ((execN m ∘ K.fillCfg) ⟨.lit (.loc σ.heap.fresh), τ⟩)
                ((fun x => x.expr) ⁻¹' S)) :=
            (erasure_integrand_measurable hS).comp
              (Cfg.measurable_mk.comp (measurable_const.prodMk measurable_id))
          rw [tapePresample_lintegral_update_heap (g := f_heap) hg_fheap
                (fun τ => ((execN m ∘ K.fillCfg) ⟨.lit (.loc σ.heap.fresh), τ⟩)
                  ((fun x => x.expr) ⁻¹' S)) hf_int,
              ih_fill _ (σ.update_heap f_heap) t htape_upd hN,
              halloc σ rfl]
          simp [Exp.asValM, hcheck, lintegral_dirac, f_heap]

/-- `store ℓ ev` case. Dispatches on whether `ev` is a value and whether
the heap lookup succeeds; the live branch mirrors `erasure_alloc_close`. -/
theorem erasure_store_close
    {m : Nat} {K : (Ectx rT)} {S : Set (Exp rT)} {σ : (State rT)} {α ℓ : Loc} {t : Tape} {ev : (Exp rT)}
    (hS : MeasurableSet S)
    (h : σ.tapes[α]? = some t) (hN : 0 < t.bound)
    (ih_fill : ErasureIHFill m K S α) :
    ∫⁻ σ', ∫⁻ ρ, ((execN m ∘ K.fillCfg) ρ) ((fun x => x.expr) ⁻¹' S)
              ∂headStep ⟨.store (.lit (.loc ℓ)) ev, σ'⟩ ∂tapePresample σ α
      = ∫⁻ ρ, ((execN m ∘ K.fillCfg) ρ) ((fun x => x.expr) ⁻¹' S)
          ∂headStep ⟨.store (.lit (.loc ℓ)) ev, σ⟩ := by
  have hstore : ∀ (σ₀ : (State rT)), σ₀.heap = σ.heap →
      headStep (⟨.store (.lit (.loc ℓ)) ev, σ₀⟩ : (Cfg rT)) =
        ev.asValM fun v =>
          match σ.heap[ℓ]? with
          | none => (0 : Measure (Cfg rT))
          | some _ => Measure.dirac ⟨.lit .unit, σ₀.update_heap fun hp => hp.insert ℓ v⟩ := by
    intro σ₀ hh
    show Exp.asValM ev (fun v => match σ₀.heap[ℓ]? with | none => _ | some _ => _) = _
    rw [hh]
  -- Shared closer for the two "zero" branches (ev not a value; heap miss):
  -- `headStep = 0` at every heap-equivalent `σ₀`, so both sides vanish.
  have zero_branch : ∀ (_hz : ∀ (σ₀ : (State rT)), σ₀.heap = σ.heap →
      headStep (⟨.store (.lit (.loc ℓ)) ev, σ₀⟩ : (Cfg rT)) = 0),
      ∫⁻ σ', ∫⁻ ρ, ((execN m ∘ K.fillCfg) ρ) ((fun x => x.expr) ⁻¹' S)
              ∂headStep ⟨.store (.lit (.loc ℓ)) ev, σ'⟩ ∂tapePresample σ α
        = ∫⁻ ρ, ((execN m ∘ K.fillCfg) ρ) ((fun x => x.expr) ⁻¹' S)
            ∂headStep ⟨.store (.lit (.loc ℓ)) ev, σ⟩ := fun hz => by
    rw [hz σ rfl, lintegral_zero_measure]
    calc ∫⁻ σ', ∫⁻ ρ, ((execN m ∘ K.fillCfg) ρ) ((fun x => x.expr) ⁻¹' S)
                  ∂headStep ⟨.store (.lit (.loc ℓ)) ev, σ'⟩ ∂tapePresample σ α
        = ∫⁻ _, (0 : ENNReal) ∂tapePresample σ α := by
          refine lintegral_congr_ae ?_
          filter_upwards [tapePresample_heap_eq (σ := σ) (α := α)] with σ' hheap
          rw [hz σ' hheap]; exact lintegral_zero_measure _
      _ = 0 := lintegral_zero
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
      set f_heap : Std.ExtTreeMap Loc (Val rT) compare → Std.ExtTreeMap Loc (Val rT) compare :=
        (fun hp => hp.insert ℓ v)
      calc ∫⁻ σ', ∫⁻ ρ, ((execN m ∘ K.fillCfg) ρ) ((fun x => x.expr) ⁻¹' S)
                    ∂headStep ⟨.store (.lit (.loc ℓ)) ev, σ'⟩ ∂tapePresample σ α
          = ∫⁻ σ', ((execN m ∘ K.fillCfg) ⟨.lit .unit, σ'.update_heap f_heap⟩)
                      ((fun x => x.expr) ⁻¹' S) ∂tapePresample σ α := by
            refine lintegral_congr_ae ?_
            filter_upwards [tapePresample_heap_eq (σ := σ) (α := α)] with σ' hheap
            rw [hstore σ' hheap]
            simp only [Exp.asValM, hcheck, hlook, lintegral_dirac]
            simp only [f_heap]
        _ = ∫⁻ ρ, ((execN m ∘ K.fillCfg) ρ) ((fun x => x.expr) ⁻¹' S)
              ∂headStep ⟨.store (.lit (.loc ℓ)) ev, σ⟩ := by
            have htape_upd : (σ.update_heap f_heap).tapes[α]? = some t := by
              simp [State.update_heap, h]
            have hg_fheap : Measurable f_heap :=
              (Measurable.locHeap_insert ℓ).comp (measurable_id.prodMk measurable_const)
            have hf_int : Measurable (fun τ : (State rT) =>
                ((execN m ∘ K.fillCfg) ⟨.lit .unit, τ⟩) ((fun x => x.expr) ⁻¹' S)) :=
              (erasure_integrand_measurable hS).comp
                (Cfg.measurable_mk.comp (measurable_const.prodMk measurable_id))
            rw [tapePresample_lintegral_update_heap (g := f_heap) hg_fheap
                  (fun τ => ((execN m ∘ K.fillCfg) ⟨.lit .unit, τ⟩)
                    ((fun x => x.expr) ⁻¹' S)) hf_int,
                ih_fill _ (σ.update_heap f_heap) t htape_upd hN,
                hstore σ rfl]
            simp [Exp.asValM, hcheck, hlook, lintegral_dirac, f_heap]

/-- `tape z` case. Presample never touches a fresh location, so
`σ'.tapes.fresh = σ.tapes.fresh` a.e.; the fresh-tape insert then commutes
with `tapePresample` via `tapePresample_update_tapes_ne_comm`. -/
theorem erasure_tape_close
    {m : Nat} {K : (Ectx rT)} {S : Set (Exp rT)} {σ : (State rT)} {α : Loc} {t : Tape} {z : Int}
    (hS : MeasurableSet S)
    (h : σ.tapes[α]? = some t) (hN : 0 < t.bound)
    (ih_fill : ErasureIHFill m K S α) :
    ∫⁻ σ', ∫⁻ ρ, ((execN m ∘ K.fillCfg) ρ) ((fun x => x.expr) ⁻¹' S)
              ∂headStep ⟨.tape (.lit (.int z)), σ'⟩ ∂tapePresample σ α
      = ∫⁻ ρ, ((execN m ∘ K.fillCfg) ρ) ((fun x => x.expr) ⁻¹' S)
          ∂headStep ⟨.tape (.lit (.int z)), σ⟩ := by
  have hne : σ.tapes.fresh ≠ α := Std.ExtTreeMap.elem_fresh_ne h
  have hfresh_eq : ∀ᵐ σ' ∂(tapePresample σ α), σ'.tapes.fresh = σ.tapes.fresh := by
    obtain ⟨N, bs⟩ := t
    exact tapePresample_ae h (by measurability) fun _ => State.fresh_loc_upd_some h
  have htape_rw : ∀ (σ₀ : (State rT)), σ₀.tapes.fresh = σ.tapes.fresh →
      headStep (⟨.tape (.lit (.int z)), σ₀⟩ : (Cfg rT)) =
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
        rw [htape_rw σ' hfr, lintegral_dirac]
    _ = ∫⁻ ρ, ((execN m ∘ K.fillCfg) ρ) ((fun x => x.expr) ⁻¹' S)
          ∂headStep ⟨.tape (.lit (.int z)), σ⟩ := by
        have htape_upd :
            (σ.update_tapes (·.insert σ.tapes.fresh (Tape.empty z))).tapes[α]?
              = some t := by
          rw [State.upd_diff_tape_tot (Ne.symm hne)]; exact h
        have hf_int : Measurable (fun τ : (State rT) =>
            ((execN m ∘ K.fillCfg) ⟨.lit (.lbl σ.tapes.fresh), τ⟩)
              ((fun x => x.expr) ⁻¹' S)) :=
          (erasure_integrand_measurable hS).comp
            (Cfg.measurable_mk.comp (measurable_const.prodMk measurable_id))
        rw [tapePresample_lintegral_update_tapes_ne hne
              (fun τ => ((execN m ∘ K.fillCfg) ⟨.lit (.lbl σ.tapes.fresh), τ⟩)
                ((fun x => x.expr) ⁻¹' S)) hf_int,
            ih_fill _ (σ.update_tapes (·.insert σ.tapes.fresh (Tape.empty z)))
              t htape_upd hN,
            htape_rw σ rfl, lintegral_dirac]

/-- Zero-head-step case. `headStep ⟨e_red, σ⟩ = 0` propagates a.e. over
`tapePresample σ α` via `State.head_step_dzero_upd_tapes`, collapsing both
sides to `0`. -/
theorem erasure_zero_close
    {m : Nat} {K : (Ectx rT)} {S : Set (Exp rT)} {σ : (State rT)} {α : Loc} {t : Tape} {e_red : (Exp rT)}
    (h : σ.tapes[α]? = some t) (_hN : 0 < t.bound)
    (hzero : headStep ⟨e_red, σ⟩ = 0) :
    ∫⁻ σ', ∫⁻ ρ, ((execN m ∘ K.fillCfg) ρ) ((fun x => x.expr) ⁻¹' S)
              ∂headStep ⟨e_red, σ'⟩ ∂tapePresample σ α
      = ∫⁻ ρ, ((execN m ∘ K.fillCfg) ρ) ((fun x => x.expr) ⁻¹' S)
          ∂headStep ⟨e_red, σ⟩ := by
  have hzero_ae : ∀ᵐ σ' ∂(tapePresample σ α), headStep ⟨e_red, σ'⟩ = 0 := by
    obtain ⟨N, bs⟩ := t
    have hg : Measurable (fun σ' : (State rT) => headStep (⟨e_red, σ'⟩ : (Cfg rT))) :=
      headStep.measurable.comp (Cfg.measurable_iff.mpr ⟨measurable_const, measurable_id⟩)
    have hPm : MeasurableSet {σ' : (State rT) | headStep (⟨e_red, σ'⟩ : (Cfg rT)) = 0} := by
      have hset : {σ' : (State rT) | headStep (⟨e_red, σ'⟩ : (Cfg rT)) = 0}
          = (fun σ' => (headStep (⟨e_red, σ'⟩ : (Cfg rT))) Set.univ) ⁻¹' {0} := by
        ext σ'; simp [Measure.measure_univ_eq_zero]
      rw [hset]
      exact ((Measure.measurable_coe MeasurableSet.univ).comp hg) (measurableSet_singleton 0)
    exact tapePresample_ae h hPm fun _ => State.head_step_dzero_upd_tapes h hzero
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
    {σ : (State rT)} {α : Loc} {e : (Exp rT)} {m : Nat} {t : Tape}
    (h : σ.tapes[α]? = some t) (hN : 0 < t.bound) :
    asExpr ((tapePresample σ α).bind (fun σ' => execN m ⟨e, σ'⟩)) =
      asExpr (execN m ⟨e, σ⟩) := by
  unfold asExpr
  -- Induction on `m`, generalized over `e`, `σ`, `t` so the IH applies at
  -- the post-step state (which may hold different tape content but retains
  -- tape `α` with the same bound, via tape-bound persistence).
  induction m generalizing e σ t with
  | zero =>
    -- `execN 0 _ = 0`, so both sides project to the zero measure.
    show ((tapePresample σ α).bind (fun _ => (0 : Measure (Cfg rT)))).map (·.expr) =
         ((0 : Measure (Cfg rT))).map (·.expr)
    refine Measure.ext fun S hS => ?_
    rw [Measure.map_apply Cfg.measurable_expr hS,
        Measure.map_apply Cfg.measurable_expr hS,
        Measure.bind_apply (Cfg.measurable_expr hS) measurable_const.aemeasurable]
    simp only [Measure.coe_zero, Pi.zero_apply, lintegral_zero]
  | succ m ih =>
    by_cases hv : e.isValue
    · -- Value case. `execN (m+1) ⟨e, σ'⟩ = dirac ⟨e, σ'⟩`, so after projecting
      -- by `(·.expr)` both sides become `dirac e` (using that `tapePresample`
      -- is a probability measure).
      have hstep : ∀ σ' : (State rT),
          execN (m + 1) ⟨e, σ'⟩ = Measure.dirac ⟨e, σ'⟩ := fun σ' =>
        execN_succ_isValue (ρ := ⟨e, σ'⟩) hv m
      simp_rw [hstep]
      have hkdir : Measurable (fun σ' : (State rT) => Measure.dirac (⟨e, σ'⟩ : (Cfg rT))) :=
        Cfg.measurable_dirac_mk (fe := fun _ => e) measurable_const measurable_id
      rw [Measure.bind_map_comm' _ _ _ hkdir.aemeasurable Cfg.measurable_expr]
      -- Explicit pointwise kernel equality avoids `simp_rw` metavariable issues.
      have hker : (fun σ' : (State rT) => Measure.map (·.expr) (Measure.dirac (⟨e, σ'⟩ : (Cfg rT))))
          = (fun _ => Measure.dirac e) := by
        funext σ'
        rw [Measure.map_dirac (f := fun c : (Cfg rT) => c.expr) (⟨e, σ'⟩ : (Cfg rT))]
      rw [hker, Measure.map_dirac (f := fun c : (Cfg rT) => c.expr) (⟨e, σ⟩ : (Cfg rT))]
      refine Measure.ext fun S hS => ?_
      rw [Measure.bind_apply hS measurable_const.aemeasurable,
          lintegral_const, tapePresample_univ_eq_one h hN, mul_one]
    · -- Non-value case. Unfold `execN (m+1)` to `primStep ≫= execN m`,
      -- decompose `primStep` into `headStep` at the redex, and dispatch by
      -- `det_or_prob_or_zero`. The K.fillCfg, map-bind shuffling, and
      -- integral-form reshaping done below are mechanical setup; the
      -- substance lives in the three case helpers (`det_close_state_pres`,
      -- `uniform_close`, and the bespoke handling of each rand/heap case).
      have hstep : ∀ σ' : (State rT),
          execN (m + 1) ⟨e, σ'⟩ = (primStep ⟨e, σ'⟩).bind (execN m) :=
        fun σ' => execN_succ_not_isValue (ρ := ⟨e, σ'⟩) hv m
      simp_rw [hstep]
      set K := e.decomp.1
      set e_red := e.decomp.2
      have hprim : ∀ σ' : (State rT),
          primStep ⟨e, σ'⟩ = (headStep ⟨e_red, σ'⟩).map K.fillCfg := by
        intro σ'; simp only [primStep, e_red, K]
      have hg_exec : Measurable (execN m ∘ K.fillCfg) :=
        (execN_measurable m).comp (Ectx.fillCfg.measurable K)
      have hker_hs : Measurable (fun σ' : (State rT) => headStep (⟨e_red, σ'⟩ : (Cfg rT))) :=
        headStep.measurable.comp (Cfg.measurable_iff.mpr ⟨measurable_const, measurable_id⟩)
      have hbind_ker : Measurable (fun σ' : (State rT) =>
          (headStep (⟨e_red, σ'⟩ : (Cfg rT))).bind (execN m ∘ K.fillCfg)) :=
        (Measure.measurable_join.comp (Measure.measurable_map _ hg_exec)).comp hker_hs
      simp_rw [hprim, Measure.bind_map' (Ectx.fillCfg.measurable K) (execN_measurable m)]
      refine Measure.ext fun S hS => ?_
      rw [Measure.map_apply Cfg.measurable_expr hS,
          Measure.map_apply Cfg.measurable_expr hS]
      rw [Measure.bind_apply (Cfg.measurable_expr hS) hbind_ker.aemeasurable]
      simp_rw [Measure.bind_apply (Cfg.measurable_expr hS) hg_exec.aemeasurable]
      -- Reshape the IH (`.map (·.expr)` form) into the pointwise integral
      -- form used by the case helpers below.
      have ih_pointwise : ∀ (e' : (Exp rT)) (σ' : (State rT)) (t' : Tape),
          σ'.tapes[α]? = some t' → 0 < t'.bound →
          ∫⁻ σ'', (execN m ⟨e', σ''⟩) ((fun x => x.expr) ⁻¹' S) ∂tapePresample σ' α
            = (execN m ⟨e', σ'⟩) ((fun x => x.expr) ⁻¹' S) := by
        intro e' σ' t' ht' hN'
        have hih : ((tapePresample σ' α).bind (fun σ'' => execN m ⟨e', σ''⟩)).map (·.expr)
                  = (execN m ⟨e', σ'⟩).map (·.expr) := ih ht' hN'
        have hval : ((tapePresample σ' α).bind (fun σ'' => execN m ⟨e', σ''⟩)).map (·.expr) S
                  = (execN m ⟨e', σ'⟩).map (·.expr) S := by rw [hih]
        have hk_exec : Measurable (fun σ'' : (State rT) => execN m (⟨e', σ''⟩ : (Cfg rT))) :=
          (execN_measurable m).comp
            (Cfg.measurable_mk.comp (measurable_const.prodMk measurable_id))
        rw [Measure.map_apply Cfg.measurable_expr hS,
            Measure.map_apply Cfg.measurable_expr hS,
            Measure.bind_apply (Cfg.measurable_expr hS) hk_exec.aemeasurable] at hval
        exact hval
      -- Specialization composing `ih_pointwise` with `K.fill`, matching the
      -- shape of the post-`K.fillCfg` integrand.
      have ih_fill : ∀ (e' : (Exp rT)) (σ' : (State rT)) (t' : Tape),
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
        erasure_uniform_close (m := m) (K := K) (S := S) hS h hN ih_fill
          e_h z_r hz hstep_ae hstep_σ
      have uniformReal_close := fun e_h hstep_ae hstep_σ =>
        erasure_uniformReal_close (m := m) (K := K) (S := S) hS h hN ih_fill
          e_h hstep_ae hstep_σ
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
          exact erasure_alloc_close (ed := ed) hS h hN ih_fill
        | store hv hsome =>
          rename_i ℓ ev
          exact erasure_store_close (ℓ := ℓ) (ev := ev) hS h hN ih_fill
        | tape =>
          rename_i z
          exact erasure_tape_close (z := z) hS h hN ih_fill
      · -- Probabilistic case: `headStep` is either `Cfg.uniform` (non-tape
        -- or "other-tape" rand) or a tape-popping dirac (same-tape rand).
        clear_value e_red K
        cases hprob with
        | randNoTape hz =>
          rename_i z_r
          exact uniform_close _ z_r hz
            (MeasureTheory.ae_of_all _ fun _ => rfl) rfl
        | @randTape z_r α_lbl _ N_b nn ns htapes hzN =>
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
            have hker_rand : Measurable (fun σ' : (State rT) =>
                headStep (⟨.rand (.lit (.int z_r)) (.lit (.lbl α)), σ'⟩ : (Cfg rT))) :=
              headStep.measurable.comp (Cfg.measurable_iff.mpr ⟨measurable_const, measurable_id⟩)
            rw [hrhs, lintegral_dirac,
                tapePresample_lintegral h
                  (fun σ' => ∫⁻ ρ, ((execN m ∘ K.fillCfg) ρ) ((fun x => x.expr) ⁻¹' S)
                    ∂headStep ⟨.rand (.lit (.int z_r)) (.lit (.lbl α)), σ'⟩)
                  ((Measure.measurable_lintegral (erasure_integrand_measurable hS)).comp
                    hker_rand)]
            have hstep_upd : ∀ n' : { z : Int // 0 ≤ z ∧ z < z_r },
                headStep ⟨.rand (.lit (.int z_r)) (.lit (.lbl α)),
                  σ.update_tapes (·.insert α ⟨z_r, (nn :: ns) ++ [↑n']⟩)⟩ =
                Measure.dirac ⟨.lit (.int ↑nn),
                  σ.update_tapes (·.insert α ⟨z_r, ns ++ [↑n']⟩)⟩ := by
              intro ⟨n', hn'⟩
              simp only [headStep, State.upd_tape_some, List.cons_append, ↓reduceIte]
              rw [State.update_tapes_twice]
            simp_rw [hstep_upd, lintegral_dirac]
            -- Fold the residual integral back into `tapePresample σ_popped α`.
            have htape_popped : (σ.update_tapes (·.insert α ⟨z_r, ns⟩)).tapes[α]? =
                some ⟨z_r, ns⟩ := State.upd_tape_some _ _ _
            convert
              ih_fill (.lit (.int ↑nn)) (σ.update_tapes (·.insert α ⟨z_r, ns⟩))
                ⟨z_r, ns⟩ htape_popped hN using 1
            rw [tapePresample_lintegral htape_popped
                  (fun σ'' => ((execN m ∘ K.fillCfg) ⟨.lit (.int ↑nn), σ''⟩)
                    ((fun x => x.expr) ⁻¹' S))
                  ((erasure_integrand_measurable hS).comp
                    (Cfg.measurable_mk.comp (measurable_const.prodMk measurable_id)))]
            simp_rw [State.update_tapes_twice]
          · -- α_lbl ≠ α: tapePresample doesn't affect tape α_lbl.
            have hstep_rw : ∀ (σ₀ : (State rT)), σ₀.tapes[α_lbl]? = some ⟨z_r, nn :: ns⟩ →
                headStep (⟨.rand (.lit (.int z_r)) (.lit (.lbl α_lbl)), σ₀⟩ : (Cfg rT)) =
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
                  rw [hstep_rw σ' ht', lintegral_dirac]
              _ = ∫⁻ ρ, ((execN m ∘ K.fillCfg) ρ) ((fun x => x.expr) ⁻¹' S)
                    ∂headStep ⟨.rand (.lit (.int z_r)) (.lit (.lbl α_lbl)), σ⟩ := by
                  have htape_upd :
                      (σ.update_tapes (·.insert α_lbl ⟨z_r, ns⟩)).tapes[α]?
                        = some t := by
                    rw [State.upd_diff_tape_tot hαeq]; exact h
                  rw [tapePresample_lintegral_update_tapes_ne (Ne.symm hαeq)
                        (fun τ =>
                          ((execN m ∘ K.fillCfg) ⟨.lit (.int nn), τ⟩)
                            ((fun x => x.expr) ⁻¹' S))
                        ((erasure_integrand_measurable hS).comp
                          (Cfg.measurable_mk.comp (measurable_const.prodMk measurable_id))),
                      ih_fill _ (σ.update_tapes (·.insert α_lbl ⟨z_r, ns⟩))
                        t htape_upd hN,
                      hstep_rw σ htapes, lintegral_dirac]
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
            have hker_rand : Measurable (fun σ' : (State rT) =>
                headStep (⟨.rand (.lit (.int z_r)) (.lit (.lbl α)), σ'⟩ : (Cfg rT))) :=
              headStep.measurable.comp (Cfg.measurable_iff.mpr ⟨measurable_const, measurable_id⟩)
            rw [hrhs, tapePresample_lintegral h
                  (fun σ' => ∫⁻ ρ, ((execN m ∘ K.fillCfg) ρ) ((fun x => x.expr) ⁻¹' S)
                    ∂headStep ⟨.rand (.lit (.int z_r)) (.lit (.lbl α)), σ'⟩)
                  ((Measure.measurable_lintegral (erasure_integrand_measurable hS)).comp
                    hker_rand)]
            have hstep_upd : ∀ n' : { z : Int // 0 ≤ z ∧ z < z_r },
                headStep ⟨.rand (.lit (.int z_r)) (.lit (.lbl α)),
                  σ.update_tapes (·.insert α ⟨z_r, [n']⟩)⟩ =
                Measure.dirac ⟨.lit (.int ↑n'),
                  σ.update_tapes (·.insert α ⟨z_r, []⟩)⟩ := by
              intro ⟨n', hn'⟩
              simp only [headStep, State.upd_tape_some, ↓reduceIte]
              rw [State.update_tapes_twice]
            simp only [List.nil_append]
            simp_rw [hstep_upd, lintegral_dirac]
            -- `σ.update_tapes(insert α ⟨z_r, []⟩) = σ` since the tape was
            -- already `⟨z_r, []⟩`; then the LHS and RHS are two encodings of
            -- the same uniform integral over indices in `[0, z_r)`.
            rw [State.update_tapes_insert_id htapes]
            exact tapeIndexUniform_lintegral_eq_cfg_uniform hz σ
              (fun ρ => ((execN m ∘ K.fillCfg) ρ) ((fun x => x.expr) ⁻¹' S))
              (erasure_integrand_measurable hS)
          · -- Different tape: lookup preserved a.e., so `headStep` stays
            -- `Cfg.uniform z_r σ'` and `uniform_close` closes the goal.
            have hstep_σ : headStep (⟨.rand (.lit (.int z_r)) (.lit (.lbl α_lbl)), σ⟩ : (Cfg rT))
                = Cfg.uniform z_r σ := by simp [headStep, htapes]
            refine uniform_close _ z_r hz ?_ hstep_σ
            filter_upwards [tapePresample_tape_ne_ae h (Ne.symm hαeq)] with σ' htape_eq
            simp [headStep, htape_eq.trans htapes]
        | @randTapeOther z_r α_lbl _ N_b L hz htapes hzN =>
          -- `z_r ≠ N_b`, so headStep falls through to `Cfg.uniform z_r σ'`.
          -- For `α_lbl = α`, tapePresample appends to α but preserves bound
          -- `N_b`; for `α_lbl ≠ α`, the lookup is unchanged.
          -- Helper: when tape at `α_lbl` has bound `≠ z_r`, headStep is uniform.
          have hrand_uniform : ∀ (σ₀ : (State rT)) {M : Int} {ns : List _},
              σ₀.tapes[α_lbl]? = some ⟨M, ns⟩ → M ≠ z_r →
              headStep (⟨.rand (.lit (.int z_r)) (.lit (.lbl α_lbl)), σ₀⟩ : (Cfg rT))
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
            -- a.e. the tape at `α` still has bound `N` (presample only appends);
            -- this is a measurable lookup predicate, from which the `headStep`
            -- equality follows pointwise.
            have hmb : Measurable (fun σ' : (State rT) => (σ'.tapes[α]?).map Tape.bound) :=
              (Measurable.of_discrete (f := fun o : Option Tape => o.map Tape.bound)).comp
                ((LocHeap.measurable_getElem? α).comp State.measurable_tapes)
            have hbound_ae : ∀ᵐ σ' ∂tapePresample σ α,
                (σ'.tapes[α]?).map Tape.bound = some N := by
              refine tapePresample_ae h (hmb (measurableSet_singleton _)) fun n => ?_
              simp [State.update_tapes]
            filter_upwards [hbound_ae] with σ' hb
            rcases hq : σ'.tapes[α]? with _ | ⟨M, L⟩
            · simp [hq] at hb
            · simp only [hq, Option.map_some, Option.some.injEq] at hb
              exact hrand_uniform _ hq (by omega)
          · -- Different tape: lookup preserved.
            filter_upwards [tapePresample_tape_ne_ae h (Ne.symm hαeq)] with σ' htape_eq
            exact hrand_uniform _ (htape_eq.trans htapes) (Ne.symm hzN)
        | randNonpos hz =>
          -- New nonpos case: headStep = dirac ⟨lit -1, σ'⟩, state-preserving.
          rename_i z_r
          refine det_close_state_pres _ (.lit (.int (-1))) fun σ' => ?_
          show Cfg.uniform z_r σ' = _
          exact Cfg.uniform_nonpos_eq hz
        | @randTapeNonposEmpty z_r α_lbl _ N_b hz htapes hzN =>
          have hαne : α ≠ α_lbl := by
            intro heq; subst heq
            have ht_eq : t = ⟨N_b, []⟩ := by
              rw [htapes] at h; exact (Option.some.inj h).symm
            apply hz; rw [hzN]
            have : t.bound = N_b := by rw [ht_eq]
            exact this ▸ hN
          subst hzN
          have hstep : ∀ {σ' : (State rT)}, σ'.tapes[α_lbl]? = some ⟨z_r, []⟩ →
              headStep (⟨.rand (.lit (.int z_r)) (.lit (.lbl α_lbl)), σ'⟩ : (Cfg rT)) =
                Measure.dirac ⟨.lit (.int (-1)), σ'⟩ := by
            intro σ' hσ'
            simp only [headStep, hσ', ↓reduceIte]
            exact Cfg.uniform_nonpos_eq hz
          refine erasure_det_close_ae h hN ih_fill _ (.lit (.int (-1))) ?_ ?_
          · filter_upwards [tapePresample_tape_ne_ae h (Ne.symm hαne)] with σ' htape_eq
            exact hstep (htape_eq.trans htapes)
          · exact hstep htapes
        | @randTapeNonposOther z_r α_lbl _ N_b L hz htapes hzN =>
          have hstep : ∀ {σ' : (State rT)}, σ'.tapes[α_lbl]? = some ⟨N_b, L⟩ →
              headStep (⟨.rand (.lit (.int z_r)) (.lit (.lbl α_lbl)), σ'⟩ : (Cfg rT)) =
                Measure.dirac ⟨.lit (.int (-1)), σ'⟩ := by
            intro σ' hσ'
            simp only [headStep, hσ']
            rw [if_neg (Ne.symm hzN)]
            exact Cfg.uniform_nonpos_eq hz
          refine erasure_det_close_ae h hN ih_fill _ (.lit (.int (-1))) ?_ (hstep htapes)
          by_cases hαeq : α = α_lbl
          · subst hαeq
            -- Original tape at α is t = ⟨N_b, L⟩ (from htapes = h).
            have ht_eq : t = ⟨N_b, L⟩ := by
              rw [htapes] at h; exact (Option.some.inj h).symm
            subst ht_eq
            -- a.e. the tape at `α` keeps bound `N_b`; derive `headStep = dirac -1`
            -- pointwise (the bound predicate is a measurable lookup).
            have hmb : Measurable (fun σ' : (State rT) => (σ'.tapes[α]?).map Tape.bound) :=
              (Measurable.of_discrete (f := fun o : Option Tape => o.map Tape.bound)).comp
                ((LocHeap.measurable_getElem? α).comp State.measurable_tapes)
            have hbound_ae : ∀ᵐ σ' ∂tapePresample σ α,
                (σ'.tapes[α]?).map Tape.bound = some N_b := by
              refine tapePresample_ae h (hmb (measurableSet_singleton _)) fun n => ?_
              simp [State.update_tapes]
            filter_upwards [hbound_ae] with σ' hb
            rcases hq : σ'.tapes[α]? with _ | ⟨M, L'⟩
            · simp [hq] at hb
            · simp only [hq, Option.map_some, Option.some.injEq] at hb
              simp only [headStep, hq]
              rw [if_neg (show ¬ M = z_r by omega)]
              exact Cfg.uniform_nonpos_eq hz
          · filter_upwards [tapePresample_tape_ne_ae h (Ne.symm hαeq)] with σ' htape_eq
            exact hstep (htape_eq.trans htapes)
        | urand =>
          -- Continuous sampler: ignores tapes, so `headStep = Cfg.uniformReal`
          -- regardless of presampling. Closed by the continuous closer.
          exact uniformReal_close Exp.urand (MeasureTheory.ae_of_all _ fun _ => rfl) rfl
      · -- Zero case handled by `erasure_zero_close`.
        exact erasure_zero_close (e_red := e_red) h hN hzero

/-! ## Iterated and limit variants -/

/-- `n`-fold presample iterator on a single tape `α`. Used to state
`execN_iterM_tape_presample_expr_eq` below: the anonymous `Nat.rec` in
Clutch's `erasure.v` tape-batching statement is definitionally equal to
this `Nat.rec`-free variant. -/
noncomputable def tapePresampleIter (α : Loc) (σ : (State rT)) : Nat → Measure (State rT)
  | 0 => Measure.dirac σ
  | n + 1 => (tapePresampleIter α σ n).bind (fun σ' => tapePresample σ' α)

/-- Tape-bound persistence under `tapePresampleIter`: every state in the
support retains tape `α` with the same bound as the initial `σ`. -/
theorem tapePresampleIter_tape_bound_ae [Countable rT] [MeasurableSingletonClass rT]
    {σ : (State rT)} {α : Loc} {t : Tape}
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
    refine MeasureTheory.ae_iff.mp (Discrete.tapePresample_ae ht'' fun n' => ?_)
    exact ⟨⟨Nb, bs ++ [n']⟩, by simp [State.update_tapes], hbound⟩

/-- Iterated-presample variant of `execN_tape_presample_expr_eq`:
`n`-fold presampling onto tape `α` is invisible to `execN m ⟨e, ·⟩` at the
expression level, provided the initial tape exists and has positive bound. -/
theorem execN_tapePresampleIter_expr_eq [Countable rT] [MeasurableSingletonClass rT]
    {σ : (State rT)} {α : Loc} {e : (Exp rT)} {m : Nat} {t : Tape} (n : Nat)
    (h : σ.tapes[α]? = some t) (hN : 0 < t.bound) :
    asExpr ((tapePresampleIter α σ n).bind (fun σ' => execN m ⟨e, σ'⟩)) =
      asExpr (execN m ⟨e, σ⟩) := by
  unfold asExpr
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
          have h_eq := execN_tape_presample_expr_eq (e := e) (m := m) ht' (hbound ▸ hN)
          unfold asExpr at h_eq
          rw [h_eq]
      _ = ((tapePresampleIter α σ k).bind (fun σ' => execN m ⟨e, σ'⟩)).map (·.expr) S := by
          rw [Measure.map_apply Measurable.of_discrete hS,
              Measure.bind_apply (Measurable.of_discrete hS)
                Measurable.of_discrete.aemeasurable]
          simp_rw [Measure.map_apply Measurable.of_discrete hS]
      _ = (execN m ⟨e, σ⟩).map (·.expr) S := by
          have h_ih := ih h
          unfold asExpr at h_ih
          rw [h_ih, Measure.map_apply Measurable.of_discrete hS]

theorem execN_iterM_tape_presample_expr_eq [Countable rT] [MeasurableSingletonClass rT]
    {σ : (State rT)} {α : Loc} {e : (Exp rT)} {m : Nat} {t : Tape} (n : Nat)
    (h : σ.tapes[α]? = some t) (hN : 0 < t.bound) :
    asExpr (((Nat.rec (motive := fun _ => Measure (State rT))
                (Measure.dirac σ)
                (fun _ μ => μ.bind (fun σ' => tapePresample σ' α))) n).bind
       (fun σ' => execN m ⟨e, σ'⟩)) =
      asExpr (execN m ⟨e, σ⟩) := by
  -- The anonymous `Nat.rec` is definitionally equal to `tapePresampleIter`.
  have hiter_eq : (Nat.rec (motive := fun _ => Measure (State rT))
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
    {σ : (State rT)} {α : Loc} {t : Tape} {e : (Exp rT)}
    (h : σ.tapes[α]? = some t) (hN : 0 < t.bound) :
    asExpr ((tapePresample σ α).bind (fun σ' => limExec ⟨e, σ'⟩)) =
      limExecV ⟨e, σ⟩ := by
  unfold asExpr limExecV asExpr
  -- We replay the `ErasableExpr.lim_exec` proof inline with
  -- `execN_tape_presample_expr_eq` as the per-n hypothesis.
  have hbuild : Measurable (fun σ' : (State rT) => (⟨e, σ'⟩ : (Cfg rT))) :=
    Cfg.measurable_mk.comp (measurable_const.prodMk measurable_id)
  have hker_lim : AEMeasurable (fun σ' : (State rT) => limExec (⟨e, σ'⟩ : (Cfg rT)))
      (tapePresample σ α) := (limExec.measurable.comp hbuild).aemeasurable
  have hker_exec : ∀ n : Nat, AEMeasurable (fun σ' : (State rT) => execN n (⟨e, σ'⟩ : (Cfg rT)))
      (tapePresample σ α) := fun n => ((execN_measurable n).comp hbuild).aemeasurable
  refine Measure.ext fun S hS => ?_
  rw [Measure.map_apply Cfg.measurable_expr hS,
      Measure.map_apply Cfg.measurable_expr hS,
      Measure.bind_apply (Cfg.measurable_expr hS) hker_lim]
  have hind : ∀ ρ : (Cfg rT),
      limExec ρ ((·.expr) ⁻¹' S)
        = ∫⁻ x, (((·.expr) ⁻¹' S) : Set (Cfg rT)).indicator 1 x ∂(limExec ρ) := by
    intro ρ
    rw [lintegral_indicator_one (Cfg.measurable_expr hS)]
  simp_rw [hind]
  simp_rw [lintegral_limExec']
  have hf_isup : ∀ n : Nat, Measurable (fun σ' : (State rT) =>
      ∫⁻ x, (((·.expr) ⁻¹' S) : Set (Cfg rT)).indicator 1 x ∂execN n (⟨e, σ'⟩ : (Cfg rT))) :=
    fun n => (Measure.measurable_lintegral
      (measurable_const.indicator (Cfg.measurable_expr hS))).comp
      ((execN_measurable n).comp hbuild)
  rw [lintegral_iSup hf_isup
        (fun i j hij σ' =>
          lintegral_mono' (execN_mono hij ⟨e, σ'⟩) (le_refl _))]
  refine iSup_congr fun n => ?_
  have hn := execN_tape_presample_expr_eq (e := e) (m := n) h hN
  unfold asExpr at hn
  have hval : ((tapePresample σ α).bind (fun σ' => execN n ⟨e, σ'⟩)).map (·.expr) S
            = (execN n ⟨e, σ⟩).map (·.expr) S := by
    rw [hn]
  rw [Measure.map_apply Cfg.measurable_expr hS,
      Measure.map_apply Cfg.measurable_expr hS,
      Measure.bind_apply (Cfg.measurable_expr hS) (hker_exec n)] at hval
  rw [show (∫⁻ x, (((·.expr) ⁻¹' S) : Set (Cfg rT)).indicator 1 x ∂(execN n ⟨e, σ⟩))
        = (execN n ⟨e, σ⟩) ((·.expr) ⁻¹' S)
      from lintegral_indicator_one (Cfg.measurable_expr hS)]
  simp_rw [show ∀ σ' : (State rT),
        (∫⁻ x, (((·.expr) ⁻¹' S) : Set (Cfg rT)).indicator 1 x ∂(execN n ⟨e, σ'⟩))
          = (execN n ⟨e, σ'⟩) ((·.expr) ⁻¹' S)
      from fun σ' => lintegral_indicator_one (Cfg.measurable_expr hS)]
  exact hval

@[discrete]
theorem Discrete.limExec_tape_presample_expr_eq [Countable rT] [MeasurableSingletonClass rT]
    {σ : (State rT)} {α : Loc} {t : Tape} {e : (Exp rT)}
    (h : σ.tapes[α]? = some t) (hN : 0 < t.bound) :
    asExpr ((tapePresample σ α).bind (fun σ' => limExec ⟨e, σ'⟩)) =
      limExecV ⟨e, σ⟩ :=
  ProbLang.limExec_tape_presample_expr_eq h hN

/-! ## `ErasableExpr`: the weak erasability notion

Clutch's `erasable` is defined over val-projected `exec`, so it implicitly
projects away state differences at final configurations. Our `Erasable`
(in `Erasable.lean`) is phrased over `Measure (Cfg rT)` and is therefore
strictly stronger — `dret σ` satisfies it, but `tapePresample σ α`
generally does not.

`ErasableExpr` is the projected notion: the distributions agree *after
projecting to the expression component*. This is the semantically correct
analogue of Clutch's `erasable` for our `(Cfg rT)`-valued operational semantics.
Both `dret`-style and `tapePresample`-style distributions satisfy it. -/
def ErasableExpr (μ : Measure (State rT)) (σ : (State rT)) : Prop :=
  ∀ (e : (Exp rT)) (m : Nat),
    asExpr (μ.bind (fun σ' => execN m ⟨e, σ'⟩)) =
      asExpr (execN m ⟨e, σ⟩)

namespace ErasableExpr

/-- Strict `Erasable` implies `ErasableExpr`. -/
theorem of_erasable {μ : Measure (State rT)} {σ : (State rT)} (h : Erasable μ σ) :
    ErasableExpr μ σ := by
  intro e m
  rw [h e m]

/-- An `ErasableExpr` measure is a probability measure (total mass `1`). Evaluated
at a value expression with one step, `execN 1 ⟨v, ·⟩ = dirac ⟨v, ·⟩`, so the
expression-projected total masses on both sides of `ErasableExpr` force `μ univ = 1`.
Mirrors `Erasable.mass`, unwrapping the `asExpr` projection on `univ`. -/
theorem mass {μ : Measure (State rT)} {σ : (State rT)} (h : ErasableExpr μ σ) :
    μ Set.univ = 1 := by
  have hv : IsVal (Exp.lit (rT := rT) .unit) := .lit
  have hstep : ∀ σ' : State rT,
      execN 1 ((⟨.lit .unit, σ'⟩ : Cfg rT)) = Measure.dirac (⟨.lit .unit, σ'⟩ : Cfg rT) :=
    fun σ' => execN_succ_isValue (ρ := ⟨.lit .unit, σ'⟩) hv.toIsValue 0
  have hexpr : ∀ ν : Measure (Cfg rT), asExpr ν Set.univ = ν Set.univ := fun ν => by
    rw [asExpr, Measure.map_apply Cfg.measurable_expr MeasurableSet.univ, Set.preimage_univ]
  have h1 := h (.lit .unit) 1
  have hboth := congrArg (fun ν => ν (Set.univ : Set (Exp rT))) h1
  simp only [hexpr] at hboth
  rw [hstep σ] at hboth
  rw [Measure.dirac_apply' _ .univ] at hboth
  simp at hboth
  rw [bind_apply .univ (Measurable.aemeasurable (by measurability))] at hboth
  simp_rw [hstep] at hboth
  simp_rw [Measure.dirac_apply' _ .univ] at hboth
  simp at hboth
  exact hboth

/-- Dirac distributions are `ErasableExpr`. -/
theorem dret [Countable rT] [MeasurableSingletonClass rT]
    (σ : (State rT)) : ErasableExpr (Measure.dirac σ) σ :=
  of_erasable (Erasable.dret σ)

/-- `tapePresample σ α` is `ErasableExpr`. This is the main theorem
`execN_tape_presample_expr_eq`, repackaged as an `ErasableExpr` witness.
Countability-free (`execN_tape_presample_expr_eq` is). -/
theorem tapePresample
    {σ : (State rT)} {α : Loc} {t : Tape}
    (h : σ.tapes[α]? = some t) (hN : 0 < t.bound) :
    ErasableExpr (tapePresample σ α) σ := by
  intro e m
  exact execN_tape_presample_expr_eq h hN

/-- `ErasableExpr` is closed under `bind`. -/
theorem dbind [Countable rT] [MeasurableSingletonClass rT]
    {μ₁ : Measure (State rT)} {μ₂ : (State rT) → Measure (State rT)} {σ : (State rT)}
    (h₁ : ErasableExpr μ₁ σ) (h₂ : ∀ σ', ErasableExpr (μ₂ σ') σ') :
    ErasableExpr (μ₁.bind μ₂) σ := by
  intro e m
  unfold asExpr
  -- Flatten the outer `(μ₁.bind μ₂).bind (execN m ⟨e, ·⟩)` into a
  -- double bind; apply `h₂` pointwise to each σ' in the inner kernel
  -- (at the projected level); then use `h₁` to finish.
  rw [Measure.bind_bind
        Measurable.of_discrete.aemeasurable
        Measurable.of_discrete.aemeasurable]
  -- Push the outer `.map (·.expr)` inside the bind.
  rw [Measure.bind_map_comm]
  -- Pointwise: for each σ', replace the inner bind+map with the IH.
  have hker : (fun σ' : (State rT) =>
      Measure.map (·.expr : (Cfg rT) → (Exp rT))
        ((μ₂ σ').bind (fun σ'' => execN m ⟨e, σ''⟩)))
      = (fun σ' : (State rT) =>
          Measure.map (·.expr) (execN m ⟨e, σ'⟩)) := by
    funext σ'
    have := h₂ σ' e m
    unfold asExpr at this
    exact this
  rw [hker]
  -- Now the goal is: μ₁.bind (fun σ' => (execN m ⟨e, σ'⟩).map (·.expr)) =
  --                  (execN m ⟨e, σ⟩).map (·.expr).
  -- Pull the `.map` back out, then apply `h₁ e m`.
  rw [← Measure.bind_map_comm]
  have := h₁ e m
  unfold asExpr at this
  exact this

/-- `ErasableExpr` lifts through `limExec` at the expression-projection
level. This is the load-bearing corollary for the adequacy wrappers.

Proof via `lintegral_limExec`: we test both sides against the indicator of
`(·.expr) ⁻¹' S`, use the integral-vs-iSup equation `lintegral_limExec`,
and apply the `ErasableExpr` hypothesis pointwise at each `n`. -/
theorem lim_exec
    {μ : Measure (State rT)} {σ : (State rT)} (h : ErasableExpr μ σ)
    (e : (Exp rT)) :
    asExpr (μ.bind (fun σ' => limExec ⟨e, σ'⟩)) =
      limExecV ⟨e, σ⟩ := by
  -- Countability-free: replace the `Measurable.of_discrete` shortcuts with the
  -- genuine measurability lemmas (`Cfg.measurable_expr`, `execN_measurable`,
  -- `limExec.measurable`).
  have hexpr : Measurable (·.expr : Cfg rT → Exp rT) := Cfg.measurable_expr
  have hmk : Measurable (fun σ' : State rT => (⟨e, σ'⟩ : Cfg rT)) := by fun_prop
  unfold asExpr limExecV asExpr
  refine Measure.ext fun S hS => ?_
  -- Rewrite both sides as `limExec ... (preimage S)`:
  rw [Measure.map_apply hexpr hS,
      Measure.map_apply hexpr hS,
      Measure.bind_apply (hexpr hS)
        (show Measurable (fun σ' : State rT => limExec (⟨e, σ'⟩ : Cfg rT)) from
          limExec.measurable.comp hmk).aemeasurable]
  -- Express each `limExec ρ A` as `∫⁻ x, indicator A 1 x ∂(limExec ρ)`:
  have hind : ∀ ρ : (Cfg rT),
      limExec ρ ((·.expr) ⁻¹' S)
        = ∫⁻ x, (((·.expr) ⁻¹' S) : Set (Cfg rT)).indicator 1 x ∂(limExec ρ) := by
    intro ρ
    rw [lintegral_indicator_one (hexpr hS)]
  simp_rw [hind]
  -- Use `lintegral_limExec'` on both sides (outer iSup swap; countability-free).
  simp_rw [lintegral_limExec']
  -- Pull the outer iSup through the outer integral:
  rw [lintegral_iSup
        (fun n => by
          have hrw : (fun σ' => ∫⁻ x,
                  (((·.expr) ⁻¹' S) : Set (Cfg rT)).indicator 1 x ∂(execN n ⟨e, σ'⟩))
                = (fun σ' => (execN n ⟨e, σ'⟩) ((·.expr) ⁻¹' S)) := by
            funext σ'; exact lintegral_indicator_one (hexpr hS)
          rw [hrw]
          exact (Measure.measurable_coe (hexpr hS)).comp ((execN_measurable n).comp hmk))
        (fun i j hij σ' =>
          lintegral_mono' (execN_mono hij ⟨e, σ'⟩) (le_refl _))]
  -- Now just pointwise equality at each n, via the `ErasableExpr` hypothesis.
  refine iSup_congr fun n => ?_
  have hn := h e n
  unfold asExpr at hn
  have hval : (μ.bind (fun σ' => execN n ⟨e, σ'⟩)).map (·.expr) S
            = (execN n ⟨e, σ⟩).map (·.expr) S := by
    rw [hn]
  rw [Measure.map_apply hexpr hS,
      Measure.map_apply hexpr hS,
      Measure.bind_apply (hexpr hS)
        (show Measurable (fun σ' : State rT => execN n (⟨e, σ'⟩ : Cfg rT)) from
          (execN_measurable n).comp hmk).aemeasurable] at hval
  -- Convert both sides' integrals from indicator form:
  rw [show (∫⁻ x, (((·.expr) ⁻¹' S) : Set (Cfg rT)).indicator 1 x ∂(execN n ⟨e, σ⟩))
        = (execN n ⟨e, σ⟩) ((·.expr) ⁻¹' S)
      from lintegral_indicator_one (hexpr hS)]
  simp_rw [show ∀ σ' : (State rT),
        (∫⁻ x, (((·.expr) ⁻¹' S) : Set (Cfg rT)).indicator 1 x ∂(execN n ⟨e, σ'⟩))
          = (execN n ⟨e, σ'⟩) ((·.expr) ⁻¹' S)
      from fun σ' => lintegral_indicator_one (hexpr hS)]
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
`(Exp rT) × (Exp rT)` relation, we lift to a coupling on
`(execN n ⟨e₁, σ₁⟩).map (·.expr) / (limExec ⟨e₁', σ₁'⟩).map (·.expr)`.
The error slacks add. -/
theorem AddCoupl_erasure_erasable [Countable rT] [MeasurableSingletonClass rT]
    {e₁ e₁' : (Exp rT)} {σ₁ σ₁' : (State rT)}
    {μ₁ μ₂ : Measure (State rT)} {R : Set ((State rT) × (State rT))}
    {Φexp : Set ((Exp rT) × (Exp rT))}
    {ε ε₁ ε₂ : ENNReal} {n : Nat}
    (hSum : ε₁ + ε₂ ≤ ε)
    (hμ₁mass : μ₁ Set.univ ≤ 1)
    (hCoupl : AddCoupl ε₁ R μ₁ μ₂)
    (hErase₁ : ErasableExpr μ₁ σ₁)
    (hErase₂ : ErasableExpr μ₂ σ₁')
    (hCont : ∀ σ₂ σ₂', R (σ₂, σ₂') →
        AddCoupl ε₂ Φexp
          (asExpr (execN n ⟨e₁, σ₂⟩))
          (limExecV ⟨e₁', σ₂'⟩)) :
    AddCoupl ε Φexp
      (asExpr (execN n ⟨e₁, σ₁⟩))
      (limExecV ⟨e₁', σ₁'⟩) := by
  -- Rewrite both projected targets via the `ErasableExpr` hypotheses.
  rw [← hErase₁ e₁ n, ← hErase₂.lim_exec e₁']
  unfold asExpr
  -- Push `.map (·.expr)` through both outer binds.
  rw [Measure.bind_map_comm, Measure.bind_map_comm]
  -- Sub-probability of the inner kernels (projected `execN n`).
  have hmassk : ∀ σ : (State rT), (execN n ⟨e₁, σ⟩).map (·.expr) Set.univ ≤ 1 := by
    intro σ
    rw [Measure.map_apply Measurable.of_discrete MeasurableSet.univ]
    simpa using execN_univ_le_one n ⟨e₁, σ⟩
  -- Apply `AddCoupl.bind` to get the `(ε₁ + ε₂)`-slack coupling, then
  -- strengthen to `ε`-slack via `mono_grading`.
  have hBind := AddCoupl.bind
    (Hfm := Measurable.of_discrete) (Hgm := Measurable.of_discrete)
    (Hμₗ := hμ₁mass) (Hfsprob := hmassk)
    (Hcpl := hCoupl)
    (Hbind := fun {σ₂ σ₂'} (hR : R (σ₂, σ₂')) => by
      have := hCont σ₂ σ₂' hR
      unfold asExpr limExecV asExpr at this
      exact this)
  exact AddCoupl.mono_grading hSum hBind

/-- **Clutch `ARcoupl_erasure_erasable_exp_rhs`, reformulated (projected form).**
RHS expected-value variant (advanced composition). The continuation's
slack `E₂` depends on the RHS sample, paid as additional slack on the LHS. -/
theorem AddCoupl_erasure_erasable_exp_rhs [Countable rT] [MeasurableSingletonClass rT]
    {e₁ e₁' : (Exp rT)} {σ₁ σ₁' : (State rT)}
    {μ₁ μ₁' : Measure (State rT)} {R : Set ((State rT) × (Cfg rT))}
    {Φexp : Set ((Exp rT) × (Exp rT))}
    {ε ε₁ ε₂ : ENNReal} {E₂ : (Cfg rT) → ENNReal} {n m : Nat}
    (hE₂meas : Measurable E₂)
    (hCoupl : AddCoupl ε₁ R μ₁
        (μ₁'.bind (fun σ₂' => pexecN m ⟨e₁', σ₂'⟩)))
    (hBoundSum : ∫⁻ ρ, E₂ ρ ∂(μ₁'.bind (fun σ₂' => pexecN m ⟨e₁', σ₂'⟩)) ≤ ε₂)
    (hEpsSum : ε₁ + ε₂ ≤ ε)
    (hErase₁ : ErasableExpr μ₁ σ₁)
    (hErase₁' : ErasableExpr μ₁' σ₁')
    (hCont : ∀ σ₂ ρ', R (σ₂, ρ') →
        AddCoupl (E₂ ρ') Φexp
          (asExpr (execN n ⟨e₁, σ₂⟩))
          (limExecV ρ')) :
    AddCoupl ε Φexp
      (asExpr (execN n ⟨e₁, σ₁⟩))
      (limExecV ⟨e₁', σ₁'⟩) := by
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
  unfold asExpr
  -- Push `.map (·.expr)` through both outer binds.
  rw [Measure.bind_map_comm, Measure.bind_map_comm]
  -- Sub-probability of the inner kernels (projected `execN n ⟨e₁, ·⟩`).
  have hmassk : ∀ σ : (State rT), (execN n ⟨e₁, σ⟩).map (·.expr) Set.univ ≤ 1 := by
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
    (Hbind := fun {σ₂ ρ'} hR => by
      have := hCont σ₂ ρ' hR
      unfold asExpr limExecV asExpr at this
      exact this)
  exact AddCoupl.mono_grading hEpsSum hBind

/-- **Clutch `ARcoupl_erasure_erasable_exp_lhs`, reformulated (projected form).**
LHS expected-value variant. Symmetric to `AddCoupl_erasure_erasable_exp_rhs`. -/
theorem AddCoupl_erasure_erasable_exp_lhs [Countable rT] [MeasurableSingletonClass rT]
    {e₁ e₁' : (Exp rT)} {σ₁ σ₁' : (State rT)}
    {μ₁' : Measure (State rT)} {R : Set ((Cfg rT) × (State rT))}
    {Φexp : Set ((Exp rT) × (Exp rT))}
    {ε ε₁ ε₂ : ENNReal} {E₂ : (Cfg rT) → ENNReal} {n : Nat}
    (hE₂meas : Measurable E₂)
    (hCoupl : AddCoupl ε₁ R (primStep ⟨e₁, σ₁⟩) μ₁')
    (hBoundSum : ∫⁻ ρ, E₂ ρ ∂(primStep ⟨e₁, σ₁⟩) ≤ ε₂)
    (hEpsSum : ε₁ + ε₂ ≤ ε)
    (hErase₁' : ErasableExpr μ₁' σ₁')
    (hCont : ∀ ρ σ₂', R (ρ, σ₂') →
        AddCoupl (E₂ ρ) Φexp
          (asExpr (execN n ρ))
          (limExecV ⟨e₁', σ₂'⟩)) :
    AddCoupl ε Φexp
      (asExpr ((primStep ⟨e₁, σ₁⟩).bind (execN n)))
      (limExecV ⟨e₁', σ₁'⟩) := by
  -- Rewrite the RHS via `hErase₁'`:
  --   `(limExec ⟨e₁', σ₁'⟩).map (·.expr) = (μ₁'.bind (limExec ⟨e₁', ·⟩)).map (·.expr)`.
  rw [← hErase₁'.lim_exec e₁']
  unfold asExpr
  -- Push `.map (·.expr)` through both outer binds.
  rw [Measure.bind_map_comm, Measure.bind_map_comm]
  -- Sub-probability of inner `execN n ρ` projected kernels.
  have hmassk : ∀ ρ : (Cfg rT), (execN n ρ).map (·.expr) Set.univ ≤ 1 := by
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
    (Hbind := fun {ρ σ₂'} hR => by
      have := hCont ρ σ₂' hR
      unfold asExpr limExecV asExpr at this
      exact this)
  exact AddCoupl.mono_grading hEpsSum hBind

/-- **Clutch `ARcoupl_erasure_erasable_exp_lhs_kanto`, reformulated (projected form).**

Kantorovich-style LHS variant. The slack `E₂ : (Cfg rT) → (Cfg rT) → ENNReal` depends
on both the LHS and RHS samples, and the wrapper takes a higher-order
test-function expectation-bound hypothesis (`hExp`): for every pair of
`[0,1]`-bounded measurable `h₁, h₂` with `h₁ ρ ≤ h₂ ρ' + E₂ ρ ρ'`,
`∫⁻ h₁ ∂(primStep ⟨e₁,σ₁⟩) ≤ ∫⁻ h₂ ∂(μ₁'.bind (pexecN m ⟨e₁', ·⟩)) + ε`.

The conclusion operates on the LHS *after* one `primStep` bind — i.e. on
`(primStep ⟨e₁,σ₁⟩ >>= execN n).map (·.expr)` — matching `execN (n+1)` for
non-value `e₁` via `execN_succ_not_isValue`. -/
theorem AddCoupl_erasure_erasable_exp_lhs_kanto [Countable rT] [MeasurableSingletonClass rT]
    {e₁ e₁' : (Exp rT)} {σ₁ σ₁' : (State rT)}
    {μ₁' : Measure (State rT)} {Φexp : Set ((Exp rT) × (Exp rT))}
    {ε : ENNReal} {E₂ : (Cfg rT) → (Cfg rT) → ENNReal}
    {n m : Nat}
    (hErase₁' : ErasableExpr μ₁' σ₁')
    (hExp : ∀ (h₁ h₂ : (Cfg rT) → ENNReal),
        (∀ ρ, h₁ ρ ≤ 1) → (∀ ρ, h₂ ρ ≤ 1) →
        (∀ ρ ρ', h₁ ρ ≤ h₂ ρ' + E₂ ρ ρ') →
        ∫⁻ ρ, h₁ ρ ∂(primStep ⟨e₁, σ₁⟩) ≤
          ∫⁻ ρ', h₂ ρ' ∂(μ₁'.bind (fun σ => pexecN m ⟨e₁', σ⟩)) + ε)
    (hCont : ∀ ρ ρ',
        AddCoupl (E₂ ρ ρ') Φexp
          (asExpr (execN n ρ))
          (limExecV ρ')) :
    AddCoupl ε Φexp
      (asExpr ((primStep ⟨e₁, σ₁⟩).bind (execN n)))
      (limExecV ⟨e₁', σ₁'⟩) := by
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
  unfold asExpr
  -- Push `.map (·.expr)` through both outer binds.
  rw [Measure.bind_map_comm, Measure.bind_map_comm]
  -- Subprobability of inner kernels.
  have hmassk_L : ∀ ρ : (Cfg rT), (execN n ρ).map (·.expr) Set.univ ≤ 1 := by
    intro ρ
    rw [Measure.map_apply Measurable.of_discrete MeasurableSet.univ]
    simpa using execN_univ_le_one n ρ
  have hmassk_R : ∀ ρ' : (Cfg rT), (limExec ρ').map (·.expr) Set.univ ≤ 1 := by
    intro ρ'
    rw [Measure.map_apply Measurable.of_discrete MeasurableSet.univ]
    simpa using limExec_leq_mass (r := 1) (fun n => execN_univ_le_one n ρ')
  -- Apply `bind_adv_kanto`. Test-function measurability is automatic on (Cfg rT)
  -- (discrete space) via `Measurable.of_discrete`.
  exact AddCoupl.bind_adv_kanto
    (Hfm := Measurable.of_discrete) (Hgm := Measurable.of_discrete)
    (Hfsprob := hmassk_L) (Hgsprob := hmassk_R)
    (Hexp := fun h₁ h₂ _ _ => hExp h₁ h₂)
    (Hcont := fun ρ ρ' => by
      have := hCont ρ ρ'
      unfold asExpr limExecV asExpr at this
      exact this)

end ProbLang
