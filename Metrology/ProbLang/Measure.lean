module

public import Mathlib.MeasureTheory.MeasurableSpace.Defs
public import Mathlib.Probability.ProbabilityMassFunction.Basic
public import Mathlib.Probability.Kernel.Defs
public import Mathlib.Probability.Distributions.Uniform

@[expose] public section

noncomputable section
open Classical MeasureTheory ProbabilityTheory Measure

instance [MeasurableSpace α] : MeasurableSpace (Option α) :=
  MeasurableSpace.comap (Equiv.optionEquivSumPUnit.{0, _} α) inferInstance

theorem measurable_some [MeasurableSpace α] : Measurable (Option.some : α → _) := by
  refine measurable_comap_iff.mpr ?_
  unfold Function.comp
  simp [Equiv.optionEquivSumPUnit]
  fun_prop

/-! ### Option-cylinders and their measurable-leaf generator system. -/

/-- `some : α → Option α` is a measurable embedding. -/
theorem MeasurableEmbedding.some_mk {α : Type _} [MeasurableSpace α] :
    MeasurableEmbedding (some : α → Option α) := by
  refine ⟨Option.some_injective _, measurable_some, ?_⟩
  intro s hs
  refine ⟨Sum.inl '' s, ?_, ?_⟩
  · exact MeasurableSet.inl_image hs
  · ext x; cases x with
    | none => simp [Equiv.optionEquivSumPUnit]
    | some a => simp [Equiv.optionEquivSumPUnit]

/-- A cylinder for `Option α`: either `none` or `some` of a `Set α`. -/
abbrev OptionCyl (α : Type _) := Option (Set α)

/-- Interpret an Option-cylinder as a subset of `Option α`. -/
@[simp] def OptionCyl.flatten {α : Type _} : OptionCyl α → Set (Option α)
  | none => {none}
  | some S => some '' S

/-- An Option-cylinder has measurable leaves iff its `Set α` payload (when present) is measurable. -/
inductive OptionCyl.HasMeasurableLeaves {α : Type _} [MeasurableSpace α] : OptionCyl α → Prop
  | none : HasMeasurableLeaves none
  | some {S : Set α} : MeasurableSet S → HasMeasurableLeaves (some S)

/-- `{none} ⊆ Option α` is measurable. -/
theorem MeasurableSet.singleton_none {α : Type _} [MeasurableSpace α] :
    MeasurableSet ({none} : Set (Option α)) := by
  refine ⟨Sum.inr '' Set.univ, MeasurableSet.inr_image MeasurableSet.univ, ?_⟩
  ext x; cases x with
  | none => simp [Equiv.optionEquivSumPUnit]
  | some a => simp [Equiv.optionEquivSumPUnit]

/-- Every Option-cylinder is measurable in the project's `Option` σ-algebra. -/
theorem OptionCyl.flatten_measurable {α : Type _} [MeasurableSpace α]
    {c : OptionCyl α} (hc : c.HasMeasurableLeaves) :
    MeasurableSet (OptionCyl.flatten c) := by
  cases hc with
  | none => exact MeasurableSet.singleton_none
  | @some S hS => exact MeasurableEmbedding.some_mk.measurableSet_image.mpr hS

/-- **Measurability via Option-cylinder generators.** To prove `Measurable (f : X → Option α)`,
it suffices to check preimages of Option-cylinders (`{none}` and `some '' M` for measurable `M`). -/
theorem Measurable.option_of_cyl_preimages
    {X α : Type _} [MeasurableSpace X] [MeasurableSpace α]
    (f : X → Option α)
    (h : ∀ c : OptionCyl α, c.HasMeasurableLeaves → MeasurableSet (f ⁻¹' OptionCyl.flatten c)) :
    Measurable f := by
  refine measurable_comap_iff.mpr ?_
  intro T hT
  have hA : MeasurableSet (Sum.inl ⁻¹' T : Set α) := measurable_inl hT
  have hnone_mset := h none .none
  have hsome_mset := h (some (Sum.inl ⁻¹' T)) (.some hA)
  by_cases hnone : Sum.inr PUnit.unit ∈ T
  · have hrw : (Equiv.optionEquivSumPUnit α ∘ f) ⁻¹' T
             = (f ⁻¹' OptionCyl.flatten (some (Sum.inl ⁻¹' T)))
             ∪ (f ⁻¹' OptionCyl.flatten (none : OptionCyl α)) := by
      ext x
      simp only [Function.comp_apply, Set.mem_preimage, Set.mem_union, OptionCyl.flatten,
                 Set.mem_image, Set.mem_singleton_iff]
      generalize hfx : f x = fx
      cases fx with
      | none =>
        constructor
        · intro _; right; rfl
        · intro _; exact hnone
      | some a =>
        change Sum.inl a ∈ T ↔ _
        constructor
        · intro hT'; left; exact ⟨a, hT', rfl⟩
        · rintro (⟨a', ha', heq⟩ | hcontr)
          · rw [Option.some_inj] at heq; subst heq; exact ha'
          · exact absurd hcontr (Option.some_ne_none _)
    rw [hrw]; exact hsome_mset.union hnone_mset
  · have hrw : (Equiv.optionEquivSumPUnit α ∘ f) ⁻¹' T
             = f ⁻¹' OptionCyl.flatten (some (Sum.inl ⁻¹' T)) := by
      ext x
      simp only [Function.comp_apply, Set.mem_preimage, OptionCyl.flatten, Set.mem_image]
      generalize hfx : f x = fx
      cases fx with
      | none =>
        change Sum.inr PUnit.unit ∈ T ↔ _
        constructor
        · intro hcontr; exact absurd hcontr hnone
        · rintro ⟨_, _, hcontr⟩; exact absurd hcontr (Option.some_ne_none _)
      | some a =>
        change Sum.inl a ∈ T ↔ _
        constructor
        · intro hT'; exact ⟨a, hT', rfl⟩
        · rintro ⟨a', ha', heq⟩; rw [Option.some_inj] at heq; subst heq; exact ha'
    rw [hrw]; exact hsome_mset

/-- **Range-as-cover rewrite for `Option`-valued projections.** If `π : β → Option α` is the
metaprogrammed inverse of an injection `c : α → β` — returning `some x` on `c x` — then
`c '' T = range c ∩ π⁻¹' (some '' T)`. -/
theorem Set.image_eq_range_inter_preimage_option
    {α β : Type _} (c : α → β) (π : β → Option α)
    (hπ : ∀ x, π (c x) = some x) (T : Set α) :
    c '' T = Set.range c ∩ π ⁻¹' (some '' T) := by
  ext b
  simp only [Set.mem_image, Set.mem_inter_iff, Set.mem_preimage, Set.mem_range]
  constructor
  · rintro ⟨x, hT, rfl⟩
    refine ⟨⟨x, rfl⟩, ?_⟩
    rw [hπ]; exact ⟨x, hT, rfl⟩
  · rintro ⟨⟨x, rfl⟩, hπx⟩
    rw [hπ] at hπx
    obtain ⟨a, ha, hsome⟩ := hπx
    rw [Option.some_inj] at hsome
    exact ⟨a, ha, by rw [hsome]⟩

/-- `Option.map f` is measurable when `f` is. -/
theorem Measurable.option_map {α β : Type _} [MeasurableSpace α] [MeasurableSpace β]
    {f : α → β} (hf : Measurable f) : Measurable (Option.map f) := by
  apply Measurable.option_of_cyl_preimages
  rintro (_ | S) hc
  · have hrw : (Option.map f) ⁻¹' (OptionCyl.flatten (none : OptionCyl β))
             = ({none} : Set (Option α)) := by
      ext x
      simp only [OptionCyl.flatten, Set.mem_preimage, Set.mem_singleton_iff]
      cases x with
      | none => simp [Option.map]
      | some a => simp [Option.map]
    rw [hrw]; exact MeasurableSet.singleton_none
  · cases hc with
    | some hS =>
      have hrw : (Option.map f) ⁻¹' (OptionCyl.flatten (some S))
               = some '' (f ⁻¹' S) := by
        ext x
        simp only [OptionCyl.flatten, Set.mem_preimage, Set.mem_image]
        cases x with
        | none =>
          simp only [Option.map]
          refine ⟨?_, ?_⟩
          · rintro ⟨a, _, hcontr⟩; exact absurd hcontr (Option.some_ne_none _)
          · rintro ⟨a, _, hcontr⟩; exact absurd hcontr (Option.some_ne_none _)
        | some a =>
          simp only [Option.map]
          constructor
          · rintro ⟨b, hb, heq⟩
            rw [Option.some_inj] at heq
            refine ⟨a, ?_, rfl⟩
            rw [← heq]; exact hb
          · rintro ⟨a', ha', heq⟩
            rw [Option.some_inj] at heq
            refine ⟨f a', ha', ?_⟩
            rw [heq]
      rw [hrw]
      exact MeasurableEmbedding.some_mk.measurableSet_image.mpr (hf hS)

/-- Joint Option-pairing: `(none, none) ↦ none`, `(some a, some b) ↦ some (a, b)`,
mixed cases `↦ none`. -/
def Option.pair {α β : Type _} : Option α × Option β → Option (α × β)
  | (some a, some b) => some (a, b)
  | _ => none

/-- `Option.pair` is measurable as a function `Option α × Option β → Option (α × β)`. -/
theorem Measurable.option_pair {α β : Type _} [MeasurableSpace α] [MeasurableSpace β] :
    Measurable (Option.pair : Option α × Option β → Option (α × β)) := by
  apply Measurable.option_of_cyl_preimages
  rintro (_ | S) hc
  · have hrw : (Option.pair : Option α × Option β → Option (α × β)) ⁻¹'
                  OptionCyl.flatten (none : OptionCyl (α × β))
             = ({none} ×ˢ (Set.univ : Set (Option β))) ∪
               ((Set.univ : Set (Option α)) ×ˢ {none}) := by
      ext ⟨x, y⟩
      simp only [OptionCyl.flatten, Set.mem_preimage, Set.mem_singleton_iff,
                 Set.mem_union, Set.mem_prod, Set.mem_univ]
      cases x with
      | none => simp [Option.pair]
      | some a =>
        cases y with
        | none => simp [Option.pair]
        | some b => simp [Option.pair]
    rw [hrw]
    refine MeasurableSet.union ?_ ?_
    · exact (MeasurableSet.singleton_none).prod MeasurableSet.univ
    · exact MeasurableSet.univ.prod (MeasurableSet.singleton_none)
  · cases hc with
    | some hS =>
      have hrw : (Option.pair : Option α × Option β → Option (α × β)) ⁻¹' (some '' S)
               = (Prod.map (some : α → Option α) (some : β → Option β)) '' S := by
        ext ⟨x, y⟩
        cases x with
        | none =>
          constructor
          · intro h
            simp only [Set.mem_preimage, OptionCyl.flatten, Set.mem_image] at h
            obtain ⟨a, _, heq⟩ := h
            exact absurd heq (Option.some_ne_none _)
          · intro h
            obtain ⟨⟨a, b⟩, _, heq⟩ := h
            exfalso
            have := congrArg Prod.fst heq
            simp [Prod.map] at this
        | some a =>
          cases y with
          | none =>
            constructor
            · intro h
              simp only [Set.mem_preimage, OptionCyl.flatten, Set.mem_image] at h
              obtain ⟨a', _, heq⟩ := h
              exact absurd heq (Option.some_ne_none _)
            · intro h
              obtain ⟨⟨a', b'⟩, _, heq⟩ := h
              exfalso
              have := congrArg Prod.snd heq
              simp [Prod.map] at this
          | some b =>
            simp only [Set.mem_preimage, OptionCyl.flatten, Set.mem_image]
            show Option.pair (some a, some b) ∈ some '' S ↔ _
            show some (a, b) ∈ some '' S ↔ ∃ p ∈ S, Prod.map some some p = (some a, some b)
            constructor
            · rintro ⟨p, hin, heq⟩
              obtain ⟨a', b'⟩ := p
              rw [Option.some_inj] at heq
              obtain ⟨rfl, rfl⟩ := heq
              refine ⟨(a, b), hin, rfl⟩
            · rintro ⟨p, hin, heq⟩
              obtain ⟨a', b'⟩ := p
              show some (a, b) ∈ some '' S
              refine ⟨(a', b'), hin, ?_⟩
              show some (a', b') = some (a, b)
              have h1 : some a' = some a := (Prod.mk.injEq _ _ _ _).mp heq |>.1
              have h2 : some b' = some b := (Prod.mk.injEq _ _ _ _).mp heq |>.2
              rw [Option.some_inj] at h1 h2
              rw [h1, h2]
      show MeasurableSet (Option.pair ⁻¹' (some '' S))
      rw [hrw]
      have hemb : MeasurableEmbedding (Prod.map (some : α → Option α) (some : β → Option β)) :=
        (MeasurableEmbedding.some_mk).prodMap (MeasurableEmbedding.some_mk)
      exact hemb.measurableSet_image.mpr hS

theorem measure_pos_of_singleton_pos {α : Type _} [MeasurableSpace α] [MeasurableSingletonClass α]
    [Countable α] (μ : Measure α) (S : Set α) (hS : 0 < μ S) :
    ∃ x ∈ S, 0 < μ {x} := by
  by_contra! h
  have : μ (⋃ x ∈ S, {x}) = 0 :=
    (measure_biUnion_null_iff (Set.to_countable S)).mpr fun x _ =>
      nonpos_iff_eq_zero.mp (h x ‹_›)
  rw [Set.biUnion_of_singleton] at this
  exact absurd this (ne_of_gt hS)

theorem map_singleton_pos {α β : Type _}
    [MeasurableSpace α] [MeasurableSpace β]
    [DiscreteMeasurableSpace α] [DiscreteMeasurableSpace β] [Countable α]
    {f : α → β} {μ : Measure α} {b : β}
    (h : 0 < (μ.map f) {b}) :
    ∃ a, f a = b ∧ 0 < μ {a} := by
  rw [Measure.map_apply .of_discrete .of_discrete] at h
  obtain ⟨a, ha, hpos⟩ := measure_pos_of_singleton_pos μ _ h
  simp [Set.mem_preimage, Set.mem_singleton_iff] at ha
  exact ⟨a, ha, hpos⟩

theorem Measure.bind_map {α β γ : Type} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    [DiscreteMeasurableSpace β] {μ : Measure α} {f : α → β} {g : β → Measure γ}
    (hf : Measurable f) (hg : Measurable g) : g ∘ₘ (μ.map f) = (g ∘ f) ∘ₘ μ := by
  refine ext fun S HS => ?_
  unfold Measure.bind
  rw [map_map hg hf]

/-- `.map` distributes through `.bind`: mapping over a bind is a bind of maps. -/
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

abbrev count (f : α → ENNReal) [MeasurableSpace α] := Measure.count.withDensity f

theorem count_singleton [MeasurableSpace T] [MeasurableSingletonClass T]
    (f : T → ENNReal) (t : T) : count f {t} = f t := by simp
