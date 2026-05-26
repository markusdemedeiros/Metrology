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

@[fun_prop]
theorem measurable_some [MeasurableSpace α] : Measurable (Option.some : α → _) := by
  refine measurable_comap_iff.mpr ?_
  unfold Function.comp
  simp [Equiv.optionEquivSumPUnit]
  fun_prop

/-! ### Option-cylinders and their measurable-leaf generator system. -/

/-- `some : α → Option α` is a measurable embedding. -/
theorem MeasurableEmbedding.some_mk {α : Type _} [MeasurableSpace α] :
    MeasurableEmbedding (some : α → Option α) := by
  refine ⟨Option.some_injective _, measurable_some, fun s hs =>
    ⟨Sum.inl '' s, MeasurableSet.inl_image hs, ?_⟩⟩
  ext x; cases x <;> simp

/-- `some '' S` is measurable when `S` is. -/
@[measurability]
theorem MeasurableSet.image_some {α : Type _} [MeasurableSpace α] {S : Set α}
    (hS : MeasurableSet S) : MeasurableSet ((some : α → Option α) '' S) :=
  MeasurableEmbedding.some_mk.measurableSet_image' hS

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

/-- Image of `Set.univ` under `some : α → Option α` is the complement of `{none}`. -/
theorem Set.image_univ_some {α : Type _} :
    (some : α → Option α) '' Set.univ = ({none} : Set (Option α))ᶜ := by
  rw [Set.image_univ, ← Set.compl_range_some, compl_compl]

/-- Image of a complement under `some`: `some '' Gᶜ = {none}ᶜ \ some '' G`.
Used in the compl-case of σ-algebra induction over `Option α`-valued projections. -/
theorem Set.image_compl_some {α : Type _} (G : Set α) :
    (some : α → Option α) '' Gᶜ
      = ({none} : Set (Option α))ᶜ \ (some '' G) := by
  rw [← Set.image_univ_some, Set.compl_eq_univ_diff,
      Set.image_diff (Option.some_injective α)]

/-- `{none} ⊆ Option α` is measurable. -/
@[measurability]
theorem MeasurableSet.singleton_none {α : Type _} [MeasurableSpace α] :
    MeasurableSet ({none} : Set (Option α)) := by
  refine ⟨Sum.inr '' Set.univ, MeasurableSet.inr_image MeasurableSet.univ, ?_⟩
  ext x; cases x <;> simp

/-- `Option.getD · d` is measurable for any default value. -/
@[measurability]
theorem Option.measurable_getD {α : Type _} [MeasurableSpace α] (d : α) :
    Measurable (fun x : Option α => x.getD d) := by
  intro S hS
  have heq : (fun x : Option α => x.getD d) ⁻¹' S
       = (some '' S) ∪ (if d ∈ S then ({none} : Set (Option α)) else ∅) := by
    ext x; cases x <;> simp [Option.getD]
  rw [heq]
  refine MeasurableSet.union (MeasurableSet.image_some hS) ?_
  split_ifs
  · exact MeasurableSet.singleton_none
  · exact .empty

/-- Every Option-cylinder is measurable in the project's `Option` σ-algebra. -/
@[measurability]
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
  refine measurable_comap_iff.mpr fun T hT => ?_
  have hsome_mset := h (some (Sum.inl ⁻¹' T)) (.some (measurable_inl hT))
  -- The preimage `(Equiv ∘ f)⁻¹' T` always contains `f⁻¹' (some '' Sum.inl⁻¹' T)`, plus
  -- `f⁻¹' {none}` iff `Sum.inr ⋆ ∈ T`. Combine the two pieces; the second is empty otherwise.
  suffices h_union : (Equiv.optionEquivSumPUnit α ∘ f) ⁻¹' T
                   = f ⁻¹' OptionCyl.flatten (some (Sum.inl ⁻¹' T))
                   ∪ (if Sum.inr PUnit.unit ∈ T
                      then f ⁻¹' OptionCyl.flatten (none : OptionCyl α)
                      else ∅) by
    rw [h_union]; split_ifs
    · exact hsome_mset.union (h none .none)
    · simpa using hsome_mset
  ext x; cases hfx : f x <;> split_ifs <;> simp_all

/-- **Skeleton for `Option α`-valued measurability via cover + per-set hypothesis.**

To prove `Measurable π` where `π : β → Option α`, it suffices to provide:
  * a measurable "cover" `cov : Set β` whose complement is `π ⁻¹' {none}`, and
  * for every measurable `S : Set α`, measurability of `π ⁻¹' (some '' S)`. -/
theorem Measurable.option_of_cov
    {α β : Type _} [MeasurableSpace α] [MeasurableSpace β]
    {π : β → Option α}
    {cov : Set β}
    (h_cov_meas : MeasurableSet cov)
    (h_none : π ⁻¹' ({none} : Set (Option α)) = covᶜ)
    (h_some : ∀ S : Set α, MeasurableSet S → MeasurableSet (π ⁻¹' (some '' S))) :
    Measurable π := by
  apply Measurable.option_of_cyl_preimages
  rintro (_ | S) hc
  · change MeasurableSet (π ⁻¹' ({none} : Set (Option α)))
    rw [h_none]; exact h_cov_meas.compl
  · cases hc with
    | some hS => exact h_some _ hS

/-- **Range-as-cover rewrite for `Option`-valued projections.** If `π : β → Option α` is the
metaprogrammed inverse of an injection `c : α → β` — returning `some x` on `c x` — then
`c '' T = range c ∩ π⁻¹' (some '' T)`. -/
theorem Set.image_eq_range_inter_preimage_option
    {α β : Type _} (c : α → β) (π : β → Option α)
    (hπ : ∀ x, π (c x) = some x) (T : Set α) :
    c '' T = Set.range c ∩ π ⁻¹' (some '' T) := by
  ext b; aesop

/-- `Option.map f` pulls a `some`-image back to a `some`-image of the preimage. -/
@[simp] theorem Option.map_preimage_some {α β : Type _} (f : α → β) (S : Set β) :
    Option.map f ⁻¹' (some '' S) = some '' (f ⁻¹' S) := by
  ext x; cases x <;> simp [Option.map]

/-- `Option.map f` is measurable when `f` is. -/
@[fun_prop]
theorem Measurable.option_map {α β : Type _} [MeasurableSpace α] [MeasurableSpace β]
    {f : α → β} (hf : Measurable f) : Measurable (Option.map f) :=
  Measurable.option_of_cov
    (cov := ({none} : Set (Option α))ᶜ)
    MeasurableSet.singleton_none.compl
    (by ext x; cases x <;> simp [Option.map])
    (fun S hS => by
      simp only [Option.map_preimage_some]
      exact MeasurableEmbedding.some_mk.measurableSet_image.mpr (hf hS))

/-- Joint Option-pairing: `(none, none) ↦ none`, `(some a, some b) ↦ some (a, b)`,
mixed cases `↦ none`. -/
def Option.pair {α β : Type _} : Option α × Option β → Option (α × β)
  | (some a, some b) => some (a, b)
  | _ => none

/-- `Option.pair` pulls a `some`-image back to a `Prod.map some some`-image. -/
@[simp] theorem Option.pair_preimage_some {α β : Type _} (S : Set (α × β)) :
    Option.pair ⁻¹' (some '' S) = (Prod.map some some) '' S := by
  ext ⟨x, y⟩; cases x <;> cases y <;> simp [Option.pair, Prod.map]

/-- `Option.pair` is measurable as a function `Option α × Option β → Option (α × β)`. -/
@[fun_prop]
theorem Measurable.option_pair {α β : Type _} [MeasurableSpace α] [MeasurableSpace β] :
    Measurable (Option.pair : Option α × Option β → Option (α × β)) :=
  Measurable.option_of_cov
    (cov := ({none} : Set (Option α))ᶜ ×ˢ ({none} : Set (Option β))ᶜ)
    (MeasurableSet.singleton_none.compl.prod MeasurableSet.singleton_none.compl)
    (by ext ⟨x, y⟩; cases x <;> cases y <;> simp [Option.pair])
    (fun S hS => by
      simp only [Option.pair_preimage_some]
      exact ((MeasurableEmbedding.some_mk (α := α)).prodMap
        MeasurableEmbedding.some_mk).measurableSet_image.mpr hS)

/-! ### Generic σ-algebra induction for cover-restricted measurability. -/

/-- **Generic σ-algebra induction for cover-restricted measurability.**

If the target's σ-algebra is `generateFrom 𝒞`, and `cov ∩ f⁻¹' G` is measurable for every
generator `G ∈ 𝒞`, then the same holds for every measurable `G`. The σ-algebra induction
threads `cov ∩ _` through the lattice operations. -/
theorem MeasurableSet.cover_inter_preimage_of_gen
    {α β : Type _} [MeasurableSpace α] [mβ : MeasurableSpace β]
    {𝒞 : Set (Set β)} (hβ : mβ = MeasurableSpace.generateFrom 𝒞)
    {cov : Set α} (hcov : MeasurableSet cov) (f : α → β)
    (hgen : ∀ G ∈ 𝒞, MeasurableSet (cov ∩ f ⁻¹' G)) :
    ∀ G : Set β, MeasurableSet G → MeasurableSet (cov ∩ f ⁻¹' G) := by
  intro G hG
  rw [hβ] at hG
  induction hG with
  | basic G' hG' => exact hgen G' hG'
  | empty => simp
  | compl G' _ ih =>
    rw [Set.preimage_compl, ← Set.diff_eq, ← Set.diff_self_inter]
    exact hcov.diff ih
  | iUnion G' _ ih =>
    rw [Set.preimage_iUnion, Set.inter_iUnion]
    exact .iUnion ih

private theorem subtype_preimage_eq {α β : Type _} {cov : Set α} (f : α → β) (G : Set β) :
    (fun (b : ↥cov) => f b.val) ⁻¹' G = (Subtype.val : ↥cov → α) ⁻¹' (cov ∩ f ⁻¹' G) := by
  ext ⟨b, hb⟩; simp

/-- **Subtype-restricted measurability from cover-restricted measurability.**

If `cov ⊆ α` is measurable and `cov ∩ f⁻¹' G` is measurable for every measurable `G ⊆ β`,
then the subtype-restricted function `↥cov → β` is measurable. -/
theorem Measurable.of_cover_inter_preimage
    {α β : Type _} [MeasurableSpace α] [MeasurableSpace β]
    {cov : Set α} {f : α → β}
    (h : ∀ G : Set β, MeasurableSet G → MeasurableSet (cov ∩ f ⁻¹' G)) :
    Measurable (fun (b : ↥cov) => f b.val) := fun G hG => by
  rw [subtype_preimage_eq]
  exact MeasurableSet.preimage (h G hG) measurable_subtype_coe

/-- **Cover-restricted measurability from subtype-restricted measurability** (the converse). -/
theorem MeasurableSet.cover_inter_preimage_of_subtype
    {α β : Type _} [MeasurableSpace α] [MeasurableSpace β]
    {cov : Set α} (hcov : MeasurableSet cov) {f : α → β}
    (h : Measurable (fun (b : ↥cov) => f b.val)) :
    ∀ G : Set β, MeasurableSet G → MeasurableSet (cov ∩ f ⁻¹' G) := fun G hG => by
  rw [← Set.inter_self cov, Set.inter_assoc, ← Subtype.image_preimage_coe]
  exact MeasurableSet.subtype_image hcov ((subtype_preimage_eq f G) ▸ h hG)

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

/-! ### Building `MeasurableEmbedding` from a π-system of rectangles.

For an n-ary function `f : X₁ × ⋯ × Xₙ → Z`, given (i) injectivity, (ii) measurability,
(iii) a π-system on each factor whose product rectangles generate the product σ-algebra,
(iv) measurability of `f` on a basic rectangle, and (v) a measurable cover of `Set.range f`,
we get `MeasurableEmbedding f`. Each higher-arity version reduces to the binary one by
nesting rectangles on the right. -/

/-- Binary version. -/
theorem measurableEmbedding_of_piSystem₂
    {X Y Z : Type*} [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]
    {f : X × Y → Z} (h_inj : Function.Injective f) (h_meas : Measurable f)
    {𝓒₁ : Set (Set X)} {𝓒₂ : Set (Set Y)}
    (h_gen : (Prod.instMeasurableSpace : MeasurableSpace (X × Y))
              = MeasurableSpace.generateFrom (Set.image2 (· ×ˢ ·) 𝓒₁ 𝓒₂))
    (h_pi : IsPiSystem (Set.image2 (· ×ˢ ·) 𝓒₁ 𝓒₂))
    (h_basic : ∀ ⦃A⦄, A ∈ 𝓒₁ → ∀ ⦃B⦄, B ∈ 𝓒₂ → MeasurableSet (f '' (A ×ˢ B)))
    {cov : Set Z} (h_cov_meas : MeasurableSet cov) (h_cov_range : cov = .range f) :
    MeasurableEmbedding f := by
  refine ⟨h_inj, h_meas, fun S hS => ?_⟩
  refine MeasurableSpace.induction_on_inter (C := fun S _ => MeasurableSet (f '' S))
      h_gen h_pi ?_ ?_ ?_ ?_ S hS
  · simp
  · rintro _ ⟨_, hA, _, hB, rfl⟩; exact h_basic hA hB
  · intro T _ ih
    rw [Set.compl_eq_univ_diff, Set.image_diff h_inj, Set.image_univ, ← h_cov_range]
    exact h_cov_meas.diff ih
  · intro f _ _ ih
    rw [Set.image_iUnion]
    exact .iUnion ih

/-- Ternary version: reduces to binary by treating `Y × Z` as a single factor. -/
theorem measurableEmbedding_of_piSystem₃
    {X₁ X₂ X₃ Z : Type*} [MeasurableSpace X₁] [MeasurableSpace X₂] [MeasurableSpace X₃]
    [MeasurableSpace Z]
    {f : X₁ × X₂ × X₃ → Z} (h_inj : Function.Injective f) (h_meas : Measurable f)
    {𝓒₁ : Set (Set X₁)} {𝓒₂ : Set (Set X₂)} {𝓒₃ : Set (Set X₃)}
    (h_gen : (Prod.instMeasurableSpace : MeasurableSpace (X₁ × X₂ × X₃))
              = MeasurableSpace.generateFrom
                  (Set.image2 (· ×ˢ ·) 𝓒₁ (Set.image2 (· ×ˢ ·) 𝓒₂ 𝓒₃)))
    (h_pi : IsPiSystem (Set.image2 (· ×ˢ ·) 𝓒₁ (Set.image2 (· ×ˢ ·) 𝓒₂ 𝓒₃)))
    (h_basic : ∀ ⦃A₁⦄, A₁ ∈ 𝓒₁ → ∀ ⦃A₂⦄, A₂ ∈ 𝓒₂ → ∀ ⦃A₃⦄, A₃ ∈ 𝓒₃ →
                MeasurableSet (f '' (A₁ ×ˢ A₂ ×ˢ A₃)))
    {cov : Set Z} (h_cov_meas : MeasurableSet cov) (h_cov_range : cov = .range f) :
    MeasurableEmbedding f :=
  measurableEmbedding_of_piSystem₂ (f := f) h_inj h_meas h_gen h_pi
    (fun _ hA₁ _ hRest => by
      obtain ⟨_, hA₂, _, hA₃, rfl⟩ := hRest
      exact h_basic hA₁ hA₂ hA₃)
    h_cov_meas h_cov_range

/-- 4-ary version: reduces to ternary by destructuring the right-nested rectangle. -/
theorem measurableEmbedding_of_piSystem₄
    {X₁ X₂ X₃ X₄ Z : Type*}
    [MeasurableSpace X₁] [MeasurableSpace X₂] [MeasurableSpace X₃] [MeasurableSpace X₄]
    [MeasurableSpace Z]
    {f : X₁ × X₂ × X₃ × X₄ → Z} (h_inj : Function.Injective f) (h_meas : Measurable f)
    {𝓒₁ : Set (Set X₁)} {𝓒₂ : Set (Set X₂)} {𝓒₃ : Set (Set X₃)} {𝓒₄ : Set (Set X₄)}
    (h_gen : (Prod.instMeasurableSpace : MeasurableSpace (X₁ × X₂ × X₃ × X₄))
              = MeasurableSpace.generateFrom
                  (Set.image2 (· ×ˢ ·) 𝓒₁
                    (Set.image2 (· ×ˢ ·) 𝓒₂ (Set.image2 (· ×ˢ ·) 𝓒₃ 𝓒₄))))
    (h_pi : IsPiSystem
              (Set.image2 (· ×ˢ ·) 𝓒₁
                (Set.image2 (· ×ˢ ·) 𝓒₂ (Set.image2 (· ×ˢ ·) 𝓒₃ 𝓒₄))))
    (h_basic : ∀ ⦃A₁⦄, A₁ ∈ 𝓒₁ → ∀ ⦃A₂⦄, A₂ ∈ 𝓒₂ → ∀ ⦃A₃⦄, A₃ ∈ 𝓒₃ → ∀ ⦃A₄⦄, A₄ ∈ 𝓒₄ →
                MeasurableSet (f '' (A₁ ×ˢ A₂ ×ˢ A₃ ×ˢ A₄)))
    {cov : Set Z} (h_cov_meas : MeasurableSet cov) (h_cov_range : cov = .range f) :
    MeasurableEmbedding f :=
  measurableEmbedding_of_piSystem₂ (f := f) h_inj h_meas h_gen h_pi
    (fun _ hA₁ _ hRest => by
      obtain ⟨_, hA₂, _, hRest', rfl⟩ := hRest
      obtain ⟨_, hA₃, _, hA₄, rfl⟩ := hRest'
      exact h_basic hA₁ hA₂ hA₃ hA₄)
    h_cov_meas h_cov_range

/-- 5-ary version. -/
theorem measurableEmbedding_of_piSystem₅
    {X₁ X₂ X₃ X₄ X₅ Z : Type*}
    [MeasurableSpace X₁] [MeasurableSpace X₂] [MeasurableSpace X₃] [MeasurableSpace X₄]
    [MeasurableSpace X₅] [MeasurableSpace Z]
    {f : X₁ × X₂ × X₃ × X₄ × X₅ → Z}
    (h_inj : Function.Injective f) (h_meas : Measurable f)
    {𝓒₁ : Set (Set X₁)} {𝓒₂ : Set (Set X₂)} {𝓒₃ : Set (Set X₃)} {𝓒₄ : Set (Set X₄)}
    {𝓒₅ : Set (Set X₅)}
    (h_gen : (Prod.instMeasurableSpace : MeasurableSpace (X₁ × X₂ × X₃ × X₄ × X₅))
              = MeasurableSpace.generateFrom
                  (Set.image2 (· ×ˢ ·) 𝓒₁
                    (Set.image2 (· ×ˢ ·) 𝓒₂
                      (Set.image2 (· ×ˢ ·) 𝓒₃ (Set.image2 (· ×ˢ ·) 𝓒₄ 𝓒₅)))))
    (h_pi : IsPiSystem
              (Set.image2 (· ×ˢ ·) 𝓒₁
                (Set.image2 (· ×ˢ ·) 𝓒₂
                  (Set.image2 (· ×ˢ ·) 𝓒₃ (Set.image2 (· ×ˢ ·) 𝓒₄ 𝓒₅)))))
    (h_basic : ∀ ⦃A₁⦄, A₁ ∈ 𝓒₁ → ∀ ⦃A₂⦄, A₂ ∈ 𝓒₂ → ∀ ⦃A₃⦄, A₃ ∈ 𝓒₃ →
                ∀ ⦃A₄⦄, A₄ ∈ 𝓒₄ → ∀ ⦃A₅⦄, A₅ ∈ 𝓒₅ →
                MeasurableSet (f '' (A₁ ×ˢ A₂ ×ˢ A₃ ×ˢ A₄ ×ˢ A₅)))
    {cov : Set Z} (h_cov_meas : MeasurableSet cov) (h_cov_range : cov = .range f) :
    MeasurableEmbedding f :=
  measurableEmbedding_of_piSystem₂ (f := f) h_inj h_meas h_gen h_pi
    (fun _ hA₁ _ hR => by
      obtain ⟨_, hA₂, _, hR', rfl⟩ := hR
      obtain ⟨_, hA₃, _, hR'', rfl⟩ := hR'
      obtain ⟨_, hA₄, _, hA₅, rfl⟩ := hR''
      exact h_basic hA₁ hA₂ hA₃ hA₄ hA₅)
    h_cov_meas h_cov_range
