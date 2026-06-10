module

public import Mathlib.MeasureTheory.MeasurableSpace.Defs
public import Mathlib.Probability.ProbabilityMassFunction.Basic
public import Mathlib.Probability.Kernel.Defs
public import Mathlib.Probability.Kernel.MeasurableLIntegral
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

@[deprecated "TODO: Generalize me!" (since := "2026/06/08")]
theorem measure_pos_of_singleton_pos {α : Type _} [MeasurableSpace α] [MeasurableSingletonClass α]
    [Countable α] (μ : Measure α) (S : Set α) (hS : 0 < μ S) :
    ∃ x ∈ S, 0 < μ {x} := by
  by_contra! h
  have : μ (⋃ x ∈ S, {x}) = 0 :=
    (measure_biUnion_null_iff (Set.to_countable S)).mpr fun x _ =>
      nonpos_iff_eq_zero.mp (h x ‹_›)
  rw [Set.biUnion_of_singleton] at this
  exact absurd this (ne_of_gt hS)

@[deprecated "TODO: Generalize me!" (since := "2026/06/08")]
theorem map_singleton_pos {α β : Type _}
    [MeasurableSpace α] [MeasurableSpace β]
    [DiscreteMeasurableSpace α] [DiscreteMeasurableSpace β] [Countable α]
    {f : α → β} {μ : Measure α} {b : β}
    (h : 0 < (μ.map f) {b}) :
    ∃ a, f a = b ∧ 0 < μ {a} := by
  rw [Measure.map_apply (by measurability) (by measurability)] at h
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
    (μ : Measure α) (k : α → Measure β) (f : β → γ) (Hf : Measurable f) (Hae : AEMeasurable k μ):
    (μ.bind k).map f = μ.bind (fun a => (k a).map f) := by
  refine Measure.ext fun S hS => ?_
  have H1 : MeasurableSet (f ⁻¹' S) := MeasurableSet.preimage hS Hf
  have H2 : AEMeasurable (fun a ↦ map f (k a)) μ := by
    refine Measurable.comp_aemeasurable' ?_ Hae
    exact measurable_map f Hf
  rw [Measure.map_apply Hf hS,
      Measure.bind_apply H1 Hae,
      Measure.bind_apply hS H2]
  simp_rw [Measure.map_apply Hf hS]

abbrev count (f : α → ENNReal) [MeasurableSpace α] := Measure.count.withDensity f

theorem count_singleton [MeasurableSpace T] [MeasurableSingletonClass T]
    (f : T → ENNReal) (t : T) : count f {t} = f t := by simp

/-! ### Building `MeasurableEmbedding` from a π-system of rectangles.

For an n-ary function `f : X₁ × ⋯ × Xₙ → Z`, given (i) injectivity, (ii) measurability,
(iii) a π-system on each factor whose product rectangles generate the product σ-algebra,
(iv) measurability of `f` on a basic rectangle, and (v) a measurable cover of `Set.range f`,
we get `MeasurableEmbedding f`. Each higher-arity version reduces to the binary one by
nesting rectangles on the right. -/

/-- Unary version. -/
theorem measurableEmbedding_of_piSystem₁
    {X Z : Type*} [mX : MeasurableSpace X] [MeasurableSpace Z]
    {f : X → Z} (h_inj : Function.Injective f) (h_meas : Measurable f)
    {𝓒 : Set (Set X)}
    (h_gen : mX = MeasurableSpace.generateFrom 𝓒)
    (h_pi : IsPiSystem 𝓒)
    (h_basic : ∀ ⦃A⦄, A ∈ 𝓒 → MeasurableSet (f '' A))
    {cov : Set Z} (h_cov_meas : MeasurableSet cov) (h_cov_range : cov = .range f) :
    MeasurableEmbedding f := by
  refine ⟨h_inj, h_meas, fun S hS => ?_⟩
  refine MeasurableSpace.induction_on_inter (C := fun S _ => MeasurableSet (f '' S))
      h_gen h_pi ?_ h_basic ?_ ?_ S hS
  · simp
  · intro T _ ih
    rw [Set.compl_eq_univ_diff, Set.image_diff h_inj, Set.image_univ, ← h_cov_range]
    exact h_cov_meas.diff ih
  · intro f _ _ ih
    rw [Set.image_iUnion]
    exact .iUnion ih

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

/-! ### Discrete (top σ-algebra, countable) helpers. -/

/-- Family of singletons-or-`univ` (so it always has the universe). -/
def singletonsAndUniv (X : Type*) : Set (Set X) :=
  insert Set.univ (Set.range (Singleton.singleton : X → Set X))

theorem singletonsAndUniv_isPiSystem {X : Type*} : IsPiSystem (singletonsAndUniv X) := by
  rintro A hA B hB hne
  rcases hA with rfl | ⟨a, rfl⟩ <;> rcases hB with rfl | ⟨b, rfl⟩
  · simp [singletonsAndUniv]
  · exact Or.inr ⟨b, by simp⟩
  · exact Or.inr ⟨a, by simp⟩
  · obtain ⟨x, hxa, hxb⟩ := hne
    cases hxa; cases hxb
    simp [singletonsAndUniv]

theorem singletonsAndUniv_isCountablySpanning {X : Type*} [Countable X] :
    IsCountablySpanning (singletonsAndUniv X) := by
  refine ⟨fun _ => (Set.univ : Set X), fun _ => Or.inl rfl, ?_⟩
  ext x; simp

theorem singletonsAndUniv_generateFrom {X : Type*} [Countable X] [MeasurableSpace X]
    [DiscreteMeasurableSpace X] :
    MeasurableSpace.generateFrom (singletonsAndUniv X) = (inferInstance : MeasurableSpace X) := by
  refine le_antisymm (MeasurableSpace.generateFrom_le ?_) ?_
  · rintro _ (rfl | ⟨x, rfl⟩)
    · exact MeasurableSet.univ
    · exact MeasurableSet.singleton x
  · intro S _
    have hS : S = ⋃ x ∈ S, ({x} : Set X) := by ext y; simp
    rw [hS]
    refine .biUnion S.to_countable (fun x _ => .basic _ ?_)
    exact Or.inr ⟨x, rfl⟩

/-! ### 5-ary version. -/

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

/-! ## Generic shape-stratified measurability helpers. -/

namespace StructRec

/-! The cell `{p | shape p = s ∧ f p ∈ U}` is the source-side workhorse. -/

variable {T α : Type _} [MeasurableSpace T] [MeasurableSpace α]
variable {Sh : Type _} (shape : T → Sh)
variable {f : T → α}

omit [MeasurableSpace α] in
/-- **Nullary cell**: e.g. a fixed constructor `ctor : T` with no arguments. -/
theorem cell_nullary {ctor : T} {s : Sh} {c : α} {U : Set α}
    (h_shape : ∀ p : T, shape p = s ↔ p = ctor)
    (h_eq : f ctor = c)
    (h_flat : MeasurableSet ({ctor} : Set T)) :
    MeasurableSet {p : T | shape p = s ∧ f p ∈ U} := by
  by_cases hc : c ∈ U
  · convert h_flat using 1; ext p; simp [h_shape]; rintro rfl; exact h_eq ▸ hc
  · convert MeasurableSet.empty; ext p; simp [h_shape]; rintro rfl; exact h_eq ▸ hc

/-- **Data-leaf cell**: e.g. `ctor (b : β) : T`. The cell is the image of `c ⁻¹' U`
under the constructor's measurable embedding. -/
theorem cell_dataLeaf {β : Type _} [MeasurableSpace β]
    {ctor : β → T} {s : Sh} {c : β → α} {U : Set α}
    (h_emb : MeasurableEmbedding ctor)
    (h_shape : ∀ p : T, shape p = s ↔ ∃ b, p = ctor b)
    (h_eq : ∀ b, f (ctor b) = c b)
    (h_c : Measurable c) (hU : MeasurableSet U) :
    MeasurableSet {p : T | shape p = s ∧ f p ∈ U} := by
  have : {p : T | shape p = s ∧ f p ∈ U} = ctor '' (c ⁻¹' U) := by
    ext p
    constructor
    · rintro ⟨hs, hp⟩
      obtain ⟨b, rfl⟩ := (h_shape p).mp hs
      exact ⟨b, by rw [h_eq] at hp; exact hp, rfl⟩
    · rintro ⟨b, hb, rfl⟩
      exact ⟨(h_shape _).mpr ⟨b, rfl⟩, by rw [h_eq]; exact hb⟩
  rw [this]; exact h_emb.measurableSet_image' (h_c hU)

/-- **Unary recursive cell**: e.g. `ctor (p : T) : T`. Reduces to the child cell. -/
theorem cell_unary {ctor : T → T} {s s' : Sh}
    {c : α → α} {U : Set α}
    (h_emb : MeasurableEmbedding ctor)
    (h_shape : ∀ p : T, shape p = s ↔ ∃ p', p = ctor p' ∧ shape p' = s')
    (h_eq : ∀ p, f (ctor p) = c (f p))
    (h_c : Measurable c)
    (ih : ∀ {U' : Set α}, MeasurableSet U' →
      MeasurableSet {p : T | shape p = s' ∧ f p ∈ U'})
    (hU : MeasurableSet U) :
    MeasurableSet {p : T | shape p = s ∧ f p ∈ U} := by
  have heq : {p : T | shape p = s ∧ f p ∈ U}
      = ctor '' {p : T | shape p = s' ∧ f p ∈ (c ⁻¹' U)} := by
    ext p
    constructor
    · rintro ⟨hs, hp⟩
      obtain ⟨p', rfl, hs'⟩ := (h_shape p).mp hs
      exact ⟨p', ⟨hs', by rw [h_eq] at hp; exact hp⟩, rfl⟩
    · rintro ⟨p', ⟨hs', hp'⟩, rfl⟩
      exact ⟨(h_shape _).mpr ⟨p', rfl, hs'⟩, by rw [h_eq]; exact hp'⟩
  rw [heq]; exact h_emb.measurableSet_image' (ih (h_c hU))

/-- **Binary joint-recursive cell**: e.g. `ctor (p1 p2 : T) : T`. Reduces to a
joint shape×shape×measurable-rectangle argument via π-system induction. -/
theorem cell_binary
    {ctor : T → T → T} {s s1 s2 : Sh}
    {c : α → α → α} {U : Set α}
    (h_emb : MeasurableEmbedding (Function.uncurry ctor))
    (h_shape : ∀ p : T, shape p = s ↔
      ∃ p1 p2, p = ctor p1 p2 ∧ shape p1 = s1 ∧ shape p2 = s2)
    (h_eq : ∀ p1 p2, f (ctor p1 p2) = c (f p1) (f p2))
    (h_c : Measurable (Function.uncurry c))
    (ih1 : ∀ {U' : Set α}, MeasurableSet U' →
      MeasurableSet {p : T | shape p = s1 ∧ f p ∈ U'})
    (ih2 : ∀ {U' : Set α}, MeasurableSet U' →
      MeasurableSet {p : T | shape p = s2 ∧ f p ∈ U'})
    (hU : MeasurableSet U) :
    MeasurableSet {p : T | shape p = s ∧ f p ∈ U} := by
  have heq : {p : T | shape p = s ∧ f p ∈ U}
      = (Function.uncurry ctor) ''
        {q : T × T | shape q.1 = s1 ∧ shape q.2 = s2 ∧
          Function.uncurry c (f q.1, f q.2) ∈ U} := by
    ext p
    constructor
    · rintro ⟨hs, hp⟩
      obtain ⟨p1, p2, rfl, hs1, hs2⟩ := (h_shape p).mp hs
      refine ⟨(p1, p2), ⟨hs1, hs2, ?_⟩, rfl⟩
      simp [Function.uncurry]; rw [h_eq] at hp; exact hp
    · rintro ⟨⟨p1, p2⟩, ⟨hs1, hs2, h⟩, rfl⟩
      simp [Function.uncurry] at h
      refine ⟨(h_shape _).mpr ⟨p1, p2, rfl, hs1, hs2⟩, ?_⟩
      show f (Function.uncurry ctor (p1, p2)) ∈ U
      simp [Function.uncurry]; rw [h_eq]; exact h
  rw [heq]
  refine h_emb.measurableSet_image' ?_
  set Joint : Set (α × α) → Set (T × T) :=
    fun S => {q : T × T | shape q.1 = s1 ∧ shape q.2 = s2 ∧
      (f q.1, f q.2) ∈ S} with hJoint
  suffices h : ∀ S, MeasurableSet S → MeasurableSet (Joint S) by exact h _ (h_c hU)
  intro S hS
  have hgen : (Prod.instMeasurableSpace : MeasurableSpace (α × α))
      = .generateFrom (Set.image2 (· ×ˢ ·) {S : Set α | MeasurableSet S}
                                            {S : Set α | MeasurableSet S}) :=
    generateFrom_prod.symm
  have hpi : IsPiSystem
      (Set.image2 (· ×ˢ ·) {S : Set α | MeasurableSet S} {S : Set α | MeasurableSet S}) :=
    MeasurableSpace.isPiSystem_measurableSet.prod MeasurableSpace.isPiSystem_measurableSet
  refine MeasurableSpace.induction_on_inter
    (C := fun S _ => MeasurableSet (Joint S)) hgen hpi ?_ ?_ ?_ ?_ S hS
  · show MeasurableSet (Joint ∅); convert MeasurableSet.empty; ext ⟨_, _⟩; simp [hJoint]
  · rintro _ ⟨V₁, hV₁, V₂, hV₂, rfl⟩
    show MeasurableSet (Joint (V₁ ×ˢ V₂))
    have : Joint (V₁ ×ˢ V₂)
        = {p : T | shape p = s1 ∧ f p ∈ V₁} ×ˢ
          {p : T | shape p = s2 ∧ f p ∈ V₂} := by
      ext ⟨p1, p2⟩; simp [hJoint]; tauto
    rw [this]; exact (ih1 hV₁).prod (ih2 hV₂)
  · intro S' hS'_meas IH
    show MeasurableSet (Joint S'ᶜ)
    have : Joint S'ᶜ = (({p | shape p = s1} ×ˢ {p | shape p = s2}) \ Joint S') := by
      ext ⟨p1, p2⟩; simp [hJoint]; tauto
    rw [this]
    refine MeasurableSet.diff ?_ IH
    refine MeasurableSet.prod ?_ ?_
    · simpa using ih1 MeasurableSet.univ
    · simpa using ih2 MeasurableSet.univ
  · intro F _ _ IH
    show MeasurableSet (Joint (⋃ i, F i))
    have : Joint (⋃ i, F i) = ⋃ i, Joint (F i) := by
      ext ⟨p1, p2⟩; simp only [hJoint, Set.mem_iUnion, Set.mem_setOf_eq]; tauto
    rw [this]; exact MeasurableSet.iUnion IH

/-- **Shape-partition assembly**: glues per-shape cell measurability into global
measurability of `f`. Requires `Sh` countable. -/
theorem measurable_of_cells [Countable Sh]
    (h_cell : ∀ (s : Sh) {U : Set α}, MeasurableSet U →
      MeasurableSet {p : T | shape p = s ∧ f p ∈ U}) :
    Measurable f := by
  intro S hS
  rw [show (f ⁻¹' S) = ⋃ s : Sh, {p : T | shape p = s ∧ f p ∈ S} from by
    ext p
    simp only [Set.mem_preimage, Set.mem_iUnion, Set.mem_setOf_eq]
    exact ⟨fun h => ⟨_, rfl, h⟩, fun ⟨_, _, h⟩ => h⟩]
  exact MeasurableSet.iUnion fun s => h_cell s hS

/-- **Ternary joint-recursive cell**: e.g. `cond ec et ef`. Same template as `cell_binary`
but with a 3-fold product π-system. -/
theorem cell_ternary
    {ctor : T → T → T → T} {s s1 s2 s3 : Sh}
    {c : α → α → α → α} {U : Set α}
    (h_emb : MeasurableEmbedding (fun (p : T × T × T) => ctor p.1 p.2.1 p.2.2))
    (h_shape : ∀ p : T, shape p = s ↔
      ∃ p1 p2 p3, p = ctor p1 p2 p3 ∧ shape p1 = s1 ∧ shape p2 = s2 ∧ shape p3 = s3)
    (h_eq : ∀ p1 p2 p3, f (ctor p1 p2 p3) = c (f p1) (f p2) (f p3))
    (h_c : Measurable (fun (q : α × α × α) => c q.1 q.2.1 q.2.2))
    (ih1 : ∀ {U' : Set α}, MeasurableSet U' →
      MeasurableSet {p : T | shape p = s1 ∧ f p ∈ U'})
    (ih2 : ∀ {U' : Set α}, MeasurableSet U' →
      MeasurableSet {p : T | shape p = s2 ∧ f p ∈ U'})
    (ih3 : ∀ {U' : Set α}, MeasurableSet U' →
      MeasurableSet {p : T | shape p = s3 ∧ f p ∈ U'})
    (hU : MeasurableSet U) :
    MeasurableSet {p : T | shape p = s ∧ f p ∈ U} := by
  have heq : {p : T | shape p = s ∧ f p ∈ U}
      = (fun (p : T × T × T) => ctor p.1 p.2.1 p.2.2) ''
        {q : T × T × T | shape q.1 = s1 ∧ shape q.2.1 = s2 ∧ shape q.2.2 = s3 ∧
          c (f q.1) (f q.2.1) (f q.2.2) ∈ U} := by
    ext p
    constructor
    · rintro ⟨hs, hp⟩
      obtain ⟨p1, p2, p3, rfl, hs1, hs2, hs3⟩ := (h_shape p).mp hs
      exact ⟨(p1, p2, p3), ⟨hs1, hs2, hs3, by rw [h_eq] at hp; exact hp⟩, rfl⟩
    · rintro ⟨⟨p1, p2, p3⟩, ⟨hs1, hs2, hs3, h⟩, rfl⟩
      exact ⟨(h_shape _).mpr ⟨p1, p2, p3, rfl, hs1, hs2, hs3⟩, by rw [h_eq]; exact h⟩
  rw [heq]
  refine h_emb.measurableSet_image' ?_
  set Joint : Set (α × α × α) → Set (T × T × T) :=
    fun S => {q : T × T × T | shape q.1 = s1 ∧ shape q.2.1 = s2 ∧ shape q.2.2 = s3 ∧
      (f q.1, f q.2.1, f q.2.2) ∈ S} with hJoint
  suffices h : ∀ S, MeasurableSet S → MeasurableSet (Joint S) by
    have hS : MeasurableSet ((fun (q : α × α × α) => c q.1 q.2.1 q.2.2) ⁻¹' U) := h_c hU
    convert h _ hS
  intro S hS
  -- Decompose the ternary cell into the binary cell × extra-shape-cell, then
  -- apply the cell_binary machinery twice. The codomain α × α × α is treated as
  -- α × (α × α). The Joint on this matches the iterated cell_binary structure.
  -- Two-step approach: first show measurability of the inner joint cell on α × α
  -- via cell_binary's machinery for shapes (s2, s3); then combine with shape s1
  -- and the outer measurable T.
  --
  -- The outer π-system uses pairs (V × W) where V ⊆ α measurable and W ⊆ α × α
  -- measurable. By generateFrom_prod, this generates the σ-algebra on α × (α × α).
  have hgen : (Prod.instMeasurableSpace : MeasurableSpace (α × α × α))
      = .generateFrom (Set.image2 (· ×ˢ ·) {V : Set α | MeasurableSet V}
                                            {W : Set (α × α) | MeasurableSet W}) :=
    generateFrom_prod.symm
  have hpi : IsPiSystem (Set.image2 (· ×ˢ ·) {V : Set α | MeasurableSet V}
                                              {W : Set (α × α) | MeasurableSet W}) :=
    MeasurableSpace.isPiSystem_measurableSet.prod MeasurableSpace.isPiSystem_measurableSet
  -- Helper for binary joint cell on (s2, s3): measurability over all measurable W ⊆ α × α.
  have hjoint23 : ∀ W : Set (α × α), MeasurableSet W →
      MeasurableSet {q : T × T | shape q.1 = s2 ∧ shape q.2 = s3 ∧ (f q.1, f q.2) ∈ W} := by
    intro W hW
    set J23 : Set (α × α) → Set (T × T) :=
      fun W' => {q : T × T | shape q.1 = s2 ∧ shape q.2 = s3 ∧ (f q.1, f q.2) ∈ W'}
      with hJ23
    suffices ∀ W', MeasurableSet W' → MeasurableSet (J23 W') by exact this _ hW
    intro W' hW'
    have hgen' : (Prod.instMeasurableSpace : MeasurableSpace (α × α))
        = .generateFrom (Set.image2 (· ×ˢ ·) {S : Set α | MeasurableSet S}
                                              {S : Set α | MeasurableSet S}) :=
      generateFrom_prod.symm
    have hpi' : IsPiSystem
        (Set.image2 (· ×ˢ ·) {S : Set α | MeasurableSet S} {S : Set α | MeasurableSet S}) :=
      MeasurableSpace.isPiSystem_measurableSet.prod MeasurableSpace.isPiSystem_measurableSet
    refine MeasurableSpace.induction_on_inter
      (C := fun W'' _ => MeasurableSet (J23 W'')) hgen' hpi' ?_ ?_ ?_ ?_ W' hW'
    · show MeasurableSet (J23 ∅); convert MeasurableSet.empty; ext ⟨_, _⟩; simp [hJ23]
    · rintro _ ⟨V₂, hV₂, V₃, hV₃, rfl⟩
      show MeasurableSet (J23 (V₂ ×ˢ V₃))
      have : J23 (V₂ ×ˢ V₃)
          = {p : T | shape p = s2 ∧ f p ∈ V₂} ×ˢ {p : T | shape p = s3 ∧ f p ∈ V₃} := by
        ext ⟨p2, p3⟩; simp [hJ23]; tauto
      rw [this]; exact (ih2 hV₂).prod (ih3 hV₃)
    · intro W'' _ IH
      show MeasurableSet (J23 W''ᶜ)
      have : J23 W''ᶜ = (({p | shape p = s2} ×ˢ {p | shape p = s3}) \ J23 W'') := by
        ext ⟨p2, p3⟩; simp [hJ23]; tauto
      rw [this]
      refine MeasurableSet.diff ?_ IH
      refine MeasurableSet.prod ?_ ?_
      · simpa using ih2 MeasurableSet.univ
      · simpa using ih3 MeasurableSet.univ
    · intro F _ _ IH
      show MeasurableSet (J23 (⋃ i, F i))
      have : J23 (⋃ i, F i) = ⋃ i, J23 (F i) := by
        ext ⟨p2, p3⟩; simp only [hJ23, Set.mem_iUnion, Set.mem_setOf_eq]; tauto
      rw [this]; exact MeasurableSet.iUnion IH
  -- Now the outer induction on S using rectangles V × W in α × (α × α).
  refine MeasurableSpace.induction_on_inter
    (C := fun S _ => MeasurableSet (Joint S)) hgen hpi ?_ ?_ ?_ ?_ S hS
  · show MeasurableSet (Joint ∅); convert MeasurableSet.empty; ext ⟨_, _, _⟩; simp [hJoint]
  · rintro _ ⟨V, hV, W, hW, rfl⟩
    show MeasurableSet (Joint (V ×ˢ W))
    have : Joint (V ×ˢ W)
        = {p : T | shape p = s1 ∧ f p ∈ V} ×ˢ
          {q : T × T | shape q.1 = s2 ∧ shape q.2 = s3 ∧ (f q.1, f q.2) ∈ W} := by
      ext ⟨p1, p2, p3⟩; simp [hJoint]; tauto
    rw [this]; exact (ih1 hV).prod (hjoint23 W hW)
  · intro S' _ IH
    show MeasurableSet (Joint S'ᶜ)
    have : Joint S'ᶜ
        = ({p | shape p = s1} ×ˢ {q : T × T | shape q.1 = s2 ∧ shape q.2 = s3}) \ Joint S' := by
      ext ⟨p1, p2, p3⟩; simp [hJoint]; tauto
    rw [this]
    refine MeasurableSet.diff ?_ IH
    refine MeasurableSet.prod ?_ ?_
    · simpa using ih1 MeasurableSet.univ
    · have := hjoint23 Set.univ MeasurableSet.univ
      convert this using 1
      ext ⟨p2, p3⟩; simp
  · intro F _ _ IH
    show MeasurableSet (Joint (⋃ i, F i))
    have : Joint (⋃ i, F i) = ⋃ i, Joint (F i) := by
      ext ⟨p1, p2, p3⟩; simp only [hJoint, Set.mem_iUnion, Set.mem_setOf_eq]; tauto
    rw [this]; exact MeasurableSet.iUnion IH

/-- **Quaternary joint-recursive cell** (arity-extension appendix, §21): copied from
`cell_ternary` with one extra child `s4`/`ih4`. The codomain `α × α × α × α` is treated
as `α × (α × α × α)`: the last three factors reuse the ternary inner-joint machinery,
then combine with `s1`. -/
theorem cell_quaternary
    {ctor : T → T → T → T → T} {s s1 s2 s3 s4 : Sh}
    {c : α → α → α → α → α} {U : Set α}
    (h_emb : MeasurableEmbedding (fun (p : T × T × T × T) => ctor p.1 p.2.1 p.2.2.1 p.2.2.2))
    (h_shape : ∀ p : T, shape p = s ↔
      ∃ p1 p2 p3 p4, p = ctor p1 p2 p3 p4 ∧
        shape p1 = s1 ∧ shape p2 = s2 ∧ shape p3 = s3 ∧ shape p4 = s4)
    (h_eq : ∀ p1 p2 p3 p4, f (ctor p1 p2 p3 p4) = c (f p1) (f p2) (f p3) (f p4))
    (h_c : Measurable (fun (q : α × α × α × α) => c q.1 q.2.1 q.2.2.1 q.2.2.2))
    (ih1 : ∀ {U' : Set α}, MeasurableSet U' →
      MeasurableSet {p : T | shape p = s1 ∧ f p ∈ U'})
    (ih2 : ∀ {U' : Set α}, MeasurableSet U' →
      MeasurableSet {p : T | shape p = s2 ∧ f p ∈ U'})
    (ih3 : ∀ {U' : Set α}, MeasurableSet U' →
      MeasurableSet {p : T | shape p = s3 ∧ f p ∈ U'})
    (ih4 : ∀ {U' : Set α}, MeasurableSet U' →
      MeasurableSet {p : T | shape p = s4 ∧ f p ∈ U'})
    (hU : MeasurableSet U) :
    MeasurableSet {p : T | shape p = s ∧ f p ∈ U} := by
  have heq : {p : T | shape p = s ∧ f p ∈ U}
      = (fun (p : T × T × T × T) => ctor p.1 p.2.1 p.2.2.1 p.2.2.2) ''
        {q : T × T × T × T | shape q.1 = s1 ∧ shape q.2.1 = s2 ∧ shape q.2.2.1 = s3 ∧
          shape q.2.2.2 = s4 ∧ c (f q.1) (f q.2.1) (f q.2.2.1) (f q.2.2.2) ∈ U} := by
    ext p
    constructor
    · rintro ⟨hs, hp⟩
      obtain ⟨p1, p2, p3, p4, rfl, hs1, hs2, hs3, hs4⟩ := (h_shape p).mp hs
      exact ⟨(p1, p2, p3, p4), ⟨hs1, hs2, hs3, hs4, by rw [h_eq] at hp; exact hp⟩, rfl⟩
    · rintro ⟨⟨p1, p2, p3, p4⟩, ⟨hs1, hs2, hs3, hs4, h⟩, rfl⟩
      exact ⟨(h_shape _).mpr ⟨p1, p2, p3, p4, rfl, hs1, hs2, hs3, hs4⟩, by rw [h_eq]; exact h⟩
  rw [heq]
  refine h_emb.measurableSet_image' ?_
  set Joint : Set (α × α × α × α) → Set (T × T × T × T) :=
    fun S => {q : T × T × T × T | shape q.1 = s1 ∧ shape q.2.1 = s2 ∧ shape q.2.2.1 = s3 ∧
      shape q.2.2.2 = s4 ∧ (f q.1, f q.2.1, f q.2.2.1, f q.2.2.2) ∈ S} with hJoint
  suffices h : ∀ S, MeasurableSet S → MeasurableSet (Joint S) by
    have hS : MeasurableSet ((fun (q : α × α × α × α) => c q.1 q.2.1 q.2.2.1 q.2.2.2) ⁻¹' U) :=
      h_c hU
    convert h _ hS
  intro S hS
  -- π-system on α × (α × α × α): rectangles V × W where W ⊆ α × α × α measurable.
  have hgen : (Prod.instMeasurableSpace : MeasurableSpace (α × α × α × α))
      = .generateFrom (Set.image2 (· ×ˢ ·) {V : Set α | MeasurableSet V}
                                            {W : Set (α × α × α) | MeasurableSet W}) :=
    generateFrom_prod.symm
  have hpi : IsPiSystem (Set.image2 (· ×ˢ ·) {V : Set α | MeasurableSet V}
                                              {W : Set (α × α × α) | MeasurableSet W}) :=
    MeasurableSpace.isPiSystem_measurableSet.prod MeasurableSpace.isPiSystem_measurableSet
  -- Inner ternary joint cell on (s2, s3, s4): measurability over all measurable W ⊆ α × α × α.
  have hjoint234 : ∀ W : Set (α × α × α), MeasurableSet W →
      MeasurableSet {q : T × T × T | shape q.1 = s2 ∧ shape q.2.1 = s3 ∧ shape q.2.2 = s4 ∧
        (f q.1, f q.2.1, f q.2.2) ∈ W} := by
    intro W hW
    set J234 : Set (α × α × α) → Set (T × T × T) :=
      fun W' => {q : T × T × T | shape q.1 = s2 ∧ shape q.2.1 = s3 ∧ shape q.2.2 = s4 ∧
        (f q.1, f q.2.1, f q.2.2) ∈ W'} with hJ234
    suffices ∀ W', MeasurableSet W' → MeasurableSet (J234 W') by exact this _ hW
    intro W' hW'
    have hgen' : (Prod.instMeasurableSpace : MeasurableSpace (α × α × α))
        = .generateFrom (Set.image2 (· ×ˢ ·) {V : Set α | MeasurableSet V}
                                              {W : Set (α × α) | MeasurableSet W}) :=
      generateFrom_prod.symm
    have hpi' : IsPiSystem (Set.image2 (· ×ˢ ·) {V : Set α | MeasurableSet V}
                                                {W : Set (α × α) | MeasurableSet W}) :=
      MeasurableSpace.isPiSystem_measurableSet.prod MeasurableSpace.isPiSystem_measurableSet
    -- Inner-inner helper for (s3, s4) on α × α.
    have hjoint34 : ∀ W : Set (α × α), MeasurableSet W →
        MeasurableSet {q : T × T | shape q.1 = s3 ∧ shape q.2 = s4 ∧ (f q.1, f q.2) ∈ W} := by
      intro W hW
      set J34 : Set (α × α) → Set (T × T) :=
        fun W' => {q : T × T | shape q.1 = s3 ∧ shape q.2 = s4 ∧ (f q.1, f q.2) ∈ W'} with hJ34
      suffices ∀ W', MeasurableSet W' → MeasurableSet (J34 W') by exact this _ hW
      intro W' hW'
      have hgen'' : (Prod.instMeasurableSpace : MeasurableSpace (α × α))
          = .generateFrom (Set.image2 (· ×ˢ ·) {S : Set α | MeasurableSet S}
                                                {S : Set α | MeasurableSet S}) :=
        generateFrom_prod.symm
      have hpi'' : IsPiSystem
          (Set.image2 (· ×ˢ ·) {S : Set α | MeasurableSet S} {S : Set α | MeasurableSet S}) :=
        MeasurableSpace.isPiSystem_measurableSet.prod MeasurableSpace.isPiSystem_measurableSet
      refine MeasurableSpace.induction_on_inter
        (C := fun W'' _ => MeasurableSet (J34 W'')) hgen'' hpi'' ?_ ?_ ?_ ?_ W' hW'
      · show MeasurableSet (J34 ∅); convert MeasurableSet.empty; ext ⟨_, _⟩; simp [hJ34]
      · rintro _ ⟨V₃, hV₃, V₄, hV₄, rfl⟩
        show MeasurableSet (J34 (V₃ ×ˢ V₄))
        have : J34 (V₃ ×ˢ V₄)
            = {p : T | shape p = s3 ∧ f p ∈ V₃} ×ˢ {p : T | shape p = s4 ∧ f p ∈ V₄} := by
          ext ⟨p3, p4⟩; simp [hJ34]; tauto
        rw [this]; exact (ih3 hV₃).prod (ih4 hV₄)
      · intro W'' _ IH
        show MeasurableSet (J34 W''ᶜ)
        have : J34 W''ᶜ = (({p | shape p = s3} ×ˢ {p | shape p = s4}) \ J34 W'') := by
          ext ⟨p3, p4⟩; simp [hJ34]; tauto
        rw [this]
        refine MeasurableSet.diff ?_ IH
        refine MeasurableSet.prod ?_ ?_
        · simpa using ih3 MeasurableSet.univ
        · simpa using ih4 MeasurableSet.univ
      · intro F _ _ IH
        show MeasurableSet (J34 (⋃ i, F i))
        have : J34 (⋃ i, F i) = ⋃ i, J34 (F i) := by
          ext ⟨p3, p4⟩; simp only [hJ34, Set.mem_iUnion, Set.mem_setOf_eq]; tauto
        rw [this]; exact MeasurableSet.iUnion IH
    refine MeasurableSpace.induction_on_inter
      (C := fun W'' _ => MeasurableSet (J234 W'')) hgen' hpi' ?_ ?_ ?_ ?_ W' hW'
    · show MeasurableSet (J234 ∅); convert MeasurableSet.empty; ext ⟨_, _, _⟩; simp [hJ234]
    · rintro _ ⟨V₂, hV₂, W34, hW34, rfl⟩
      show MeasurableSet (J234 (V₂ ×ˢ W34))
      have : J234 (V₂ ×ˢ W34)
          = {p : T | shape p = s2 ∧ f p ∈ V₂} ×ˢ
            {q : T × T | shape q.1 = s3 ∧ shape q.2 = s4 ∧ (f q.1, f q.2) ∈ W34} := by
        ext ⟨p2, p3, p4⟩; simp [hJ234]; tauto
      rw [this]; exact (ih2 hV₂).prod (hjoint34 W34 hW34)
    · intro W'' _ IH
      show MeasurableSet (J234 W''ᶜ)
      have : J234 W''ᶜ
          = ({p | shape p = s2} ×ˢ {q : T × T | shape q.1 = s3 ∧ shape q.2 = s4}) \ J234 W'' := by
        ext ⟨p2, p3, p4⟩; simp [hJ234]; tauto
      rw [this]
      refine MeasurableSet.diff ?_ IH
      refine MeasurableSet.prod ?_ ?_
      · simpa using ih2 MeasurableSet.univ
      · have := hjoint34 Set.univ MeasurableSet.univ
        convert this using 1
        ext ⟨p3, p4⟩; simp
    · intro F _ _ IH
      show MeasurableSet (J234 (⋃ i, F i))
      have : J234 (⋃ i, F i) = ⋃ i, J234 (F i) := by
        ext ⟨p2, p3, p4⟩; simp only [hJ234, Set.mem_iUnion, Set.mem_setOf_eq]; tauto
      rw [this]; exact MeasurableSet.iUnion IH
  -- Outer induction on S using rectangles V × W in α × (α × α × α).
  refine MeasurableSpace.induction_on_inter
    (C := fun S _ => MeasurableSet (Joint S)) hgen hpi ?_ ?_ ?_ ?_ S hS
  · show MeasurableSet (Joint ∅); convert MeasurableSet.empty; ext ⟨_, _, _, _⟩; simp [hJoint]
  · rintro _ ⟨V, hV, W, hW, rfl⟩
    show MeasurableSet (Joint (V ×ˢ W))
    have : Joint (V ×ˢ W)
        = {p : T | shape p = s1 ∧ f p ∈ V} ×ˢ
          {q : T × T × T | shape q.1 = s2 ∧ shape q.2.1 = s3 ∧ shape q.2.2 = s4 ∧
            (f q.1, f q.2.1, f q.2.2) ∈ W} := by
      ext ⟨p1, p2, p3, p4⟩; simp [hJoint]; tauto
    rw [this]; exact (ih1 hV).prod (hjoint234 W hW)
  · intro S' _ IH
    show MeasurableSet (Joint S'ᶜ)
    have : Joint S'ᶜ
        = ({p | shape p = s1} ×ˢ
            {q : T × T × T | shape q.1 = s2 ∧ shape q.2.1 = s3 ∧ shape q.2.2 = s4}) \ Joint S' := by
      ext ⟨p1, p2, p3, p4⟩; simp [hJoint]; tauto
    rw [this]
    refine MeasurableSet.diff ?_ IH
    refine MeasurableSet.prod ?_ ?_
    · simpa using ih1 MeasurableSet.univ
    · have := hjoint234 Set.univ MeasurableSet.univ
      convert this using 1
      ext ⟨p2, p3, p4⟩; simp
  · intro F _ _ IH
    show MeasurableSet (Joint (⋃ i, F i))
    have : Joint (⋃ i, F i) = ⋃ i, Joint (F i) := by
      ext ⟨p1, p2, p3, p4⟩; simp only [hJoint, Set.mem_iUnion, Set.mem_setOf_eq]; tauto
    rw [this]; exact MeasurableSet.iUnion IH

/-- **Mixed unary (discrete + recursive)**: e.g. `unop (op : UnOp) (e : Exp)`.
The discrete arg is passed through; behaves like `cell_unary` parameterized over `β`. -/
theorem cell_unaryMixed {β : Type _} [MeasurableSpace β]
    [Countable β] [MeasurableSingletonClass β]
    {ctor : β → T → T} {s : Sh} {sChild : β → Sh}
    {c : β → α → α} {U : Set α}
    (h_emb : MeasurableEmbedding (Function.uncurry ctor))
    (h_shape : ∀ p : T, shape p = s ↔ ∃ b p', p = ctor b p' ∧ shape p' = sChild b)
    (h_eq : ∀ b p, f (ctor b p) = c b (f p))
    (h_c : Measurable (Function.uncurry c))
    (ih : ∀ b {U' : Set α}, MeasurableSet U' →
      MeasurableSet {p : T | shape p = sChild b ∧ f p ∈ U'})
    (hU : MeasurableSet U) :
    MeasurableSet {p : T | shape p = s ∧ f p ∈ U} := by
  -- Split over the discrete β: union over b of ctor b '' (cell for sChild b under c b⁻¹U).
  have heq : {p : T | shape p = s ∧ f p ∈ U}
      = ⋃ b : β, ctor b '' {p' : T | shape p' = sChild b ∧ f p' ∈ (c b ⁻¹' U)} := by
    ext p
    simp only [Set.mem_iUnion, Set.mem_image, Set.mem_setOf_eq]
    constructor
    · rintro ⟨hs, hp⟩
      obtain ⟨b, p', rfl, hs'⟩ := (h_shape p).mp hs
      refine ⟨b, p', ⟨hs', ?_⟩, rfl⟩
      simp only [Set.mem_preimage]; rw [← h_eq]; exact hp
    · rintro ⟨b, p', ⟨hs', hp'⟩, rfl⟩
      refine ⟨(h_shape _).mpr ⟨b, p', rfl, hs'⟩, ?_⟩
      rw [h_eq]; exact hp'
  rw [heq]
  refine MeasurableSet.iUnion fun b => ?_
  -- For each b, ctor b is a measurable embedding (slice of Function.uncurry ctor at {b}).
  have h_emb_b : MeasurableEmbedding (ctor b) := by
    refine ⟨?_, ?_, ?_⟩
    · intro x y hxy
      have : Function.uncurry ctor (b, x) = Function.uncurry ctor (b, y) := by
        simp [Function.uncurry]; exact hxy
      have := h_emb.injective this
      exact (Prod.mk.injEq .. |>.mp this).2
    · exact h_emb.measurable.comp (by fun_prop : Measurable (fun x => (b, x)))
    · intro V hV
      have heq2 : ctor b '' V = Function.uncurry ctor '' ({b} ×ˢ V) := by
        ext y; simp [Function.uncurry]
      rw [heq2]
      exact h_emb.measurableSet_image' ((MeasurableSet.singleton b).prod hV)
  refine h_emb_b.measurableSet_image' ?_
  have h_cb : Measurable (c b) := h_c.comp (by fun_prop : Measurable (fun x => (b, x)))
  exact ih b (h_cb hU)

/-- **Mixed binary (discrete + 2 recursive)**: e.g. `binop (op : BinOp) e1 e2`.
Split over the discrete `β`, then apply the same π-system argument as `cell_binary`
fixed-`b`-fiber. -/
theorem cell_binaryMixed {β : Type _} [MeasurableSpace β]
    [Countable β] [MeasurableSingletonClass β]
    {ctor : β → T → T → T} {s : Sh} {sChild1 sChild2 : β → Sh}
    {c : β → α → α → α} {U : Set α}
    (h_emb : ∀ b, MeasurableEmbedding (Function.uncurry (ctor b)))
    (h_shape : ∀ p : T, shape p = s ↔
      ∃ b p1 p2, p = ctor b p1 p2 ∧ shape p1 = sChild1 b ∧ shape p2 = sChild2 b)
    (h_eq : ∀ b p1 p2, f (ctor b p1 p2) = c b (f p1) (f p2))
    (h_c : ∀ b, Measurable (Function.uncurry (c b)))
    (ih1 : ∀ b {U' : Set α}, MeasurableSet U' →
      MeasurableSet {p : T | shape p = sChild1 b ∧ f p ∈ U'})
    (ih2 : ∀ b {U' : Set α}, MeasurableSet U' →
      MeasurableSet {p : T | shape p = sChild2 b ∧ f p ∈ U'})
    (hU : MeasurableSet U) :
    MeasurableSet {p : T | shape p = s ∧ f p ∈ U} := by
  -- Per-b fiber: {p | shape p = s ∧ (∃ p1 p2, p = ctor b p1 p2 ∧ shapes match) ∧ f p ∈ U}
  -- = (Function.uncurry (ctor b)) '' {(p1,p2) | shape p1=sChild1 b ∧ shape p2=sChild2 b ∧
  --                                              c b (f p1) (f p2) ∈ U}
  -- For each b, this is the cell_binary cell for ctor b.
  have heq : {p : T | shape p = s ∧ f p ∈ U}
      = ⋃ b : β, (Function.uncurry (ctor b)) ''
          {q : T × T | shape q.1 = sChild1 b ∧ shape q.2 = sChild2 b ∧
            Function.uncurry (c b) (f q.1, f q.2) ∈ U} := by
    ext p
    simp only [Set.mem_iUnion, Set.mem_image, Set.mem_setOf_eq]
    constructor
    · rintro ⟨hs, hp⟩
      obtain ⟨b, p1, p2, rfl, hs1, hs2⟩ := (h_shape p).mp hs
      refine ⟨b, (p1, p2), ⟨hs1, hs2, ?_⟩, rfl⟩
      simp [Function.uncurry]; rw [h_eq] at hp; exact hp
    · rintro ⟨b, ⟨p1, p2⟩, ⟨hs1, hs2, h⟩, rfl⟩
      simp [Function.uncurry] at h
      refine ⟨(h_shape _).mpr ⟨b, p1, p2, rfl, hs1, hs2⟩, ?_⟩
      show f (Function.uncurry (ctor b) (p1, p2)) ∈ U
      simp [Function.uncurry]; rw [h_eq]; exact h
  rw [heq]
  refine MeasurableSet.iUnion fun b => ?_
  refine (h_emb b).measurableSet_image' ?_
  -- Apply the joint π-system argument for fixed b.
  set Joint : Set (α × α) → Set (T × T) :=
    fun S => {q : T × T | shape q.1 = sChild1 b ∧ shape q.2 = sChild2 b ∧
      (f q.1, f q.2) ∈ S} with hJoint
  suffices h : ∀ S, MeasurableSet S → MeasurableSet (Joint S) by exact h _ ((h_c b) hU)
  intro S hS
  have hgen : (Prod.instMeasurableSpace : MeasurableSpace (α × α))
      = .generateFrom (Set.image2 (· ×ˢ ·) {S : Set α | MeasurableSet S}
                                            {S : Set α | MeasurableSet S}) :=
    generateFrom_prod.symm
  have hpi : IsPiSystem
      (Set.image2 (· ×ˢ ·) {S : Set α | MeasurableSet S} {S : Set α | MeasurableSet S}) :=
    MeasurableSpace.isPiSystem_measurableSet.prod MeasurableSpace.isPiSystem_measurableSet
  refine MeasurableSpace.induction_on_inter
    (C := fun S _ => MeasurableSet (Joint S)) hgen hpi ?_ ?_ ?_ ?_ S hS
  · show MeasurableSet (Joint ∅); convert MeasurableSet.empty; ext ⟨_, _⟩; simp [hJoint]
  · rintro _ ⟨V₁, hV₁, V₂, hV₂, rfl⟩
    show MeasurableSet (Joint (V₁ ×ˢ V₂))
    have : Joint (V₁ ×ˢ V₂)
        = {p : T | shape p = sChild1 b ∧ f p ∈ V₁} ×ˢ
          {p : T | shape p = sChild2 b ∧ f p ∈ V₂} := by
      ext ⟨p1, p2⟩; simp [hJoint]; tauto
    rw [this]; exact ((ih1 b) hV₁).prod ((ih2 b) hV₂)
  · intro S' _ IH
    show MeasurableSet (Joint S'ᶜ)
    have : Joint S'ᶜ = (({p | shape p = sChild1 b} ×ˢ {p | shape p = sChild2 b}) \ Joint S') := by
      ext ⟨p1, p2⟩; simp [hJoint]; tauto
    rw [this]
    refine MeasurableSet.diff ?_ IH
    refine MeasurableSet.prod ?_ ?_
    · simpa using ih1 b MeasurableSet.univ
    · simpa using ih2 b MeasurableSet.univ
  · intro F _ _ IH
    show MeasurableSet (Joint (⋃ i, F i))
    have : Joint (⋃ i, F i) = ⋃ i, Joint (F i) := by
      ext ⟨p1, p2⟩; simp only [hJoint, Set.mem_iUnion, Set.mem_setOf_eq]; tauto
    rw [this]; exact MeasurableSet.iUnion IH

/-- **Recursive + foreign data leaf**: e.g. `scrut (e : Exp) (p : Pat)`. The recursive
arg has child shape `sChild`, the foreign data leaf has its own measurable space `γ`. -/
theorem cell_scrutLike {γ : Type _} [MeasurableSpace γ]
    {ctor : T → γ → T} {s sChild : Sh}
    {c : α → γ → α} {U : Set α}
    (h_emb : MeasurableEmbedding (Function.uncurry ctor))
    (h_shape : ∀ p : T, shape p = s ↔ ∃ p' g, p = ctor p' g ∧ shape p' = sChild)
    (h_eq : ∀ p' g, f (ctor p' g) = c (f p') g)
    (h_c : Measurable (Function.uncurry c))
    (ih : ∀ {U' : Set α}, MeasurableSet U' →
      MeasurableSet {p : T | shape p = sChild ∧ f p ∈ U'})
    (hU : MeasurableSet U) :
    MeasurableSet {p : T | shape p = s ∧ f p ∈ U} := by
  -- The cell is (Function.uncurry ctor) '' {(p', g) | shape p' = sChild ∧ c (f p') g ∈ U}.
  -- The joint set is reduced via π-system induction on T = c ⁻¹' U ⊆ α × γ.
  have heq : {p : T | shape p = s ∧ f p ∈ U}
      = (Function.uncurry ctor) ''
        {q : T × γ | shape q.1 = sChild ∧ Function.uncurry c (f q.1, q.2) ∈ U} := by
    ext p
    constructor
    · rintro ⟨hs, hp⟩
      obtain ⟨p', g, rfl, hs'⟩ := (h_shape p).mp hs
      refine ⟨(p', g), ⟨hs', ?_⟩, rfl⟩
      simp [Function.uncurry]; rw [h_eq] at hp; exact hp
    · rintro ⟨⟨p', g⟩, ⟨hs', h⟩, rfl⟩
      simp [Function.uncurry] at h
      refine ⟨(h_shape _).mpr ⟨p', g, rfl, hs'⟩, ?_⟩
      show f (Function.uncurry ctor (p', g)) ∈ U
      simp [Function.uncurry]; rw [h_eq]; exact h
  rw [heq]
  refine h_emb.measurableSet_image' ?_
  set Joint : Set (α × γ) → Set (T × γ) :=
    fun S => {q : T × γ | shape q.1 = sChild ∧ (f q.1, q.2) ∈ S} with hJoint
  suffices h : ∀ S, MeasurableSet S → MeasurableSet (Joint S) by exact h _ (h_c hU)
  intro S hS
  have hgen : (Prod.instMeasurableSpace : MeasurableSpace (α × γ))
      = .generateFrom (Set.image2 (· ×ˢ ·) {S : Set α | MeasurableSet S}
                                            {S : Set γ | MeasurableSet S}) :=
    generateFrom_prod.symm
  have hpi : IsPiSystem
      (Set.image2 (· ×ˢ ·) {S : Set α | MeasurableSet S} {S : Set γ | MeasurableSet S}) :=
    MeasurableSpace.isPiSystem_measurableSet.prod MeasurableSpace.isPiSystem_measurableSet
  refine MeasurableSpace.induction_on_inter
    (C := fun S _ => MeasurableSet (Joint S)) hgen hpi ?_ ?_ ?_ ?_ S hS
  · show MeasurableSet (Joint ∅); convert MeasurableSet.empty; ext ⟨_, _⟩; simp [hJoint]
  · rintro _ ⟨V₁, hV₁, V₂, hV₂, rfl⟩
    show MeasurableSet (Joint (V₁ ×ˢ V₂))
    have : Joint (V₁ ×ˢ V₂)
        = {p : T | shape p = sChild ∧ f p ∈ V₁} ×ˢ V₂ := by
      ext ⟨p, g⟩; simp [hJoint]; tauto
    rw [this]; exact (ih hV₁).prod hV₂
  · intro S' _ IH
    show MeasurableSet (Joint S'ᶜ)
    have : Joint S'ᶜ = (({p | shape p = sChild} ×ˢ (Set.univ : Set γ)) \ Joint S') := by
      ext ⟨p, g⟩; simp [hJoint]; tauto
    rw [this]
    refine MeasurableSet.diff ?_ IH
    refine MeasurableSet.prod ?_ MeasurableSet.univ
    simpa using ih MeasurableSet.univ
  · intro F _ _ IH
    show MeasurableSet (Joint (⋃ i, F i))
    have : Joint (⋃ i, F i) = ⋃ i, Joint (F i) := by
      ext ⟨p, g⟩; simp only [hJoint, Set.mem_iUnion, Set.mem_setOf_eq]; tauto
    rw [this]; exact MeasurableSet.iUnion IH

/-! ## Param-threaded variants.

Same as the unary helpers, but with an extra measurable parameter `β` carried
through every recursive call unchanged. The joint cell is over `β × T`. -/

variable {β : Type _} [MeasurableSpace β]
variable {g : β → T → α}

/-- **Nullary cell (param)**: e.g. `wildcard`. -/
theorem cell_nullary_param {ctor : T} {s : Sh} {c : β → α} {U : Set α}
    (h_shape : ∀ p : T, shape p = s ↔ p = ctor)
    (h_eq : ∀ b, g b ctor = c b)
    (h_c : Measurable c) (hU : MeasurableSet U)
    (h_cell_T : MeasurableSet ({ctor} : Set T)) :
    MeasurableSet {q : β × T | shape q.2 = s ∧ Function.uncurry g q ∈ U} := by
  have : {q : β × T | shape q.2 = s ∧ Function.uncurry g q ∈ U}
      = (c ⁻¹' U) ×ˢ ({ctor} : Set T) := by
    ext ⟨b, p⟩
    simp only [Set.mem_setOf_eq, Function.uncurry, Set.mem_prod, Set.mem_preimage,
      Set.mem_singleton_iff]
    constructor
    · rintro ⟨hs, hp⟩
      have hp' : p = ctor := (h_shape p).mp hs
      subst hp'
      exact ⟨by rw [← h_eq]; exact hp, rfl⟩
    · rintro ⟨hb, rfl⟩
      exact ⟨(h_shape _).mpr rfl, by rw [h_eq]; exact hb⟩
  rw [this]
  exact (h_c hU).prod h_cell_T

/-- **Data-leaf cell (param)**: e.g. `lit (b' : β') (e : T)` where `β'` is data. -/
theorem cell_dataLeaf_param {γ : Type _} [MeasurableSpace γ]
    {ctor : γ → T} {s : Sh} {c : β → γ → α} {U : Set α}
    (h_emb : MeasurableEmbedding ctor)
    (h_shape : ∀ p : T, shape p = s ↔ ∃ d, p = ctor d)
    (h_eq : ∀ b d, g b (ctor d) = c b d)
    (h_c : Measurable (Function.uncurry c))
    (hU : MeasurableSet U) :
    MeasurableSet {q : β × T | shape q.2 = s ∧ Function.uncurry g q ∈ U} := by
  -- Cell = image of (b, d) ↦ (b, ctor d) over {(b, d) | c b d ∈ U}.
  have heq : {q : β × T | shape q.2 = s ∧ Function.uncurry g q ∈ U}
      = (Prod.map id ctor) '' {p : β × γ | Function.uncurry c p ∈ U} := by
    ext ⟨b, p⟩
    constructor
    · rintro ⟨hs, hp⟩
      obtain ⟨d, rfl⟩ := (h_shape p).mp hs
      refine ⟨(b, d), ?_, rfl⟩
      simp only [Set.mem_setOf_eq, Function.uncurry] at hp ⊢
      rw [h_eq] at hp; exact hp
    · rintro ⟨⟨b', d⟩, hd, heq⟩
      have hbeq : b' = b := by simpa using (Prod.mk.injEq ..).mp heq |>.1
      have hpeq : ctor d = p := by simpa using (Prod.mk.injEq ..).mp heq |>.2
      subst hbeq hpeq
      refine ⟨(h_shape _).mpr ⟨d, rfl⟩, ?_⟩
      simp only [Set.mem_setOf_eq, Function.uncurry] at hd ⊢
      rw [h_eq]; exact hd
  rw [heq]
  -- Prod.map id ctor is a measurable embedding.
  refine (MeasurableEmbedding.id.prodMap h_emb).measurableSet_image' ?_
  exact h_c hU

/-- **Unary recursive cell (param)**: e.g. `lam (e : T)`. The IH is on the joint
cell at the child's shape. -/
theorem cell_unary_param {ctor : T → T} {s s' : Sh}
    {c : β → α → α} {U : Set α}
    (h_emb : MeasurableEmbedding ctor)
    (h_shape : ∀ p : T, shape p = s ↔ ∃ p', p = ctor p' ∧ shape p' = s')
    (h_eq : ∀ b p, g b (ctor p) = c b (g b p))
    (h_c : Measurable (Function.uncurry c))
    (ih : ∀ {U' : Set α}, MeasurableSet U' →
      MeasurableSet {q : β × T | shape q.2 = s' ∧ Function.uncurry g q ∈ U'})
    (hU : MeasurableSet U) :
    MeasurableSet {q : β × T | shape q.2 = s ∧ Function.uncurry g q ∈ U} := by
  -- Cell = (id × ctor) '' {(b, p') | shape p' = s' ∧ c b (g b p') ∈ U}
  --      = (id × ctor) '' {(b, p') | shape p' = s' ∧ Function.uncurry c (b, g b p') ∈ U}
  -- The inner set is the IH applied to (Function.uncurry c ⁻¹' U)'s "vertical slice",
  -- which is not directly a measurable set in `α`. So we use a joint-cell argument.
  have heq : {q : β × T | shape q.2 = s ∧ Function.uncurry g q ∈ U}
      = (Prod.map id ctor) ''
        {q : β × T | shape q.2 = s' ∧
          Function.uncurry c (q.1, Function.uncurry g q) ∈ U} := by
    ext ⟨b, p⟩
    constructor
    · rintro ⟨hs, hp⟩
      obtain ⟨p', rfl, hs'⟩ := (h_shape p).mp hs
      refine ⟨(b, p'), ⟨hs', ?_⟩, rfl⟩
      simp only [Function.uncurry] at hp ⊢
      rw [h_eq] at hp; exact hp
    · rintro ⟨⟨b', p'⟩, ⟨hs', hp'⟩, heq⟩
      have hbeq : b' = b := by simpa using (Prod.mk.injEq ..).mp heq |>.1
      have hpeq : ctor p' = p := by simpa using (Prod.mk.injEq ..).mp heq |>.2
      subst hbeq hpeq
      refine ⟨(h_shape _).mpr ⟨p', rfl, hs'⟩, ?_⟩
      simp only [Function.uncurry] at hp' ⊢
      rw [h_eq]; exact hp'
  rw [heq]
  refine (MeasurableEmbedding.id.prodMap h_emb).measurableSet_image' ?_
  -- Goal: MeasurableSet {q | shape q.2 = s' ∧ Function.uncurry c (q.1, Function.uncurry g q) ∈ U}.
  -- Strategy: π-system induction on V ⊆ β × α (the target of `(b, g b p) ↦ ...`).
  set Joint : Set (β × α) → Set (β × T) :=
    fun V => {q : β × T | shape q.2 = s' ∧ (q.1, Function.uncurry g q) ∈ V}
    with hJoint
  suffices h : ∀ V, MeasurableSet V → MeasurableSet (Joint V) by
    have hV : MeasurableSet (Function.uncurry c ⁻¹' U) := h_c hU
    convert h _ hV
  intro V hV
  have hgen : (Prod.instMeasurableSpace : MeasurableSpace (β × α))
      = .generateFrom (Set.image2 (· ×ˢ ·) {S : Set β | MeasurableSet S}
                                            {S : Set α | MeasurableSet S}) :=
    generateFrom_prod.symm
  have hpi : IsPiSystem
      (Set.image2 (· ×ˢ ·) {S : Set β | MeasurableSet S} {S : Set α | MeasurableSet S}) :=
    MeasurableSpace.isPiSystem_measurableSet.prod MeasurableSpace.isPiSystem_measurableSet
  refine MeasurableSpace.induction_on_inter
    (C := fun V _ => MeasurableSet (Joint V)) hgen hpi ?_ ?_ ?_ ?_ V hV
  · show MeasurableSet (Joint ∅); convert MeasurableSet.empty; ext ⟨_, _⟩; simp [hJoint]
  · rintro _ ⟨B, hB, A, hA, rfl⟩
    show MeasurableSet (Joint (B ×ˢ A))
    have : Joint (B ×ˢ A)
        = B ×ˢ Set.univ ∩ {q : β × T | shape q.2 = s' ∧ Function.uncurry g q ∈ A} := by
      ext ⟨b, p⟩; simp [hJoint]; tauto
    rw [this]
    exact (hB.prod MeasurableSet.univ).inter (ih hA)
  · intro V' _ IH
    show MeasurableSet (Joint V'ᶜ)
    have : Joint V'ᶜ = {q : β × T | shape q.2 = s'} \ Joint V' := by
      ext ⟨b, p⟩; simp [hJoint]; tauto
    rw [this]
    refine MeasurableSet.diff ?_ IH
    simpa using ih MeasurableSet.univ
  · intro F _ _ IH
    show MeasurableSet (Joint (⋃ i, F i))
    have : Joint (⋃ i, F i) = ⋃ i, Joint (F i) := by
      ext ⟨b, p⟩; simp only [hJoint, Set.mem_iUnion, Set.mem_setOf_eq]; tauto
    rw [this]; exact MeasurableSet.iUnion IH

/-- **Binary joint-recursive cell (param)**: e.g. `app e1 e2`. Both children share
the parameter `b`. -/
theorem cell_binary_param
    {ctor : T → T → T} {s s1 s2 : Sh}
    {c : β → α → α → α} {U : Set α}
    (h_emb : MeasurableEmbedding (Function.uncurry ctor))
    (h_shape : ∀ p : T, shape p = s ↔
      ∃ p1 p2, p = ctor p1 p2 ∧ shape p1 = s1 ∧ shape p2 = s2)
    (h_eq : ∀ b p1 p2, g b (ctor p1 p2) = c b (g b p1) (g b p2))
    (h_c : Measurable (fun (q : β × α × α) => c q.1 q.2.1 q.2.2))
    (ih1 : ∀ {U' : Set α}, MeasurableSet U' →
      MeasurableSet {q : β × T | shape q.2 = s1 ∧ Function.uncurry g q ∈ U'})
    (ih2 : ∀ {U' : Set α}, MeasurableSet U' →
      MeasurableSet {q : β × T | shape q.2 = s2 ∧ Function.uncurry g q ∈ U'})
    (hU : MeasurableSet U)
    [h_inhab : Inhabited β] :
    MeasurableSet {q : β × T | shape q.2 = s ∧ Function.uncurry g q ∈ U} := by
  -- Decompose: cell = image of (b, (p1, p2)) ↦ (b, ctor p1 p2) over inner joint cell.
  have heq : {q : β × T | shape q.2 = s ∧ Function.uncurry g q ∈ U}
      = (fun (q : β × T × T) => (q.1, ctor q.2.1 q.2.2)) ''
        {q : β × T × T | shape q.2.1 = s1 ∧ shape q.2.2 = s2 ∧
          (q.1, g q.1 q.2.1, g q.1 q.2.2) ∈
            ((fun (r : β × α × α) => c r.1 r.2.1 r.2.2) ⁻¹' U)} := by
    ext ⟨b, p⟩
    constructor
    · rintro ⟨hs, hp⟩
      obtain ⟨p1, p2, rfl, hs1, hs2⟩ := (h_shape p).mp hs
      refine ⟨(b, p1, p2), ⟨hs1, hs2, ?_⟩, rfl⟩
      simp only [Function.uncurry, Set.mem_preimage] at hp ⊢
      rw [h_eq] at hp; exact hp
    · rintro ⟨⟨b', p1, p2⟩, ⟨hs1, hs2, h⟩, heq⟩
      have hbeq : b' = b := by simpa using (Prod.mk.injEq ..).mp heq |>.1
      have hpeq : ctor p1 p2 = p := by simpa using (Prod.mk.injEq ..).mp heq |>.2
      subst hbeq hpeq
      refine ⟨(h_shape _).mpr ⟨p1, p2, rfl, hs1, hs2⟩, ?_⟩
      simp only [Function.uncurry, Set.mem_preimage] at h ⊢
      rw [h_eq]; exact h
  rw [heq]
  have h_emb_outer : MeasurableEmbedding
      (fun (q : β × T × T) => (q.1, ctor q.2.1 q.2.2)) := by
    have : (fun (q : β × T × T) => (q.1, ctor q.2.1 q.2.2))
        = Prod.map id (Function.uncurry ctor) := by ext ⟨_, _, _⟩ <;> rfl
    rw [this]
    exact MeasurableEmbedding.id.prodMap h_emb
  refine h_emb_outer.measurableSet_image' ?_
  have h_target : MeasurableSet ((fun (r : β × α × α) => c r.1 r.2.1 r.2.2) ⁻¹' U) :=
    h_c hU
  set Joint : Set (β × α × α) → Set (β × T × T) :=
    fun W => {q : β × T × T | shape q.2.1 = s1 ∧ shape q.2.2 = s2 ∧
      (q.1, g q.1 q.2.1, g q.1 q.2.2) ∈ W}
    with hJoint
  suffices h : ∀ W, MeasurableSet W → MeasurableSet (Joint W) by exact h _ h_target
  intro W hW
  have hgen : (Prod.instMeasurableSpace : MeasurableSpace (β × α × α))
      = .generateFrom (Set.image2 (· ×ˢ ·) {B : Set β | MeasurableSet B}
                                            {R : Set (α × α) | MeasurableSet R}) :=
    generateFrom_prod.symm
  have hpi : IsPiSystem (Set.image2 (· ×ˢ ·) {B : Set β | MeasurableSet B}
                                              {R : Set (α × α) | MeasurableSet R}) :=
    MeasurableSpace.isPiSystem_measurableSet.prod MeasurableSpace.isPiSystem_measurableSet
  have hs1m : MeasurableSet {p : T | shape p = s1} := by
    have h1 := ih1 (MeasurableSet.univ (α := α))
    have hpreimg : (fun p : T => (h_inhab.default, p)) ⁻¹'
        {q : β × T | shape q.2 = s1 ∧ Function.uncurry g q ∈ Set.univ}
        = {p : T | shape p = s1} := by ext p; simp
    rw [← hpreimg]
    exact MeasurableSet.preimage h1 (by fun_prop)
  have hs2m : MeasurableSet {p : T | shape p = s2} := by
    have h2 := ih2 (MeasurableSet.univ (α := α))
    have hpreimg : (fun p : T => (h_inhab.default, p)) ⁻¹'
        {q : β × T | shape q.2 = s2 ∧ Function.uncurry g q ∈ Set.univ}
        = {p : T | shape p = s2} := by ext p; simp
    rw [← hpreimg]
    exact MeasurableSet.preimage h2 (by fun_prop)
  have hjoint12 : ∀ R : Set (α × α), MeasurableSet R →
      MeasurableSet {q : β × T × T | shape q.2.1 = s1 ∧ shape q.2.2 = s2 ∧
        (g q.1 q.2.1, g q.1 q.2.2) ∈ R} := by
    intro R hR
    set J12 : Set (α × α) → Set (β × T × T) :=
      fun R' => {q : β × T × T | shape q.2.1 = s1 ∧ shape q.2.2 = s2 ∧
        (g q.1 q.2.1, g q.1 q.2.2) ∈ R'}
      with hJ12
    suffices ∀ R', MeasurableSet R' → MeasurableSet (J12 R') from this _ hR
    intro R' hR'
    have hgen' : (Prod.instMeasurableSpace : MeasurableSpace (α × α))
        = .generateFrom (Set.image2 (· ×ˢ ·) {S : Set α | MeasurableSet S}
                                              {S : Set α | MeasurableSet S}) :=
      generateFrom_prod.symm
    have hpi' : IsPiSystem
        (Set.image2 (· ×ˢ ·) {S : Set α | MeasurableSet S} {S : Set α | MeasurableSet S}) :=
      MeasurableSpace.isPiSystem_measurableSet.prod MeasurableSpace.isPiSystem_measurableSet
    refine MeasurableSpace.induction_on_inter
      (C := fun R'' _ => MeasurableSet (J12 R'')) hgen' hpi' ?_ ?_ ?_ ?_ R' hR'
    · show MeasurableSet (J12 ∅); convert MeasurableSet.empty
      ext ⟨_, _, _⟩; simp [hJ12]
    · rintro _ ⟨V1, hV1, V2, hV2, rfl⟩
      show MeasurableSet (J12 (V1 ×ˢ V2))
      have : J12 (V1 ×ˢ V2)
          = ((fun (q : β × T × T) => (q.1, q.2.1)) ⁻¹'
             {q : β × T | shape q.2 = s1 ∧ Function.uncurry g q ∈ V1})
            ∩ ((fun (q : β × T × T) => (q.1, q.2.2)) ⁻¹'
               {q : β × T | shape q.2 = s2 ∧ Function.uncurry g q ∈ V2}) := by
        ext ⟨b, p1, p2⟩; simp [hJ12, Function.uncurry]; tauto
      rw [this]
      refine MeasurableSet.inter ?_ ?_
      · exact (ih1 hV1).preimage (by fun_prop)
      · exact (ih2 hV2).preimage (by fun_prop)
    · intro R'' _ IH
      show MeasurableSet (J12 R''ᶜ)
      have : J12 R''ᶜ
          = ((Set.univ : Set β) ×ˢ ({p : T | shape p = s1} ×ˢ {p : T | shape p = s2}))
            \ J12 R'' := by
        ext ⟨b, p1, p2⟩; simp [hJ12]; tauto
      rw [this]
      refine MeasurableSet.diff ?_ IH
      refine MeasurableSet.univ.prod ?_
      exact hs1m.prod hs2m
    · intro F _ _ IH
      show MeasurableSet (J12 (⋃ i, F i))
      have : J12 (⋃ i, F i) = ⋃ i, J12 (F i) := by
        ext ⟨b, p1, p2⟩; simp only [hJ12, Set.mem_iUnion, Set.mem_setOf_eq]; tauto
      rw [this]; exact MeasurableSet.iUnion IH
  refine MeasurableSpace.induction_on_inter
    (C := fun W _ => MeasurableSet (Joint W)) hgen hpi ?_ ?_ ?_ ?_ W hW
  · show MeasurableSet (Joint ∅); convert MeasurableSet.empty
    ext ⟨_, _, _⟩; simp [hJoint]
  · rintro _ ⟨B, hB, R, hR, rfl⟩
    show MeasurableSet (Joint (B ×ˢ R))
    have : Joint (B ×ˢ R)
        = (B ×ˢ (Set.univ : Set T) ×ˢ (Set.univ : Set T))
          ∩ {q : β × T × T | shape q.2.1 = s1 ∧ shape q.2.2 = s2 ∧
              (g q.1 q.2.1, g q.1 q.2.2) ∈ R} := by
      ext ⟨b, p1, p2⟩; simp [hJoint]; tauto
    rw [this]
    refine MeasurableSet.inter ?_ ?_
    · exact hB.prod (MeasurableSet.univ.prod MeasurableSet.univ)
    · exact hjoint12 R hR
  · intro W' _ IH
    show MeasurableSet (Joint W'ᶜ)
    have : Joint W'ᶜ
        = ((Set.univ : Set β) ×ˢ ({p : T | shape p = s1} ×ˢ {p : T | shape p = s2}))
          \ Joint W' := by
      ext ⟨b, p1, p2⟩; simp [hJoint]; tauto
    rw [this]
    refine MeasurableSet.diff ?_ IH
    refine MeasurableSet.univ.prod ?_
    exact hs1m.prod hs2m
  · intro F _ _ IH
    show MeasurableSet (Joint (⋃ i, F i))
    have : Joint (⋃ i, F i) = ⋃ i, Joint (F i) := by
      ext ⟨b, p1, p2⟩; simp only [hJoint, Set.mem_iUnion, Set.mem_setOf_eq]; tauto
    rw [this]; exact MeasurableSet.iUnion IH

/-! ### Binder-shifting variants.

`cell_unary_param_shift` is `cell_unary_param` but with the recursive call's
parameter **transformed** by a measurable map `t : β → β`. This supports
recursion through binders (`lam`, `fix`) where the parameter changes at the
binder boundary. -/

/-- **Unary recursive cell (param + shift)**: like `cell_unary_param` but the
recursive call uses `g (t b) p'` instead of `g b p'`, with `t : β → β` measurable. -/
theorem cell_unary_param_shift {ctor : T → T} {s s' : Sh}
    {c : β → α → α} {t : β → β} {U : Set α}
    (h_emb : MeasurableEmbedding ctor)
    (h_shape : ∀ p : T, shape p = s ↔ ∃ p', p = ctor p' ∧ shape p' = s')
    (h_eq : ∀ b p, g b (ctor p) = c b (g (t b) p))
    (h_c : Measurable (Function.uncurry c))
    (h_t : Measurable t)
    (ih : ∀ {U' : Set α}, MeasurableSet U' →
      MeasurableSet {q : β × T | shape q.2 = s' ∧ Function.uncurry g q ∈ U'})
    (hU : MeasurableSet U)
    [h_inhab : Inhabited β] :
    MeasurableSet {q : β × T | shape q.2 = s ∧ Function.uncurry g q ∈ U} := by
  have heq : {q : β × T | shape q.2 = s ∧ Function.uncurry g q ∈ U}
      = (Prod.map id ctor) ''
        {q : β × T | shape q.2 = s' ∧
          Function.uncurry c (q.1, Function.uncurry g (t q.1, q.2)) ∈ U} := by
    ext ⟨b, p⟩
    constructor
    · rintro ⟨hs, hp⟩
      obtain ⟨p', rfl, hs'⟩ := (h_shape p).mp hs
      refine ⟨(b, p'), ⟨hs', ?_⟩, rfl⟩
      simp only [Function.uncurry] at hp ⊢
      rw [h_eq] at hp; exact hp
    · rintro ⟨⟨b', p'⟩, ⟨hs', hp'⟩, heq⟩
      have hbeq : b' = b := by simpa using (Prod.mk.injEq ..).mp heq |>.1
      have hpeq : ctor p' = p := by simpa using (Prod.mk.injEq ..).mp heq |>.2
      subst hbeq hpeq
      refine ⟨(h_shape _).mpr ⟨p', rfl, hs'⟩, ?_⟩
      simp only [Function.uncurry] at hp' ⊢
      rw [h_eq]; exact hp'
  rw [heq]
  refine (MeasurableEmbedding.id.prodMap h_emb).measurableSet_image' ?_
  -- Goal: MeasurableSet {q | shape q.2 = s' ∧ Function.uncurry c (q.1, g (t q.1) q.2) ∈ U}
  set Joint : Set (β × α) → Set (β × T) :=
    fun V => {q : β × T | shape q.2 = s' ∧ (q.1, Function.uncurry g (t q.1, q.2)) ∈ V}
    with hJoint
  suffices h : ∀ V, MeasurableSet V → MeasurableSet (Joint V) by
    have hV : MeasurableSet (Function.uncurry c ⁻¹' U) := h_c hU
    convert h _ hV
  intro V hV
  have hgen : (Prod.instMeasurableSpace : MeasurableSpace (β × α))
      = .generateFrom (Set.image2 (· ×ˢ ·) {S : Set β | MeasurableSet S}
                                            {S : Set α | MeasurableSet S}) :=
    generateFrom_prod.symm
  have hpi : IsPiSystem
      (Set.image2 (· ×ˢ ·) {S : Set β | MeasurableSet S} {S : Set α | MeasurableSet S}) :=
    MeasurableSpace.isPiSystem_measurableSet.prod MeasurableSpace.isPiSystem_measurableSet
  refine MeasurableSpace.induction_on_inter
    (C := fun V _ => MeasurableSet (Joint V)) hgen hpi ?_ ?_ ?_ ?_ V hV
  · show MeasurableSet (Joint ∅); convert MeasurableSet.empty; ext ⟨_, _⟩; simp [hJoint]
  · rintro _ ⟨B, hB, A, hA, rfl⟩
    show MeasurableSet (Joint (B ×ˢ A))
    -- Joint (B ×ˢ A) = B ×ˢ univ ∩ (change-of-vars to apply IH at (t q.1, q.2))
    have : Joint (B ×ˢ A)
        = (B ×ˢ Set.univ) ∩
          (fun q : β × T => (t q.1, q.2)) ⁻¹'
            {q : β × T | shape q.2 = s' ∧ Function.uncurry g q ∈ A} := by
      ext ⟨b, p⟩; simp [hJoint]; tauto
    rw [this]
    refine MeasurableSet.inter ?_ ?_
    · exact hB.prod MeasurableSet.univ
    · refine MeasurableSet.preimage (ih hA) ?_
      exact (h_t.comp measurable_fst).prodMk measurable_snd
  · intro V' _ IH
    show MeasurableSet (Joint V'ᶜ)
    have : Joint V'ᶜ = {q : β × T | shape q.2 = s'} \ Joint V' := by
      ext ⟨b, p⟩; simp [hJoint]; tauto
    rw [this]
    refine MeasurableSet.diff ?_ IH
    -- {q | shape q.2 = s'} measurable: from ih with U' = univ, slice over b.
    have h := ih (MeasurableSet.univ (α := α))
    have hslice : {q : β × T | shape q.2 = s'}
        = (fun q : β × T => q.2) ⁻¹' (Prod.snd '' {q : β × T | shape q.2 = s' ∧ Function.uncurry g q ∈ Set.univ}) := by
      ext ⟨b, p⟩
      simp only [Set.mem_setOf_eq, Set.mem_preimage, Set.mem_image]
      constructor
      · intro hs; exact ⟨(b, p), ⟨hs, by simp [Function.uncurry]⟩, rfl⟩
      · rintro ⟨⟨b', p'⟩, ⟨hs', _⟩, rfl⟩; exact hs'
    -- Simpler: shape q.2 = s' is just preimage of {shape = s'} under snd.
    have hshape : {q : β × T | shape q.2 = s'}
        = (fun q : β × T => q.2) ⁻¹' {p : T | shape p = s'} := by
      ext ⟨_, _⟩; simp
    rw [hshape]
    -- {p : T | shape p = s'} measurable: from ih with U' = univ, slice at default b.
    have h' : MeasurableSet {p : T | shape p = s'} := by
      have hihU := ih (MeasurableSet.univ (α := α))
      have hreduce : {q : β × T | shape q.2 = s' ∧ Function.uncurry g q ∈ (Set.univ : Set α)}
          = {q : β × T | shape q.2 = s'} := by
        ext ⟨_, _⟩; simp
      rw [hreduce] at hihU
      have hslice : {p : T | shape p = s'}
          = (fun p : T => (h_inhab.default, p)) ⁻¹' {q : β × T | shape q.2 = s'} := by
        ext p; simp
      rw [hslice]
      exact MeasurableSet.preimage hihU (by fun_prop)
    exact MeasurableSet.preimage h' measurable_snd
  · intro F _ _ IH
    show MeasurableSet (Joint (⋃ i, F i))
    have : Joint (⋃ i, F i) = ⋃ i, Joint (F i) := by
      ext ⟨b, p⟩; simp only [hJoint, Set.mem_iUnion, Set.mem_setOf_eq]; tauto
    rw [this]; exact MeasurableSet.iUnion IH

/-- **Ternary recursive cell (param)**: e.g. `cond ec et ef`. Three children share `b`. -/
theorem cell_ternary_param
    {ctor : T → T → T → T} {s s1 s2 s3 : Sh}
    {c : β → α → α → α → α} {U : Set α}
    (h_emb : MeasurableEmbedding (fun (p : T × T × T) => ctor p.1 p.2.1 p.2.2))
    (h_shape : ∀ p : T, shape p = s ↔
      ∃ p1 p2 p3, p = ctor p1 p2 p3 ∧ shape p1 = s1 ∧ shape p2 = s2 ∧ shape p3 = s3)
    (h_eq : ∀ b p1 p2 p3, g b (ctor p1 p2 p3) = c b (g b p1) (g b p2) (g b p3))
    (h_c : Measurable (fun (q : β × α × α × α) => c q.1 q.2.1 q.2.2.1 q.2.2.2))
    (ih1 : ∀ {U' : Set α}, MeasurableSet U' →
      MeasurableSet {q : β × T | shape q.2 = s1 ∧ Function.uncurry g q ∈ U'})
    (ih2 : ∀ {U' : Set α}, MeasurableSet U' →
      MeasurableSet {q : β × T | shape q.2 = s2 ∧ Function.uncurry g q ∈ U'})
    (ih3 : ∀ {U' : Set α}, MeasurableSet U' →
      MeasurableSet {q : β × T | shape q.2 = s3 ∧ Function.uncurry g q ∈ U'})
    (hU : MeasurableSet U)
    [h_inhab : Inhabited β] :
    MeasurableSet {q : β × T | shape q.2 = s ∧ Function.uncurry g q ∈ U} := by
  -- Decompose: cell = image of (b, (p1, p2, p3)) ↦ (b, ctor p1 p2 p3) over inner joint cell.
  have heq : {q : β × T | shape q.2 = s ∧ Function.uncurry g q ∈ U}
      = (fun (q : β × T × T × T) => (q.1, ctor q.2.1 q.2.2.1 q.2.2.2)) ''
        {q : β × T × T × T | shape q.2.1 = s1 ∧ shape q.2.2.1 = s2 ∧ shape q.2.2.2 = s3 ∧
          (q.1, g q.1 q.2.1, g q.1 q.2.2.1, g q.1 q.2.2.2) ∈
            ((fun (r : β × α × α × α) => c r.1 r.2.1 r.2.2.1 r.2.2.2) ⁻¹' U)} := by
    ext ⟨b, p⟩
    constructor
    · rintro ⟨hs, hp⟩
      obtain ⟨p1, p2, p3, rfl, hs1, hs2, hs3⟩ := (h_shape p).mp hs
      refine ⟨(b, p1, p2, p3), ⟨hs1, hs2, hs3, ?_⟩, rfl⟩
      simp only [Function.uncurry, Set.mem_preimage] at hp ⊢
      rw [h_eq] at hp; exact hp
    · rintro ⟨⟨b', p1, p2, p3⟩, ⟨hs1, hs2, hs3, h⟩, heq⟩
      have hbeq : b' = b := by simpa using (Prod.mk.injEq ..).mp heq |>.1
      have hpeq : ctor p1 p2 p3 = p := by simpa using (Prod.mk.injEq ..).mp heq |>.2
      subst hbeq hpeq
      refine ⟨(h_shape _).mpr ⟨p1, p2, p3, rfl, hs1, hs2, hs3⟩, ?_⟩
      simp only [Function.uncurry, Set.mem_preimage] at h ⊢
      rw [h_eq]; exact h
  rw [heq]
  have h_emb_outer : MeasurableEmbedding
      (fun (q : β × T × T × T) => (q.1, ctor q.2.1 q.2.2.1 q.2.2.2)) := by
    have : (fun (q : β × T × T × T) => (q.1, ctor q.2.1 q.2.2.1 q.2.2.2))
        = Prod.map id (fun (p : T × T × T) => ctor p.1 p.2.1 p.2.2) := by
      ext ⟨_, _, _, _⟩ <;> rfl
    rw [this]
    exact MeasurableEmbedding.id.prodMap h_emb
  refine h_emb_outer.measurableSet_image' ?_
  have h_target : MeasurableSet
      ((fun (r : β × α × α × α) => c r.1 r.2.1 r.2.2.1 r.2.2.2) ⁻¹' U) := h_c hU
  set Joint : Set (β × α × α × α) → Set (β × T × T × T) :=
    fun W => {q : β × T × T × T | shape q.2.1 = s1 ∧ shape q.2.2.1 = s2 ∧ shape q.2.2.2 = s3 ∧
      (q.1, g q.1 q.2.1, g q.1 q.2.2.1, g q.1 q.2.2.2) ∈ W}
    with hJoint
  suffices h : ∀ W, MeasurableSet W → MeasurableSet (Joint W) by exact h _ h_target
  intro W hW
  -- π-system on β × α × α × α: rectangles B × R where R ⊆ α × α × α.
  have hgen : (Prod.instMeasurableSpace : MeasurableSpace (β × α × α × α))
      = .generateFrom (Set.image2 (· ×ˢ ·) {B : Set β | MeasurableSet B}
                                            {R : Set (α × α × α) | MeasurableSet R}) :=
    generateFrom_prod.symm
  have hpi : IsPiSystem (Set.image2 (· ×ˢ ·) {B : Set β | MeasurableSet B}
                                              {R : Set (α × α × α) | MeasurableSet R}) :=
    MeasurableSpace.isPiSystem_measurableSet.prod MeasurableSpace.isPiSystem_measurableSet
  have hs1m : MeasurableSet {p : T | shape p = s1} := by
    have h1 := ih1 (MeasurableSet.univ (α := α))
    have hpreimg : (fun p : T => (h_inhab.default, p)) ⁻¹'
        {q : β × T | shape q.2 = s1 ∧ Function.uncurry g q ∈ Set.univ}
        = {p : T | shape p = s1} := by ext p; simp
    rw [← hpreimg]
    exact MeasurableSet.preimage h1 (by fun_prop)
  have hs2m : MeasurableSet {p : T | shape p = s2} := by
    have h2 := ih2 (MeasurableSet.univ (α := α))
    have hpreimg : (fun p : T => (h_inhab.default, p)) ⁻¹'
        {q : β × T | shape q.2 = s2 ∧ Function.uncurry g q ∈ Set.univ}
        = {p : T | shape p = s2} := by ext p; simp
    rw [← hpreimg]
    exact MeasurableSet.preimage h2 (by fun_prop)
  have hs3m : MeasurableSet {p : T | shape p = s3} := by
    have h3 := ih3 (MeasurableSet.univ (α := α))
    have hpreimg : (fun p : T => (h_inhab.default, p)) ⁻¹'
        {q : β × T | shape q.2 = s3 ∧ Function.uncurry g q ∈ Set.univ}
        = {p : T | shape p = s3} := by ext p; simp
    rw [← hpreimg]
    exact MeasurableSet.preimage h3 (by fun_prop)
  -- Inner joint for α × α × α (no β stratification).
  have hjoint123 : ∀ R : Set (α × α × α), MeasurableSet R →
      MeasurableSet {q : β × T × T × T | shape q.2.1 = s1 ∧ shape q.2.2.1 = s2 ∧
        shape q.2.2.2 = s3 ∧ (g q.1 q.2.1, g q.1 q.2.2.1, g q.1 q.2.2.2) ∈ R} := by
    intro R hR
    set J : Set (α × α × α) → Set (β × T × T × T) :=
      fun R' => {q : β × T × T × T | shape q.2.1 = s1 ∧ shape q.2.2.1 = s2 ∧
        shape q.2.2.2 = s3 ∧ (g q.1 q.2.1, g q.1 q.2.2.1, g q.1 q.2.2.2) ∈ R'}
      with hJ
    suffices ∀ R', MeasurableSet R' → MeasurableSet (J R') from this _ hR
    intro R' hR'
    -- π-system on α × α × α: iterated rectangles (V1 × (V2 × V3)).
    have hgen' : (Prod.instMeasurableSpace : MeasurableSpace (α × α × α))
        = .generateFrom (Set.image2 (· ×ˢ ·) {S : Set α | MeasurableSet S}
                                              {W : Set (α × α) | MeasurableSet W}) :=
      generateFrom_prod.symm
    have hpi' : IsPiSystem (Set.image2 (· ×ˢ ·) {S : Set α | MeasurableSet S}
                                                {W : Set (α × α) | MeasurableSet W}) :=
      MeasurableSpace.isPiSystem_measurableSet.prod MeasurableSpace.isPiSystem_measurableSet
    -- Inner-inner helper for α × α.
    have hjoint23 : ∀ W : Set (α × α), MeasurableSet W →
        MeasurableSet {q : β × T × T × T | shape q.2.1 = s1 ∧ shape q.2.2.1 = s2 ∧
          shape q.2.2.2 = s3 ∧ (g q.1 q.2.2.1, g q.1 q.2.2.2) ∈ W} := by
      intro W hW
      set K : Set (α × α) → Set (β × T × T × T) :=
        fun W' => {q : β × T × T × T | shape q.2.1 = s1 ∧ shape q.2.2.1 = s2 ∧
          shape q.2.2.2 = s3 ∧ (g q.1 q.2.2.1, g q.1 q.2.2.2) ∈ W'}
        with hK
      suffices ∀ W', MeasurableSet W' → MeasurableSet (K W') from this _ hW
      intro W' hW'
      have hgen'' : (Prod.instMeasurableSpace : MeasurableSpace (α × α))
          = .generateFrom (Set.image2 (· ×ˢ ·) {S : Set α | MeasurableSet S}
                                                {S : Set α | MeasurableSet S}) :=
        generateFrom_prod.symm
      have hpi'' : IsPiSystem (Set.image2 (· ×ˢ ·) {S : Set α | MeasurableSet S}
                                                  {S : Set α | MeasurableSet S}) :=
        MeasurableSpace.isPiSystem_measurableSet.prod MeasurableSpace.isPiSystem_measurableSet
      refine MeasurableSpace.induction_on_inter
        (C := fun W'' _ => MeasurableSet (K W'')) hgen'' hpi'' ?_ ?_ ?_ ?_ W' hW'
      · show MeasurableSet (K ∅); convert MeasurableSet.empty
        ext ⟨_, _, _, _⟩; simp [hK]
      · rintro _ ⟨V2, hV2, V3, hV3, rfl⟩
        show MeasurableSet (K (V2 ×ˢ V3))
        have : K (V2 ×ˢ V3)
            = ((fun (q : β × T × T × T) => q.2.1) ⁻¹' {p : T | shape p = s1})
              ∩ ((fun (q : β × T × T × T) => (q.1, q.2.2.1)) ⁻¹'
                 {q : β × T | shape q.2 = s2 ∧ Function.uncurry g q ∈ V2})
              ∩ ((fun (q : β × T × T × T) => (q.1, q.2.2.2)) ⁻¹'
                 {q : β × T | shape q.2 = s3 ∧ Function.uncurry g q ∈ V3}) := by
          ext ⟨b, p1, p2, p3⟩; simp [hK, Function.uncurry]; tauto
        rw [this]
        refine MeasurableSet.inter (MeasurableSet.inter ?_ ?_) ?_
        · exact hs1m.preimage (by fun_prop)
        · exact (ih2 hV2).preimage (by fun_prop)
        · exact (ih3 hV3).preimage (by fun_prop)
      · intro W'' _ IH
        show MeasurableSet (K W''ᶜ)
        have : K W''ᶜ
            = ((Set.univ : Set β) ×ˢ ({p : T | shape p = s1} ×ˢ {p : T | shape p = s2} ×ˢ
               {p : T | shape p = s3})) \ K W'' := by
          ext ⟨b, p1, p2, p3⟩; simp [hK]; tauto
        rw [this]
        refine MeasurableSet.diff ?_ IH
        exact MeasurableSet.univ.prod (hs1m.prod (hs2m.prod hs3m))
      · intro F _ _ IH
        show MeasurableSet (K (⋃ i, F i))
        have : K (⋃ i, F i) = ⋃ i, K (F i) := by
          ext ⟨b, p1, p2, p3⟩; simp only [hK, Set.mem_iUnion, Set.mem_setOf_eq]; tauto
        rw [this]; exact MeasurableSet.iUnion IH
    refine MeasurableSpace.induction_on_inter
      (C := fun R'' _ => MeasurableSet (J R'')) hgen' hpi' ?_ ?_ ?_ ?_ R' hR'
    · show MeasurableSet (J ∅); convert MeasurableSet.empty
      ext ⟨_, _, _, _⟩; simp [hJ]
    · rintro _ ⟨V1, hV1, W23, hW23, rfl⟩
      show MeasurableSet (J (V1 ×ˢ W23))
      have : J (V1 ×ˢ W23)
          = ((fun (q : β × T × T × T) => (q.1, q.2.1)) ⁻¹'
             {q : β × T | shape q.2 = s1 ∧ Function.uncurry g q ∈ V1})
            ∩ {q : β × T × T × T | shape q.2.1 = s1 ∧ shape q.2.2.1 = s2 ∧
                shape q.2.2.2 = s3 ∧ (g q.1 q.2.2.1, g q.1 q.2.2.2) ∈ W23} := by
        ext ⟨b, p1, p2, p3⟩; simp [hJ, Function.uncurry]; tauto
      rw [this]
      refine MeasurableSet.inter ?_ ?_
      · exact (ih1 hV1).preimage (by fun_prop)
      · exact hjoint23 W23 hW23
    · intro R'' _ IH
      show MeasurableSet (J R''ᶜ)
      have : J R''ᶜ
          = ((Set.univ : Set β) ×ˢ ({p : T | shape p = s1} ×ˢ {p : T | shape p = s2} ×ˢ
             {p : T | shape p = s3})) \ J R'' := by
        ext ⟨b, p1, p2, p3⟩; simp [hJ]; tauto
      rw [this]
      refine MeasurableSet.diff ?_ IH
      exact MeasurableSet.univ.prod (hs1m.prod (hs2m.prod hs3m))
    · intro F _ _ IH
      show MeasurableSet (J (⋃ i, F i))
      have : J (⋃ i, F i) = ⋃ i, J (F i) := by
        ext ⟨b, p1, p2, p3⟩; simp only [hJ, Set.mem_iUnion, Set.mem_setOf_eq]; tauto
      rw [this]; exact MeasurableSet.iUnion IH
  refine MeasurableSpace.induction_on_inter
    (C := fun W _ => MeasurableSet (Joint W)) hgen hpi ?_ ?_ ?_ ?_ W hW
  · show MeasurableSet (Joint ∅); convert MeasurableSet.empty
    ext ⟨_, _, _, _⟩; simp [hJoint]
  · rintro _ ⟨B, hB, R, hR, rfl⟩
    show MeasurableSet (Joint (B ×ˢ R))
    have : Joint (B ×ˢ R)
        = (B ×ˢ (Set.univ : Set T) ×ˢ (Set.univ : Set T) ×ˢ (Set.univ : Set T))
          ∩ {q : β × T × T × T | shape q.2.1 = s1 ∧ shape q.2.2.1 = s2 ∧
              shape q.2.2.2 = s3 ∧ (g q.1 q.2.1, g q.1 q.2.2.1, g q.1 q.2.2.2) ∈ R} := by
      ext ⟨b, p1, p2, p3⟩; simp [hJoint]; tauto
    rw [this]
    refine MeasurableSet.inter ?_ ?_
    · exact hB.prod (MeasurableSet.univ.prod (MeasurableSet.univ.prod MeasurableSet.univ))
    · exact hjoint123 R hR
  · intro W' _ IH
    show MeasurableSet (Joint W'ᶜ)
    have : Joint W'ᶜ
        = ((Set.univ : Set β) ×ˢ ({p : T | shape p = s1} ×ˢ {p : T | shape p = s2} ×ˢ
           {p : T | shape p = s3})) \ Joint W' := by
      ext ⟨b, p1, p2, p3⟩; simp [hJoint]; tauto
    rw [this]
    refine MeasurableSet.diff ?_ IH
    exact MeasurableSet.univ.prod (hs1m.prod (hs2m.prod hs3m))
  · intro F _ _ IH
    show MeasurableSet (Joint (⋃ i, F i))
    have : Joint (⋃ i, F i) = ⋃ i, Joint (F i) := by
      ext ⟨b, p1, p2, p3⟩; simp only [hJoint, Set.mem_iUnion, Set.mem_setOf_eq]; tauto
    rw [this]; exact MeasurableSet.iUnion IH

set_option maxHeartbeats 1000000 in
/-- **Quaternary joint-recursive cell (param)** (arity-extension appendix, §21): copied
from `cell_ternary_param` with one extra child `s4`/`ih4`. Codomain `α × α × α × α`
treated as `α × (α × α × α)`. Needs `[Inhabited β]`.

The triple-nested π-system induction (Jouter ⊇ hjoint234 ⊇ hjoint34) makes this the
single largest cell in the file; its cumulative elaboration exceeds the default
heartbeat budget, hence the local `set_option`. This is a generic-infra bump, not a
per-type-file one — the per-type keystone arm that *calls* this cell is a single
`exact` and needs no bump. -/
theorem cell_quaternary_param
    {ctor : T → T → T → T → T} {s s1 s2 s3 s4 : Sh}
    {c : β → α → α → α → α → α} {U : Set α}
    (h_emb : MeasurableEmbedding (fun (p : T × T × T × T) => ctor p.1 p.2.1 p.2.2.1 p.2.2.2))
    (h_shape : ∀ p : T, shape p = s ↔
      ∃ p1 p2 p3 p4, p = ctor p1 p2 p3 p4 ∧
        shape p1 = s1 ∧ shape p2 = s2 ∧ shape p3 = s3 ∧ shape p4 = s4)
    (h_eq : ∀ b p1 p2 p3 p4,
      g b (ctor p1 p2 p3 p4) = c b (g b p1) (g b p2) (g b p3) (g b p4))
    (h_c : Measurable (fun (q : β × α × α × α × α) => c q.1 q.2.1 q.2.2.1 q.2.2.2.1 q.2.2.2.2))
    (ih1 : ∀ {U' : Set α}, MeasurableSet U' →
      MeasurableSet {q : β × T | shape q.2 = s1 ∧ Function.uncurry g q ∈ U'})
    (ih2 : ∀ {U' : Set α}, MeasurableSet U' →
      MeasurableSet {q : β × T | shape q.2 = s2 ∧ Function.uncurry g q ∈ U'})
    (ih3 : ∀ {U' : Set α}, MeasurableSet U' →
      MeasurableSet {q : β × T | shape q.2 = s3 ∧ Function.uncurry g q ∈ U'})
    (ih4 : ∀ {U' : Set α}, MeasurableSet U' →
      MeasurableSet {q : β × T | shape q.2 = s4 ∧ Function.uncurry g q ∈ U'})
    (hU : MeasurableSet U)
    [h_inhab : Inhabited β] :
    MeasurableSet {q : β × T | shape q.2 = s ∧ Function.uncurry g q ∈ U} := by
  have heq : {q : β × T | shape q.2 = s ∧ Function.uncurry g q ∈ U}
      = (fun (q : β × T × T × T × T) => (q.1, ctor q.2.1 q.2.2.1 q.2.2.2.1 q.2.2.2.2)) ''
        {q : β × T × T × T × T | shape q.2.1 = s1 ∧ shape q.2.2.1 = s2 ∧
          shape q.2.2.2.1 = s3 ∧ shape q.2.2.2.2 = s4 ∧
          (q.1, g q.1 q.2.1, g q.1 q.2.2.1, g q.1 q.2.2.2.1, g q.1 q.2.2.2.2) ∈
            ((fun (r : β × α × α × α × α) => c r.1 r.2.1 r.2.2.1 r.2.2.2.1 r.2.2.2.2) ⁻¹' U)} := by
    ext ⟨b, p⟩
    constructor
    · rintro ⟨hs, hp⟩
      obtain ⟨p1, p2, p3, p4, rfl, hs1, hs2, hs3, hs4⟩ := (h_shape p).mp hs
      refine ⟨(b, p1, p2, p3, p4), ⟨hs1, hs2, hs3, hs4, ?_⟩, rfl⟩
      simp only [Function.uncurry, Set.mem_preimage] at hp ⊢
      rw [h_eq] at hp; exact hp
    · rintro ⟨⟨b', p1, p2, p3, p4⟩, ⟨hs1, hs2, hs3, hs4, h⟩, heq⟩
      have hbeq : b' = b := by simpa using (Prod.mk.injEq ..).mp heq |>.1
      have hpeq : ctor p1 p2 p3 p4 = p := by simpa using (Prod.mk.injEq ..).mp heq |>.2
      subst hbeq hpeq
      refine ⟨(h_shape _).mpr ⟨p1, p2, p3, p4, rfl, hs1, hs2, hs3, hs4⟩, ?_⟩
      simp only [Function.uncurry, Set.mem_preimage] at h ⊢
      rw [h_eq]; exact h
  rw [heq]
  have h_emb_outer : MeasurableEmbedding
      (fun (q : β × T × T × T × T) => (q.1, ctor q.2.1 q.2.2.1 q.2.2.2.1 q.2.2.2.2)) := by
    have : (fun (q : β × T × T × T × T) => (q.1, ctor q.2.1 q.2.2.1 q.2.2.2.1 q.2.2.2.2))
        = Prod.map id (fun (p : T × T × T × T) => ctor p.1 p.2.1 p.2.2.1 p.2.2.2) := by
      ext ⟨_, _, _, _, _⟩ <;> rfl
    rw [this]
    exact MeasurableEmbedding.id.prodMap h_emb
  refine h_emb_outer.measurableSet_image' ?_
  have h_target : MeasurableSet
      ((fun (r : β × α × α × α × α) => c r.1 r.2.1 r.2.2.1 r.2.2.2.1 r.2.2.2.2) ⁻¹' U) := h_c hU
  set Joint : Set (β × α × α × α × α) → Set (β × T × T × T × T) :=
    fun W => {q : β × T × T × T × T | shape q.2.1 = s1 ∧ shape q.2.2.1 = s2 ∧
      shape q.2.2.2.1 = s3 ∧ shape q.2.2.2.2 = s4 ∧
      (q.1, g q.1 q.2.1, g q.1 q.2.2.1, g q.1 q.2.2.2.1, g q.1 q.2.2.2.2) ∈ W}
    with hJoint
  suffices h : ∀ W, MeasurableSet W → MeasurableSet (Joint W) by exact h _ h_target
  intro W hW
  -- π-system on β × α × α × α × α: rectangles B × R where R ⊆ α × α × α × α.
  have hgen : (Prod.instMeasurableSpace : MeasurableSpace (β × α × α × α × α))
      = .generateFrom (Set.image2 (· ×ˢ ·) {B : Set β | MeasurableSet B}
                                            {R : Set (α × α × α × α) | MeasurableSet R}) :=
    generateFrom_prod.symm
  have hpi : IsPiSystem (Set.image2 (· ×ˢ ·) {B : Set β | MeasurableSet B}
                                              {R : Set (α × α × α × α) | MeasurableSet R}) :=
    MeasurableSpace.isPiSystem_measurableSet.prod MeasurableSpace.isPiSystem_measurableSet
  have hsm : ∀ (sᵢ : Sh),
      (∀ {U' : Set α}, MeasurableSet U' →
        MeasurableSet {q : β × T | shape q.2 = sᵢ ∧ Function.uncurry g q ∈ U'}) →
      MeasurableSet {p : T | shape p = sᵢ} := by
    intro sᵢ ihᵢ
    have h1 := ihᵢ (MeasurableSet.univ (α := α))
    have hpreimg : (fun p : T => (h_inhab.default, p)) ⁻¹'
        {q : β × T | shape q.2 = sᵢ ∧ Function.uncurry g q ∈ Set.univ}
        = {p : T | shape p = sᵢ} := by ext p; simp
    rw [← hpreimg]
    exact MeasurableSet.preimage h1 (by fun_prop)
  have hs1m := hsm s1 ih1
  have hs2m := hsm s2 ih2
  have hs3m := hsm s3 ih3
  have hs4m := hsm s4 ih4
  -- Inner quaternary joint for all four children, over α × α × α × α.
  have hjoint1234 : ∀ R : Set (α × α × α × α), MeasurableSet R →
      MeasurableSet {q : β × T × T × T × T | shape q.2.1 = s1 ∧ shape q.2.2.1 = s2 ∧
        shape q.2.2.2.1 = s3 ∧ shape q.2.2.2.2 = s4 ∧
        (g q.1 q.2.1, g q.1 q.2.2.1, g q.1 q.2.2.2.1, g q.1 q.2.2.2.2) ∈ R} := by
    intro R hR
    set Jouter : Set (α × α × α × α) → Set (β × T × T × T × T) :=
      fun R' => {q : β × T × T × T × T | shape q.2.1 = s1 ∧ shape q.2.2.1 = s2 ∧
        shape q.2.2.2.1 = s3 ∧ shape q.2.2.2.2 = s4 ∧
        (g q.1 q.2.1, g q.1 q.2.2.1, g q.1 q.2.2.2.1, g q.1 q.2.2.2.2) ∈ R'}
      with hJouter
    suffices ∀ R', MeasurableSet R' → MeasurableSet (Jouter R') from this _ hR
    intro Rₒ hRₒ
    have hgenₒ : (Prod.instMeasurableSpace : MeasurableSpace (α × α × α × α))
        = .generateFrom (Set.image2 (· ×ˢ ·) {S : Set α | MeasurableSet S}
                                              {W : Set (α × α × α) | MeasurableSet W}) :=
      generateFrom_prod.symm
    have hpiₒ : IsPiSystem (Set.image2 (· ×ˢ ·) {S : Set α | MeasurableSet S}
                                                {W : Set (α × α × α) | MeasurableSet W}) :=
      MeasurableSpace.isPiSystem_measurableSet.prod MeasurableSpace.isPiSystem_measurableSet
    -- Inner ternary joint for children (s2, s3, s4), over α × α × α.
    have hjoint234 : ∀ R : Set (α × α × α), MeasurableSet R →
        MeasurableSet {q : β × T × T × T × T | shape q.2.1 = s1 ∧ shape q.2.2.1 = s2 ∧
          shape q.2.2.2.1 = s3 ∧ shape q.2.2.2.2 = s4 ∧
          (g q.1 q.2.2.1, g q.1 q.2.2.2.1, g q.1 q.2.2.2.2) ∈ R} := by
      intro R hR
      set J : Set (α × α × α) → Set (β × T × T × T × T) :=
        fun R' => {q : β × T × T × T × T | shape q.2.1 = s1 ∧ shape q.2.2.1 = s2 ∧
          shape q.2.2.2.1 = s3 ∧ shape q.2.2.2.2 = s4 ∧
          (g q.1 q.2.2.1, g q.1 q.2.2.2.1, g q.1 q.2.2.2.2) ∈ R'}
        with hJ
      suffices ∀ R', MeasurableSet R' → MeasurableSet (J R') from this _ hR
      intro R' hR'
      have hgen' : (Prod.instMeasurableSpace : MeasurableSpace (α × α × α))
          = .generateFrom (Set.image2 (· ×ˢ ·) {S : Set α | MeasurableSet S}
                                                {W : Set (α × α) | MeasurableSet W}) :=
        generateFrom_prod.symm
      have hpi' : IsPiSystem (Set.image2 (· ×ˢ ·) {S : Set α | MeasurableSet S}
                                                  {W : Set (α × α) | MeasurableSet W}) :=
        MeasurableSpace.isPiSystem_measurableSet.prod MeasurableSpace.isPiSystem_measurableSet
      -- Inner-inner helper for the last two children (s3, s4) over α × α.
      have hjoint34 : ∀ W : Set (α × α), MeasurableSet W →
          MeasurableSet {q : β × T × T × T × T | shape q.2.1 = s1 ∧ shape q.2.2.1 = s2 ∧
            shape q.2.2.2.1 = s3 ∧ shape q.2.2.2.2 = s4 ∧
            (g q.1 q.2.2.2.1, g q.1 q.2.2.2.2) ∈ W} := by
        intro W hW
        set K : Set (α × α) → Set (β × T × T × T × T) :=
          fun W' => {q : β × T × T × T × T | shape q.2.1 = s1 ∧ shape q.2.2.1 = s2 ∧
            shape q.2.2.2.1 = s3 ∧ shape q.2.2.2.2 = s4 ∧
            (g q.1 q.2.2.2.1, g q.1 q.2.2.2.2) ∈ W'}
          with hK
        suffices ∀ W', MeasurableSet W' → MeasurableSet (K W') from this _ hW
        intro W' hW'
        have hgen'' : (Prod.instMeasurableSpace : MeasurableSpace (α × α))
            = .generateFrom (Set.image2 (· ×ˢ ·) {S : Set α | MeasurableSet S}
                                                  {S : Set α | MeasurableSet S}) :=
          generateFrom_prod.symm
        have hpi'' : IsPiSystem (Set.image2 (· ×ˢ ·) {S : Set α | MeasurableSet S}
                                                    {S : Set α | MeasurableSet S}) :=
          MeasurableSpace.isPiSystem_measurableSet.prod MeasurableSpace.isPiSystem_measurableSet
        refine MeasurableSpace.induction_on_inter
          (C := fun W'' _ => MeasurableSet (K W'')) hgen'' hpi'' ?_ ?_ ?_ ?_ W' hW'
        · show MeasurableSet (K ∅); convert MeasurableSet.empty
          ext ⟨_, _, _, _, _⟩; simp [hK]
        · rintro _ ⟨V3, hV3, V4, hV4, rfl⟩
          show MeasurableSet (K (V3 ×ˢ V4))
          have : K (V3 ×ˢ V4)
              = ((fun (q : β × T × T × T × T) => q.2.1) ⁻¹' {p : T | shape p = s1})
                ∩ ((fun (q : β × T × T × T × T) => q.2.2.1) ⁻¹' {p : T | shape p = s2})
                ∩ ((fun (q : β × T × T × T × T) => (q.1, q.2.2.2.1)) ⁻¹'
                   {q : β × T | shape q.2 = s3 ∧ Function.uncurry g q ∈ V3})
                ∩ ((fun (q : β × T × T × T × T) => (q.1, q.2.2.2.2)) ⁻¹'
                   {q : β × T | shape q.2 = s4 ∧ Function.uncurry g q ∈ V4}) := by
            ext ⟨b, p1, p2, p3, p4⟩; simp [hK, Function.uncurry]; tauto
          rw [this]
          refine MeasurableSet.inter (MeasurableSet.inter (MeasurableSet.inter ?_ ?_) ?_) ?_
          · exact hs1m.preimage (by fun_prop)
          · exact hs2m.preimage (by fun_prop)
          · exact (ih3 hV3).preimage (by fun_prop)
          · exact (ih4 hV4).preimage (by fun_prop)
        · intro W'' _ IH
          show MeasurableSet (K W''ᶜ)
          have : K W''ᶜ
              = ((Set.univ : Set β) ×ˢ ({p : T | shape p = s1} ×ˢ {p : T | shape p = s2} ×ˢ
                 {p : T | shape p = s3} ×ˢ {p : T | shape p = s4})) \ K W'' := by
            ext ⟨b, p1, p2, p3, p4⟩; simp [hK]; tauto
          rw [this]
          refine MeasurableSet.diff ?_ IH
          exact MeasurableSet.univ.prod (hs1m.prod (hs2m.prod (hs3m.prod hs4m)))
        · intro F _ _ IH
          show MeasurableSet (K (⋃ i, F i))
          have : K (⋃ i, F i) = ⋃ i, K (F i) := by
            ext ⟨b, p1, p2, p3, p4⟩; simp only [hK, Set.mem_iUnion, Set.mem_setOf_eq]; tauto
          rw [this]; exact MeasurableSet.iUnion IH
      refine MeasurableSpace.induction_on_inter
        (C := fun R'' _ => MeasurableSet (J R'')) hgen' hpi' ?_ ?_ ?_ ?_ R' hR'
      · show MeasurableSet (J ∅); convert MeasurableSet.empty
        ext ⟨_, _, _, _, _⟩; simp [hJ]
      · rintro _ ⟨V2, hV2, W34, hW34, rfl⟩
        show MeasurableSet (J (V2 ×ˢ W34))
        have : J (V2 ×ˢ W34)
            = ((fun (q : β × T × T × T × T) => (q.1, q.2.2.1)) ⁻¹'
               {q : β × T | shape q.2 = s2 ∧ Function.uncurry g q ∈ V2})
              ∩ {q : β × T × T × T × T | shape q.2.1 = s1 ∧ shape q.2.2.1 = s2 ∧
                  shape q.2.2.2.1 = s3 ∧ shape q.2.2.2.2 = s4 ∧
                  (g q.1 q.2.2.2.1, g q.1 q.2.2.2.2) ∈ W34} := by
          ext ⟨b, p1, p2, p3, p4⟩; simp [hJ, Function.uncurry]; tauto
        rw [this]
        refine MeasurableSet.inter ?_ ?_
        · exact (ih2 hV2).preimage (by fun_prop)
        · exact hjoint34 W34 hW34
      · intro R'' _ IH
        show MeasurableSet (J R''ᶜ)
        have : J R''ᶜ
            = ((Set.univ : Set β) ×ˢ ({p : T | shape p = s1} ×ˢ {p : T | shape p = s2} ×ˢ
               {p : T | shape p = s3} ×ˢ {p : T | shape p = s4})) \ J R'' := by
          ext ⟨b, p1, p2, p3, p4⟩; simp [hJ]; tauto
        rw [this]
        refine MeasurableSet.diff ?_ IH
        exact MeasurableSet.univ.prod (hs1m.prod (hs2m.prod (hs3m.prod hs4m)))
      · intro F _ _ IH
        show MeasurableSet (J (⋃ i, F i))
        have : J (⋃ i, F i) = ⋃ i, J (F i) := by
          ext ⟨b, p1, p2, p3, p4⟩; simp only [hJ, Set.mem_iUnion, Set.mem_setOf_eq]; tauto
        rw [this]; exact MeasurableSet.iUnion IH
    -- outer induction (over Rₒ ⊆ α × α × α × α) for hjoint1234, factoring s1.
    refine MeasurableSpace.induction_on_inter
      (C := fun Rₒ' _ => MeasurableSet (Jouter Rₒ')) hgenₒ hpiₒ ?_ ?_ ?_ ?_ Rₒ hRₒ
    · show MeasurableSet (Jouter ∅); convert MeasurableSet.empty
      ext ⟨_, _, _, _, _⟩; simp [hJouter]
    · rintro _ ⟨V1, hV1, W234, hW234, rfl⟩
      show MeasurableSet (Jouter (V1 ×ˢ W234))
      have : Jouter (V1 ×ˢ W234)
          = ((fun (q : β × T × T × T × T) => (q.1, q.2.1)) ⁻¹'
             {q : β × T | shape q.2 = s1 ∧ Function.uncurry g q ∈ V1})
            ∩ {q : β × T × T × T × T | shape q.2.1 = s1 ∧ shape q.2.2.1 = s2 ∧
                shape q.2.2.2.1 = s3 ∧ shape q.2.2.2.2 = s4 ∧
                (g q.1 q.2.2.1, g q.1 q.2.2.2.1, g q.1 q.2.2.2.2) ∈ W234} := by
        ext ⟨b, p1, p2, p3, p4⟩; simp [hJouter, Function.uncurry]; tauto
      rw [this]
      refine MeasurableSet.inter ?_ ?_
      · exact (ih1 hV1).preimage (by fun_prop)
      · exact hjoint234 W234 hW234
    · intro Rₒ' _ IH
      show MeasurableSet (Jouter Rₒ'ᶜ)
      have : Jouter Rₒ'ᶜ
          = ((Set.univ : Set β) ×ˢ ({p : T | shape p = s1} ×ˢ {p : T | shape p = s2} ×ˢ
             {p : T | shape p = s3} ×ˢ {p : T | shape p = s4})) \ Jouter Rₒ' := by
        ext ⟨b, p1, p2, p3, p4⟩; simp [hJouter]; tauto
      rw [this]
      refine MeasurableSet.diff ?_ IH
      exact MeasurableSet.univ.prod (hs1m.prod (hs2m.prod (hs3m.prod hs4m)))
    · intro F _ _ IH
      show MeasurableSet (Jouter (⋃ i, F i))
      have : Jouter (⋃ i, F i) = ⋃ i, Jouter (F i) := by
        rw [hJouter]; ext ⟨b, p1, p2, p3, p4⟩; simp only [Set.mem_iUnion, Set.mem_setOf_eq]; tauto
      rw [this]; exact MeasurableSet.iUnion IH
  refine MeasurableSpace.induction_on_inter
    (C := fun W _ => MeasurableSet (Joint W)) hgen hpi ?_ ?_ ?_ ?_ W hW
  · show MeasurableSet (Joint ∅); convert MeasurableSet.empty
    rw [hJoint]; ext ⟨_, _, _, _, _⟩; simp
  · rintro _ ⟨B, hB, R, hR, rfl⟩
    show MeasurableSet (Joint (B ×ˢ R))
    have : Joint (B ×ˢ R)
        = (B ×ˢ (Set.univ : Set T) ×ˢ (Set.univ : Set T) ×ˢ (Set.univ : Set T) ×ˢ
            (Set.univ : Set T))
          ∩ {q : β × T × T × T × T | shape q.2.1 = s1 ∧ shape q.2.2.1 = s2 ∧
              shape q.2.2.2.1 = s3 ∧ shape q.2.2.2.2 = s4 ∧
              (g q.1 q.2.1, g q.1 q.2.2.1, g q.1 q.2.2.2.1, g q.1 q.2.2.2.2) ∈ R} := by
      rw [hJoint]; ext ⟨b, p1, p2, p3, p4⟩; simp; tauto
    rw [this]
    refine MeasurableSet.inter ?_ ?_
    · exact hB.prod (MeasurableSet.univ.prod (MeasurableSet.univ.prod
        (MeasurableSet.univ.prod MeasurableSet.univ)))
    · exact hjoint1234 R hR
  · intro W' _ IH
    show MeasurableSet (Joint W'ᶜ)
    have : Joint W'ᶜ
        = ((Set.univ : Set β) ×ˢ ({p : T | shape p = s1} ×ˢ {p : T | shape p = s2} ×ˢ
           {p : T | shape p = s3} ×ˢ {p : T | shape p = s4})) \ Joint W' := by
      rw [hJoint]; ext ⟨b, p1, p2, p3, p4⟩; simp; tauto
    rw [this]
    refine MeasurableSet.diff ?_ IH
    exact MeasurableSet.univ.prod (hs1m.prod (hs2m.prod (hs3m.prod hs4m)))
  · intro F _ _ IH
    show MeasurableSet (Joint (⋃ i, F i))
    have : Joint (⋃ i, F i) = ⋃ i, Joint (F i) := by
      rw [hJoint]; ext ⟨b, p1, p2, p3, p4⟩; simp only [Set.mem_iUnion, Set.mem_setOf_eq]; tauto
    rw [this]; exact MeasurableSet.iUnion IH

/-- **Mixed unary (param)**: e.g. `unop (op : UnOp) (e : T)`. Discrete `γ` arg + recursion. -/
theorem cell_unaryMixed_param {γ : Type _} [MeasurableSpace γ]
    [Countable γ] [MeasurableSingletonClass γ]
    {ctor : γ → T → T} {s : Sh} {sChild : γ → Sh}
    {c : β → γ → α → α} {U : Set α}
    (h_emb : MeasurableEmbedding (Function.uncurry ctor))
    (h_shape : ∀ p : T, shape p = s ↔ ∃ d p', p = ctor d p' ∧ shape p' = sChild d)
    (h_eq : ∀ b d p, g b (ctor d p) = c b d (g b p))
    (h_c : Measurable (fun (q : β × γ × α) => c q.1 q.2.1 q.2.2))
    (ih : ∀ d {U' : Set α}, MeasurableSet U' →
      MeasurableSet {q : β × T | shape q.2 = sChild d ∧ Function.uncurry g q ∈ U'})
    (hU : MeasurableSet U) :
    MeasurableSet {q : β × T | shape q.2 = s ∧ Function.uncurry g q ∈ U} := by
  -- Split over the discrete γ.
  have heq : {q : β × T | shape q.2 = s ∧ Function.uncurry g q ∈ U}
      = ⋃ d : γ, {q : β × T | (∃ p', q.2 = ctor d p' ∧ shape p' = sChild d)
                              ∧ Function.uncurry g q ∈ U} := by
    ext ⟨b, p⟩
    simp only [Set.mem_iUnion, Set.mem_setOf_eq]
    constructor
    · rintro ⟨hs, hp⟩
      obtain ⟨d, p', rfl, hs'⟩ := (h_shape p).mp hs
      exact ⟨d, ⟨p', rfl, hs'⟩, hp⟩
    · rintro ⟨d, ⟨p', rfl, hs'⟩, hp⟩
      exact ⟨(h_shape _).mpr ⟨d, p', rfl, hs'⟩, hp⟩
  rw [heq]
  refine MeasurableSet.iUnion fun d => ?_
  -- Per-d fiber: {(b, p) | ∃ p', p = ctor d p' ∧ shape p' = sChild d ∧ g b p ∈ U}
  -- = image of (b, p') ↦ (b, ctor d p') over {(b, p') | shape p' = sChild d ∧ c b d (g b p') ∈ U}.
  have hfiber : {q : β × T | (∃ p', q.2 = ctor d p' ∧ shape p' = sChild d)
                              ∧ Function.uncurry g q ∈ U}
      = (fun (q : β × T) => (q.1, ctor d q.2)) ''
        {q : β × T | shape q.2 = sChild d ∧
          (q.1, Function.uncurry g q) ∈ ((fun (r : β × α) => c r.1 d r.2) ⁻¹' U)} := by
    ext ⟨b, p⟩
    constructor
    · rintro ⟨⟨p', rfl, hs'⟩, hp⟩
      refine ⟨(b, p'), ⟨hs', ?_⟩, rfl⟩
      simp only [Set.mem_preimage, Function.uncurry] at hp ⊢
      rw [h_eq] at hp; exact hp
    · rintro ⟨⟨b', p'⟩, ⟨hs', hp'⟩, heq⟩
      have hbeq : b' = b := by simpa using (Prod.mk.injEq ..).mp heq |>.1
      have hpeq : ctor d p' = p := by simpa using (Prod.mk.injEq ..).mp heq |>.2
      subst hbeq hpeq
      refine ⟨⟨p', rfl, hs'⟩, ?_⟩
      simp only [Set.mem_preimage, Function.uncurry] at hp' ⊢
      rw [h_eq]; exact hp'
  rw [hfiber]
  -- Image under (b, p') ↦ (b, ctor d p') = Prod.map id (ctor d).
  have h_emb_d : MeasurableEmbedding (ctor d) := by
    refine ⟨?_, ?_, ?_⟩
    · intro x y hxy
      have : Function.uncurry ctor (d, x) = Function.uncurry ctor (d, y) := by
        simpa [Function.uncurry] using hxy
      exact ((Prod.mk.injEq ..).mp (h_emb.injective this)).2
    · exact h_emb.measurable.comp (by fun_prop : Measurable (fun x : T => (d, x)))
    · intro V hV
      have hreq : ctor d '' V = Function.uncurry ctor '' (({d} : Set γ) ×ˢ V) := by
        ext y; simp [Function.uncurry]
      rw [hreq]
      exact h_emb.measurableSet_image' ((MeasurableSet.singleton d).prod hV)
  have h_emb_pm : MeasurableEmbedding (fun (q : β × T) => (q.1, ctor d q.2)) := by
    have : (fun (q : β × T) => (q.1, ctor d q.2)) = Prod.map id (ctor d) := by
      ext ⟨_, _⟩ <;> rfl
    rw [this]
    exact MeasurableEmbedding.id.prodMap h_emb_d
  refine h_emb_pm.measurableSet_image' ?_
  -- Inner cell: π-system on β × α.
  have h_target : MeasurableSet ((fun (r : β × α) => c r.1 d r.2) ⁻¹' U) :=
    (h_c.comp (by fun_prop : Measurable (fun r : β × α => (r.1, d, r.2)))) hU
  set Joint : Set (β × α) → Set (β × T) :=
    fun W => {q : β × T | shape q.2 = sChild d ∧ (q.1, Function.uncurry g q) ∈ W}
    with hJoint
  suffices h : ∀ W, MeasurableSet W → MeasurableSet (Joint W) by exact h _ h_target
  intro W hW
  have hgen : (Prod.instMeasurableSpace : MeasurableSpace (β × α))
      = .generateFrom (Set.image2 (· ×ˢ ·) {B : Set β | MeasurableSet B}
                                            {A : Set α | MeasurableSet A}) :=
    generateFrom_prod.symm
  have hpi : IsPiSystem (Set.image2 (· ×ˢ ·) {B : Set β | MeasurableSet B}
                                              {A : Set α | MeasurableSet A}) :=
    MeasurableSpace.isPiSystem_measurableSet.prod MeasurableSpace.isPiSystem_measurableSet
  refine MeasurableSpace.induction_on_inter
    (C := fun W _ => MeasurableSet (Joint W)) hgen hpi ?_ ?_ ?_ ?_ W hW
  · show MeasurableSet (Joint ∅); convert MeasurableSet.empty
    ext ⟨_, _⟩; simp [hJoint]
  · rintro _ ⟨B, hB, A, hA, rfl⟩
    show MeasurableSet (Joint (B ×ˢ A))
    have : Joint (B ×ˢ A)
        = (B ×ˢ (Set.univ : Set T))
          ∩ {q : β × T | shape q.2 = sChild d ∧ Function.uncurry g q ∈ A} := by
      ext ⟨b, p⟩; simp [hJoint]; tauto
    rw [this]
    refine MeasurableSet.inter ?_ (ih d hA)
    exact hB.prod MeasurableSet.univ
  · intro W' _ IH
    show MeasurableSet (Joint W'ᶜ)
    have h_sd : MeasurableSet {q : β × T | shape q.2 = sChild d} := by
      have h1 := ih d (MeasurableSet.univ (α := α))
      convert h1 using 1
      ext ⟨b, p⟩; simp
    have : Joint W'ᶜ = {q : β × T | shape q.2 = sChild d} \ Joint W' := by
      ext ⟨b, p⟩; simp [hJoint]; tauto
    rw [this]
    exact h_sd.diff IH
  · intro F _ _ IH
    show MeasurableSet (Joint (⋃ i, F i))
    have : Joint (⋃ i, F i) = ⋃ i, Joint (F i) := by
      ext ⟨b, p⟩; simp only [hJoint, Set.mem_iUnion, Set.mem_setOf_eq]; tauto
    rw [this]; exact MeasurableSet.iUnion IH

/-- **Mixed binary (param)**: e.g. `binop (op : BinOp) e1 e2`. -/
theorem cell_binaryMixed_param {γ : Type _} [MeasurableSpace γ]
    [Countable γ] [MeasurableSingletonClass γ]
    {ctor : γ → T → T → T} {s : Sh} {sChild1 sChild2 : γ → Sh}
    {c : β → γ → α → α → α} {U : Set α}
    (h_emb : ∀ d, MeasurableEmbedding (Function.uncurry (ctor d)))
    (h_shape : ∀ p : T, shape p = s ↔
      ∃ d p1 p2, p = ctor d p1 p2 ∧ shape p1 = sChild1 d ∧ shape p2 = sChild2 d)
    (h_eq : ∀ b d p1 p2, g b (ctor d p1 p2) = c b d (g b p1) (g b p2))
    (h_c : ∀ d, Measurable (fun (q : β × α × α) => c q.1 d q.2.1 q.2.2))
    (ih1 : ∀ d {U' : Set α}, MeasurableSet U' →
      MeasurableSet {q : β × T | shape q.2 = sChild1 d ∧ Function.uncurry g q ∈ U'})
    (ih2 : ∀ d {U' : Set α}, MeasurableSet U' →
      MeasurableSet {q : β × T | shape q.2 = sChild2 d ∧ Function.uncurry g q ∈ U'})
    (hU : MeasurableSet U)
    [Inhabited β] :
    MeasurableSet {q : β × T | shape q.2 = s ∧ Function.uncurry g q ∈ U} := by
  -- Split over the discrete γ. For each d the per-fiber cell has a uniquely-pinned
  -- shape from h_shape; collect over γ to recover the full cell.
  have heq : {q : β × T | shape q.2 = s ∧ Function.uncurry g q ∈ U}
      = ⋃ d : γ, {q : β × T | (∃ p1 p2, q.2 = ctor d p1 p2
                                ∧ shape p1 = sChild1 d ∧ shape p2 = sChild2 d)
                              ∧ Function.uncurry g q ∈ U} := by
    ext ⟨b, p⟩
    simp only [Set.mem_iUnion, Set.mem_setOf_eq]
    constructor
    · rintro ⟨hs, hp⟩
      obtain ⟨d, p1, p2, rfl, hs1, hs2⟩ := (h_shape p).mp hs
      exact ⟨d, ⟨p1, p2, rfl, hs1, hs2⟩, hp⟩
    · rintro ⟨d, ⟨p1, p2, rfl, hs1, hs2⟩, hp⟩
      exact ⟨(h_shape _).mpr ⟨d, p1, p2, rfl, hs1, hs2⟩, hp⟩
  rw [heq]
  refine MeasurableSet.iUnion fun d => ?_
  -- Per-d fiber: identical to cell_binary_param's cell, modulo h_shape relabeling.
  -- Inline the cell_binary_param proof for this fiber.
  have hfiber : {q : β × T | (∃ p1 p2, q.2 = ctor d p1 p2
                                ∧ shape p1 = sChild1 d ∧ shape p2 = sChild2 d)
                              ∧ Function.uncurry g q ∈ U}
      = (fun (q : β × T × T) => (q.1, ctor d q.2.1 q.2.2)) ''
        {q : β × T × T | shape q.2.1 = sChild1 d ∧ shape q.2.2 = sChild2 d ∧
          (q.1, g q.1 q.2.1, g q.1 q.2.2) ∈
            ((fun (r : β × α × α) => c r.1 d r.2.1 r.2.2) ⁻¹' U)} := by
    ext ⟨b, p⟩
    constructor
    · rintro ⟨⟨p1, p2, rfl, hs1, hs2⟩, hp⟩
      refine ⟨(b, p1, p2), ⟨hs1, hs2, ?_⟩, rfl⟩
      simp only [Function.uncurry, Set.mem_preimage] at hp ⊢
      rw [h_eq] at hp; exact hp
    · rintro ⟨⟨b', p1, p2⟩, ⟨hs1, hs2, h⟩, heq⟩
      have hbeq : b' = b := by simpa using (Prod.mk.injEq ..).mp heq |>.1
      have hpeq : ctor d p1 p2 = p := by simpa using (Prod.mk.injEq ..).mp heq |>.2
      subst hbeq hpeq
      refine ⟨⟨p1, p2, rfl, hs1, hs2⟩, ?_⟩
      simp only [Function.uncurry, Set.mem_preimage] at h ⊢
      rw [h_eq]; exact h
  rw [hfiber]
  -- Same machinery as cell_binary_param body, with ctor d and c · d · ·.
  have h_emb_outer : MeasurableEmbedding
      (fun (q : β × T × T) => (q.1, ctor d q.2.1 q.2.2)) := by
    have : (fun (q : β × T × T) => (q.1, ctor d q.2.1 q.2.2))
        = Prod.map id (Function.uncurry (ctor d)) := by ext ⟨_, _, _⟩ <;> rfl
    rw [this]
    exact MeasurableEmbedding.id.prodMap (h_emb d)
  refine h_emb_outer.measurableSet_image' ?_
  have h_target : MeasurableSet ((fun (r : β × α × α) => c r.1 d r.2.1 r.2.2) ⁻¹' U) :=
    (h_c d) hU
  set Joint : Set (β × α × α) → Set (β × T × T) :=
    fun W => {q : β × T × T | shape q.2.1 = sChild1 d ∧ shape q.2.2 = sChild2 d ∧
      (q.1, g q.1 q.2.1, g q.1 q.2.2) ∈ W}
    with hJoint
  suffices h : ∀ W, MeasurableSet W → MeasurableSet (Joint W) by exact h _ h_target
  intro W hW
  have hgen : (Prod.instMeasurableSpace : MeasurableSpace (β × α × α))
      = .generateFrom (Set.image2 (· ×ˢ ·) {B : Set β | MeasurableSet B}
                                            {R : Set (α × α) | MeasurableSet R}) :=
    generateFrom_prod.symm
  have hpi : IsPiSystem (Set.image2 (· ×ˢ ·) {B : Set β | MeasurableSet B}
                                              {R : Set (α × α) | MeasurableSet R}) :=
    MeasurableSpace.isPiSystem_measurableSet.prod MeasurableSpace.isPiSystem_measurableSet
  have hs1m : MeasurableSet {p : T | shape p = sChild1 d} := by
    have h1 := ih1 d (MeasurableSet.univ (α := α))
    have hpreimg : (fun p : T => ((default : β), p)) ⁻¹'
        {q : β × T | shape q.2 = sChild1 d ∧ Function.uncurry g q ∈ Set.univ}
        = {p : T | shape p = sChild1 d} := by ext p; simp
    rw [← hpreimg]
    exact MeasurableSet.preimage h1 (by fun_prop)
  have hs2m : MeasurableSet {p : T | shape p = sChild2 d} := by
    have h2 := ih2 d (MeasurableSet.univ (α := α))
    have hpreimg : (fun p : T => ((default : β), p)) ⁻¹'
        {q : β × T | shape q.2 = sChild2 d ∧ Function.uncurry g q ∈ Set.univ}
        = {p : T | shape p = sChild2 d} := by ext p; simp
    rw [← hpreimg]
    exact MeasurableSet.preimage h2 (by fun_prop)
  have hjoint12 : ∀ R : Set (α × α), MeasurableSet R →
      MeasurableSet {q : β × T × T | shape q.2.1 = sChild1 d ∧ shape q.2.2 = sChild2 d ∧
        (g q.1 q.2.1, g q.1 q.2.2) ∈ R} := by
    intro R hR
    set J12 : Set (α × α) → Set (β × T × T) :=
      fun R' => {q : β × T × T | shape q.2.1 = sChild1 d ∧ shape q.2.2 = sChild2 d ∧
        (g q.1 q.2.1, g q.1 q.2.2) ∈ R'}
      with hJ12
    suffices ∀ R', MeasurableSet R' → MeasurableSet (J12 R') from this _ hR
    intro R' hR'
    have hgen' : (Prod.instMeasurableSpace : MeasurableSpace (α × α))
        = .generateFrom (Set.image2 (· ×ˢ ·) {S : Set α | MeasurableSet S}
                                              {S : Set α | MeasurableSet S}) :=
      generateFrom_prod.symm
    have hpi' : IsPiSystem
        (Set.image2 (· ×ˢ ·) {S : Set α | MeasurableSet S} {S : Set α | MeasurableSet S}) :=
      MeasurableSpace.isPiSystem_measurableSet.prod MeasurableSpace.isPiSystem_measurableSet
    refine MeasurableSpace.induction_on_inter
      (C := fun R'' _ => MeasurableSet (J12 R'')) hgen' hpi' ?_ ?_ ?_ ?_ R' hR'
    · show MeasurableSet (J12 ∅); convert MeasurableSet.empty
      ext ⟨_, _, _⟩; simp [hJ12]
    · rintro _ ⟨V1, hV1, V2, hV2, rfl⟩
      show MeasurableSet (J12 (V1 ×ˢ V2))
      have : J12 (V1 ×ˢ V2)
          = ((fun (q : β × T × T) => (q.1, q.2.1)) ⁻¹'
             {q : β × T | shape q.2 = sChild1 d ∧ Function.uncurry g q ∈ V1})
            ∩ ((fun (q : β × T × T) => (q.1, q.2.2)) ⁻¹'
               {q : β × T | shape q.2 = sChild2 d ∧ Function.uncurry g q ∈ V2}) := by
        ext ⟨b, p1, p2⟩; simp [hJ12, Function.uncurry]; tauto
      rw [this]
      refine MeasurableSet.inter ?_ ?_
      · exact (ih1 d hV1).preimage (by fun_prop)
      · exact (ih2 d hV2).preimage (by fun_prop)
    · intro R'' _ IH
      show MeasurableSet (J12 R''ᶜ)
      have : J12 R''ᶜ
          = ((Set.univ : Set β) ×ˢ ({p : T | shape p = sChild1 d} ×ˢ
             {p : T | shape p = sChild2 d}))
            \ J12 R'' := by
        ext ⟨b, p1, p2⟩; simp [hJ12]; tauto
      rw [this]
      refine MeasurableSet.diff ?_ IH
      refine MeasurableSet.univ.prod ?_
      exact hs1m.prod hs2m
    · intro F _ _ IH
      show MeasurableSet (J12 (⋃ i, F i))
      have : J12 (⋃ i, F i) = ⋃ i, J12 (F i) := by
        ext ⟨b, p1, p2⟩; simp only [hJ12, Set.mem_iUnion, Set.mem_setOf_eq]; tauto
      rw [this]; exact MeasurableSet.iUnion IH
  refine MeasurableSpace.induction_on_inter
    (C := fun W _ => MeasurableSet (Joint W)) hgen hpi ?_ ?_ ?_ ?_ W hW
  · show MeasurableSet (Joint ∅); convert MeasurableSet.empty
    ext ⟨_, _, _⟩; simp [hJoint]
  · rintro _ ⟨B, hB, R, hR, rfl⟩
    show MeasurableSet (Joint (B ×ˢ R))
    have : Joint (B ×ˢ R)
        = (B ×ˢ (Set.univ : Set T) ×ˢ (Set.univ : Set T))
          ∩ {q : β × T × T | shape q.2.1 = sChild1 d ∧ shape q.2.2 = sChild2 d ∧
              (g q.1 q.2.1, g q.1 q.2.2) ∈ R} := by
      ext ⟨b, p1, p2⟩; simp [hJoint]; tauto
    rw [this]
    refine MeasurableSet.inter ?_ ?_
    · exact hB.prod (MeasurableSet.univ.prod MeasurableSet.univ)
    · exact hjoint12 R hR
  · intro W' _ IH
    show MeasurableSet (Joint W'ᶜ)
    have : Joint W'ᶜ
        = ((Set.univ : Set β) ×ˢ ({p : T | shape p = sChild1 d} ×ˢ
           {p : T | shape p = sChild2 d}))
          \ Joint W' := by
      ext ⟨b, p1, p2⟩; simp [hJoint]; tauto
    rw [this]
    refine MeasurableSet.diff ?_ IH
    refine MeasurableSet.univ.prod ?_
    exact hs1m.prod hs2m
  · intro F _ _ IH
    show MeasurableSet (Joint (⋃ i, F i))
    have : Joint (⋃ i, F i) = ⋃ i, Joint (F i) := by
      ext ⟨b, p1, p2⟩; simp only [hJoint, Set.mem_iUnion, Set.mem_setOf_eq]; tauto
    rw [this]; exact MeasurableSet.iUnion IH

/-- **Foreign data leaf (param)**: e.g. `scrut (e : T) (p : Pat)`. -/
theorem cell_scrutLike_param {γ : Type _} [MeasurableSpace γ]
    {ctor : T → γ → T} {s sChild : Sh}
    {c : β → α → γ → α} {U : Set α}
    (h_emb : MeasurableEmbedding (Function.uncurry ctor))
    (h_shape : ∀ p : T, shape p = s ↔ ∃ p' d, p = ctor p' d ∧ shape p' = sChild)
    (h_eq : ∀ b p d, g b (ctor p d) = c b (g b p) d)
    (h_c : Measurable (fun (q : β × α × γ) => c q.1 q.2.1 q.2.2))
    (ih : ∀ {U' : Set α}, MeasurableSet U' →
      MeasurableSet {q : β × T | shape q.2 = sChild ∧ Function.uncurry g q ∈ U'})
    (hU : MeasurableSet U)
    [h_inhab : Inhabited β] :
    MeasurableSet {q : β × T | shape q.2 = s ∧ Function.uncurry g q ∈ U} := by
  -- Cell = image of (b, (p', d)) ↦ (b, ctor p' d).
  have heq : {q : β × T | shape q.2 = s ∧ Function.uncurry g q ∈ U}
      = (fun (q : β × T × γ) => (q.1, ctor q.2.1 q.2.2)) ''
        {q : β × T × γ | shape q.2.1 = sChild ∧
          (q.1, g q.1 q.2.1, q.2.2) ∈
            ((fun (r : β × α × γ) => c r.1 r.2.1 r.2.2) ⁻¹' U)} := by
    ext ⟨b, p⟩
    constructor
    · rintro ⟨hs, hp⟩
      obtain ⟨p', d, rfl, hs'⟩ := (h_shape p).mp hs
      refine ⟨(b, p', d), ⟨hs', ?_⟩, rfl⟩
      simp only [Function.uncurry, Set.mem_preimage] at hp ⊢
      rw [h_eq] at hp; exact hp
    · rintro ⟨⟨b', p', d⟩, ⟨hs', h⟩, heq⟩
      have hbeq : b' = b := by simpa using (Prod.mk.injEq ..).mp heq |>.1
      have hpeq : ctor p' d = p := by simpa using (Prod.mk.injEq ..).mp heq |>.2
      subst hbeq hpeq
      refine ⟨(h_shape _).mpr ⟨p', d, rfl, hs'⟩, ?_⟩
      simp only [Function.uncurry, Set.mem_preimage] at h ⊢
      rw [h_eq]; exact h
  rw [heq]
  have h_emb_outer : MeasurableEmbedding (fun (q : β × T × γ) => (q.1, ctor q.2.1 q.2.2)) := by
    have : (fun (q : β × T × γ) => (q.1, ctor q.2.1 q.2.2))
        = Prod.map id (Function.uncurry ctor) := by ext ⟨_, _, _⟩ <;> rfl
    rw [this]
    exact MeasurableEmbedding.id.prodMap h_emb
  refine h_emb_outer.measurableSet_image' ?_
  have h_target : MeasurableSet ((fun (r : β × α × γ) => c r.1 r.2.1 r.2.2) ⁻¹' U) :=
    h_c hU
  -- Joint cell: π-system on β × α × γ.
  set Joint : Set (β × α × γ) → Set (β × T × γ) :=
    fun W => {q : β × T × γ | shape q.2.1 = sChild ∧ (q.1, g q.1 q.2.1, q.2.2) ∈ W}
    with hJoint
  suffices h : ∀ W, MeasurableSet W → MeasurableSet (Joint W) by exact h _ h_target
  intro W hW
  have hgen : (Prod.instMeasurableSpace : MeasurableSpace (β × α × γ))
      = .generateFrom (Set.image2 (· ×ˢ ·) {B : Set β | MeasurableSet B}
                                            {R : Set (α × γ) | MeasurableSet R}) :=
    generateFrom_prod.symm
  have hpi : IsPiSystem (Set.image2 (· ×ˢ ·) {B : Set β | MeasurableSet B}
                                              {R : Set (α × γ) | MeasurableSet R}) :=
    MeasurableSpace.isPiSystem_measurableSet.prod MeasurableSpace.isPiSystem_measurableSet
  have hschildm : MeasurableSet {p : T | shape p = sChild} := by
    have h1 := ih (MeasurableSet.univ (α := α))
    have hpreimg : (fun p : T => (h_inhab.default, p)) ⁻¹'
        {q : β × T | shape q.2 = sChild ∧ Function.uncurry g q ∈ Set.univ}
        = {p : T | shape p = sChild} := by ext p; simp
    rw [← hpreimg]
    exact MeasurableSet.preimage h1 (by fun_prop)
  -- Inner joint helper for α × γ rectangles.
  have hjoint : ∀ R : Set (α × γ), MeasurableSet R →
      MeasurableSet {q : β × T × γ | shape q.2.1 = sChild ∧ (g q.1 q.2.1, q.2.2) ∈ R} := by
    intro R hR
    set J : Set (α × γ) → Set (β × T × γ) :=
      fun R' => {q : β × T × γ | shape q.2.1 = sChild ∧ (g q.1 q.2.1, q.2.2) ∈ R'}
      with hJ
    suffices ∀ R', MeasurableSet R' → MeasurableSet (J R') from this _ hR
    intro R' hR'
    have hgen' : (Prod.instMeasurableSpace : MeasurableSpace (α × γ))
        = .generateFrom (Set.image2 (· ×ˢ ·) {S : Set α | MeasurableSet S}
                                              {S : Set γ | MeasurableSet S}) :=
      generateFrom_prod.symm
    have hpi' : IsPiSystem
        (Set.image2 (· ×ˢ ·) {S : Set α | MeasurableSet S} {S : Set γ | MeasurableSet S}) :=
      MeasurableSpace.isPiSystem_measurableSet.prod MeasurableSpace.isPiSystem_measurableSet
    refine MeasurableSpace.induction_on_inter
      (C := fun R'' _ => MeasurableSet (J R'')) hgen' hpi' ?_ ?_ ?_ ?_ R' hR'
    · show MeasurableSet (J ∅); convert MeasurableSet.empty
      ext ⟨_, _, _⟩; simp [hJ]
    · rintro _ ⟨V1, hV1, V2, hV2, rfl⟩
      show MeasurableSet (J (V1 ×ˢ V2))
      have : J (V1 ×ˢ V2)
          = ((fun (q : β × T × γ) => (q.1, q.2.1)) ⁻¹'
             {q : β × T | shape q.2 = sChild ∧ Function.uncurry g q ∈ V1})
            ∩ ((fun (q : β × T × γ) => q.2.2) ⁻¹' V2) := by
        ext ⟨b, p, d⟩; simp [hJ, Function.uncurry]; tauto
      rw [this]
      refine MeasurableSet.inter ?_ ?_
      · exact (ih hV1).preimage (by fun_prop)
      · exact hV2.preimage (by fun_prop)
    · intro R'' _ IH
      show MeasurableSet (J R''ᶜ)
      have : J R''ᶜ
          = ((Set.univ : Set β) ×ˢ ({p : T | shape p = sChild} ×ˢ (Set.univ : Set γ)))
            \ J R'' := by
        ext ⟨b, p, d⟩; simp [hJ]; tauto
      rw [this]
      refine MeasurableSet.diff ?_ IH
      exact MeasurableSet.univ.prod (hschildm.prod MeasurableSet.univ)
    · intro F _ _ IH
      show MeasurableSet (J (⋃ i, F i))
      have : J (⋃ i, F i) = ⋃ i, J (F i) := by
        ext ⟨b, p, d⟩; simp only [hJ, Set.mem_iUnion, Set.mem_setOf_eq]; tauto
      rw [this]; exact MeasurableSet.iUnion IH
  refine MeasurableSpace.induction_on_inter
    (C := fun W _ => MeasurableSet (Joint W)) hgen hpi ?_ ?_ ?_ ?_ W hW
  · show MeasurableSet (Joint ∅); convert MeasurableSet.empty
    ext ⟨_, _, _⟩; simp [hJoint]
  · rintro _ ⟨B, hB, R, hR, rfl⟩
    show MeasurableSet (Joint (B ×ˢ R))
    have : Joint (B ×ˢ R)
        = (B ×ˢ (Set.univ : Set T) ×ˢ (Set.univ : Set γ))
          ∩ {q : β × T × γ | shape q.2.1 = sChild ∧ (g q.1 q.2.1, q.2.2) ∈ R} := by
      ext ⟨b, p, d⟩; simp [hJoint]; tauto
    rw [this]
    refine MeasurableSet.inter ?_ ?_
    · exact hB.prod (MeasurableSet.univ.prod MeasurableSet.univ)
    · exact hjoint R hR
  · intro W' _ IH
    show MeasurableSet (Joint W'ᶜ)
    have : Joint W'ᶜ
        = ((Set.univ : Set β) ×ˢ ({p : T | shape p = sChild} ×ˢ (Set.univ : Set γ)))
          \ Joint W' := by
      ext ⟨b, p, d⟩; simp [hJoint]; tauto
    rw [this]
    refine MeasurableSet.diff ?_ IH
    exact MeasurableSet.univ.prod (hschildm.prod MeasurableSet.univ)
  · intro F _ _ IH
    show MeasurableSet (Joint (⋃ i, F i))
    have : Joint (⋃ i, F i) = ⋃ i, Joint (F i) := by
      ext ⟨b, p, d⟩; simp only [hJoint, Set.mem_iUnion, Set.mem_setOf_eq]; tauto
    rw [this]; exact MeasurableSet.iUnion IH

/-- **Shape-partition assembly (param)**: glues per-shape joint cell measurability
into global measurability of `Function.uncurry g`. -/
theorem measurable_of_cells_param [Countable Sh]
    (h_cell : ∀ (s : Sh) {U : Set α}, MeasurableSet U →
      MeasurableSet {q : β × T | shape q.2 = s ∧ Function.uncurry g q ∈ U}) :
    Measurable (Function.uncurry g) := by
  intro S hS
  rw [show (Function.uncurry g ⁻¹' S)
        = ⋃ s : Sh, {q : β × T | shape q.2 = s ∧ Function.uncurry g q ∈ S} from by
    ext q
    simp only [Set.mem_preimage, Set.mem_iUnion, Set.mem_setOf_eq]
    exact ⟨fun h => ⟨_, rfl, h⟩, fun ⟨_, _, h⟩ => h⟩]
  exact MeasurableSet.iUnion fun s => h_cell s hS

end StructRec

/-! ## Measurable space on `List X`.

`List X` is a countable disjoint union of products, parameterized by length:
`List X ≃ Σ n, Fin n → X`. We induce the σ-algebra via the forward map
`l ↦ ⟨l.length, l.get⟩` — i.e. as the comap of this map.

This gives us: a set `S ⊆ List X` is measurable iff the corresponding sets of
length-`n` lists are measurable in the product σ-algebra, for each `n`.

Downstream lemmas (measurability of `List.cons`, `List.foldl`, etc.) are
straightforward but voluminous; we add them as needed. -/

/-- Forward equivalence: a list to (length, indexed function). -/
def List.toSigma {X : Type _} (l : List X) : Σ n, Fin n → X := ⟨l.length, l.get⟩

/-- The σ-algebra on `List X`: comap from the `Σ n, Fin n → X` encoding. -/
instance List.instMeasurableSpace {X : Type _} [MeasurableSpace X] :
    MeasurableSpace (List X) :=
  MeasurableSpace.comap List.toSigma inferInstance

@[fun_prop]
theorem List.measurable_toSigma {X : Type _} [MeasurableSpace X] :
    Measurable (List.toSigma : List X → Σ n, Fin n → X) :=
  fun _ hS => ⟨_, hS, rfl⟩

/-- Sigma-fiber measurability: a function `f : (Σ a, β a) → γ` is measurable iff
its restriction to each fiber `fun b : β a => f ⟨a, b⟩` is measurable.

The Sigma σ-algebra is `⨅ a, (m a).map (Sigma.mk a)`, so this is direct from the
definition. Symmetric to `Sigma.instMeasurableSpace` being the coinduced σ-alg. -/
theorem measurable_sigma_iff {α : Type _} {β : α → Type _}
    [∀ a, MeasurableSpace (β a)] {γ : Type _} [MeasurableSpace γ]
    {f : (Σ a, β a) → γ} : Measurable f ↔ ∀ a, Measurable (fun b => f ⟨a, b⟩) := by
  refine ⟨fun hf a => hf.comp ?_, fun h S hS => MeasurableSpace.measurableSet_iInf.mpr fun a => h a hS⟩
  -- `Sigma.mk a` is measurable: target is `⨅ a', _.map (Sigma.mk a')`; under this,
  -- preimage of any set `S` under `Sigma.mk a` is required to be measurable.
  intro S hS
  exact MeasurableSpace.measurableSet_iInf.mp hS a

/-- Iterated application of `f` indexed by `Fin n`. Equals `(List.ofFn g).foldl f a`. -/
def List.foldlOfFn {α β : Type _} (f : α → β → α) : ∀ (n : ℕ), α → (Fin n → β) → α
  | 0, a, _ => a
  | n+1, a, g => List.foldlOfFn f n (f a (g 0)) (fun i => g i.succ)

theorem List.foldlOfFn_eq_foldl_ofFn {α β : Type _} (f : α → β → α) :
    ∀ (n : ℕ) (a : α) (g : Fin n → β), List.foldlOfFn f n a g = (List.ofFn g).foldl f a := by
  intro n
  induction n with
  | zero => intros; rfl
  | succ n ih =>
    intro a g
    show List.foldlOfFn f n (f a (g 0)) (fun i => g i.succ)
        = (List.ofFn g).foldl f a
    rw [ih]
    rw [List.ofFn_succ, List.foldl_cons]

theorem List.measurable_foldlOfFn {α β : Type _}
    [MeasurableSpace α] [MeasurableSpace β]
    {f : α → β → α} (hf : Measurable (Function.uncurry f)) :
    ∀ n, Measurable (fun (p : (Fin n → β) × α) => List.foldlOfFn f n p.2 p.1) := by
  intro n
  induction n with
  | zero =>
    show Measurable (fun (p : (Fin 0 → β) × α) => p.2)
    exact measurable_snd
  | succ n ih =>
    have h0 : Measurable (fun p : (Fin (n+1) → β) × α => p.1 0) :=
      (measurable_pi_apply 0).comp measurable_fst
    have hsucc : Measurable
        (fun p : (Fin (n+1) → β) × α => (fun i : Fin n => p.1 i.succ)) := by
      refine measurable_pi_lambda _ ?_
      intro i
      exact (measurable_pi_apply _).comp measurable_fst
    have hfa : Measurable (fun p : (Fin (n+1) → β) × α => f p.2 (p.1 0)) := by
      have hrw : (fun p : (Fin (n+1) → β) × α => f p.2 (p.1 0))
          = Function.uncurry f ∘ (fun p => (p.2, p.1 0)) := rfl
      rw [hrw]; exact hf.comp (measurable_snd.prodMk h0)
    have hcomp : Measurable
        (fun p : (Fin (n+1) → β) × α =>
          (((fun i : Fin n => p.1 i.succ) : Fin n → β), f p.2 (p.1 0))) :=
      hsucc.prodMk hfa
    exact ih.comp hcomp

/-- `Sigma.mk i` is a measurable embedding for the standard Σ σ-algebra. -/
theorem MeasurableEmbedding.sigmaMk {ι : Type _} {β : ι → Type _}
    [∀ i, MeasurableSpace (β i)] (i : ι) :
    MeasurableEmbedding (Sigma.mk i : β i → Σ j, β j) := by
  refine ⟨?_, ?_, ?_⟩
  · -- Injective
    intro x y h; exact eq_of_heq (Sigma.mk.inj h).2
  · -- Measurable
    intro V hV
    exact MeasurableSpace.measurableSet_iInf.mp hV i
  · -- Image of measurable is measurable
    intro s hs
    refine MeasurableSpace.measurableSet_iInf.mpr fun j => ?_
    by_cases hj : j = i
    · subst hj
      show MeasurableSet ((Sigma.mk j) ⁻¹' (Sigma.mk j '' s))
      convert hs
      ext x
      refine ⟨?_, fun hx => ⟨x, hx, rfl⟩⟩
      rintro ⟨y, hy, h⟩
      exact eq_of_heq (Sigma.mk.inj h).2 ▸ hy
    · show MeasurableSet ((Sigma.mk j) ⁻¹' (Sigma.mk i '' s))
      convert MeasurableSet.empty
      ext x; simp only [Set.mem_preimage, Set.mem_image, Set.mem_empty_iff_false, iff_false]
      rintro ⟨y, _, h⟩
      exact (hj (Sigma.mk.inj h).1.symm).elim

/-- **`List.foldl` is measurable** in `(list, init)` whenever the binary operation
`f` is jointly measurable.

Decomposition via `List.toSigma`: a function out of `List β` factors through the
per-length fibers `(Fin n → β) × α → α`, each of which is a finite composition
of `n` applications of `f`. Sigma-fiber measurability glues these together. -/
@[fun_prop]
theorem List.measurable_foldl {α β : Type _} [MeasurableSpace α] [MeasurableSpace β]
    {f : α → β → α} (hf : Measurable (Function.uncurry f)) :
    Measurable (fun (p : List β × α) => p.1.foldl f p.2) := by
  -- Factor: foldl = H ∘ swap ∘ (toSigma × id), where
  --   H : Σ n, (Fin n → β) × α → α,   H ⟨n, (g, a)⟩ := List.foldlOfFn f n a g
  --   swap : (Σ n, Fin n → β) × α → Σ n, (Fin n → β) × α,
  --          swap ((⟨n, g⟩), a) := ⟨n, (g, a)⟩
  set H : (Σ n : ℕ, (Fin n → β) × α) → α :=
    fun s => List.foldlOfFn f s.1 s.2.2 s.2.1
  have hH : Measurable H := by
    rw [measurable_sigma_iff]
    intro n; exact List.measurable_foldlOfFn hf n
  -- Identity: foldl p = H (swap (toSigma p.1, p.2))
  have hgoal_eq : (fun p : List β × α => p.1.foldl f p.2)
      = H ∘ (fun q : (Σ k : ℕ, Fin k → β) × α =>
          (⟨q.1.1, (q.1.2, q.2)⟩ : Σ k : ℕ, (Fin k → β) × α))
        ∘ (fun p : List β × α => (List.toSigma p.1, p.2)) := by
    funext p
    show p.1.foldl f p.2 = List.foldlOfFn f (List.toSigma p.1).1 p.2 (List.toSigma p.1).2
    rw [List.foldlOfFn_eq_foldl_ofFn]
    show p.1.foldl f p.2 = (List.ofFn p.1.get).foldl f p.2
    rw [List.ofFn_get]
  rw [hgoal_eq]
  -- Compose measurabilities.
  refine hH.comp ?_
  refine Measurable.comp ?_
    ((List.measurable_toSigma).comp measurable_fst |>.prodMk measurable_snd)
  -- Prove `swap` measurable.
  intro U hU
  -- For each k₀, `Sigma.mk k₀ ⁻¹' U` is measurable in (Fin k₀ → β) × α.
  have hUfib : ∀ k₀, MeasurableSet
      ((@Sigma.mk ℕ (fun k => (Fin k → β) × α) k₀) ⁻¹' U) := by
    intro k₀
    exact MeasurableSpace.measurableSet_iInf.mp hU k₀
  -- swap ⁻¹' U = ⋃ k₀, (Sigma.mk k₀ × id) '' (Sigma.mk k₀ ⁻¹' U).
  have hrw : (fun q : (Σ k : ℕ, Fin k → β) × α =>
        (⟨q.1.1, (q.1.2, q.2)⟩ : Σ k : ℕ, (Fin k → β) × α)) ⁻¹' U
      = ⋃ k₀ : ℕ, (Prod.map (@Sigma.mk ℕ (fun k => Fin k → β) k₀) (id : α → α))
          '' ((@Sigma.mk ℕ (fun k => (Fin k → β) × α) k₀) ⁻¹' U) := by
    ext q
    obtain ⟨⟨k, g⟩, a⟩ := q
    simp only [Set.mem_preimage, Set.mem_iUnion, Set.mem_image, Prod.map_apply, id_eq]
    constructor
    · intro h
      exact ⟨k, (g, a), h, rfl⟩
    · rintro ⟨k₀, ⟨g₀, a₀⟩, hga, hq⟩
      -- hq : (Sigma.mk k₀ g₀, a₀) = (⟨k, g⟩, a)
      rw [Prod.mk.injEq, Sigma.mk.injEq] at hq
      obtain ⟨⟨hk, hg⟩, ha⟩ := hq
      subst hk
      cases hg
      subst ha
      exact hga
  rw [hrw]
  refine MeasurableSet.iUnion fun k₀ => ?_
  -- Image of measurable under product of measurable embeddings.
  have hEmb : MeasurableEmbedding
      (Prod.map (@Sigma.mk ℕ (fun k => Fin k → β) k₀) (id : α → α)) :=
    (MeasurableEmbedding.sigmaMk k₀).prodMap MeasurableEmbedding.id
  exact hEmb.measurableSet_image' (hUfib k₀)

/-- Per-`n`, `Fin.snoc` is jointly measurable in `(g, b)`. -/
@[fun_prop]
theorem Fin.measurable_snoc {n : ℕ} {β : Type _} [MeasurableSpace β] :
    Measurable (fun (p : (Fin n → β) × β) => (@Fin.snoc n (fun _ => β) p.1 p.2) : (Fin n → β) × β → (Fin (n+1) → β)) := by
  refine measurable_pi_lambda _ fun i => ?_
  by_cases h : i.val < n
  · have heq : ∀ p : (Fin n → β) × β,
        ((@Fin.snoc n (fun _ => β) p.1 p.2) i : β) = p.1 ⟨i.val, h⟩ := by
      intro p
      simp [Fin.snoc, h, Fin.castLT]
    rw [show (fun p : (Fin n → β) × β => ((@Fin.snoc n (fun _ => β) p.1 p.2) i : β))
          = fun p => p.1 ⟨i.val, h⟩ from funext heq]
    exact (measurable_pi_apply _).comp measurable_fst
  · push_neg at h
    have hi : i = Fin.last n := Fin.ext (le_antisymm (Nat.lt_succ_iff.mp i.isLt) h)
    have heq : ∀ p : (Fin n → β) × β, ((@Fin.snoc n (fun _ => β) p.1 p.2) i : β) = p.2 := by
      intro p; rw [hi, Fin.snoc_last]
    rw [show (fun p : (Fin n → β) × β => ((@Fin.snoc n (fun _ => β) p.1 p.2) i : β))
          = fun p => p.2 from funext heq]
    exact measurable_snd

/-- The "snoc into Σ" function: `((⟨k, g⟩), b) ↦ ⟨k+1, Fin.snoc g b⟩`. Measurable. -/
@[fun_prop]
theorem measurable_sigma_snoc {β : Type _} [MeasurableSpace β] :
    Measurable (fun (q : (Σ k : ℕ, Fin k → β) × β) =>
      (⟨q.1.1 + 1, Fin.snoc q.1.2 q.2⟩ : Σ k : ℕ, Fin k → β)) := by
  intro U hU
  -- Strategy mirrors swap measurability in List.measurable_foldl.
  have hUfib : ∀ k₀, MeasurableSet
      ((@Sigma.mk ℕ (fun k => Fin k → β) k₀) ⁻¹' U) := by
    intro k₀
    exact MeasurableSpace.measurableSet_iInf.mp hU k₀
  -- Preimage decomposes by q.1.1 = k₀:
  have hrw : (fun q : (Σ k : ℕ, Fin k → β) × β =>
        (⟨q.1.1 + 1, Fin.snoc q.1.2 q.2⟩ : Σ k : ℕ, Fin k → β)) ⁻¹' U
      = ⋃ k₀ : ℕ, (Prod.map (@Sigma.mk ℕ (fun k => Fin k → β) k₀) (id : β → β))
          '' ((fun p : (Fin k₀ → β) × β => (@Fin.snoc k₀ (fun _ => β) p.1 p.2))
              ⁻¹' ((@Sigma.mk ℕ (fun k => Fin k → β) (k₀ + 1)) ⁻¹' U)) := by
    ext q
    obtain ⟨⟨k, g⟩, b⟩ := q
    simp only [Set.mem_preimage, Set.mem_iUnion, Set.mem_image, Prod.map_apply, id_eq]
    constructor
    · intro h
      exact ⟨k, (g, b), h, rfl⟩
    · rintro ⟨k₀, ⟨g₀, b₀⟩, hsnoc, hq⟩
      rw [Prod.mk.injEq, Sigma.mk.injEq] at hq
      obtain ⟨⟨hk, hg⟩, hb⟩ := hq
      subst hk
      cases hg
      subst hb
      exact hsnoc
  rw [hrw]
  refine MeasurableSet.iUnion fun k₀ => ?_
  have hEmb : MeasurableEmbedding
      (Prod.map (@Sigma.mk ℕ (fun k => Fin k → β) k₀) (id : β → β)) :=
    (MeasurableEmbedding.sigmaMk k₀).prodMap MeasurableEmbedding.id
  refine hEmb.measurableSet_image' ?_
  exact Fin.measurable_snoc (hUfib (k₀ + 1))

/-- **`(L, x) ↦ L ++ [x]`** is measurable. -/
@[fun_prop]
theorem List.measurable_append_singleton {β : Type _} [MeasurableSpace β] :
    Measurable (fun (p : List β × β) => p.1 ++ [p.2]) := by
  rw [measurable_comap_iff (g := (List.toSigma : List β → Σ k, Fin k → β))]
  -- Goal: Measurable (toSigma ∘ (fun p => p.1 ++ [p.2])).
  -- Show equal to `measurable_sigma_snoc.fn ∘ (toSigma × id)`, which is measurable.
  have hrw : (List.toSigma : List β → Σ k, Fin k → β) ∘ (fun p : List β × β => p.1 ++ [p.2])
      = (fun q : (Σ k, Fin k → β) × β =>
          (⟨q.1.1 + 1, Fin.snoc q.1.2 q.2⟩ : Σ k, Fin k → β))
        ∘ (fun p : List β × β => (List.toSigma p.1, p.2)) := by
    funext p
    obtain ⟨L, x⟩ := p
    show (@Sigma.mk ℕ (fun k => Fin k → β) (L ++ [x]).length (L ++ [x]).get)
        = ⟨L.length + 1, @Fin.snoc L.length (fun _ => β) L.get x⟩
    have hlen : (L ++ [x]).length = L.length + 1 := by simp
    refine Sigma.ext hlen ?_
    refine (Fin.heq_fun_iff hlen).mpr ?_
    intro i
    have hlt : i.val < L.length + 1 := hlen ▸ i.isLt
    show (L ++ [x]).get i = (@Fin.snoc L.length (fun _ => β) L.get x) ⟨i.val, hlt⟩
    by_cases hi : i.val < L.length
    · have hcast : (⟨i.val, hlt⟩ : Fin (L.length + 1))
          = ((⟨i.val, hi⟩ : Fin L.length).castSucc) := Fin.ext rfl
      rw [hcast, Fin.snoc_castSucc]
      simp [List.getElem_append, hi]
    · push_neg at hi
      have hival : i.val = L.length := by omega
      have hcast : ((⟨i.val, hlt⟩ : Fin (L.length + 1)))
          = Fin.last L.length := Fin.ext hival
      rw [hcast, Fin.snoc_last]
      have hi' : ¬ i.val < L.length := Nat.not_lt.mpr hi
      simp [List.getElem_append, hi', hival]
  rw [hrw]
  exact measurable_sigma_snoc.comp
    ((List.measurable_toSigma).comp measurable_fst |>.prodMk measurable_snd)

/-- **Joint parameterized pushforward**. Given a jointly measurable function
`h : α × β → γ` and a kernel-valued source `k : α → Measure β` measurable that
is moreover an s-finite kernel, the parameterized pushforward
`fun a => (k a).map (fun b => h (a, b))` is measurable.

Proof: via `measurable_of_measurable_coe`, each `S`-evaluation reduces to
`fun a => k a (Prod.mk a ⁻¹' (h ⁻¹' S))`, which is exactly the section-measure
lemma `Kernel.measurable_kernel_prodMk_left` applied to the kernel `Kernel.mk k hk`.
The `IsSFiniteKernel` assumption ensures the section-measure machinery applies. -/
theorem Measure.measurable_map_uncurry {α β γ : Type _}
    [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    {h : α × β → γ} (hh : Measurable h)
    {k : α → Measure β} (hk : Measurable k)
    [hSF : ProbabilityTheory.IsSFiniteKernel (ProbabilityTheory.Kernel.mk k hk)] :
    Measurable (fun a : α => (k a).map (fun b => h (a, b))) := by
  refine Measure.measurable_of_measurable_coe _ ?_
  intro S hS
  have hpre : ∀ a, Measurable (fun b : β => h (a, b)) := fun a =>
    hh.comp (measurable_const.prodMk measurable_id)
  simp_rw [fun a => Measure.map_apply (hpre a) hS]
  set T := h ⁻¹' S with hT_def
  have hT : MeasurableSet T := hh hS
  have hrw : ∀ a, (fun b => h (a, b)) ⁻¹' S = Prod.mk a ⁻¹' T := fun _ => rfl
  simp_rw [hrw]
  show Measurable (fun a => k a (Prod.mk a ⁻¹' T))
  have hker_eq : ∀ a, k a = (ProbabilityTheory.Kernel.mk k hk) a :=
    fun _ => by rw [ProbabilityTheory.Kernel.coe_mk]
  simp_rw [hker_eq]
  exact ProbabilityTheory.Kernel.measurable_kernel_prodMk_left hT

/-- Candidate measure built pointwise from a `ℕ`-monotone family of measures.

For a monotone family `μ : ℕ → Measure α`, define `myν` via `Measure.ofMeasurable`
with `myν s := ⨆ i, μ i s` (for measurable `s`). The σ-additivity reduces to
swapping `⨆` past `∑'` on monotone ENNReal data. -/
noncomputable def Measure.monotoneSupNat {α : Type _} [MeasurableSpace α]
    (μ : ℕ → Measure α) (hmono : Monotone μ) : Measure α :=
  Measure.ofMeasurable (fun s _ => ⨆ i, μ i s)
    (by simp)
    (fun f hf hd => by
      have h1 : ∀ i, μ i (⋃ k, f k) = ∑' k, μ i (f k) :=
        fun i => measure_iUnion hd hf
      have hmono' : ∀ k, Monotone (fun i => μ i (f k)) :=
        fun k i j hij => hmono hij (f k)
      simp_rw [h1, ENNReal.tsum_eq_iSup_sum]
      rw [iSup_comm]
      refine iSup_congr fun s => ?_
      exact (ENNReal.finsetSum_iSup_of_monotone
        (s := s) (f := fun k i => μ i (f k)) hmono').symm)

theorem Measure.monotoneSupNat_apply {α : Type _} [MeasurableSpace α]
    (μ : ℕ → Measure α) (hmono : Monotone μ)
    {s : Set α} (hs : MeasurableSet s) :
    Measure.monotoneSupNat μ hmono s = ⨆ i, μ i s :=
  Measure.ofMeasurable_apply _ hs

/-- For a `ℕ`-monotone family of measures, the pointwise sup `(⨆ i, μ i) s` on
measurable sets `s` equals the sup of values `⨆ i, μ i s`. -/
theorem Measure.iSup_apply_of_monotone {α : Type _} [MeasurableSpace α]
    (μ : ℕ → Measure α) (hmono : Monotone μ)
    {s : Set α} (hs : MeasurableSet s) :
    (⨆ i, μ i) s = ⨆ i, μ i s := by
  have h : Measure.monotoneSupNat μ hmono = ⨆ i, μ i := by
    apply le_antisymm
    · rw [Measure.le_iff]; intro t ht
      rw [Measure.monotoneSupNat_apply _ _ ht]
      exact iSup_le fun i => Measure.le_iff.mp (le_iSup μ i) t ht
    · refine iSup_le fun i => ?_
      rw [Measure.le_iff]; intro t ht
      rw [Measure.monotoneSupNat_apply _ _ ht]
      exact le_iSup (fun j => μ j t) i
  rw [← h, Measure.monotoneSupNat_apply _ _ hs]

/-- **Pointwise `ℕ`-monotone sup of measure-valued functions is measurable**.

For a family `μ : ℕ → α → Measure β` of measurable maps, the pointwise
supremum `fun a => ⨆ i, μ i a` is measurable into `Measure β`, provided that at
every `a`, the family is monotone in `i`. -/
theorem Measure.measurable_iSup_countable {α β : Type _}
    [MeasurableSpace α] [MeasurableSpace β]
    {μ : ℕ → α → Measure β} (hμ : ∀ i, Measurable (μ i))
    (hmono : ∀ a, Monotone (fun i => μ i a)) :
    Measurable (fun a : α => ⨆ i, μ i a) := by
  refine Measure.measurable_of_measurable_coe _ ?_
  intro s hs
  simp_rw [fun a => Measure.iSup_apply_of_monotone (μ · a) (hmono a) hs]
  exact Measurable.iSup fun i => (Measure.measurable_coe hs).comp (hμ i)
