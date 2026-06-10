module

public import Metrology.ProbLang.Measure

meta import Metrology.Meta

@[expose] public section

noncomputable section ProbLangMeasures
open Classical MeasureTheory ProbabilityTheory Measure

/-! # Shared stamping infrastructure (Phase 1)

This file is the single shared home for the CoreMeasures "stamping" technique that
`BaseLit.lean`, `Pat.lean`, `Exp.lean`, and `EctxItem.lean` each instantiate. It must
**not** import any of those four type files (no cycles): it depends only on
`Metrology.ProbLang.Measure` and `Metrology.Meta`.

It provides:

* the four (formerly per-file) tactic macros `solve_ι_inj`, `solve_cover_measurable`,
  `solve_cover_eq_image`, `solve_discrete_ME`, plus `solve_nullary_ME`;
* a dedicated `@[stamp_simp]` simp set used to tag the per-type `flatten`, `shape`,
  `Cylinder.shape`, `Shape.cylinder`, and `cover.*` defining equations;
* the Class A (verbatim-generic-modulo-type) lemmas, proved once with explicit
  arguments.  Per-type files instantiate these in one line.

See `STAMPING.md` and `notes/stampability-plan.md`. -/

/-! ## §1 Shared tactic macros

These were previously re-defined in each of the four type files. The unqualified
identifiers in their bodies (`flatten_measurable`) resolve at the macro *expansion*
site, i.e. inside the per-type namespace, so a single shared definition works. -/

/-- Injectivity of an η-expanded constructor `T.<ctor>.ι`. One `first`-arm per arity;
the third arm fires for ctors with ≥3 arguments (`Exp`, `EctxItem`). -/
macro "solve_ι_inj" : tactic => `(tactic|
  (intro a b h;
   first
   | (cases h; rfl)
   | (obtain ⟨_, _⟩ := a; obtain ⟨_, _⟩ := b; cases h; rfl)
   | (obtain ⟨_, _, _⟩ := a; obtain ⟨_, _, _⟩ := b; cases h; rfl)
   | (obtain ⟨_, _, _, _⟩ := a; obtain ⟨_, _, _, _⟩ := b; cases h; rfl)))

-- Measurability of a per-constructor cover: the `⋃`-covers go through the first arm,
-- the direct (data-leaf) covers through the second.  `set_option hygiene false` so the
-- unqualified `flatten_measurable` resolves to the per-type lemma at the expansion site.
set_option hygiene false in
macro "solve_cover_measurable" : tactic => `(tactic|
  first
  | exact .biUnion (Set.to_countable _) fun _ _ => flatten_measurable ((by measurability))
  | exact flatten_measurable ((by measurability)))

/-- A per-constructor cover equals the corresponding image / range; proved by case
analysis on the term and unfolding the named cover definition. -/
macro "solve_cover_eq_image" ctor:ident : tactic => `(tactic|
  (ext p; cases p <;> simp [$ctor:ident]))

/-- `MeasurableEmbedding` of a discrete (syntax-leaf or data-leaf) constructor, given
the cover-`eq_image` lemma and the cover-measurability lemma. -/
macro "solve_discrete_ME" eq_image:term ", " meas:term : tactic => `(tactic|
  (refine ⟨fun _ _ h => by injection h, (by measurability), fun S _ => ?_⟩
   rw [← $eq_image S]
   exact $meas S))

/-- `MeasurableEmbedding` of a nullary (Unit-domain) constructor via the
`of_measurable_inverse` route. Used when a type has ≥2 nullary constructors
(`EctxItem`); single-nullary files may inline it instead.

Takes the per-constructor `cover` function, its `_eq_image` lemma, and its
`.measurable` lemma (all sharing the constructor's namespace, so the three call-site
arguments differ only in the constructor name). The cover application must be named
explicitly (not a metavariable) so the forward `rw [eq_image]` finds its pattern. -/
macro "solve_nullary_ME" cover:term ", " eq_image:term ", " meas:term : tactic => `(tactic|
  (apply MeasurableEmbedding.of_measurable_inverse (g := fun _ => ())
   · exact measurable_const
   · rw [show Set.range _ = $cover Set.univ from by rw [$eq_image:term]; ext; simp]
     exact $meas _
   · exact measurable_const
   · intro; rfl))

/-! ## §1b Fixed-left-factor embedding (mixed syntax-leaf × recursive constructors)

A mixed constructor (a discrete syntax leaf followed by recursive children) has its
uncurried form `Function.uncurry ctor : C × X → T` as a measurable embedding (proved
once per type via `measurableEmbedding_of_piSystemₙ`). In the keystone the leaf value
`c` is already fixed by the `Shape` arm, so the per-case dispatch needs
`MeasurableEmbedding (fun x => ctor c x)` at that fixed `c`. This lemma derives the
fixed-`c` slice generically, collapsing the bespoke inline derivations that the three
`Exp` keystones previously duplicated for `unop`/`binop`. -/

/-- Slice of an uncurried measurable embedding at a fixed left factor `c`.
Given `MeasurableEmbedding (f : C × X → Y)` and `MeasurableSet ({c} : Set C)`,
the partial application `fun x => f (c, x)` is itself a measurable embedding.
In practice `C` is a countable discrete syntax-leaf type, so `{c}` is measurable. -/
theorem MeasurableEmbedding.of_uncurry_fixed_left
    {C X Y : Type _} [MeasurableSpace C] [MeasurableSpace X] [MeasurableSpace Y]
    {f : C × X → Y} (hf : MeasurableEmbedding f) {c : C} (hc : MeasurableSet ({c} : Set C)) :
    MeasurableEmbedding (fun x : X => f (c, x)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro x y hxy
    exact (Prod.mk.injEq .. |>.mp (hf.injective hxy)).2
  · exact hf.measurable.comp (by fun_prop : Measurable (fun x : X => (c, x)))
  · intro V hV
    have heq : (fun x : X => f (c, x)) '' V = f '' (({c} : Set C) ×ˢ V) := by
      ext y; simp [Set.mem_prod]
    rw [heq]
    exact hf.measurableSet_image' (hc.prod hV)

/-! ## §2 The `stamp_simp` simp set

The per-type files tag their `flatten`, `shape`, `Cylinder.shape`, `Shape.cylinder`,
and `cover.*` defining equations with `@[stamp_simp]`. Canonical stamped proofs can
then say `simp [stamp_simp]` instead of carrying an ad-hoc lemma list. (Phase 1 only
*registers and tags*; rewriting existing proofs to use it is a later phase.) -/

register_simp_attr stamp_simp

/-! ## §3 Class A generic lemmas

The "verbatim-generic" lemmas of `STAMPING.md`: identical across the four type files
modulo the type name. They are proved here **once** as plain lemmas with explicit
arguments (deliberately *not* a bundled typeclass — see the plan), parametrized over:

* `Cyl` the cylinder type, `T` the underlying type, `Shp` the (countable) shape type;
* `flatten : Cyl → Set T`, `shape : T → Shp`, `cShape : Cyl → Shp` (`Cylinder.shape`),
  `sCyl : Shp → Cyl` (`Shape.cylinder`), `inter? : Cyl → Cyl → Option Cyl`,
  `HML : Cyl → Prop` (`HasMeasurableLeaves`);

and the genuinely-structural per-type facts supplied at the instantiation site
(`shape_of_mem_flatten`, `flatten_inter`, `hasMeasurableLeaves_inter`,
`cylinder_preimage_shape`, `cylinder_hasMeasurableLeaves`). -/

namespace Stamp

variable {Cyl T Shp : Type _}
  {flatten : Cyl → Set T} {shape : T → Shp} {cShape : Cyl → Shp}

/-- Flattens of cylinders with different shapes are disjoint.
(from `shape_of_mem_flatten`). -/
theorem flatten_disjoint_of_shape_ne
    (shape_of_mem : ∀ {c : Cyl} {p : T}, p ∈ flatten c → shape p = cShape c)
    {c₁ c₂ : Cyl} (h : cShape c₁ ≠ cShape c₂) :
    flatten c₁ ∩ flatten c₂ = ∅ := by
  ext p
  simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false, not_and]
  intro hp₁ hp₂
  exact h ((shape_of_mem hp₁).symm.trans (shape_of_mem hp₂))

/-- The flatten of an intersection is the intersection of flattens (from the
`Option.elim` `flatten_inter` equation). -/
theorem flatten_inter_some {inter? : Cyl → Cyl → Option Cyl}
    (flatten_inter : ∀ c₁ c₂ : Cyl,
      flatten c₁ ∩ flatten c₂ = (inter? c₁ c₂).elim ∅ flatten)
    {c₁ c₂ c : Cyl} (h : inter? c₁ c₂ = some c) :
    flatten c = flatten c₁ ∩ flatten c₂ := by
  rw [flatten_inter, h]; rfl

/-- The cylinder-flatten family is a π-system (from `flatten_inter` +
`hasMeasurableLeaves_inter`). -/
theorem flatten_isPiSystem {inter? : Cyl → Cyl → Option Cyl} {HML : Cyl → Prop}
    (flatten_inter : ∀ c₁ c₂ : Cyl,
      flatten c₁ ∩ flatten c₂ = (inter? c₁ c₂).elim ∅ flatten)
    (hML_inter : ∀ {c₁ c₂ c : Cyl}, HML c₁ → HML c₂ → inter? c₁ c₂ = some c → HML c) :
    IsPiSystem ({S : Set T | ∃ c : Cyl, HML c ∧ flatten c = S}) := by
  rintro _ ⟨c₁, hc₁, rfl⟩ _ ⟨c₂, hc₂, rfl⟩ hne
  have hi : inter? c₁ c₂ ≠ none := by
    intro h
    have : flatten c₁ ∩ flatten c₂ = ∅ := by rw [flatten_inter, h]; rfl
    exact hne.ne_empty this
  obtain ⟨c, hc⟩ : ∃ c, inter? c₁ c₂ = some c := Option.ne_none_iff_exists'.mp hi
  exact ⟨c, hML_inter hc₁ hc₂ hc, flatten_inter_some flatten_inter hc⟩

/-- The cylinder-flatten family is countably spanning (from `Countable Shp`,
`cylinder_hasMeasurableLeaves`, `cylinder_preimage_shape`, and totality of `shape`).
`fallback : Cyl` is any cylinder with `HML fallback` (a nullary / syntax-leaf one). -/
theorem flatten_isCountablySpanning [Countable Shp] {HML : Cyl → Prop} {sCyl : Shp → Cyl}
    (hML_cyl : ∀ s : Shp, HML (sCyl s))
    (preimage_shape : ∀ s : Shp, flatten (sCyl s) = shape ⁻¹' {s})
    (fallback : Cyl) (hML_fallback : HML fallback) :
    IsCountablySpanning ({S : Set T | ∃ c : Cyl, HML c ∧ flatten c = S}) := by
  obtain ⟨enc⟩ := nonempty_encodable Shp
  refine ⟨fun n =>
    match enc.decode n with
    | some s => flatten (sCyl s)
    | none => flatten fallback, ?_, ?_⟩
  · intro n
    cases h : enc.decode n with
    | none => exact ⟨fallback, hML_fallback, by simp [h]⟩
    | some s => exact ⟨sCyl s, hML_cyl s, by simp [h]⟩
  · ext p
    simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
    refine ⟨enc.encode (shape p), ?_⟩
    have hd : enc.decode (enc.encode (shape p)) = some (shape p) := enc.encodek _
    rw [hd]
    simp [preimage_shape]

/-- Flattening a cylinder with measurable leaves yields a measurable set (from the
`generateFrom` instance shape). `hgen` records that the instance σ-algebra *is* the
generated one. -/
theorem flatten_measurable {HML : Cyl → Prop} [m : MeasurableSpace T]
    (hgen : m = .generateFrom (flatten '' {c : Cyl | HML c}))
    {c : Cyl} (hc : HML c) : MeasurableSet (flatten c) := by
  subst hgen
  exact MeasurableSpace.measurableSet_generateFrom ⟨c, hc, rfl⟩

/-- The `MeasurableSingletonClass` skeleton (from `singletonCyl_flatten` +
`singletonCyl_hasMeasurableLeaves`). -/
theorem measurableSet_singleton {HML : Cyl → Prop} [m : MeasurableSpace T]
    (hgen : m = .generateFrom (flatten '' {c : Cyl | HML c}))
    {sCylP : T → Cyl}
    (sCylP_flatten : ∀ p : T, flatten (sCylP p) = {p})
    (sCylP_hML : ∀ p : T, HML (sCylP p))
    (p : T) : MeasurableSet ({p} : Set T) := by
  rw [← sCylP_flatten p]
  subst hgen
  exact MeasurableSpace.measurableSet_generateFrom ⟨sCylP p, sCylP_hML p, rfl⟩

/-! ### Diagonal `flatten_inter` lemmas (Phase 2)

The diagonal cases of each per-type `Cylinder.flatten_inter` proof — where both
cylinders share the same recursive/leaf constructor — all have the same shape modulo
arity. These lemmas package that shape so each per-case use is a single `exact`
(after the per-type `inter?`/`flatten` match has been reduced by `simp`).

The pattern: the goal is
`flatten (W …) ∩ flatten (W …) = (inter? (W …) (W …)).elim ∅ flatten`,
where `W` is the per-type cylinder constructor that wraps the children. By
defeq, `flatten (W c…) = ctor '' (product of flatten c…)` and
`inter? (W c…) (W c'…) = (combine of inner inter?).map W`; the per-case proof
supplies these by `simp [Cylinder.inter?]` reducing the goal to the abstract form
these lemmas prove, expressed via `Option.map`. -/

/-- Unary recursive diagonal: `ctor` injective, child IH as an `Option.elim`
equation. Conclusion uses `Option.map wrap` so the per-type `inter?` match
(`some r => some (W r) | none => none`) reduces to it by `simp`. -/
theorem flatten_inter_image₁ {ctor : T → T} (hctor : Function.Injective ctor)
    (wrap : Cyl → Cyl) (hwrap : ∀ c, flatten (wrap c) = ctor '' flatten c)
    {c c' : Cyl} {o oₜ : Option Cyl}
    (hinner : flatten c ∩ flatten c' = o.elim ∅ flatten)
    (hcomb : oₜ = o.map wrap) :
    ctor '' flatten c ∩ ctor '' flatten c' = oₜ.elim ∅ flatten := by
  rw [← Set.image_inter hctor, hinner, hcomb]
  cases o with
  | none => simp
  | some r => simp [hwrap r]

/-- Binary recursive diagonal: `uncurry ctor` injective, two child IHs.  The two
inner options are combined by `Option.bind`/`map` matching the per-type
`match …, … with | some, some => … | _, _ => none`. -/
theorem flatten_inter_image₂ {ctor : T → T → T}
    (hctor : Function.Injective (Function.uncurry ctor))
    (wrap : Cyl → Cyl → Cyl)
    (hwrap : ∀ c₁ c₂, flatten (wrap c₁ c₂) = (fun p => ctor p.1 p.2) '' (flatten c₁ ×ˢ flatten c₂))
    {a b a' b' : Cyl} {o₁ o₂ oₜ : Option Cyl}
    (hinner₁ : flatten a ∩ flatten a' = o₁.elim ∅ flatten)
    (hinner₂ : flatten b ∩ flatten b' = o₂.elim ∅ flatten)
    (hcomb : oₜ = (o₁.bind fun r₁ => o₂.map fun r₂ => wrap r₁ r₂)) :
    (fun p => ctor p.1 p.2) '' (flatten a ×ˢ flatten b) ∩
        (fun p => ctor p.1 p.2) '' (flatten a' ×ˢ flatten b') =
      oₜ.elim ∅ flatten := by
  rw [← Set.image_inter (f := fun p : T × T => ctor p.1 p.2) hctor,
    Set.prod_inter_prod, hinner₁, hinner₂, hcomb]
  cases o₁ with
  | none => simp
  | some r₁ =>
    cases o₂ with
    | none => simp
    | some r₂ => simp [hwrap r₁ r₂]

/-- Ternary recursive diagonal. -/
theorem flatten_inter_image₃ {ctor : T → T → T → T}
    (hctor : Function.Injective (fun p : T × T × T => ctor p.1 p.2.1 p.2.2))
    (wrap : Cyl → Cyl → Cyl → Cyl)
    (hwrap : ∀ c₁ c₂ c₃, flatten (wrap c₁ c₂ c₃) =
      (fun p : T × T × T => ctor p.1 p.2.1 p.2.2) '' (flatten c₁ ×ˢ flatten c₂ ×ˢ flatten c₃))
    {a b d a' b' d' : Cyl} {o₁ o₂ o₃ oₜ : Option Cyl}
    (hinner₁ : flatten a ∩ flatten a' = o₁.elim ∅ flatten)
    (hinner₂ : flatten b ∩ flatten b' = o₂.elim ∅ flatten)
    (hinner₃ : flatten d ∩ flatten d' = o₃.elim ∅ flatten)
    (hcomb : oₜ = (o₁.bind fun r₁ => o₂.bind fun r₂ => o₃.map fun r₃ => wrap r₁ r₂ r₃)) :
    (fun p : T × T × T => ctor p.1 p.2.1 p.2.2) '' (flatten a ×ˢ flatten b ×ˢ flatten d) ∩
        (fun p : T × T × T => ctor p.1 p.2.1 p.2.2) '' (flatten a' ×ˢ flatten b' ×ˢ flatten d') =
      oₜ.elim ∅ flatten := by
  rw [← Set.image_inter (f := fun p : T × T × T => ctor p.1 p.2.1 p.2.2) hctor,
    Set.prod_inter_prod, Set.prod_inter_prod, hinner₁, hinner₂, hinner₃, hcomb]
  cases o₁ with
  | none => simp
  | some r₁ => cases o₂ with
    | none => simp
    | some r₂ => cases o₃ with
      | none => simp
      | some r₃ => simp [hwrap r₁ r₂ r₃]

/-- Quaternary recursive diagonal (arity-extension appendix, §21): copied from
`flatten_inter_image₃` with one extra child. -/
theorem flatten_inter_image₄ {ctor : T → T → T → T → T}
    (hctor : Function.Injective (fun p : T × T × T × T => ctor p.1 p.2.1 p.2.2.1 p.2.2.2))
    (wrap : Cyl → Cyl → Cyl → Cyl → Cyl)
    (hwrap : ∀ c₁ c₂ c₃ c₄, flatten (wrap c₁ c₂ c₃ c₄) =
      (fun p : T × T × T × T => ctor p.1 p.2.1 p.2.2.1 p.2.2.2) ''
        (flatten c₁ ×ˢ flatten c₂ ×ˢ flatten c₃ ×ˢ flatten c₄))
    {a b d e a' b' d' e' : Cyl} {o₁ o₂ o₃ o₄ oₜ : Option Cyl}
    (hinner₁ : flatten a ∩ flatten a' = o₁.elim ∅ flatten)
    (hinner₂ : flatten b ∩ flatten b' = o₂.elim ∅ flatten)
    (hinner₃ : flatten d ∩ flatten d' = o₃.elim ∅ flatten)
    (hinner₄ : flatten e ∩ flatten e' = o₄.elim ∅ flatten)
    (hcomb : oₜ = (o₁.bind fun r₁ => o₂.bind fun r₂ => o₃.bind fun r₃ =>
      o₄.map fun r₄ => wrap r₁ r₂ r₃ r₄)) :
    (fun p : T × T × T × T => ctor p.1 p.2.1 p.2.2.1 p.2.2.2) ''
        (flatten a ×ˢ flatten b ×ˢ flatten d ×ˢ flatten e) ∩
        (fun p : T × T × T × T => ctor p.1 p.2.1 p.2.2.1 p.2.2.2) ''
        (flatten a' ×ˢ flatten b' ×ˢ flatten d' ×ˢ flatten e') =
      oₜ.elim ∅ flatten := by
  rw [← Set.image_inter (f := fun p : T × T × T × T => ctor p.1 p.2.1 p.2.2.1 p.2.2.2) hctor,
    Set.prod_inter_prod, Set.prod_inter_prod, Set.prod_inter_prod,
    hinner₁, hinner₂, hinner₃, hinner₄, hcomb]
  cases o₁ with
  | none => simp
  | some r₁ => cases o₂ with
    | none => simp
    | some r₂ => cases o₃ with
      | none => simp
      | some r₃ => cases o₄ with
        | none => simp
        | some r₄ => simp [hwrap r₁ r₂ r₃ r₄]

/-- Mixed (syntax-leaf × unary recursive) diagonal: the per-type `inter?` gates on
the leaf equality `if u = u' then (recurse) else none`. When the leaves differ the
two flattens are disjoint (different shapes); the lemma handles both branches. The
syntax-leaf factor is fixed to `u` on the left, `u'` on the right. -/
theorem flatten_inter_mixed₁ {L : Type _} [DecidableEq L] {ctor : L → T → T}
    (hctor : ∀ l, Function.Injective (ctor l))
    (hctor_leaf : ∀ {l l' : L} {x y : T}, ctor l x = ctor l' y → l = l')
    (wrap : L → Cyl → Cyl) (hwrap : ∀ l c, flatten (wrap l c) = ctor l '' flatten c)
    {u u' : L} {c c' : Cyl} {o oₜ : Option Cyl}
    (hinner : flatten c ∩ flatten c' = o.elim ∅ flatten)
    (hcomb : oₜ = (if u = u' then o.map (wrap u) else none)) :
    ctor u '' flatten c ∩ ctor u' '' flatten c' = oₜ.elim ∅ flatten := by
  subst hcomb
  by_cases hu : u = u'
  · subst hu
    rw [← Set.image_inter (hctor u), hinner]
    cases o with
    | none => simp
    | some r => simp [hwrap u r]
  · simp only [hu, if_false, Option.elim_none]
    ext z
    simp only [Set.mem_inter_iff, Set.mem_image, Set.mem_empty_iff_false, iff_false, not_and]
    rintro ⟨x, _, rfl⟩ ⟨y, _, hh⟩
    exact hu (hctor_leaf hh).symm

/-- Mixed (syntax-leaf × binary recursive) diagonal. -/
theorem flatten_inter_mixed₂ {L : Type _} [DecidableEq L] {ctor : L → T → T → T}
    (hctor : ∀ l, Function.Injective (fun p : T × T => ctor l p.1 p.2))
    (hctor_leaf : ∀ {l l' : L} {x₁ x₂ y₁ y₂ : T}, ctor l x₁ x₂ = ctor l' y₁ y₂ → l = l')
    (wrap : L → Cyl → Cyl → Cyl)
    (hwrap : ∀ l c₁ c₂, flatten (wrap l c₁ c₂) =
      (fun p : T × T => ctor l p.1 p.2) '' (flatten c₁ ×ˢ flatten c₂))
    {u u' : L} {a b a' b' : Cyl} {o₁ o₂ oₜ : Option Cyl}
    (hinner₁ : flatten a ∩ flatten a' = o₁.elim ∅ flatten)
    (hinner₂ : flatten b ∩ flatten b' = o₂.elim ∅ flatten)
    (hcomb : oₜ = (if u = u' then o₁.bind (fun r₁ => o₂.map fun r₂ => wrap u r₁ r₂) else none)) :
    (fun p : T × T => ctor u p.1 p.2) '' (flatten a ×ˢ flatten b) ∩
        (fun p : T × T => ctor u' p.1 p.2) '' (flatten a' ×ˢ flatten b') = oₜ.elim ∅ flatten := by
  subst hcomb
  by_cases hu : u = u'
  · subst hu
    rw [← Set.image_inter (hctor u), Set.prod_inter_prod, hinner₁, hinner₂]
    cases o₁ with
    | none => simp
    | some r₁ => cases o₂ with
      | none => simp
      | some r₂ => simp [hwrap u r₁ r₂]
  · simp only [hu, if_false, Option.elim_none]
    ext z
    simp only [Set.mem_inter_iff, Set.mem_image, Set.mem_empty_iff_false, iff_false, not_and]
    rintro ⟨x, _, rfl⟩ ⟨y, _, hh⟩
    exact hu (hctor_leaf hh).symm

/-- Scrut-like (recursive × foreign data leaf) diagonal: the second factor is a raw
`Set` (the data leaf), intersected directly; the per-type `inter?` recurses on the
recursive factor and intersects the data sets. -/
theorem flatten_inter_scrut {D : Type _} {ctor : T → D → T}
    (hctor : Function.Injective (fun p : T × D => ctor p.1 p.2))
    (wrap : Cyl → Set D → Cyl)
    (hwrap : ∀ c S, flatten (wrap c S) = (fun p : T × D => ctor p.1 p.2) '' (flatten c ×ˢ S))
    {c c' : Cyl} {S S' : Set D} {o oₜ : Option Cyl}
    (hinner : flatten c ∩ flatten c' = o.elim ∅ flatten)
    (hcomb : oₜ = o.map (fun r => wrap r (S ∩ S'))) :
    (fun p : T × D => ctor p.1 p.2) '' (flatten c ×ˢ S) ∩
        (fun p : T × D => ctor p.1 p.2) '' (flatten c' ×ˢ S') = oₜ.elim ∅ flatten := by
  rw [← Set.image_inter (f := fun p : T × D => ctor p.1 p.2) hctor, Set.prod_inter_prod, hinner,
    hcomb]
  cases o with
  | none => simp
  | some r => simp [hwrap r (S ∩ S')]

/-- Binary data-leaf diagonal: `ctor '' (S₁ ×ˢ S₂) ∩ ctor '' (S₁' ×ˢ S₂')
= ctor '' ((S₁ ∩ S₁') ×ˢ (S₂ ∩ S₂'))`. -/
theorem flatten_inter_prod {D₁ D₂ : Type _} {ctor : D₁ → D₂ → T}
    (hctor : Function.Injective (fun p : D₁ × D₂ => ctor p.1 p.2))
    {S₁ S₁' : Set D₁} {S₂ S₂' : Set D₂} :
    (fun p : D₁ × D₂ => ctor p.1 p.2) '' (S₁ ×ˢ S₂) ∩
        (fun p : D₁ × D₂ => ctor p.1 p.2) '' (S₁' ×ˢ S₂') =
      (fun p : D₁ × D₂ => ctor p.1 p.2) '' ((S₁ ∩ S₁') ×ˢ (S₂ ∩ S₂')) := by
  rw [← Set.image_inter hctor, Set.prod_inter_prod]

/-- Leaf-gated data diagonal (syntax-leaf × data-leaf, non-recursive, e.g.
`EctxItem.binopL`): `ctor u '' S ∩ ctor u' '' S'` is `ctor u '' (S ∩ S')` when the
leaves match and `∅` otherwise. -/
theorem flatten_inter_mixed_data {L D : Type _} [DecidableEq L] {ctor : L → D → T}
    (hctor : ∀ l, Function.Injective (ctor l))
    (hctor_leaf : ∀ {l l' : L} {x y : D}, ctor l x = ctor l' y → l = l')
    (wrap : L → Set D → Cyl) (hwrap : ∀ l S, flatten (wrap l S) = ctor l '' S)
    {u u' : L} {S S' : Set D} {oₜ : Option Cyl}
    (hcomb : oₜ = (if u = u' then some (wrap u (S ∩ S')) else none)) :
    ctor u '' S ∩ ctor u' '' S' = oₜ.elim ∅ flatten := by
  subst hcomb
  by_cases hu : u = u'
  · subst hu
    rw [if_pos rfl, Option.elim_some, hwrap u (S ∩ S'), ← Set.image_inter (hctor u)]
  · simp only [hu, if_false, Option.elim_none]
    ext z
    simp only [Set.mem_inter_iff, Set.mem_image, Set.mem_empty_iff_false, iff_false, not_and]
    rintro ⟨x, _, rfl⟩ ⟨y, _, hh⟩
    exact hu (hctor_leaf hh).symm

/-- Leaf-gated singleton diagonal (syntax-leaf nullary-after-leaf, e.g.
`EctxItem.unop`): `{ctor u} ∩ {ctor u'}` is `{ctor u}` when leaves match, `∅`
otherwise. -/
theorem flatten_inter_leaf {L : Type _} [DecidableEq L] {ctor : L → T}
    (hctor : Function.Injective ctor)
    (wrap : L → Cyl) (hwrap : ∀ l, flatten (wrap l) = {ctor l})
    {u u' : L} {oₜ : Option Cyl}
    (hcomb : oₜ = (if u = u' then some (wrap u) else none)) :
    ({ctor u} : Set T) ∩ {ctor u'} = oₜ.elim ∅ flatten := by
  subst hcomb
  by_cases hu : u = u'
  · subst hu; simp [hwrap u]
  · simp only [hu, if_false, Option.elim_none]
    ext z; simp only [Set.mem_inter_iff, Set.mem_singleton_iff, Set.mem_empty_iff_false, iff_false,
      not_and]
    rintro rfl h; exact hu (hctor h)

/-! ### `Shape.cylinder_preimage_shape` (Phase 2)

The per-type `hasMeasurableLeaves_inter` proofs are stamped directly (per-constructor:
`cases c₁`/`induction c₁`, `cases c₂`, off-diagonal dies on `inter? = none`, diagonal
rebuilds the constructor with `MeasurableSet.inter` / the children IHs) rather than via
a generic helper, since they need the per-type `HasMeasurableLeaves` constructors. -/

/-- `Shape.cylinder_preimage_shape` from its two structural ingredients, splitting
the set equality into the two inclusions. The `⊆` direction is fully generic (uses
only `shape_of_mem` + `cShape (sCyl s) = s`); the `⊇` direction is the per-type
structural fact `mem_self : ∀ p, p ∈ flatten (sCyl (shape p))`, which is proved by
induction on **`p` alone** (linear in constructor count, no `s`-casing). -/
theorem cylinder_preimage_shape {sCyl : Shp → Cyl}
    (shape_of_mem : ∀ {c : Cyl} {p : T}, p ∈ flatten c → shape p = cShape c)
    (cShape_sCyl : ∀ s : Shp, cShape (sCyl s) = s)
    (mem_self : ∀ p : T, p ∈ flatten (sCyl (shape p)))
    (s : Shp) : flatten (sCyl s) = shape ⁻¹' {s} := by
  ext p
  simp only [Set.mem_preimage, Set.mem_singleton_iff]
  constructor
  · intro hp; rw [shape_of_mem hp, cShape_sCyl]
  · rintro rfl; exact mem_self p

/-- Leaf-gated diagonal (syntax-leaf constructors and mixed syntax-leaf×recursive
constructors): the intersection is nonempty only when the leaf values match. The
per-type `inter?` is `if a = b then some … else none`. `lhs`/`rhs` are the two
flatten sets; when the leaves differ the per-case `simp` discharges via shape
disjointness, so this lemma only handles the matched (`a = b`) branch, supplied as
the `Option.elim` equation directly. -/
theorem flatten_inter_data {α : Type _} {S₁ S₂ : Set α} {ι : α → T}
    (hι : Function.Injective ι) :
    ι '' S₁ ∩ ι '' S₂ = ι '' (S₁ ∩ S₂) := (Set.image_inter hι).symm

end Stamp

end ProbLangMeasures
