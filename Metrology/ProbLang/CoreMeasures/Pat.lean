module

import all Mathlib.Tactic.DeriveCountable
public import Metrology.ProbLang.Measure
public import Metrology.ProbLang.Syntax.Syntax
public import Metrology.ProbLang.CoreMeasures.BaseLit

meta import Metrology.Meta

@[expose] public section

/-## ProbLang Measure theory -/

noncomputable section ProbLangMeasures

open Classical MeasureTheory ProbabilityTheory Measure ProbLang

/-# Measure space on patterns.

Closely parallels the `BaseLit` construction above. `Pat` has:
- one nullary constructor (`wildcard`)
- one data-leaf constructor (`lit (b : BaseLit rT)`)
- three purely-recursive constructors (`pair`, `inl`, `inr`).
-/

namespace ProbLang.Pat

macro "solve_ι_inj" : tactic => `(tactic|
  (intro a b h;
   first
   | (cases h; rfl)
   | (obtain ⟨_, _⟩ := a; obtain ⟨_, _⟩ := b; cases h; rfl)))

theorem wildcard.ι.inj {rT : Type _} : Function.Injective (@Pat.wildcard.ι rT) := by solve_ι_inj

theorem lit.ι.inj {rT : Type _} : Function.Injective (@Pat.lit.ι rT) := by solve_ι_inj

theorem pair.ι.inj {rT : Type _} : Function.Injective (@Pat.pair.ι rT) := by solve_ι_inj

theorem inl.ι.inj {rT : Type _} : Function.Injective (@Pat.inl.ι rT) := by solve_ι_inj

theorem inr.ι.inj {rT : Type _} : Function.Injective (@Pat.inr.ι rT) := by solve_ι_inj

/-- A cylinder is a `Pat` whose `BaseLit rT`-payload (the `lit` data leaf) has been replaced
by a `Set (BaseLit rT)`. -/
inductive Cylinder (rT : Type _)
  | wildcard
  | lit (S : Set (BaseLit rT))
  | pair (c1 c2 : Cylinder rT)
  | inl (c : Cylinder rT)
  | inr (c : Cylinder rT)

/-- A pattern with all data forgotten, in order to be countable. -/
inductive Shape
  | wildcard
  | lit
  | pair (s1 s2 : Shape)
  | inl (s : Shape)
  | inr (s : Shape)
  deriving Countable

/-- Interpret a cylinder as the set of `Pat rT` it describes. -/
@[simp] def Cylinder.flatten {rT : Type _} : Cylinder rT → Set (Pat rT)
  | .wildcard     => {Pat.wildcard}
  | .lit S        => Pat.lit '' S
  | .pair c1 c2   => (fun p => Pat.pair p.1 p.2) '' (flatten c1 ×ˢ flatten c2)
  | .inl c        => Pat.inl '' flatten c
  | .inr c        => Pat.inr '' flatten c

/-- A cylinder has measurable leaves if every `Set (BaseLit rT)` it carries is measurable. -/
inductive Cylinder.HasMeasurableLeaves {rT : Type _} [MeasurableSpace rT] :
    Cylinder rT → Prop where
  | wildcard : HasMeasurableLeaves .wildcard
  | lit S    : MeasurableSet S → HasMeasurableLeaves (.lit S)
  | pair     : HasMeasurableLeaves c1 → HasMeasurableLeaves c2 → HasMeasurableLeaves (.pair c1 c2)
  | inl      : HasMeasurableLeaves c → HasMeasurableLeaves (.inl c)
  | inr      : HasMeasurableLeaves c → HasMeasurableLeaves (.inr c)

instance instMeasurableSpacePat [MeasurableSpace rT] : MeasurableSpace (Pat rT) :=
  .generateFrom <| Cylinder.flatten '' { c : Cylinder rT | c.HasMeasurableLeaves }

@[simp] def shape : Pat rT → Shape
  | .wildcard     => .wildcard
  | .lit _        => .lit
  | .pair p1 p2   => .pair (shape p1) (shape p2)
  | .inl p        => .inl (shape p)
  | .inr p        => .inr (shape p)

/-- Shape of a cylinder (forgets data leaves). -/
@[simp] def Cylinder.shape {rT : Type _} : Cylinder rT → Shape
  | .wildcard     => .wildcard
  | .lit _        => .lit
  | .pair c1 c2   => .pair (shape c1) (shape c2)
  | .inl c        => .inl (shape c)
  | .inr c        => .inr (shape c)

/-- The "universe cylinder" for a given shape: `univ` at every data leaf. -/
@[simp] def Shape.cylinder {rT : Type _} : Shape → Cylinder rT
  | .wildcard     => .wildcard
  | .lit          => .lit Set.univ
  | .pair s1 s2   => .pair (cylinder s1) (cylinder s2)
  | .inl s        => .inl (cylinder s)
  | .inr s        => .inr (cylinder s)

/-! ### Cylinder intersection. -/

/-- Partial intersection of cylinders. -/
def Cylinder.inter? {rT : Type _} : Cylinder rT → Cylinder rT → Option (Cylinder rT)
  | .wildcard, .wildcard => some .wildcard
  | .lit S₁,  .lit S₂   => some (.lit (S₁ ∩ S₂))
  | .pair c₁ c₂, .pair c₁' c₂' =>
      match Cylinder.inter? c₁ c₁', Cylinder.inter? c₂ c₂' with
      | some r₁, some r₂ => some (.pair r₁ r₂)
      | _, _ => none
  | .inl c, .inl c' =>
      match Cylinder.inter? c c' with
      | some r => some (.inl r)
      | none   => none
  | .inr c, .inr c' =>
      match Cylinder.inter? c c' with
      | some r => some (.inr r)
      | none   => none
  | _, _ => none

/-- Every element of a cylinder's flatten has that cylinder's shape. -/
theorem Cylinder.shape_of_mem_flatten {rT : Type _} {c : Cylinder rT} {p : Pat rT}
    (h : p ∈ Cylinder.flatten c) : Pat.shape p = Cylinder.shape c := by
  induction c generalizing p with
  | wildcard => simp_all
  | lit _ => obtain ⟨_, _, rfl⟩ := h; rfl
  | pair c₁ c₂ ih₁ ih₂ =>
    obtain ⟨⟨x, y⟩, ⟨hx, hy⟩, rfl⟩ := h
    show Pat.shape (Pat.pair x y) = _
    simp [Pat.shape, ih₁ hx, ih₂ hy]
  | inl c ih =>
    obtain ⟨x, hx, rfl⟩ := h
    show Pat.shape (Pat.inl x) = _
    simp [Pat.shape, ih hx]
  | inr c ih =>
    obtain ⟨x, hx, rfl⟩ := h
    show Pat.shape (Pat.inr x) = _
    simp [Pat.shape, ih hx]

/-- Flattens of cylinders with different shapes are disjoint. -/
theorem Cylinder.flatten_disjoint_of_shape_ne {rT : Type _} {c₁ c₂ : Cylinder rT}
    (h : Cylinder.shape c₁ ≠ Cylinder.shape c₂) : Cylinder.flatten c₁ ∩ Cylinder.flatten c₂ = ∅ := by
  ext p
  simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false, not_and]
  intro hp₁ hp₂
  exact h ((Cylinder.shape_of_mem_flatten hp₁).symm.trans (Cylinder.shape_of_mem_flatten hp₂))

/-- The cylinder flatten of the intersection equals the intersection of the flattens. -/
theorem Cylinder.flatten_inter {rT : Type _} (c₁ c₂ : Cylinder rT) :
    Cylinder.flatten c₁ ∩ Cylinder.flatten c₂
      = (Cylinder.inter? c₁ c₂).elim ∅ Cylinder.flatten := by
  induction c₁ generalizing c₂ with
  | wildcard =>
    cases c₂
    case wildcard => simp [Cylinder.inter?]
    all_goals (rw [Cylinder.flatten_disjoint_of_shape_ne (by simp [Cylinder.shape])]; rfl)
  | lit S₁ =>
    cases c₂
    case lit S₂ => simp [Cylinder.inter?]; ext p; cases p <;> simp
    all_goals (rw [Cylinder.flatten_disjoint_of_shape_ne (by simp [Cylinder.shape])]; rfl)
  | pair a b ih₁ ih₂ =>
    cases c₂
    case pair a' b' =>
      show (Pat.pair.ι '' (Cylinder.flatten a ×ˢ Cylinder.flatten b)) ∩
           (Pat.pair.ι '' (Cylinder.flatten a' ×ˢ Cylinder.flatten b')) = _
      rw [← Set.image_inter Pat.pair.ι.inj, Set.prod_inter_prod, ih₁, ih₂]
      cases hr₁ : Cylinder.inter? a a' <;> cases hr₂ : Cylinder.inter? b b' <;>
        simp [Cylinder.inter?, hr₁, hr₂]
    all_goals (rw [Cylinder.flatten_disjoint_of_shape_ne (by simp [Cylinder.shape])]; rfl)
  | inl c ih =>
    cases c₂
    case inl c' =>
      show (Pat.inl.ι '' Cylinder.flatten c) ∩ (Pat.inl.ι '' Cylinder.flatten c') = _
      rw [← Set.image_inter Pat.inl.ι.inj, ih]
      cases hr : Cylinder.inter? c c' <;> simp [Cylinder.inter?, hr]
    all_goals (rw [Cylinder.flatten_disjoint_of_shape_ne (by simp [Cylinder.shape])]; rfl)
  | inr c ih =>
    cases c₂
    case inr c' =>
      show (Pat.inr.ι '' Cylinder.flatten c) ∩ (Pat.inr.ι '' Cylinder.flatten c') = _
      rw [← Set.image_inter Pat.inr.ι.inj, ih]
      cases hr : Cylinder.inter? c c' <;> simp [Cylinder.inter?, hr]
    all_goals (rw [Cylinder.flatten_disjoint_of_shape_ne (by simp [Cylinder.shape])]; rfl)

theorem Cylinder.flatten_inter_some {rT : Type _} {c₁ c₂ c : Cylinder rT}
    (h : Cylinder.inter? c₁ c₂ = some c) :
    Cylinder.flatten c = Cylinder.flatten c₁ ∩ Cylinder.flatten c₂ := by
  rw [Cylinder.flatten_inter, h]; rfl

theorem Cylinder.hasMeasurableLeaves_inter [MeasurableSpace rT]
    {c₁ c₂ c : Cylinder rT}
    (h₁ : c₁.HasMeasurableLeaves) (h₂ : c₂.HasMeasurableLeaves)
    (h : Cylinder.inter? c₁ c₂ = some c) : c.HasMeasurableLeaves := by
  induction h₁ generalizing c₂ c <;> cases h₂ <;>
    simp_all [Cylinder.inter?] <;> grind [HasMeasurableLeaves, MeasurableSet.inter]

/-! ### Per-constructor covers. -/

def cover.wildcard (S : Set Unit) : Set (Pat rT) :=
  ⋃ _ ∈ S, Cylinder.flatten (Cylinder.wildcard : Cylinder rT)

def cover.lit (S : Set (BaseLit rT)) : Set (Pat rT) :=
  Cylinder.flatten (.lit S)

def cover.pair (S : Set (Shape × Shape)) : Set (Pat rT) :=
  ⋃ p ∈ S, Cylinder.flatten (.pair p.1.cylinder p.2.cylinder)

def cover.inl (S : Set Shape) : Set (Pat rT) :=
  ⋃ s ∈ S, Cylinder.flatten (.inl s.cylinder)

def cover.inr (S : Set Shape) : Set (Pat rT) :=
  ⋃ s ∈ S, Cylinder.flatten (.inr s.cylinder)

/-- Cylinder of a given shape has measurable leaves. -/
theorem Shape.cylinder_hasMeasurableLeaves [MeasurableSpace rT] (s : Shape) :
    (s.cylinder (rT := rT)).HasMeasurableLeaves := by
  induction s <;> constructor <;> measurability

/-- Flattening a cylinder of a shape equals set of terms with a given shape. -/
@[simp] theorem Shape.cylinder_preimage_shape (s : Shape) :
    (s.cylinder (rT := rT)).flatten = shape ⁻¹' {s} := by
  ext p; induction p generalizing s <;> cases s <;> simp_all

/-- Flattening a cylinder gives a measurable set. -/
@[measurability]
theorem flatten_measurable [MeasurableSpace rT] {c : Cylinder rT}
    (hc : c.HasMeasurableLeaves) : MeasurableSet c.flatten :=
  MeasurableSpace.measurableSet_generateFrom ⟨c, hc, rfl⟩

attribute [aesop safe constructors (rule_sets := [Measurable])]
  ProbLang.Pat.Cylinder.HasMeasurableLeaves

attribute [aesop safe apply (rule_sets := [Measurable])]
  Shape.cylinder_hasMeasurableLeaves

/-! ### The cylinder flatten family is a π-system that spans `Pat rT`. -/

theorem Cylinder.flatten_isPiSystem [MeasurableSpace rT] :
    IsPiSystem
      ({S : Set (Pat rT) | ∃ c : Cylinder rT, c.HasMeasurableLeaves ∧ Cylinder.flatten c = S}) := by
  rintro _ ⟨c₁, hc₁, rfl⟩ _ ⟨c₂, hc₂, rfl⟩ hne
  have hi : Cylinder.inter? c₁ c₂ ≠ none := by
    intro h
    have : c₁.flatten ∩ c₂.flatten = ∅ := by rw [Cylinder.flatten_inter, h]; rfl
    exact hne.ne_empty this
  obtain ⟨c, hc⟩ : ∃ c, Cylinder.inter? c₁ c₂ = some c := Option.ne_none_iff_exists'.mp hi
  exact ⟨c, Cylinder.hasMeasurableLeaves_inter hc₁ hc₂ hc, Cylinder.flatten_inter_some hc⟩

theorem Cylinder.flatten_isCountablySpanning [MeasurableSpace rT] :
    IsCountablySpanning
      ({S : Set (Pat rT) | ∃ c : Cylinder rT, c.HasMeasurableLeaves ∧ Cylinder.flatten c = S}) := by
  obtain ⟨enc⟩ := nonempty_encodable Shape
  refine ⟨fun n =>
    match enc.decode n with
    | some s => Cylinder.flatten (Shape.cylinder s : Cylinder rT)
    | none => Cylinder.flatten (.wildcard : Cylinder rT), ?_, ?_⟩
  · intro n
    cases h : enc.decode n with
    | none => exact ⟨.wildcard, .wildcard, by simp [h]⟩
    | some s => exact ⟨Shape.cylinder s, Shape.cylinder_hasMeasurableLeaves s, by simp [h]⟩
  · ext p
    simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
    refine ⟨enc.encode (Pat.shape p), ?_⟩
    have hd : enc.decode (enc.encode (Pat.shape p)) = some (Pat.shape p) := enc.encodek _
    rw [hd]
    simp [Shape.cylinder_preimage_shape]

/-! ### Measurability of the per-constructor covers. -/

macro "solve_cover_measurable" : tactic => `(tactic|
  first
  | exact .biUnion (Set.to_countable _) fun _ _ => flatten_measurable (by measurability)
  | exact flatten_measurable (by measurability))

@[measurability]
theorem cover.wildcard.measurable [MeasurableSpace rT] (S : Set Unit) :
    MeasurableSet (wildcard (rT := rT) S) := by
  solve_cover_measurable

@[measurability]
theorem cover.lit.measurable [MeasurableSpace rT] {S : Set (BaseLit rT)} (hS : MeasurableSet S) :
    MeasurableSet (lit (rT := rT) S) :=
  flatten_measurable (.lit _ hS)

@[measurability]
theorem cover.pair.measurable [MeasurableSpace rT] (S : Set (Shape × Shape)) :
    MeasurableSet (pair (rT := rT) S) := by
  solve_cover_measurable

@[measurability]
theorem cover.inl.measurable [MeasurableSpace rT] (S : Set Shape) :
    MeasurableSet (inl (rT := rT) S) := by
  solve_cover_measurable

@[measurability]
theorem cover.inr.measurable [MeasurableSpace rT] (S : Set Shape) :
    MeasurableSet (inr (rT := rT) S) := by
  solve_cover_measurable

macro "solve_cover_eq_image" ctor:ident : tactic => `(tactic|
  (ext p; cases p <;> simp [$ctor:ident]))

theorem cover.wildcard_eq_image (S : Set Unit) :
    cover.wildcard (rT := rT) S = (fun _ : Unit => (Pat.wildcard : Pat rT)) '' S := by
  solve_cover_eq_image cover.wildcard

theorem cover.lit_eq_image (S : Set (BaseLit rT)) :
    cover.lit (rT := rT) S = Pat.lit '' S := by
  solve_cover_eq_image cover.lit

theorem cover.pair_univ_eq_range :
    cover.pair (rT := rT) Set.univ = .range (Function.uncurry Pat.pair) := by
  solve_cover_eq_image cover.pair

theorem cover.inl_univ_eq_range :
    cover.inl (rT := rT) Set.univ = .range (Pat.inl : Pat rT → Pat rT) := by
  solve_cover_eq_image cover.inl

theorem cover.inr_univ_eq_range :
    cover.inr (rT := rT) Set.univ = .range (Pat.inr : Pat rT → Pat rT) := by
  solve_cover_eq_image cover.inr

/-! ### Measurable constructors. -/

@[fun_prop]
theorem wildcard.ι.measurable {rT : Type _} [MeasurableSpace rT] :
    Measurable (Pat.wildcard.ι (rT := rT)) := Measurable.of_discrete

@[fun_prop]
theorem lit.ι.measurable {rT : Type _} [MeasurableSpace rT] :
    Measurable (Pat.lit.ι (rT := rT)) := by
  apply measurable_generateFrom
  rintro G ⟨c, hc, rfl⟩
  cases hc with
  | @lit S hS =>
    suffices h : Pat.lit.ι ⁻¹' Cylinder.flatten (.lit S) = S by rw [h]; exact hS
    ext b; simp
  | _ => convert MeasurableSet.empty; ext b; simp

@[fun_prop]
theorem pair.ι.measurable [MeasurableSpace rT] :
    Measurable (Pat.pair.ι (rT := rT)) := by
  apply measurable_generateFrom
  rintro G ⟨c, hc, rfl⟩
  cases hc with
  | @pair c1 c2 h1 h2 =>
    suffices h : Pat.pair.ι ⁻¹' Cylinder.flatten (.pair c1 c2)
                = Cylinder.flatten c1 ×ˢ Cylinder.flatten c2 by rw [h]; measurability
    ext ⟨_, _⟩; simp
  | _ => convert MeasurableSet.empty; ext ⟨_, _⟩; simp

@[fun_prop]
theorem inl.ι.measurable [MeasurableSpace rT] :
    Measurable (Pat.inl.ι (rT := rT)) := by
  apply measurable_generateFrom
  rintro G ⟨c, hc, rfl⟩
  cases hc with
  | @inl c h =>
    suffices heq : Pat.inl.ι ⁻¹' Cylinder.flatten (.inl c) = Cylinder.flatten c by
      rw [heq]; exact flatten_measurable h
    ext p; simp
  | _ => convert MeasurableSet.empty; ext p; simp

@[fun_prop]
theorem inr.ι.measurable [MeasurableSpace rT] :
    Measurable (Pat.inr.ι (rT := rT)) := by
  apply measurable_generateFrom
  rintro G ⟨c, hc, rfl⟩
  cases hc with
  | @inr c h =>
    suffices heq : Pat.inr.ι ⁻¹' Cylinder.flatten (.inr c) = Cylinder.flatten c by
      rw [heq]; exact flatten_measurable h
    ext p; simp
  | _ => convert MeasurableSet.empty; ext p; simp

/-- Solves `MeasurableEmbedding f` for a discrete-leaf constructor `f`. -/
macro "solve_discrete_ME" eq_image:term ", " meas:term : tactic => `(tactic|
  (refine ⟨fun _ _ h => by injection h, Measurable.of_discrete, fun S _ => ?_⟩
   rw [← $eq_image S]
   exact $meas S))

theorem wildcard.measurableEmbedding [MeasurableSpace rT] :
    MeasurableEmbedding (fun _ : Unit => (Pat.wildcard : Pat rT)) := by
  apply MeasurableEmbedding.of_measurable_inverse (g := fun _ => ())
  · exact measurable_const
  · rw [show Set.range (fun _ : Unit => (Pat.wildcard : Pat rT)) = cover.wildcard .univ from by
             rw [cover.wildcard_eq_image]; ext; simp]
    exact cover.wildcard.measurable _
  · exact measurable_const
  · intro; rfl

theorem lit.measurableEmbedding [MeasurableSpace rT] :
    MeasurableEmbedding (Pat.lit : BaseLit rT → Pat rT) :=
  ⟨fun _ _ h => by injection h, Pat.lit.ι.measurable,
    fun _ hS => flatten_measurable (.lit _ hS)⟩

theorem pair.measurableEmbedding [MeasurableSpace rT] :
    MeasurableEmbedding (Function.uncurry (Pat.pair : Pat rT → Pat rT → Pat rT)) :=
  measurableEmbedding_of_piSystem₂
    (h_inj := Pat.pair.ι.inj) (h_meas := Pat.pair.ι.measurable)
    (h_gen := (generateFrom_eq_prod rfl rfl
                Cylinder.flatten_isCountablySpanning Cylinder.flatten_isCountablySpanning).symm)
    (h_pi := Cylinder.flatten_isPiSystem.prod Cylinder.flatten_isPiSystem)
    (h_basic := by rintro _ ⟨c₁, hc₁, rfl⟩ _ ⟨c₂, hc₂, rfl⟩; exact flatten_measurable (.pair hc₁ hc₂))
    (h_cov_meas := cover.pair.measurable _) (h_cov_range := cover.pair_univ_eq_range)

theorem inl.measurableEmbedding [MeasurableSpace rT] :
    MeasurableEmbedding (Pat.inl : Pat rT → Pat rT) :=
  measurableEmbedding_of_piSystem₁
    (h_inj := Pat.inl.ι.inj) (h_meas := Pat.inl.ι.measurable)
    (h_gen := rfl) (h_pi := Cylinder.flatten_isPiSystem)
    (h_basic := by rintro _ ⟨c, hc, rfl⟩; exact flatten_measurable (.inl hc))
    (h_cov_meas := cover.inl.measurable _) (h_cov_range := cover.inl_univ_eq_range)

theorem inr.measurableEmbedding [MeasurableSpace rT] :
    MeasurableEmbedding (Pat.inr : Pat rT → Pat rT) :=
  measurableEmbedding_of_piSystem₁
    (h_inj := Pat.inr.ι.inj) (h_meas := Pat.inr.ι.measurable)
    (h_gen := rfl) (h_pi := Cylinder.flatten_isPiSystem)
    (h_basic := by rintro _ ⟨c, hc, rfl⟩; exact flatten_measurable (.inr hc))
    (h_cov_meas := cover.inr.measurable _) (h_cov_range := cover.inr_univ_eq_range)

theorem casesOn_preimage_decomp
    {rT : Type _} {α : Type _} (S : Set α)
    (f_wildcard : Unit → α) (f_lit : BaseLit rT → α)
    (f_pair : Pat rT × Pat rT → α)
    (f_inl  : Pat rT → α) (f_inr : Pat rT → α) :
    (fun p : Pat rT => Pat.casesOn (motive := fun _ => α) p
        (f_wildcard ()) f_lit
        (fun p1 p2 => f_pair (p1, p2)) f_inl f_inr) ⁻¹' S
      = (Pat.wildcard.ι '' (f_wildcard ⁻¹' S))
      ∪ (Pat.lit.ι      '' (f_lit      ⁻¹' S))
      ∪ (Pat.pair.ι     '' (f_pair     ⁻¹' S))
      ∪ (Pat.inl.ι      '' (f_inl      ⁻¹' S))
      ∪ (Pat.inr.ι      '' (f_inr      ⁻¹' S)) := by
  ext p; cases p <;> aesop

@[fun_prop]
theorem measurable_rec
    {rT : Type _} [MeasurableSpace rT]
    {α : Type _} [MeasurableSpace α]
    (f_wildcard : Unit → α) (f_lit : BaseLit rT → α)
    (f_pair : Pat rT × Pat rT → α)
    (f_inl  : Pat rT → α) (f_inr : Pat rT → α)
    (h_lit  : Measurable f_lit)
    (h_pair : Measurable f_pair)
    (h_inl  : Measurable f_inl) (h_inr : Measurable f_inr) :
    Measurable (fun p : Pat rT =>
      Pat.casesOn (motive := fun _ => α) p
        (f_wildcard ()) f_lit
        (fun p1 p2 => f_pair (p1, p2)) f_inl f_inr) := by
  intro S hS
  rw [Pat.casesOn_preimage_decomp]
  iterate 4 refine .union ?_ ?_
  · exact wildcard.measurableEmbedding.measurableSet_image' .of_discrete
  · exact lit.measurableEmbedding.measurableSet_image'      (h_lit hS)
  · exact pair.measurableEmbedding.measurableSet_image'     (h_pair hS)
  · exact inl.measurableEmbedding.measurableSet_image'      (h_inl hS)
  · exact inr.measurableEmbedding.measurableSet_image'      (h_inr hS)

end Pat
end ProbLang
end ProbLangMeasures
