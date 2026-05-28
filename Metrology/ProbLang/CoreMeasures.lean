module

import all Mathlib.Tactic.DeriveCountable
public import Metrology.ProbLang.Measure
public import Metrology.ProbLang.Syntax.Syntax2

meta import Metrology.Meta

@[expose] public section

/-## ProbLang Measure theory -/

-- TODO move this to the semantics file once we have that (leave here until then though,
-- during drop-in step, so we can prove discreteness assuming discrete R type)

-- NOTE Tecnically speaking this is a strict extension: we can instanstiate the reals type
-- with Unit and then I guess also make the ops trivial? Perhaps I need a class with
-- all of this stuff. I do NOT want to have to do the whole thing at once, so I need
-- the option to take the discrete measure over whatever the reals type is

-- NOTE This actually could be a good thing to be honest, since I can also instanstiate
-- reals with floats? Pog?

noncomputable section ProbLangMeasures

open Classical MeasureTheory ProbabilityTheory Measure ProbLang

instance instMeasurableSpaceVar : MeasurableSpace Var := ⊤

instance instMeasurableSpaceLoc : MeasurableSpace Loc := ⊤

instance instMeasurableSpaceLbl : MeasurableSpace Lbl := ⊤

instance instMeasurableSpaceUnOp : MeasurableSpace UnOp := ⊤

instance instMeasurableSpaceBinOp : MeasurableSpace BinOp := ⊤

instance instMeasurableSpaceTy : MeasurableSpace Ty := ⊤

-- #synth DiscreteMeasurableSpace Loc

section BaseLit

/-# Measure space on base lits -/


namespace ProbLang.BaseLit

macro "solve_ι_inj" : tactic => `(tactic|
  (intro a b h;
   first
   | (cases h; rfl)
   | (obtain ⟨_, _⟩ := a; obtain ⟨_, _⟩ := b; cases h; rfl)))

theorem int.ι.inj  {rT : Type _} : Function.Injective (@BaseLit.int.ι  rT) := by solve_ι_inj

theorem bool.ι.inj {rT : Type _} : Function.Injective (@BaseLit.bool.ι rT) := by solve_ι_inj

theorem loc.ι.inj  {rT : Type _} : Function.Injective (@BaseLit.loc.ι  rT) := by solve_ι_inj

theorem lbl.ι.inj  {rT : Type _} : Function.Injective (@BaseLit.lbl.ι  rT) := by solve_ι_inj

theorem real.ι.inj {rT : Type _} : Function.Injective (@BaseLit.real.ι rT) := by solve_ι_inj

theorem prod.ι.inj {rT : Type _} : Function.Injective (@BaseLit.prod.ι rT) := by solve_ι_inj

theorem nest.ι.inj {rT : Type _} : Function.Injective (@BaseLit.nest.ι rT) := by solve_ι_inj

/-- A cylinder is a `BaseLit` whose `rT`-payloads have been replaced by `Set rT`. -/
abbrev Cylinder (rT : Type _) := BaseLit (Set rT)

/-- A tree with all data forgotten, in order to be countable. -/
abbrev Shape := BaseLit Unit

/-- Interpret a cylinder as the set of `BaseLit rT` it describes. Each branch is the image of
the corresponding constructor over the cartesian product of its arg-sets — singleton sets for
discrete leaves, the carried `Set rT` for real-leaves, and recursive `flatten` for sub-cylinders. -/
@[simp] def Cylinder.flatten {rT : Type _} : Cylinder rT → Set (BaseLit rT)
  | int z        => int '' {z}
  | bool b       => bool '' {b}
  | unit         => {unit}
  | loc l        => loc '' {l}
  | lbl l        => lbl '' {l}
  | real Sr      => real '' Sr
  | prod c1 c2   => (fun p => prod p.1 p.2) '' (flatten c1 ×ˢ flatten c2)
  | nest c Sr    => (fun p => nest p.1 p.2) '' (flatten c ×ˢ Sr)

/-- A cylinder has measurable leaves if every `Set rT` it carries is measurable. -/
inductive HasMeasurableLeaves {rT : Type _} [MeasurableSpace rT] :
    Cylinder rT → Prop where
  | int     : HasMeasurableLeaves (int z)
  | bool    : HasMeasurableLeaves (bool b)
  | unit    : HasMeasurableLeaves unit
  | loc     : HasMeasurableLeaves (loc z)
  | lbl     : HasMeasurableLeaves (lbl z)
  | real Sᵣ : MeasurableSet Sᵣ → HasMeasurableLeaves (real Sᵣ)
  | prod    : HasMeasurableLeaves c1 → HasMeasurableLeaves c2 → HasMeasurableLeaves (prod c1 c2)
  | nest Sᵣ : HasMeasurableLeaves c → MeasurableSet Sᵣ → HasMeasurableLeaves (nest c Sᵣ)

instance instMeasurableSpaceBaseLit [MeasurableSpace rT] : MeasurableSpace (BaseLit rT) :=
  .generateFrom <| Cylinder.flatten '' { c : Cylinder rT | c.HasMeasurableLeaves }

@[simp] def shape : BaseLit rT → Shape
  | int z        => int z
  | bool b       => bool b
  | unit         => unit
  | loc l        => loc l
  | lbl l        => lbl l
  | real _       => real ()
  | prod b1 b2   => prod (shape b1) (shape b2)
  | nest b _     => nest (shape b) ()

/-- The "universe cylinder" for a given shape: `univ` at every leaf, same skeleton as the shape. -/
@[simp] def Shape.cylinder : Shape → Cylinder rT
  | int z        => int z
  | bool b       => bool b
  | unit         => unit
  | loc l        => loc l
  | lbl l        => lbl l
  | real ()      => real Set.univ
  | prod s1 s2   => prod (cylinder s1) (cylinder s2)
  | nest s ()    => nest (cylinder s) Set.univ

/-! ### Cylinder intersection.

`Cylinder.inter? c c'` returns `some c''` when `flatten c'' = flatten c ∩ flatten c'`, and
`none` when the structural intersection is empty (different top constructors or mismatched
discrete leaves). The cylinder type is closed under intersection because every cylinder has
a top constructor and the recursive structure matches up. -/

/-- Partial intersection of cylinders. -/
def Cylinder.inter? {rT : Type _} : Cylinder rT → Cylinder rT → Option (Cylinder rT)
  | .int z₁,  .int z₂  => if z₁ = z₂ then some (.int z₁) else none
  | .bool b₁, .bool b₂ => if b₁ = b₂ then some (.bool b₁) else none
  | .unit,    .unit    => some .unit
  | .loc l₁,  .loc l₂  => if l₁ = l₂ then some (.loc l₁) else none
  | .lbl l₁,  .lbl l₂  => if l₁ = l₂ then some (.lbl l₁) else none
  | .real S₁, .real S₂ => some (.real (S₁ ∩ S₂))
  | .prod c₁ c₂, .prod c₁' c₂' =>
      match Cylinder.inter? c₁ c₁', Cylinder.inter? c₂ c₂' with
      | some r₁, some r₂ => some (.prod r₁ r₂)
      | _, _ => none
  | .nest c S, .nest c' S' =>
      match Cylinder.inter? c c' with
      | some r => some (.nest r (S ∩ S'))
      | none   => none
  | _, _ => none

/-- Every element of a cylinder's flatten has that cylinder's shape. -/
theorem Cylinder.shape_of_mem_flatten {rT : Type _} {c : Cylinder rT} {b : BaseLit rT}
    (h : b ∈ Cylinder.flatten c) : shape b = shape c := by
  induction c generalizing b with
  | int _ | bool _ | unit | loc _ | lbl _ => simp_all
  | real _ => obtain ⟨_, _, rfl⟩ := h; rfl
  | prod c₁ c₂ ih₁ ih₂ =>
    obtain ⟨⟨x, y⟩, ⟨hx, hy⟩, rfl⟩ := h
    show shape (BaseLit.prod x y) = _
    simp [shape, ih₁ hx, ih₂ hy]
  | nest c S ih =>
    obtain ⟨⟨x, r⟩, ⟨hx, _⟩, rfl⟩ := h
    show shape (BaseLit.nest x r) = _
    simp [shape, ih hx]

/-- Flattens of cylinders with different shapes are disjoint. -/
theorem Cylinder.flatten_disjoint_of_shape_ne {rT : Type _} {c₁ c₂ : Cylinder rT}
    (h : shape c₁ ≠ shape c₂) : Cylinder.flatten c₁ ∩ Cylinder.flatten c₂ = ∅ := by
  ext b
  simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false, not_and]
  intro hb₁ hb₂
  exact h ((Cylinder.shape_of_mem_flatten hb₁).symm.trans (Cylinder.shape_of_mem_flatten hb₂))

/-- The cylinder flatten of the intersection equals the intersection of the flattens.
For mismatched cylinders (where `inter?` returns `none`) the intersection is empty. -/
theorem Cylinder.flatten_inter {rT : Type _} (c₁ c₂ : Cylinder rT) :
    Cylinder.flatten c₁ ∩ Cylinder.flatten c₂
      = (Cylinder.inter? c₁ c₂).elim ∅ Cylinder.flatten := by
  induction c₁ generalizing c₂ with
  | int z₁ =>
    cases c₂
    case int z₂ => simp [Cylinder.inter?]; split_ifs <;> simp_all
    all_goals (rw [Cylinder.flatten_disjoint_of_shape_ne (by simp [shape])]; rfl)
  | bool b₁ =>
    cases c₂
    case bool b₂ => simp [Cylinder.inter?]; split_ifs <;> simp_all
    all_goals (rw [Cylinder.flatten_disjoint_of_shape_ne (by simp [shape])]; rfl)
  | unit =>
    cases c₂
    case unit => simp [Cylinder.inter?]
    all_goals (rw [Cylinder.flatten_disjoint_of_shape_ne (by simp [shape])]; rfl)
  | loc l₁ =>
    cases c₂
    case loc l₂ => simp [Cylinder.inter?]; split_ifs <;> simp_all
    all_goals (rw [Cylinder.flatten_disjoint_of_shape_ne (by simp [shape])]; rfl)
  | lbl l₁ =>
    cases c₂
    case lbl l₂ => simp [Cylinder.inter?]; split_ifs <;> simp_all
    all_goals (rw [Cylinder.flatten_disjoint_of_shape_ne (by simp [shape])]; rfl)
  | real S₁ =>
    cases c₂
    case real S₂ => simp [Cylinder.inter?]; ext b; cases b <;> simp
    all_goals (rw [Cylinder.flatten_disjoint_of_shape_ne (by simp [shape])]; rfl)
  | prod a b ih₁ ih₂ =>
    cases c₂
    case prod a' b' =>
      show (BaseLit.prod.ι '' (Cylinder.flatten a ×ˢ Cylinder.flatten b)) ∩
           (BaseLit.prod.ι '' (Cylinder.flatten a' ×ˢ Cylinder.flatten b')) = _
      rw [← Set.image_inter BaseLit.prod.ι.inj, Set.prod_inter_prod, ih₁, ih₂]
      cases hr₁ : Cylinder.inter? a a' <;> cases hr₂ : Cylinder.inter? b b' <;>
        simp [Cylinder.inter?, hr₁, hr₂]
    all_goals (rw [Cylinder.flatten_disjoint_of_shape_ne (by simp [shape])]; rfl)
  | nest c S ih =>
    cases c₂
    case nest c' S' =>
      show (BaseLit.nest.ι '' (Cylinder.flatten c ×ˢ S)) ∩
           (BaseLit.nest.ι '' (Cylinder.flatten c' ×ˢ S')) = _
      rw [← Set.image_inter BaseLit.nest.ι.inj, Set.prod_inter_prod, ih]
      cases hr : Cylinder.inter? c c' <;> simp [Cylinder.inter?, hr]
    all_goals (rw [Cylinder.flatten_disjoint_of_shape_ne (by simp [shape])]; rfl)

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


/-! ### Per-constructor covers.

Each term in an inductive type is classified as one of
- Recursive
- Syntax Leaf (must be countable)
- Data Leaf (must be measurable)

Now we define cover sets: a set equal to `Set.range ctor` which is easier to deal with
measurability conditions for. Here's how each argument contributes:
- Recursie: Union over all shapes of shapeCyl
- Syntax leaf: Union over all elements of that element
- Data leaf: ⊤

Nullary constructors get no arguments.
-/

def cover.int (S : Set Int) : Set (BaseLit rT) :=
  ⋃ z ∈ S, Cylinder.flatten (.int z)

def cover.bool (S : Set Bool) : Set (BaseLit rT) :=
  ⋃ b ∈ S, Cylinder.flatten (.bool b)

def cover.unit (S : Set Unit) : Set (BaseLit rT) :=
  ⋃ _ ∈ S, Cylinder.flatten (BaseLit.unit : Cylinder rT)

def cover.loc (S : Set Loc) : Set (BaseLit rT) :=
  ⋃ l ∈ S, Cylinder.flatten (.loc l)

def cover.lbl (S : Set Lbl) : Set (BaseLit rT) :=
  ⋃ l ∈ S, Cylinder.flatten (.lbl l)

def cover.real (S : Set rT) : Set (BaseLit rT) :=
  Cylinder.flatten (.real S)

def cover.prod (S : Set (Shape × Shape)) : Set (BaseLit rT) :=
  ⋃ p ∈ S, Cylinder.flatten (.prod p.1.cylinder p.2.cylinder)

def cover.nest (S : Set Shape) : Set (BaseLit rT) :=
  ⋃ s ∈ S, Cylinder.flatten (.nest s.cylinder ⊤)

/-! Three generic helper lemmas next for provving measurability of a cover -/

/-- Cylinder of a given shape has measurable leaves -/
theorem Shape.cylinder_hasMeasurableLeaves [MeasurableSpace rT] (s : Shape) :
    (s.cylinder (rT := rT)).HasMeasurableLeaves := by
  induction s <;> constructor <;> measurability

/-- Flattening a cylinder of a shape equals set of terms with a given shape -/
@[simp] theorem Shape.cylinder_preimage_shape (s : Shape) :
    (s.cylinder (rT := rT)).flatten = shape ⁻¹' {s} := by
  ext b; induction b generalizing s <;> cases s <;> simp_all

/-- Flattening a cylinder gives a measurable set -/
@[measurability]
theorem flatten_measurable [MeasurableSpace rT] {c : Cylinder rT}
    (hc : c.HasMeasurableLeaves) : MeasurableSet c.flatten :=
  MeasurableSpace.measurableSet_generateFrom ⟨c, hc, rfl⟩

attribute [aesop safe constructors (rule_sets := [Measurable])]
  ProbLang.BaseLit.HasMeasurableLeaves

attribute [aesop safe apply (rule_sets := [Measurable])]
  Shape.cylinder_hasMeasurableLeaves

/-! ### The cylinder flatten family is a π-system that spans `BaseLit rT`. -/

/-- The cylinder flatten family is closed under nonempty intersection. -/
theorem Cylinder.flatten_isPiSystem [MeasurableSpace rT] :
    IsPiSystem
      ({S : Set (BaseLit rT) | ∃ c : Cylinder rT, c.HasMeasurableLeaves ∧ Cylinder.flatten c = S}) := by
  rintro _ ⟨c₁, hc₁, rfl⟩ _ ⟨c₂, hc₂, rfl⟩ hne
  have hi : Cylinder.inter? c₁ c₂ ≠ none := by
    intro h
    have : c₁.flatten ∩ c₂.flatten = ∅ := by rw [Cylinder.flatten_inter, h]; rfl
    exact hne.ne_empty this
  obtain ⟨c, hc⟩ : ∃ c, Cylinder.inter? c₁ c₂ = some c := Option.ne_none_iff_exists'.mp hi
  exact ⟨c, Cylinder.hasMeasurableLeaves_inter hc₁ hc₂ hc, Cylinder.flatten_inter_some hc⟩

/-- The cylinder flatten family is countably spanning. -/
theorem Cylinder.flatten_isCountablySpanning [MeasurableSpace rT] :
    IsCountablySpanning
      ({S : Set (BaseLit rT) | ∃ c : Cylinder rT, c.HasMeasurableLeaves ∧ Cylinder.flatten c = S}) := by
  obtain ⟨enc⟩ := nonempty_encodable Shape
  refine ⟨fun n =>
    match enc.decode n with
    | some s => Cylinder.flatten (Shape.cylinder s : Cylinder rT)
    | none => Cylinder.flatten (.unit : Cylinder rT), ?_, ?_⟩
  · intro n
    cases h : enc.decode n with
    | none => exact ⟨.unit, .unit, by simp [h]⟩
    | some s => exact ⟨Shape.cylinder s, Shape.cylinder_hasMeasurableLeaves s, by simp [h]⟩
  · ext b
    simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
    refine ⟨enc.encode (shape b), ?_⟩
    have hd : enc.decode (enc.encode (shape b)) = some (shape b) := enc.encodek _
    rw [hd]
    simp [Shape.cylinder_preimage_shape]

/-! ### Measurability of the per-constructor covers. -/

macro "solve_cover_measurable" : tactic => `(tactic|
  first
  | exact .biUnion (Set.to_countable _) fun _ _ => flatten_measurable (by measurability)
  | exact flatten_measurable (by measurability))

@[measurability]
theorem cover.int.measurable [MeasurableSpace rT] (S : Set Int) :
    MeasurableSet (int (rT := rT) S) := by
  solve_cover_measurable

@[measurability]
theorem cover.bool.measurable [MeasurableSpace rT] (S : Set Bool) :
    MeasurableSet (bool (rT := rT) S) := by
  solve_cover_measurable

@[measurability]
theorem cover.unit.measurable [MeasurableSpace rT] (S : Set Unit) :
    MeasurableSet (unit (rT := rT) S) := by
  solve_cover_measurable

@[measurability]
theorem cover.loc.measurable [MeasurableSpace rT] (S : Set Loc) :
    MeasurableSet (loc (rT := rT) S) := by
  solve_cover_measurable

@[measurability]
theorem cover.lbl.measurable [MeasurableSpace rT] (S : Set Lbl) :
    MeasurableSet (lbl (rT := rT) S) := by
  solve_cover_measurable

@[measurability]
theorem cover.real.measurable [MeasurableSpace rT] {S : Set rT} (hS : MeasurableSet S) :
    MeasurableSet (real (rT := rT) S) :=
  flatten_measurable (.real _ hS)

@[measurability]
theorem cover.prod.measurable [MeasurableSpace rT] (S : Set (Shape × Shape)) :
    MeasurableSet (prod (rT := rT) S) := by
  solve_cover_measurable

@[measurability]
theorem cover.nest.measurable [MeasurableSpace rT] (S : Set Shape) :
    MeasurableSet (nest (rT := rT) S) := by
  solve_cover_measurable

-- TODO: When metaprogramming, try changing this to a new simp set
-- Can't do here because it's defined in the same file, but it might work when defining programatically
macro "solve_cover_eq_image" ctor:ident : tactic => `(tactic|
  (ext b; cases b <;> simp [$ctor:ident]))

theorem cover.int_eq_image (S : Set Int) :
    cover.int (rT := rT) S = BaseLit.int '' S := by
  solve_cover_eq_image cover.int

theorem cover.bool_eq_image (S : Set Bool) :
    cover.bool (rT := rT) S = BaseLit.bool '' S := by
  solve_cover_eq_image cover.bool

theorem cover.unit_eq_image (S : Set Unit) :
    cover.unit (rT := rT) S = (fun _ : Unit => (BaseLit.unit : BaseLit rT)) '' S := by
  solve_cover_eq_image cover.unit

theorem cover.loc_eq_image (S : Set Loc) :
    cover.loc (rT := rT) S = BaseLit.loc '' S := by
  solve_cover_eq_image cover.loc

theorem cover.lbl_eq_image (S : Set Lbl) :
    cover.lbl (rT := rT) S = BaseLit.lbl '' S := by
  solve_cover_eq_image cover.lbl

theorem cover.real_eq_image (S : Set rT) :
    cover.real (rT := rT) S = BaseLit.real '' S := by
  solve_cover_eq_image cover.real

theorem cover.prod_univ_eq_range :
    cover.prod (rT := rT) Set.univ = .range (Function.uncurry BaseLit.prod) := by
  solve_cover_eq_image cover.prod

theorem cover.nest_univ_eq_range :
    cover.nest (rT := rT) Set.univ = .range (Function.uncurry BaseLit.nest) := by
  solve_cover_eq_image cover.nest

/-! ### Measurable constructors. One `BaseLit.<ctor>.ι.measurable` per constructor. -/

@[fun_prop]
theorem int.ι.measurable {rT : Type _} [MeasurableSpace rT] :
    Measurable (BaseLit.int.ι (rT := rT)) := Measurable.of_discrete

@[fun_prop]
theorem bool.ι.measurable {rT : Type _} [MeasurableSpace rT] :
    Measurable (BaseLit.bool.ι (rT := rT)) := Measurable.of_discrete

@[fun_prop]
theorem unit.ι.measurable {rT : Type _} [MeasurableSpace rT] :
    Measurable (BaseLit.unit.ι (rT := rT)) := Measurable.of_discrete

@[fun_prop]
theorem loc.ι.measurable {rT : Type _} [MeasurableSpace rT] :
    Measurable (BaseLit.loc.ι (rT := rT)) := Measurable.of_discrete

@[fun_prop]
theorem lbl.ι.measurable {rT : Type _} [MeasurableSpace rT] :
    Measurable (BaseLit.lbl.ι (rT := rT)) := Measurable.of_discrete

@[fun_prop]
theorem real.ι.measurable {rT : Type _} [MeasurableSpace rT] :
    Measurable (BaseLit.real.ι (rT := rT)) := by
  apply measurable_generateFrom
  rintro G ⟨c, hc, rfl⟩
  cases hc with
  | @real S hS =>
    suffices h : BaseLit.real.ι ⁻¹' Cylinder.flatten (.real S) = S by rw [h]; exact hS
    ext r; simp
  | _ => convert MeasurableSet.empty; ext r; simp

@[fun_prop]
theorem prod.ι.measurable [MeasurableSpace rT] :
    Measurable (BaseLit.prod.ι (rT := rT)) := by
  apply measurable_generateFrom
  rintro G ⟨c, hc, rfl⟩
  cases hc with
  | @prod c1 c2 h1 h2 =>
    suffices h : BaseLit.prod.ι ⁻¹' Cylinder.flatten (.prod c1 c2)
                = Cylinder.flatten c1 ×ˢ Cylinder.flatten c2 by rw [h]; measurability
    ext ⟨_, _⟩; simp
  | _ => convert MeasurableSet.empty; ext ⟨_, _⟩; simp

@[fun_prop]
theorem nest.ι.measurable [MeasurableSpace rT] :
    Measurable (BaseLit.nest.ι (rT := rT)) := by
  apply measurable_generateFrom
  rintro G ⟨c, hc, rfl⟩
  cases hc with
  | @nest c Sr h hSr =>
    suffices h : BaseLit.nest.ι ⁻¹' Cylinder.flatten (.nest c Sr)
                = Cylinder.flatten c ×ˢ Sr by rw [h]; measurability
    ext ⟨_, _⟩; simp
  | _ => convert MeasurableSet.empty; ext ⟨_, _⟩; simp

/-- Solves `MeasurableEmbedding f` for a discrete-leaf constructor `f`, given the cover's
`_eq_image` lemma and `.measurable` lemma. -/
macro "solve_discrete_ME" eq_image:term ", " meas:term : tactic => `(tactic|
  (refine ⟨fun _ _ h => by injection h, Measurable.of_discrete, fun S _ => ?_⟩
   rw [← $eq_image S]
   exact $meas S))

theorem int.measurableEmbedding [MeasurableSpace rT] :
    MeasurableEmbedding (BaseLit.int : Int → BaseLit rT) := by
  solve_discrete_ME cover.int_eq_image, cover.int.measurable

theorem bool.measurableEmbedding [MeasurableSpace rT] :
    MeasurableEmbedding (BaseLit.bool : Bool → BaseLit rT) := by
  solve_discrete_ME cover.bool_eq_image, cover.bool.measurable

theorem loc.measurableEmbedding [MeasurableSpace rT] :
    MeasurableEmbedding (BaseLit.loc : Loc → BaseLit rT) := by
  solve_discrete_ME cover.loc_eq_image, cover.loc.measurable

theorem lbl.measurableEmbedding [MeasurableSpace rT] :
    MeasurableEmbedding (BaseLit.lbl : Lbl → BaseLit rT) := by
  solve_discrete_ME cover.lbl_eq_image, cover.lbl.measurable

theorem unit.measurableEmbedding [MeasurableSpace rT] :
    MeasurableEmbedding (fun _ : Unit => (BaseLit.unit : BaseLit rT)) := by
  apply MeasurableEmbedding.of_measurable_inverse (g := fun _ => ())
  · exact measurable_const
  · rw [show Set.range (fun _ : Unit => BaseLit.unit) = cover.unit .univ from by
             rw [cover.unit_eq_image]; ext; simp]
    exact cover.unit.measurable _
  · exact measurable_const
  · intro; rfl

theorem real.measurableEmbedding [MeasurableSpace rT] :
    MeasurableEmbedding (BaseLit.real : rT → BaseLit rT) :=
  ⟨fun _ _ h => by injection h, BaseLit.real.ι.measurable,
    fun _ hS => flatten_measurable (.real _ hS)⟩

/-- Direct proof of `MeasurableEmbedding (uncurry prod)` via σ-algebra induction over the
π-system of cylinder rectangles, with no detour through `prod.π`. -/
theorem prod.measurableEmbedding [MeasurableSpace rT] :
    MeasurableEmbedding (Function.uncurry (BaseLit.prod : BaseLit rT → BaseLit rT → BaseLit rT)) :=
  measurableEmbedding_of_piSystem₂
    (h_inj := BaseLit.prod.ι.inj) (h_meas := BaseLit.prod.ι.measurable)
    (h_gen := (generateFrom_eq_prod rfl rfl
                Cylinder.flatten_isCountablySpanning Cylinder.flatten_isCountablySpanning).symm)
    (h_pi := Cylinder.flatten_isPiSystem.prod Cylinder.flatten_isPiSystem)
    (h_basic := by rintro _ ⟨c₁, hc₁, rfl⟩ _ ⟨c₂, hc₂, rfl⟩; exact flatten_measurable (.prod hc₁ hc₂))
    (h_cov_meas := cover.prod.measurable _) (h_cov_range := cover.prod_univ_eq_range)

/-- Direct proof of `MeasurableEmbedding (uncurry nest)`. -/
theorem nest.measurableEmbedding [MeasurableSpace rT] :
    MeasurableEmbedding (Function.uncurry (BaseLit.nest : BaseLit rT → rT → BaseLit rT)) :=
  measurableEmbedding_of_piSystem₂
    (h_inj := BaseLit.nest.ι.inj) (h_meas := BaseLit.nest.ι.measurable)
    (h_gen := (generateFrom_eq_prod rfl MeasurableSpace.generateFrom_measurableSet
                Cylinder.flatten_isCountablySpanning isCountablySpanning_measurableSet).symm)
    (h_pi := Cylinder.flatten_isPiSystem.prod fun _ hS _ hT _ => hS.inter hT)
    (h_basic := by rintro _ ⟨c, hc, rfl⟩ S hS; exact flatten_measurable (.nest _ hc hS))
    (h_cov_meas := cover.nest.measurable _) (h_cov_range := cover.nest_univ_eq_range)

theorem casesOn_preimage_decomp
    {rT : Type _} {α : Type _} (S : Set α)
    (f_int  : Int  → α) (f_bool : Bool → α) (f_unit : Unit → α)
    (f_loc  : Loc  → α) (f_lbl  : Lbl  → α) (f_real : rT → α)
    (f_prod : BaseLit rT × BaseLit rT → α)
    (f_nest : BaseLit rT × rT → α) :
    (fun b : BaseLit rT => BaseLit.casesOn (motive := fun _ => α) b
        f_int f_bool (f_unit ()) f_loc f_lbl f_real
        (fun b1 b2 => f_prod (b1, b2))
        (fun b r => f_nest (b, r))) ⁻¹' S
      = (BaseLit.int.ι  '' (f_int  ⁻¹' S))
      ∪ (BaseLit.bool.ι '' (f_bool ⁻¹' S))
      ∪ (BaseLit.unit.ι '' (f_unit ⁻¹' S))
      ∪ (BaseLit.loc.ι  '' (f_loc  ⁻¹' S))
      ∪ (BaseLit.lbl.ι  '' (f_lbl  ⁻¹' S))
      ∪ (BaseLit.real.ι '' (f_real ⁻¹' S))
      ∪ (BaseLit.prod.ι '' (f_prod ⁻¹' S))
      ∪ (BaseLit.nest.ι '' (f_nest ⁻¹' S)) := by
  ext b; cases b <;> aesop

@[fun_prop]
theorem measurable_rec
    {rT : Type _} [MeasurableSpace rT] [Inhabited rT]
    {α : Type _} [MeasurableSpace α]
    (f_int  : Int  → α) (f_bool : Bool → α) (f_unit : Unit → α)
    (f_loc  : Loc  → α) (f_lbl  : Lbl  → α) (f_real : rT → α)
    (f_prod : BaseLit rT × BaseLit rT → α)
    (f_nest : BaseLit rT × rT → α)
    (h_real : Measurable f_real)
    (h_prod : Measurable f_prod) (h_nest : Measurable f_nest) :
    Measurable (fun b : BaseLit rT =>
      BaseLit.casesOn (motive := fun _ => α) b
        f_int f_bool (f_unit ()) f_loc f_lbl f_real
        (fun b1 b2 => f_prod (b1, b2))
        (fun b r => f_nest (b, r))) := by
  intro S hS
  rw [BaseLit.casesOn_preimage_decomp]
  iterate 7 refine .union ?_ ?_
  · exact int.measurableEmbedding.measurableSet_image'   .of_discrete
  · exact bool.measurableEmbedding.measurableSet_image'  .of_discrete
  · exact unit.measurableEmbedding.measurableSet_image'  .of_discrete
  · exact loc.measurableEmbedding.measurableSet_image'   .of_discrete
  · exact lbl.measurableEmbedding.measurableSet_image'   .of_discrete
  · exact real.measurableEmbedding.measurableSet_image'  (h_real hS)
  · exact prod.measurableEmbedding.measurableSet_image'  (h_prod hS)
  · exact nest.measurableEmbedding.measurableSet_image'  (h_nest hS)

end BaseLit
