module

import all Mathlib.Tactic.DeriveCountable
public import Metrology.ProbLang.Measure
public import Metrology.ProbLang.Syntax.Syntax

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

/-- A cylinder is a `BaseLit`-shaped tree whose `rT`-payloads have been replaced by `Set rT`. -/
inductive Cylinder (rT : Type _)
  | int (z : Int)
  | bool (b : Bool)
  | unit
  | loc (l : Loc)
  | lbl (l : Lbl)
  | real (S : Set rT)
  | prod (c1 c2 : Cylinder rT)
  | nest (c : Cylinder rT) (S : Set rT)

/-- A tree with all data forgotten, in order to be countable. -/
inductive Shape
  | int (z : Int)
  | bool (b : Bool)
  | unit
  | loc (l : Loc)
  | lbl (l : Lbl)
  | real
  | prod (s1 s2 : Shape)
  | nest (s : Shape)
  deriving Countable

/-- Interpret a cylinder as the set of `BaseLit rT` it describes. Each branch is the image of
the corresponding constructor over the cartesian product of its arg-sets — singleton sets for
discrete leaves, the carried `Set rT` for real-leaves, and recursive `flatten` for sub-cylinders. -/
@[simp] def Cylinder.flatten {rT : Type _} : Cylinder rT → Set (BaseLit rT)
  | .int z        => BaseLit.int '' {z}
  | .bool b       => BaseLit.bool '' {b}
  | .unit         => {BaseLit.unit}
  | .loc l        => BaseLit.loc '' {l}
  | .lbl l        => BaseLit.lbl '' {l}
  | .real Sr      => BaseLit.real '' Sr
  | .prod c1 c2   => (fun p => BaseLit.prod p.1 p.2) '' (flatten c1 ×ˢ flatten c2)
  | .nest c Sr    => (fun p => BaseLit.nest p.1 p.2) '' (flatten c ×ˢ Sr)

/-- A cylinder has measurable leaves if every `Set rT` it carries is measurable. -/
inductive Cylinder.HasMeasurableLeaves {rT : Type _} [MeasurableSpace rT] :
    Cylinder rT → Prop where
  | int     : HasMeasurableLeaves (.int z)
  | bool    : HasMeasurableLeaves (.bool b)
  | unit    : HasMeasurableLeaves .unit
  | loc     : HasMeasurableLeaves (.loc z)
  | lbl     : HasMeasurableLeaves (.lbl z)
  | real Sᵣ : MeasurableSet Sᵣ → HasMeasurableLeaves (.real Sᵣ)
  | prod    : HasMeasurableLeaves c1 → HasMeasurableLeaves c2 → HasMeasurableLeaves (.prod c1 c2)
  | nest Sᵣ : HasMeasurableLeaves c → MeasurableSet Sᵣ → HasMeasurableLeaves (.nest c Sᵣ)

instance instMeasurableSpaceBaseLit [MeasurableSpace rT] : MeasurableSpace (BaseLit rT) :=
  .generateFrom <| Cylinder.flatten '' { c : Cylinder rT | c.HasMeasurableLeaves }

@[simp] def shape : BaseLit rT → Shape
  | .int z        => .int z
  | .bool b       => .bool b
  | .unit         => .unit
  | .loc l        => .loc l
  | .lbl l        => .lbl l
  | .real _       => .real
  | .prod b1 b2   => .prod (shape b1) (shape b2)
  | .nest b _     => .nest (shape b)

/-- Shape of a cylinder (forgets data leaves). -/
@[simp] def Cylinder.shape {rT : Type _} : Cylinder rT → Shape
  | .int z        => .int z
  | .bool b       => .bool b
  | .unit         => .unit
  | .loc l        => .loc l
  | .lbl l        => .lbl l
  | .real _       => .real
  | .prod c1 c2   => .prod (shape c1) (shape c2)
  | .nest c _     => .nest (shape c)

/-- The "universe cylinder" for a given shape: `univ` at every leaf, same skeleton as the shape. -/
@[simp] def Shape.cylinder {rT : Type _} : Shape → Cylinder rT
  | .int z        => .int z
  | .bool b       => .bool b
  | .unit         => .unit
  | .loc l        => .loc l
  | .lbl l        => .lbl l
  | .real         => .real Set.univ
  | .prod s1 s2   => .prod (cylinder s1) (cylinder s2)
  | .nest s       => .nest (cylinder s) Set.univ

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
    (h : b ∈ Cylinder.flatten c) : BaseLit.shape b = Cylinder.shape c := by
  induction c generalizing b with
  | int _ | bool _ | unit | loc _ | lbl _ => simp_all
  | real _ => obtain ⟨_, _, rfl⟩ := h; rfl
  | prod c₁ c₂ ih₁ ih₂ =>
    obtain ⟨⟨x, y⟩, ⟨hx, hy⟩, rfl⟩ := h
    show BaseLit.shape (BaseLit.prod x y) = _
    simp [BaseLit.shape, ih₁ hx, ih₂ hy]
  | nest c S ih =>
    obtain ⟨⟨x, r⟩, ⟨hx, _⟩, rfl⟩ := h
    show BaseLit.shape (BaseLit.nest x r) = _
    simp [BaseLit.shape, ih hx]

/-- Flattens of cylinders with different shapes are disjoint. -/
theorem Cylinder.flatten_disjoint_of_shape_ne {rT : Type _} {c₁ c₂ : Cylinder rT}
    (h : Cylinder.shape c₁ ≠ Cylinder.shape c₂) : Cylinder.flatten c₁ ∩ Cylinder.flatten c₂ = ∅ := by
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
    all_goals (rw [Cylinder.flatten_disjoint_of_shape_ne (by simp [Cylinder.shape])]; rfl)
  | bool b₁ =>
    cases c₂
    case bool b₂ => simp [Cylinder.inter?]; split_ifs <;> simp_all
    all_goals (rw [Cylinder.flatten_disjoint_of_shape_ne (by simp [Cylinder.shape])]; rfl)
  | unit =>
    cases c₂
    case unit => simp [Cylinder.inter?]
    all_goals (rw [Cylinder.flatten_disjoint_of_shape_ne (by simp [Cylinder.shape])]; rfl)
  | loc l₁ =>
    cases c₂
    case loc l₂ => simp [Cylinder.inter?]; split_ifs <;> simp_all
    all_goals (rw [Cylinder.flatten_disjoint_of_shape_ne (by simp [Cylinder.shape])]; rfl)
  | lbl l₁ =>
    cases c₂
    case lbl l₂ => simp [Cylinder.inter?]; split_ifs <;> simp_all
    all_goals (rw [Cylinder.flatten_disjoint_of_shape_ne (by simp [Cylinder.shape])]; rfl)
  | real S₁ =>
    cases c₂
    case real S₂ => simp [Cylinder.inter?]; ext b; cases b <;> simp
    all_goals (rw [Cylinder.flatten_disjoint_of_shape_ne (by simp [Cylinder.shape])]; rfl)
  | prod a b ih₁ ih₂ =>
    cases c₂
    case prod a' b' =>
      show (BaseLit.prod.ι '' (Cylinder.flatten a ×ˢ Cylinder.flatten b)) ∩
           (BaseLit.prod.ι '' (Cylinder.flatten a' ×ˢ Cylinder.flatten b')) = _
      rw [← Set.image_inter BaseLit.prod.ι.inj, Set.prod_inter_prod, ih₁, ih₂]
      cases hr₁ : Cylinder.inter? a a' <;> cases hr₂ : Cylinder.inter? b b' <;>
        simp [Cylinder.inter?, hr₁, hr₂]
    all_goals (rw [Cylinder.flatten_disjoint_of_shape_ne (by simp [Cylinder.shape])]; rfl)
  | nest c S ih =>
    cases c₂
    case nest c' S' =>
      show (BaseLit.nest.ι '' (Cylinder.flatten c ×ˢ S)) ∩
           (BaseLit.nest.ι '' (Cylinder.flatten c' ×ˢ S')) = _
      rw [← Set.image_inter BaseLit.nest.ι.inj, Set.prod_inter_prod, ih]
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
  ⋃ _ ∈ S, Cylinder.flatten (Cylinder.unit : Cylinder rT)

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
  ProbLang.BaseLit.Cylinder.HasMeasurableLeaves

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
    refine ⟨enc.encode (BaseLit.shape b), ?_⟩
    have hd : enc.decode (enc.encode (BaseLit.shape b)) = some (BaseLit.shape b) := enc.encodek _
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

end ProbLang.BaseLit -- namespace

end BaseLit -- section

section Pat

/-# Measure space on patterns.

Closely parallels the `BaseLit` construction above. `Pat` has:
- one nullary constructor (`wildcard`)
- one data-leaf constructor (`lit (b : BaseLit rT)`)
- three purely-recursive constructors (`pair`, `inl`, `inr`).

The goal here is to demonstrate that the cylinder-flatten machinery from `BaseLit` ports
directly. We don't push downstream; we stop once `measurable_rec` is in hand.
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

end ProbLang.Pat -- namespace

end Pat -- section

section Exp

/-# Measure space on expressions.

Follows the same `BaseLit`/`Pat` template. `Exp` has:
- two syntax-leaf constructors (`bvar : Nat`, `fvar : Var`)
- one data-leaf constructor (`lit : BaseLit rT`)
- one nullary constructor (`fail`)
- many recursive constructors of arities 1–3 (`lam`, `fix`, `fst`, `snd`, `inl`, `inr`,
  `alloc`, `load`, `tape`; `app`, `pair`, `store`, `rand`; `cond`, `case`)
- mixed constructors:
  - `unop : UnOp + 1 rec` (UnOp is a syntax-leaf-style discrete tag retained in the shape)
  - `binop : BinOp + 2 rec`
  - `scrut : 1 rec + Pat rT` (Pat is a data leaf)
-/

namespace ProbLang.Exp

macro "solve_ι_inj" : tactic => `(tactic|
  (intro a b h;
   first
   | (cases h; rfl)
   | (obtain ⟨_, _⟩ := a; obtain ⟨_, _⟩ := b; cases h; rfl)
   | (obtain ⟨_, _, _⟩ := a; obtain ⟨_, _, _⟩ := b; cases h; rfl)))

theorem bvar.ι.inj  {rT : Type _} : Function.Injective (@Exp.bvar.ι  rT) := by solve_ι_inj
theorem fvar.ι.inj  {rT : Type _} : Function.Injective (@Exp.fvar.ι  rT) := by solve_ι_inj
theorem lit.ι.inj   {rT : Type _} : Function.Injective (@Exp.lit.ι   rT) := by solve_ι_inj
theorem lam.ι.inj   {rT : Type _} : Function.Injective (@Exp.lam.ι   rT) := by solve_ι_inj
theorem fix.ι.inj   {rT : Type _} : Function.Injective (@Exp.fix.ι   rT) := by solve_ι_inj
theorem app.ι.inj   {rT : Type _} : Function.Injective (@Exp.app.ι   rT) := by solve_ι_inj
theorem unop.ι.inj  {rT : Type _} : Function.Injective (@Exp.unop.ι  rT) := by solve_ι_inj
theorem binop.ι.inj {rT : Type _} : Function.Injective (@Exp.binop.ι rT) := by solve_ι_inj
theorem cond.ι.inj  {rT : Type _} : Function.Injective (@Exp.cond.ι  rT) := by solve_ι_inj
theorem pair.ι.inj  {rT : Type _} : Function.Injective (@Exp.pair.ι  rT) := by solve_ι_inj
theorem fst.ι.inj   {rT : Type _} : Function.Injective (@Exp.fst.ι   rT) := by solve_ι_inj
theorem snd.ι.inj   {rT : Type _} : Function.Injective (@Exp.snd.ι   rT) := by solve_ι_inj
theorem inl.ι.inj   {rT : Type _} : Function.Injective (@Exp.inl.ι   rT) := by solve_ι_inj
theorem inr.ι.inj   {rT : Type _} : Function.Injective (@Exp.inr.ι   rT) := by solve_ι_inj
theorem case.ι.inj  {rT : Type _} : Function.Injective (@Exp.case.ι  rT) := by solve_ι_inj
theorem alloc.ι.inj {rT : Type _} : Function.Injective (@Exp.alloc.ι rT) := by solve_ι_inj
theorem load.ι.inj  {rT : Type _} : Function.Injective (@Exp.load.ι  rT) := by solve_ι_inj
theorem store.ι.inj {rT : Type _} : Function.Injective (@Exp.store.ι rT) := by solve_ι_inj
theorem tape.ι.inj  {rT : Type _} : Function.Injective (@Exp.tape.ι  rT) := by solve_ι_inj
theorem rand.ι.inj  {rT : Type _} : Function.Injective (@Exp.rand.ι  rT) := by solve_ι_inj
theorem scrut.ι.inj {rT : Type _} : Function.Injective (@Exp.scrut.ι rT) := by solve_ι_inj

/-- A cylinder is an `Exp`-shaped tree whose data-leaf payloads (`BaseLit rT` in `lit`,
`Pat rT` in `scrut`) have been replaced by measurable sets of those types. Syntax-leaf args
(`bvar`'s `Nat`, `fvar`'s `Var`, `unop`'s `UnOp`, `binop`'s `BinOp`) are kept as-is. -/
inductive Cylinder (rT : Type _)
  | bvar (n : Nat)
  | fvar (x : Var)
  | lit (S : Set (BaseLit rT))
  | lam (c : Cylinder rT)
  | fix (c : Cylinder rT)
  | app (c1 c2 : Cylinder rT)
  | unop (u : UnOp) (c : Cylinder rT)
  | binop (b : BinOp) (c1 c2 : Cylinder rT)
  | cond (cc ct cf : Cylinder rT)
  | pair (c1 c2 : Cylinder rT)
  | fst (c : Cylinder rT)
  | snd (c : Cylinder rT)
  | inl (c : Cylinder rT)
  | inr (c : Cylinder rT)
  | case (cc cl cr : Cylinder rT)
  | alloc (c : Cylinder rT)
  | load (c : Cylinder rT)
  | store (c1 c2 : Cylinder rT)
  | tape (c : Cylinder rT)
  | rand (c1 c2 : Cylinder rT)
  | fail
  | scrut (c : Cylinder rT) (S : Set (Pat rT))

/-- An expression with all data-leaf payloads forgotten. Syntax-leaf args are kept. -/
inductive Shape
  | bvar (n : Nat)
  | fvar (x : Var)
  | lit
  | lam (s : Shape)
  | fix (s : Shape)
  | app (s1 s2 : Shape)
  | unop (u : UnOp) (s : Shape)
  | binop (b : BinOp) (s1 s2 : Shape)
  | cond (sc st sf : Shape)
  | pair (s1 s2 : Shape)
  | fst (s : Shape)
  | snd (s : Shape)
  | inl (s : Shape)
  | inr (s : Shape)
  | case (sc sl sr : Shape)
  | alloc (s : Shape)
  | load (s : Shape)
  | store (s1 s2 : Shape)
  | tape (s : Shape)
  | rand (s1 s2 : Shape)
  | fail
  | scrut (s : Shape)
  deriving Countable

/-- Interpret a cylinder as the set of `Exp rT` it describes. -/
@[simp] def Cylinder.flatten {rT : Type _} : Cylinder rT → Set (Exp rT)
  | .bvar n        => {Exp.bvar n}
  | .fvar x        => {Exp.fvar x}
  | .lit S         => Exp.lit '' S
  | .lam c         => Exp.lam '' flatten c
  | .fix c         => Exp.fix '' flatten c
  | .app c1 c2     => (fun p => Exp.app p.1 p.2) '' (flatten c1 ×ˢ flatten c2)
  | .unop u c      => Exp.unop u '' flatten c
  | .binop b c1 c2 => (fun p => Exp.binop b p.1 p.2) '' (flatten c1 ×ˢ flatten c2)
  | .cond cc ct cf =>
      (fun p : Exp rT × Exp rT × Exp rT => Exp.cond p.1 p.2.1 p.2.2) ''
        (flatten cc ×ˢ flatten ct ×ˢ flatten cf)
  | .pair c1 c2    => (fun p => Exp.pair p.1 p.2) '' (flatten c1 ×ˢ flatten c2)
  | .fst c         => Exp.fst '' flatten c
  | .snd c         => Exp.snd '' flatten c
  | .inl c         => Exp.inl '' flatten c
  | .inr c         => Exp.inr '' flatten c
  | .case cc cl cr =>
      (fun p : Exp rT × Exp rT × Exp rT => Exp.case p.1 p.2.1 p.2.2) ''
        (flatten cc ×ˢ flatten cl ×ˢ flatten cr)
  | .alloc c       => Exp.alloc '' flatten c
  | .load c        => Exp.load '' flatten c
  | .store c1 c2   => (fun p => Exp.store p.1 p.2) '' (flatten c1 ×ˢ flatten c2)
  | .tape c        => Exp.tape '' flatten c
  | .rand c1 c2    => (fun p => Exp.rand p.1 p.2) '' (flatten c1 ×ˢ flatten c2)
  | .fail          => {Exp.fail}
  | .scrut c S     => (fun p => Exp.scrut p.1 p.2) '' (flatten c ×ˢ S)

/-- A cylinder has measurable leaves if every data-leaf set it carries is measurable. -/
inductive Cylinder.HasMeasurableLeaves {rT : Type _} [MeasurableSpace rT] :
    Cylinder rT → Prop where
  | bvar  : HasMeasurableLeaves (.bvar n)
  | fvar  : HasMeasurableLeaves (.fvar x)
  | lit S : MeasurableSet S → HasMeasurableLeaves (.lit S)
  | lam   : HasMeasurableLeaves c → HasMeasurableLeaves (.lam c)
  | fix   : HasMeasurableLeaves c → HasMeasurableLeaves (.fix c)
  | app   : HasMeasurableLeaves c1 → HasMeasurableLeaves c2 → HasMeasurableLeaves (.app c1 c2)
  | unop  : HasMeasurableLeaves c → HasMeasurableLeaves (.unop u c)
  | binop : HasMeasurableLeaves c1 → HasMeasurableLeaves c2 → HasMeasurableLeaves (.binop b c1 c2)
  | cond  : HasMeasurableLeaves cc → HasMeasurableLeaves ct → HasMeasurableLeaves cf →
            HasMeasurableLeaves (.cond cc ct cf)
  | pair  : HasMeasurableLeaves c1 → HasMeasurableLeaves c2 → HasMeasurableLeaves (.pair c1 c2)
  | fst   : HasMeasurableLeaves c → HasMeasurableLeaves (.fst c)
  | snd   : HasMeasurableLeaves c → HasMeasurableLeaves (.snd c)
  | inl   : HasMeasurableLeaves c → HasMeasurableLeaves (.inl c)
  | inr   : HasMeasurableLeaves c → HasMeasurableLeaves (.inr c)
  | case  : HasMeasurableLeaves cc → HasMeasurableLeaves cl → HasMeasurableLeaves cr →
            HasMeasurableLeaves (.case cc cl cr)
  | alloc : HasMeasurableLeaves c → HasMeasurableLeaves (.alloc c)
  | load  : HasMeasurableLeaves c → HasMeasurableLeaves (.load c)
  | store : HasMeasurableLeaves c1 → HasMeasurableLeaves c2 → HasMeasurableLeaves (.store c1 c2)
  | tape  : HasMeasurableLeaves c → HasMeasurableLeaves (.tape c)
  | rand  : HasMeasurableLeaves c1 → HasMeasurableLeaves c2 → HasMeasurableLeaves (.rand c1 c2)
  | fail  : HasMeasurableLeaves .fail
  | scrut S : HasMeasurableLeaves c → MeasurableSet S → HasMeasurableLeaves (.scrut c S)

instance instMeasurableSpaceExp [MeasurableSpace rT] : MeasurableSpace (Exp rT) :=
  .generateFrom <| Cylinder.flatten '' { c : Cylinder rT | c.HasMeasurableLeaves }

@[simp] def shape : Exp rT → Shape
  | .bvar n        => .bvar n
  | .fvar x        => .fvar x
  | .lit _         => .lit
  | .lam e         => .lam (shape e)
  | .fix e         => .fix (shape e)
  | .app e1 e2     => .app (shape e1) (shape e2)
  | .unop u e      => .unop u (shape e)
  | .binop b e1 e2 => .binop b (shape e1) (shape e2)
  | .cond ec et ef => .cond (shape ec) (shape et) (shape ef)
  | .pair e1 e2    => .pair (shape e1) (shape e2)
  | .fst e         => .fst (shape e)
  | .snd e         => .snd (shape e)
  | .inl e         => .inl (shape e)
  | .inr e         => .inr (shape e)
  | .case ec el er => .case (shape ec) (shape el) (shape er)
  | .alloc e       => .alloc (shape e)
  | .load e        => .load (shape e)
  | .store e1 e2   => .store (shape e1) (shape e2)
  | .tape e        => .tape (shape e)
  | .rand e1 e2    => .rand (shape e1) (shape e2)
  | .fail          => .fail
  | .scrut e _     => .scrut (shape e)

/-- Shape of a cylinder (forgets data leaves). -/
@[simp] def Cylinder.shape {rT : Type _} : Cylinder rT → Shape
  | .bvar n        => .bvar n
  | .fvar x        => .fvar x
  | .lit _         => .lit
  | .lam c         => .lam (shape c)
  | .fix c         => .fix (shape c)
  | .app c1 c2     => .app (shape c1) (shape c2)
  | .unop u c      => .unop u (shape c)
  | .binop b c1 c2 => .binop b (shape c1) (shape c2)
  | .cond cc ct cf => .cond (shape cc) (shape ct) (shape cf)
  | .pair c1 c2    => .pair (shape c1) (shape c2)
  | .fst c         => .fst (shape c)
  | .snd c         => .snd (shape c)
  | .inl c         => .inl (shape c)
  | .inr c         => .inr (shape c)
  | .case cc cl cr => .case (shape cc) (shape cl) (shape cr)
  | .alloc c       => .alloc (shape c)
  | .load c        => .load (shape c)
  | .store c1 c2   => .store (shape c1) (shape c2)
  | .tape c        => .tape (shape c)
  | .rand c1 c2    => .rand (shape c1) (shape c2)
  | .fail          => .fail
  | .scrut c _     => .scrut (shape c)

/-- The "universe cylinder" for a given shape: `univ` at every data leaf, same skeleton. -/
@[simp] def Shape.cylinder {rT : Type _} : Shape → Cylinder rT
  | .bvar n        => .bvar n
  | .fvar x        => .fvar x
  | .lit           => .lit Set.univ
  | .lam s         => .lam (cylinder s)
  | .fix s         => .fix (cylinder s)
  | .app s1 s2     => .app (cylinder s1) (cylinder s2)
  | .unop u s      => .unop u (cylinder s)
  | .binop b s1 s2 => .binop b (cylinder s1) (cylinder s2)
  | .cond sc st sf => .cond (cylinder sc) (cylinder st) (cylinder sf)
  | .pair s1 s2    => .pair (cylinder s1) (cylinder s2)
  | .fst s         => .fst (cylinder s)
  | .snd s         => .snd (cylinder s)
  | .inl s         => .inl (cylinder s)
  | .inr s         => .inr (cylinder s)
  | .case sc sl sr => .case (cylinder sc) (cylinder sl) (cylinder sr)
  | .alloc s       => .alloc (cylinder s)
  | .load s        => .load (cylinder s)
  | .store s1 s2   => .store (cylinder s1) (cylinder s2)
  | .tape s        => .tape (cylinder s)
  | .rand s1 s2    => .rand (cylinder s1) (cylinder s2)
  | .fail          => .fail
  | .scrut s       => .scrut (cylinder s) Set.univ

/-! ### Cylinder intersection. -/

/-- Partial intersection of cylinders. -/
def Cylinder.inter? {rT : Type _} : Cylinder rT → Cylinder rT → Option (Cylinder rT)
  | .bvar n₁, .bvar n₂ => if n₁ = n₂ then some (.bvar n₁) else none
  | .fvar x₁, .fvar x₂ => if x₁ = x₂ then some (.fvar x₁) else none
  | .lit S₁, .lit S₂ => some (.lit (S₁ ∩ S₂))
  | .lam c, .lam c' =>
      match Cylinder.inter? c c' with
      | some r => some (.lam r)
      | none => none
  | .fix c, .fix c' =>
      match Cylinder.inter? c c' with
      | some r => some (.fix r)
      | none => none
  | .app c₁ c₂, .app c₁' c₂' =>
      match Cylinder.inter? c₁ c₁', Cylinder.inter? c₂ c₂' with
      | some r₁, some r₂ => some (.app r₁ r₂)
      | _, _ => none
  | .unop u₁ c, .unop u₂ c' =>
      if u₁ = u₂ then
        match Cylinder.inter? c c' with
        | some r => some (.unop u₁ r)
        | none => none
      else none
  | .binop b₁ c₁ c₂, .binop b₂ c₁' c₂' =>
      if b₁ = b₂ then
        match Cylinder.inter? c₁ c₁', Cylinder.inter? c₂ c₂' with
        | some r₁, some r₂ => some (.binop b₁ r₁ r₂)
        | _, _ => none
      else none
  | .cond cc ct cf, .cond cc' ct' cf' =>
      match Cylinder.inter? cc cc', Cylinder.inter? ct ct', Cylinder.inter? cf cf' with
      | some rc, some rt, some rf => some (.cond rc rt rf)
      | _, _, _ => none
  | .pair c₁ c₂, .pair c₁' c₂' =>
      match Cylinder.inter? c₁ c₁', Cylinder.inter? c₂ c₂' with
      | some r₁, some r₂ => some (.pair r₁ r₂)
      | _, _ => none
  | .fst c, .fst c' =>
      match Cylinder.inter? c c' with
      | some r => some (.fst r)
      | none => none
  | .snd c, .snd c' =>
      match Cylinder.inter? c c' with
      | some r => some (.snd r)
      | none => none
  | .inl c, .inl c' =>
      match Cylinder.inter? c c' with
      | some r => some (.inl r)
      | none => none
  | .inr c, .inr c' =>
      match Cylinder.inter? c c' with
      | some r => some (.inr r)
      | none => none
  | .case cc cl cr, .case cc' cl' cr' =>
      match Cylinder.inter? cc cc', Cylinder.inter? cl cl', Cylinder.inter? cr cr' with
      | some rc, some rl, some rr => some (.case rc rl rr)
      | _, _, _ => none
  | .alloc c, .alloc c' =>
      match Cylinder.inter? c c' with
      | some r => some (.alloc r)
      | none => none
  | .load c, .load c' =>
      match Cylinder.inter? c c' with
      | some r => some (.load r)
      | none => none
  | .store c₁ c₂, .store c₁' c₂' =>
      match Cylinder.inter? c₁ c₁', Cylinder.inter? c₂ c₂' with
      | some r₁, some r₂ => some (.store r₁ r₂)
      | _, _ => none
  | .tape c, .tape c' =>
      match Cylinder.inter? c c' with
      | some r => some (.tape r)
      | none => none
  | .rand c₁ c₂, .rand c₁' c₂' =>
      match Cylinder.inter? c₁ c₁', Cylinder.inter? c₂ c₂' with
      | some r₁, some r₂ => some (.rand r₁ r₂)
      | _, _ => none
  | .fail, .fail => some .fail
  | .scrut c S, .scrut c' S' =>
      match Cylinder.inter? c c' with
      | some r => some (.scrut r (S ∩ S'))
      | none => none
  | _, _ => none

/-- Every element of a cylinder's flatten has that cylinder's shape. -/
theorem Cylinder.shape_of_mem_flatten {rT : Type _} {c : Cylinder rT} {e : Exp rT}
    (h : e ∈ Cylinder.flatten c) : Exp.shape e = Cylinder.shape c := by
  induction c generalizing e with
  | bvar _ | fvar _ | fail => simp_all
  | lit _ => obtain ⟨_, _, rfl⟩ := h; rfl
  | lam _ ih | fix _ ih | fst _ ih | snd _ ih | inl _ ih | inr _ ih
  | alloc _ ih | load _ ih | tape _ ih =>
    obtain ⟨x, hx, rfl⟩ := h
    simp [Exp.shape, ih hx]
  | unop _ _ ih =>
    obtain ⟨x, hx, rfl⟩ := h
    simp [Exp.shape, ih hx]
  | app _ _ ih₁ ih₂ | pair _ _ ih₁ ih₂ | store _ _ ih₁ ih₂ | rand _ _ ih₁ ih₂ =>
    obtain ⟨⟨x, y⟩, ⟨hx, hy⟩, rfl⟩ := h
    simp [Exp.shape, ih₁ hx, ih₂ hy]
  | binop _ _ _ ih₁ ih₂ =>
    obtain ⟨⟨x, y⟩, ⟨hx, hy⟩, rfl⟩ := h
    simp [Exp.shape, ih₁ hx, ih₂ hy]
  | cond _ _ _ ih₁ ih₂ ih₃ | case _ _ _ ih₁ ih₂ ih₃ =>
    obtain ⟨⟨x, y, z⟩, ⟨hx, hy, hz⟩, rfl⟩ := h
    simp [Exp.shape, ih₁ hx, ih₂ hy, ih₃ hz]
  | scrut _ _ ih =>
    obtain ⟨⟨x, y⟩, ⟨hx, _⟩, rfl⟩ := h
    simp [Exp.shape, ih hx]

/-- Flattens of cylinders with different shapes are disjoint. -/
theorem Cylinder.flatten_disjoint_of_shape_ne {rT : Type _} {c₁ c₂ : Cylinder rT}
    (h : Cylinder.shape c₁ ≠ Cylinder.shape c₂) : Cylinder.flatten c₁ ∩ Cylinder.flatten c₂ = ∅ := by
  ext e
  simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false, not_and]
  intro he₁ he₂
  exact h ((Cylinder.shape_of_mem_flatten he₁).symm.trans (Cylinder.shape_of_mem_flatten he₂))

/-- The cylinder flatten of the intersection equals the intersection of the flattens. -/
theorem Cylinder.flatten_inter {rT : Type _} (c₁ c₂ : Cylinder rT) :
    Cylinder.flatten c₁ ∩ Cylinder.flatten c₂
      = (Cylinder.inter? c₁ c₂).elim ∅ Cylinder.flatten := by
  induction c₁ generalizing c₂ with
  | bvar n₁ =>
    cases c₂
    case bvar n₂ => simp [Cylinder.inter?]; split_ifs <;> simp_all
    all_goals (rw [Cylinder.flatten_disjoint_of_shape_ne (by simp [Cylinder.shape])]; rfl)
  | fvar x₁ =>
    cases c₂
    case fvar x₂ => simp [Cylinder.inter?]; split_ifs <;> simp_all
    all_goals (rw [Cylinder.flatten_disjoint_of_shape_ne (by simp [Cylinder.shape])]; rfl)
  | lit S₁ =>
    cases c₂
    case lit S₂ => simp [Cylinder.inter?]; ext e; cases e <;> simp
    all_goals (rw [Cylinder.flatten_disjoint_of_shape_ne (by simp [Cylinder.shape])]; rfl)
  | lam c ih =>
    cases c₂
    case lam c' =>
      show (Exp.lam.ι '' Cylinder.flatten c) ∩ (Exp.lam.ι '' Cylinder.flatten c') = _
      rw [← Set.image_inter Exp.lam.ι.inj, ih]
      cases hr : Cylinder.inter? c c' <;> simp [Cylinder.inter?, hr]
    all_goals (rw [Cylinder.flatten_disjoint_of_shape_ne (by simp [Cylinder.shape])]; rfl)
  | fix c ih =>
    cases c₂
    case fix c' =>
      show (Exp.fix.ι '' Cylinder.flatten c) ∩ (Exp.fix.ι '' Cylinder.flatten c') = _
      rw [← Set.image_inter Exp.fix.ι.inj, ih]
      cases hr : Cylinder.inter? c c' <;> simp [Cylinder.inter?, hr]
    all_goals (rw [Cylinder.flatten_disjoint_of_shape_ne (by simp [Cylinder.shape])]; rfl)
  | app a b ih₁ ih₂ =>
    cases c₂
    case app a' b' =>
      show (Exp.app.ι '' (Cylinder.flatten a ×ˢ Cylinder.flatten b)) ∩
           (Exp.app.ι '' (Cylinder.flatten a' ×ˢ Cylinder.flatten b')) = _
      rw [← Set.image_inter Exp.app.ι.inj, Set.prod_inter_prod, ih₁, ih₂]
      cases hr₁ : Cylinder.inter? a a' <;> cases hr₂ : Cylinder.inter? b b' <;>
        simp [Cylinder.inter?, hr₁, hr₂]
    all_goals (rw [Cylinder.flatten_disjoint_of_shape_ne (by simp [Cylinder.shape])]; rfl)
  | unop u c ih =>
    cases c₂
    case unop u' c' =>
      show (Exp.unop u '' Cylinder.flatten c) ∩ (Exp.unop u' '' Cylinder.flatten c') = _
      by_cases hu : u = u'
      · subst hu
        rw [← Set.image_inter (fun _ _ h => by injection h), ih]
        cases hr : Cylinder.inter? c c' <;> simp [Cylinder.inter?, hr]
      · have hinter : Cylinder.inter? (Cylinder.unop u c) (Cylinder.unop u' c') = none := by
          simp [Cylinder.inter?, hu]
        rw [hinter]
        ext e
        simp only [Set.mem_inter_iff, Set.mem_image, Set.mem_empty_iff_false, iff_false,
          Option.elim_none, not_and]
        rintro ⟨a, _, rfl⟩ ⟨a', _, hh⟩
        injection hh with hu_eq _
        exact hu hu_eq.symm
    all_goals (rw [Cylinder.flatten_disjoint_of_shape_ne (by simp [Cylinder.shape])]; rfl)
  | binop b a₁ a₂ ih₁ ih₂ =>
    cases c₂
    case binop b' a₁' a₂' =>
      show ((fun p => Exp.binop b p.1 p.2) '' (Cylinder.flatten a₁ ×ˢ Cylinder.flatten a₂)) ∩
           ((fun p => Exp.binop b' p.1 p.2) '' (Cylinder.flatten a₁' ×ˢ Cylinder.flatten a₂')) = _
      by_cases hb : b = b'
      · subst hb
        rw [← Set.image_inter (fun _ _ h => by injection h with _ h1 h2; exact Prod.ext h1 h2),
            Set.prod_inter_prod, ih₁, ih₂]
        cases hr₁ : Cylinder.inter? a₁ a₁' <;> cases hr₂ : Cylinder.inter? a₂ a₂' <;>
          simp [Cylinder.inter?, hr₁, hr₂]
      · have hinter : Cylinder.inter? (Cylinder.binop b a₁ a₂) (Cylinder.binop b' a₁' a₂') = none := by
          simp [Cylinder.inter?, hb]
        rw [hinter]
        ext e
        simp only [Set.mem_inter_iff, Set.mem_image, Set.mem_empty_iff_false, iff_false,
          Option.elim_none, not_and]
        rintro ⟨a, _, rfl⟩ ⟨a', _, hh⟩
        injection hh with hb_eq _ _
        exact hb hb_eq.symm
    all_goals (rw [Cylinder.flatten_disjoint_of_shape_ne (by simp [Cylinder.shape])]; rfl)
  | cond cc ct cf ihc iht ihf =>
    cases c₂
    case cond cc' ct' cf' =>
      show (Exp.cond.ι '' (Cylinder.flatten cc ×ˢ Cylinder.flatten ct ×ˢ Cylinder.flatten cf)) ∩
           (Exp.cond.ι '' (Cylinder.flatten cc' ×ˢ Cylinder.flatten ct' ×ˢ Cylinder.flatten cf')) = _
      rw [← Set.image_inter Exp.cond.ι.inj, Set.prod_inter_prod, Set.prod_inter_prod,
          ihc, iht, ihf]
      cases hrc : Cylinder.inter? cc cc' <;> cases hrt : Cylinder.inter? ct ct' <;>
        cases hrf : Cylinder.inter? cf cf' <;>
        simp [Cylinder.inter?, hrc, hrt, hrf]
    all_goals (rw [Cylinder.flatten_disjoint_of_shape_ne (by simp [Cylinder.shape])]; rfl)
  | pair a b ih₁ ih₂ =>
    cases c₂
    case pair a' b' =>
      show (Exp.pair.ι '' (Cylinder.flatten a ×ˢ Cylinder.flatten b)) ∩
           (Exp.pair.ι '' (Cylinder.flatten a' ×ˢ Cylinder.flatten b')) = _
      rw [← Set.image_inter Exp.pair.ι.inj, Set.prod_inter_prod, ih₁, ih₂]
      cases hr₁ : Cylinder.inter? a a' <;> cases hr₂ : Cylinder.inter? b b' <;>
        simp [Cylinder.inter?, hr₁, hr₂]
    all_goals (rw [Cylinder.flatten_disjoint_of_shape_ne (by simp [Cylinder.shape])]; rfl)
  | fst c ih =>
    cases c₂
    case fst c' =>
      show (Exp.fst.ι '' Cylinder.flatten c) ∩ (Exp.fst.ι '' Cylinder.flatten c') = _
      rw [← Set.image_inter Exp.fst.ι.inj, ih]
      cases hr : Cylinder.inter? c c' <;> simp [Cylinder.inter?, hr]
    all_goals (rw [Cylinder.flatten_disjoint_of_shape_ne (by simp [Cylinder.shape])]; rfl)
  | snd c ih =>
    cases c₂
    case snd c' =>
      show (Exp.snd.ι '' Cylinder.flatten c) ∩ (Exp.snd.ι '' Cylinder.flatten c') = _
      rw [← Set.image_inter Exp.snd.ι.inj, ih]
      cases hr : Cylinder.inter? c c' <;> simp [Cylinder.inter?, hr]
    all_goals (rw [Cylinder.flatten_disjoint_of_shape_ne (by simp [Cylinder.shape])]; rfl)
  | inl c ih =>
    cases c₂
    case inl c' =>
      show (Exp.inl.ι '' Cylinder.flatten c) ∩ (Exp.inl.ι '' Cylinder.flatten c') = _
      rw [← Set.image_inter Exp.inl.ι.inj, ih]
      cases hr : Cylinder.inter? c c' <;> simp [Cylinder.inter?, hr]
    all_goals (rw [Cylinder.flatten_disjoint_of_shape_ne (by simp [Cylinder.shape])]; rfl)
  | inr c ih =>
    cases c₂
    case inr c' =>
      show (Exp.inr.ι '' Cylinder.flatten c) ∩ (Exp.inr.ι '' Cylinder.flatten c') = _
      rw [← Set.image_inter Exp.inr.ι.inj, ih]
      cases hr : Cylinder.inter? c c' <;> simp [Cylinder.inter?, hr]
    all_goals (rw [Cylinder.flatten_disjoint_of_shape_ne (by simp [Cylinder.shape])]; rfl)
  | case cc cl cr ihc ihl ihr =>
    cases c₂
    case case cc' cl' cr' =>
      show (Exp.case.ι '' (Cylinder.flatten cc ×ˢ Cylinder.flatten cl ×ˢ Cylinder.flatten cr)) ∩
           (Exp.case.ι '' (Cylinder.flatten cc' ×ˢ Cylinder.flatten cl' ×ˢ Cylinder.flatten cr')) = _
      rw [← Set.image_inter Exp.case.ι.inj, Set.prod_inter_prod, Set.prod_inter_prod,
          ihc, ihl, ihr]
      cases hrc : Cylinder.inter? cc cc' <;> cases hrl : Cylinder.inter? cl cl' <;>
        cases hrr : Cylinder.inter? cr cr' <;>
        simp [Cylinder.inter?, hrc, hrl, hrr]
    all_goals (rw [Cylinder.flatten_disjoint_of_shape_ne (by simp [Cylinder.shape])]; rfl)
  | alloc c ih =>
    cases c₂
    case alloc c' =>
      show (Exp.alloc.ι '' Cylinder.flatten c) ∩ (Exp.alloc.ι '' Cylinder.flatten c') = _
      rw [← Set.image_inter Exp.alloc.ι.inj, ih]
      cases hr : Cylinder.inter? c c' <;> simp [Cylinder.inter?, hr]
    all_goals (rw [Cylinder.flatten_disjoint_of_shape_ne (by simp [Cylinder.shape])]; rfl)
  | load c ih =>
    cases c₂
    case load c' =>
      show (Exp.load.ι '' Cylinder.flatten c) ∩ (Exp.load.ι '' Cylinder.flatten c') = _
      rw [← Set.image_inter Exp.load.ι.inj, ih]
      cases hr : Cylinder.inter? c c' <;> simp [Cylinder.inter?, hr]
    all_goals (rw [Cylinder.flatten_disjoint_of_shape_ne (by simp [Cylinder.shape])]; rfl)
  | store a b ih₁ ih₂ =>
    cases c₂
    case store a' b' =>
      show (Exp.store.ι '' (Cylinder.flatten a ×ˢ Cylinder.flatten b)) ∩
           (Exp.store.ι '' (Cylinder.flatten a' ×ˢ Cylinder.flatten b')) = _
      rw [← Set.image_inter Exp.store.ι.inj, Set.prod_inter_prod, ih₁, ih₂]
      cases hr₁ : Cylinder.inter? a a' <;> cases hr₂ : Cylinder.inter? b b' <;>
        simp [Cylinder.inter?, hr₁, hr₂]
    all_goals (rw [Cylinder.flatten_disjoint_of_shape_ne (by simp [Cylinder.shape])]; rfl)
  | tape c ih =>
    cases c₂
    case tape c' =>
      show (Exp.tape.ι '' Cylinder.flatten c) ∩ (Exp.tape.ι '' Cylinder.flatten c') = _
      rw [← Set.image_inter Exp.tape.ι.inj, ih]
      cases hr : Cylinder.inter? c c' <;> simp [Cylinder.inter?, hr]
    all_goals (rw [Cylinder.flatten_disjoint_of_shape_ne (by simp [Cylinder.shape])]; rfl)
  | rand a b ih₁ ih₂ =>
    cases c₂
    case rand a' b' =>
      show (Exp.rand.ι '' (Cylinder.flatten a ×ˢ Cylinder.flatten b)) ∩
           (Exp.rand.ι '' (Cylinder.flatten a' ×ˢ Cylinder.flatten b')) = _
      rw [← Set.image_inter Exp.rand.ι.inj, Set.prod_inter_prod, ih₁, ih₂]
      cases hr₁ : Cylinder.inter? a a' <;> cases hr₂ : Cylinder.inter? b b' <;>
        simp [Cylinder.inter?, hr₁, hr₂]
    all_goals (rw [Cylinder.flatten_disjoint_of_shape_ne (by simp [Cylinder.shape])]; rfl)
  | fail =>
    cases c₂
    case fail => simp [Cylinder.inter?]
    all_goals (rw [Cylinder.flatten_disjoint_of_shape_ne (by simp [Cylinder.shape])]; rfl)
  | scrut c S ih =>
    cases c₂
    case scrut c' S' =>
      show (Exp.scrut.ι '' (Cylinder.flatten c ×ˢ S)) ∩ (Exp.scrut.ι '' (Cylinder.flatten c' ×ˢ S')) = _
      rw [← Set.image_inter Exp.scrut.ι.inj, Set.prod_inter_prod, ih]
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
  sorry

/-! ### Per-constructor covers. -/

def cover.bvar (S : Set Nat) : Set (Exp rT) :=
  ⋃ n ∈ S, Cylinder.flatten (.bvar n)

def cover.fvar (S : Set Var) : Set (Exp rT) :=
  ⋃ x ∈ S, Cylinder.flatten (.fvar x)

def cover.lit (S : Set (BaseLit rT)) : Set (Exp rT) :=
  Cylinder.flatten (.lit S)

def cover.lam (S : Set Shape) : Set (Exp rT) :=
  ⋃ s ∈ S, Cylinder.flatten (.lam s.cylinder)

def cover.fix (S : Set Shape) : Set (Exp rT) :=
  ⋃ s ∈ S, Cylinder.flatten (.fix s.cylinder)

def cover.app (S : Set (Shape × Shape)) : Set (Exp rT) :=
  ⋃ p ∈ S, Cylinder.flatten (.app p.1.cylinder p.2.cylinder)

def cover.unop (S : Set (UnOp × Shape)) : Set (Exp rT) :=
  ⋃ p ∈ S, Cylinder.flatten (.unop p.1 p.2.cylinder)

def cover.binop (S : Set (BinOp × Shape × Shape)) : Set (Exp rT) :=
  ⋃ p ∈ S, Cylinder.flatten (.binop p.1 p.2.1.cylinder p.2.2.cylinder)

def cover.cond (S : Set (Shape × Shape × Shape)) : Set (Exp rT) :=
  ⋃ p ∈ S, Cylinder.flatten (.cond p.1.cylinder p.2.1.cylinder p.2.2.cylinder)

def cover.pair (S : Set (Shape × Shape)) : Set (Exp rT) :=
  ⋃ p ∈ S, Cylinder.flatten (.pair p.1.cylinder p.2.cylinder)

def cover.fst (S : Set Shape) : Set (Exp rT) :=
  ⋃ s ∈ S, Cylinder.flatten (.fst s.cylinder)

def cover.snd (S : Set Shape) : Set (Exp rT) :=
  ⋃ s ∈ S, Cylinder.flatten (.snd s.cylinder)

def cover.inl (S : Set Shape) : Set (Exp rT) :=
  ⋃ s ∈ S, Cylinder.flatten (.inl s.cylinder)

def cover.inr (S : Set Shape) : Set (Exp rT) :=
  ⋃ s ∈ S, Cylinder.flatten (.inr s.cylinder)

def cover.case (S : Set (Shape × Shape × Shape)) : Set (Exp rT) :=
  ⋃ p ∈ S, Cylinder.flatten (.case p.1.cylinder p.2.1.cylinder p.2.2.cylinder)

def cover.alloc (S : Set Shape) : Set (Exp rT) :=
  ⋃ s ∈ S, Cylinder.flatten (.alloc s.cylinder)

def cover.load (S : Set Shape) : Set (Exp rT) :=
  ⋃ s ∈ S, Cylinder.flatten (.load s.cylinder)

def cover.store (S : Set (Shape × Shape)) : Set (Exp rT) :=
  ⋃ p ∈ S, Cylinder.flatten (.store p.1.cylinder p.2.cylinder)

def cover.tape (S : Set Shape) : Set (Exp rT) :=
  ⋃ s ∈ S, Cylinder.flatten (.tape s.cylinder)

def cover.rand (S : Set (Shape × Shape)) : Set (Exp rT) :=
  ⋃ p ∈ S, Cylinder.flatten (.rand p.1.cylinder p.2.cylinder)

def cover.fail (S : Set Unit) : Set (Exp rT) :=
  ⋃ _ ∈ S, Cylinder.flatten (Cylinder.fail : Cylinder rT)

def cover.scrut (S : Set Shape) : Set (Exp rT) :=
  ⋃ s ∈ S, Cylinder.flatten (.scrut s.cylinder Set.univ)

/-- Cylinder of a given shape has measurable leaves. -/
theorem Shape.cylinder_hasMeasurableLeaves [MeasurableSpace rT] (s : Shape) :
    (s.cylinder (rT := rT)).HasMeasurableLeaves := by
  induction s <;> constructor <;> measurability

/-- Flattening a cylinder of a shape equals set of terms with a given shape. -/
@[simp] theorem Shape.cylinder_preimage_shape (s : Shape) :
    (s.cylinder (rT := rT)).flatten = Exp.shape ⁻¹' {s} := by
  sorry

/-- Flattening a cylinder gives a measurable set. -/
@[measurability]
theorem flatten_measurable [MeasurableSpace rT] {c : Cylinder rT}
    (hc : c.HasMeasurableLeaves) : MeasurableSet c.flatten :=
  MeasurableSpace.measurableSet_generateFrom ⟨c, hc, rfl⟩

attribute [aesop safe constructors (rule_sets := [Measurable])]
  ProbLang.Exp.Cylinder.HasMeasurableLeaves

attribute [aesop safe apply (rule_sets := [Measurable])]
  Shape.cylinder_hasMeasurableLeaves

/-! ### The cylinder flatten family is a π-system that spans `Exp rT`. -/

theorem Cylinder.flatten_isPiSystem [MeasurableSpace rT] :
    IsPiSystem
      ({S : Set (Exp rT) | ∃ c : Cylinder rT, c.HasMeasurableLeaves ∧ Cylinder.flatten c = S}) := by
  rintro _ ⟨c₁, hc₁, rfl⟩ _ ⟨c₂, hc₂, rfl⟩ hne
  have hi : Cylinder.inter? c₁ c₂ ≠ none := by
    intro h
    have : c₁.flatten ∩ c₂.flatten = ∅ := by rw [Cylinder.flatten_inter, h]; rfl
    exact hne.ne_empty this
  obtain ⟨c, hc⟩ : ∃ c, Cylinder.inter? c₁ c₂ = some c := Option.ne_none_iff_exists'.mp hi
  exact ⟨c, Cylinder.hasMeasurableLeaves_inter hc₁ hc₂ hc, Cylinder.flatten_inter_some hc⟩

theorem Cylinder.flatten_isCountablySpanning [MeasurableSpace rT] :
    IsCountablySpanning
      ({S : Set (Exp rT) | ∃ c : Cylinder rT, c.HasMeasurableLeaves ∧ Cylinder.flatten c = S}) := by
  obtain ⟨enc⟩ := nonempty_encodable Shape
  refine ⟨fun n =>
    match enc.decode n with
    | some s => Cylinder.flatten (Shape.cylinder s : Cylinder rT)
    | none => Cylinder.flatten (.fail : Cylinder rT), ?_, ?_⟩
  · intro n
    cases h : enc.decode n with
    | none => exact ⟨.fail, .fail, by simp [h]⟩
    | some s => exact ⟨Shape.cylinder s, Shape.cylinder_hasMeasurableLeaves s, by simp [h]⟩
  · ext e
    simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
    refine ⟨enc.encode (Exp.shape e), ?_⟩
    have hd : enc.decode (enc.encode (Exp.shape e)) = some (Exp.shape e) := enc.encodek _
    rw [hd]
    simp [Shape.cylinder_preimage_shape]

/-! ### Measurability of the per-constructor covers. -/

macro "solve_cover_measurable" : tactic => `(tactic|
  first
  | exact .biUnion (Set.to_countable _) fun _ _ => flatten_measurable (by measurability)
  | exact flatten_measurable (by measurability))

@[measurability]
theorem cover.bvar.measurable [MeasurableSpace rT] (S : Set Nat) :
    MeasurableSet (bvar (rT := rT) S) := by solve_cover_measurable

@[measurability]
theorem cover.fvar.measurable [MeasurableSpace rT] (S : Set Var) :
    MeasurableSet (fvar (rT := rT) S) := by solve_cover_measurable

@[measurability]
theorem cover.lit.measurable [MeasurableSpace rT] {S : Set (BaseLit rT)} (hS : MeasurableSet S) :
    MeasurableSet (lit (rT := rT) S) :=
  flatten_measurable (.lit _ hS)

@[measurability]
theorem cover.lam.measurable [MeasurableSpace rT] (S : Set Shape) :
    MeasurableSet (lam (rT := rT) S) := by solve_cover_measurable

@[measurability]
theorem cover.fix.measurable [MeasurableSpace rT] (S : Set Shape) :
    MeasurableSet (fix (rT := rT) S) := by solve_cover_measurable

@[measurability]
theorem cover.app.measurable [MeasurableSpace rT] (S : Set (Shape × Shape)) :
    MeasurableSet (app (rT := rT) S) := by solve_cover_measurable

@[measurability]
theorem cover.unop.measurable [MeasurableSpace rT] (S : Set (UnOp × Shape)) :
    MeasurableSet (unop (rT := rT) S) := by solve_cover_measurable

@[measurability]
theorem cover.binop.measurable [MeasurableSpace rT] (S : Set (BinOp × Shape × Shape)) :
    MeasurableSet (binop (rT := rT) S) := by solve_cover_measurable

@[measurability]
theorem cover.cond.measurable [MeasurableSpace rT] (S : Set (Shape × Shape × Shape)) :
    MeasurableSet (cond (rT := rT) S) := by solve_cover_measurable

@[measurability]
theorem cover.pair.measurable [MeasurableSpace rT] (S : Set (Shape × Shape)) :
    MeasurableSet (pair (rT := rT) S) := by solve_cover_measurable

@[measurability]
theorem cover.fst.measurable [MeasurableSpace rT] (S : Set Shape) :
    MeasurableSet (fst (rT := rT) S) := by solve_cover_measurable

@[measurability]
theorem cover.snd.measurable [MeasurableSpace rT] (S : Set Shape) :
    MeasurableSet (snd (rT := rT) S) := by solve_cover_measurable

@[measurability]
theorem cover.inl.measurable [MeasurableSpace rT] (S : Set Shape) :
    MeasurableSet (inl (rT := rT) S) := by solve_cover_measurable

@[measurability]
theorem cover.inr.measurable [MeasurableSpace rT] (S : Set Shape) :
    MeasurableSet (inr (rT := rT) S) := by solve_cover_measurable

@[measurability]
theorem cover.case.measurable [MeasurableSpace rT] (S : Set (Shape × Shape × Shape)) :
    MeasurableSet (case (rT := rT) S) := by solve_cover_measurable

@[measurability]
theorem cover.alloc.measurable [MeasurableSpace rT] (S : Set Shape) :
    MeasurableSet (alloc (rT := rT) S) := by solve_cover_measurable

@[measurability]
theorem cover.load.measurable [MeasurableSpace rT] (S : Set Shape) :
    MeasurableSet (load (rT := rT) S) := by solve_cover_measurable

@[measurability]
theorem cover.store.measurable [MeasurableSpace rT] (S : Set (Shape × Shape)) :
    MeasurableSet (store (rT := rT) S) := by solve_cover_measurable

@[measurability]
theorem cover.tape.measurable [MeasurableSpace rT] (S : Set Shape) :
    MeasurableSet (tape (rT := rT) S) := by solve_cover_measurable

@[measurability]
theorem cover.rand.measurable [MeasurableSpace rT] (S : Set (Shape × Shape)) :
    MeasurableSet (rand (rT := rT) S) := by solve_cover_measurable

@[measurability]
theorem cover.fail.measurable [MeasurableSpace rT] (S : Set Unit) :
    MeasurableSet (fail (rT := rT) S) := by solve_cover_measurable

@[measurability]
theorem cover.scrut.measurable [MeasurableSpace rT] (S : Set Shape) :
    MeasurableSet (scrut (rT := rT) S) := by solve_cover_measurable

macro "solve_cover_eq_image" ctor:ident : tactic => `(tactic|
  (ext e; cases e <;> simp [$ctor:ident]))

theorem cover.bvar_eq_image (S : Set Nat) :
    cover.bvar (rT := rT) S = Exp.bvar '' S := by solve_cover_eq_image cover.bvar

theorem cover.fvar_eq_image (S : Set Var) :
    cover.fvar (rT := rT) S = Exp.fvar '' S := by solve_cover_eq_image cover.fvar

theorem cover.lit_eq_image (S : Set (BaseLit rT)) :
    cover.lit (rT := rT) S = Exp.lit '' S := by solve_cover_eq_image cover.lit

theorem cover.lam_univ_eq_range :
    cover.lam (rT := rT) Set.univ = .range (Exp.lam : Exp rT → Exp rT) := by
  solve_cover_eq_image cover.lam

theorem cover.fix_univ_eq_range :
    cover.fix (rT := rT) Set.univ = .range (Exp.fix : Exp rT → Exp rT) := by
  solve_cover_eq_image cover.fix

theorem cover.app_univ_eq_range :
    cover.app (rT := rT) Set.univ = .range (Function.uncurry Exp.app) := by
  solve_cover_eq_image cover.app

theorem cover.unop_univ_eq_range :
    cover.unop (rT := rT) Set.univ = .range (Function.uncurry Exp.unop) := by
  solve_cover_eq_image cover.unop

theorem cover.binop_univ_eq_range :
    cover.binop (rT := rT) Set.univ
      = .range (fun (p : BinOp × Exp rT × Exp rT) => Exp.binop p.1 p.2.1 p.2.2) := by
  solve_cover_eq_image cover.binop

theorem cover.cond_univ_eq_range :
    cover.cond (rT := rT) Set.univ
      = .range (fun (p : Exp rT × Exp rT × Exp rT) => Exp.cond p.1 p.2.1 p.2.2) := by
  solve_cover_eq_image cover.cond

theorem cover.pair_univ_eq_range :
    cover.pair (rT := rT) Set.univ = .range (Function.uncurry Exp.pair) := by
  solve_cover_eq_image cover.pair

theorem cover.fst_univ_eq_range :
    cover.fst (rT := rT) Set.univ = .range (Exp.fst : Exp rT → Exp rT) := by
  solve_cover_eq_image cover.fst

theorem cover.snd_univ_eq_range :
    cover.snd (rT := rT) Set.univ = .range (Exp.snd : Exp rT → Exp rT) := by
  solve_cover_eq_image cover.snd

theorem cover.inl_univ_eq_range :
    cover.inl (rT := rT) Set.univ = .range (Exp.inl : Exp rT → Exp rT) := by
  solve_cover_eq_image cover.inl

theorem cover.inr_univ_eq_range :
    cover.inr (rT := rT) Set.univ = .range (Exp.inr : Exp rT → Exp rT) := by
  solve_cover_eq_image cover.inr

theorem cover.case_univ_eq_range :
    cover.case (rT := rT) Set.univ
      = .range (fun (p : Exp rT × Exp rT × Exp rT) => Exp.case p.1 p.2.1 p.2.2) := by
  solve_cover_eq_image cover.case

theorem cover.alloc_univ_eq_range :
    cover.alloc (rT := rT) Set.univ = .range (Exp.alloc : Exp rT → Exp rT) := by
  solve_cover_eq_image cover.alloc

theorem cover.load_univ_eq_range :
    cover.load (rT := rT) Set.univ = .range (Exp.load : Exp rT → Exp rT) := by
  solve_cover_eq_image cover.load

theorem cover.store_univ_eq_range :
    cover.store (rT := rT) Set.univ = .range (Function.uncurry Exp.store) := by
  solve_cover_eq_image cover.store

theorem cover.tape_univ_eq_range :
    cover.tape (rT := rT) Set.univ = .range (Exp.tape : Exp rT → Exp rT) := by
  solve_cover_eq_image cover.tape

theorem cover.rand_univ_eq_range :
    cover.rand (rT := rT) Set.univ = .range (Function.uncurry Exp.rand) := by
  solve_cover_eq_image cover.rand

theorem cover.fail_eq_image (S : Set Unit) :
    cover.fail (rT := rT) S = (fun _ : Unit => (Exp.fail : Exp rT)) '' S := by
  solve_cover_eq_image cover.fail

theorem cover.scrut_univ_eq_range :
    cover.scrut (rT := rT) Set.univ = .range (Function.uncurry Exp.scrut) := by
  solve_cover_eq_image cover.scrut

/-! ### Measurable constructors. -/

@[fun_prop]
theorem bvar.ι.measurable {rT : Type _} [MeasurableSpace rT] :
    Measurable (Exp.bvar.ι (rT := rT)) := Measurable.of_discrete

@[fun_prop]
theorem fvar.ι.measurable {rT : Type _} [MeasurableSpace rT] :
    Measurable (Exp.fvar.ι (rT := rT)) := Measurable.of_discrete

@[fun_prop]
theorem fail.ι.measurable {rT : Type _} [MeasurableSpace rT] :
    Measurable (Exp.fail.ι (rT := rT)) := Measurable.of_discrete

@[fun_prop]
theorem lit.ι.measurable {rT : Type _} [MeasurableSpace rT] :
    Measurable (Exp.lit.ι (rT := rT)) := by
  apply measurable_generateFrom
  rintro G ⟨c, hc, rfl⟩
  cases hc with
  | @lit S hS =>
    suffices h : Exp.lit.ι ⁻¹' Cylinder.flatten (.lit S) = S by rw [h]; exact hS
    ext b; simp
  | _ => convert MeasurableSet.empty; ext b; simp

@[fun_prop]
theorem lam.ι.measurable [MeasurableSpace rT] :
    Measurable (Exp.lam.ι (rT := rT)) := by
  apply measurable_generateFrom
  rintro G ⟨c, hc, rfl⟩
  cases hc with
  | @lam c h =>
    suffices heq : Exp.lam.ι ⁻¹' Cylinder.flatten (.lam c) = Cylinder.flatten c by
      rw [heq]; exact flatten_measurable h
    ext e; simp
  | _ => convert MeasurableSet.empty; ext e; simp

@[fun_prop]
theorem fix.ι.measurable [MeasurableSpace rT] :
    Measurable (Exp.fix.ι (rT := rT)) := by
  apply measurable_generateFrom
  rintro G ⟨c, hc, rfl⟩
  cases hc with
  | @fix c h =>
    suffices heq : Exp.fix.ι ⁻¹' Cylinder.flatten (.fix c) = Cylinder.flatten c by
      rw [heq]; exact flatten_measurable h
    ext e; simp
  | _ => convert MeasurableSet.empty; ext e; simp

@[fun_prop]
theorem app.ι.measurable [MeasurableSpace rT] :
    Measurable (Exp.app.ι (rT := rT)) := by
  apply measurable_generateFrom
  rintro G ⟨c, hc, rfl⟩
  cases hc with
  | @app c₁ c₂ h₁ h₂ =>
    suffices h : Exp.app.ι ⁻¹' Cylinder.flatten (.app c₁ c₂)
                = Cylinder.flatten c₁ ×ˢ Cylinder.flatten c₂ by rw [h]; measurability
    ext ⟨_, _⟩; simp
  | _ => convert MeasurableSet.empty; ext ⟨_, _⟩; simp

@[fun_prop]
theorem fst.ι.measurable [MeasurableSpace rT] :
    Measurable (Exp.fst.ι (rT := rT)) := by
  apply measurable_generateFrom
  rintro G ⟨c, hc, rfl⟩
  cases hc with
  | @fst c h =>
    suffices heq : Exp.fst.ι ⁻¹' Cylinder.flatten (.fst c) = Cylinder.flatten c by
      rw [heq]; exact flatten_measurable h
    ext e; simp
  | _ => convert MeasurableSet.empty; ext e; simp

@[fun_prop]
theorem snd.ι.measurable [MeasurableSpace rT] :
    Measurable (Exp.snd.ι (rT := rT)) := by
  apply measurable_generateFrom
  rintro G ⟨c, hc, rfl⟩
  cases hc with
  | @snd c h =>
    suffices heq : Exp.snd.ι ⁻¹' Cylinder.flatten (.snd c) = Cylinder.flatten c by
      rw [heq]; exact flatten_measurable h
    ext e; simp
  | _ => convert MeasurableSet.empty; ext e; simp

@[fun_prop]
theorem inl.ι.measurable [MeasurableSpace rT] :
    Measurable (Exp.inl.ι (rT := rT)) := by
  apply measurable_generateFrom
  rintro G ⟨c, hc, rfl⟩
  cases hc with
  | @inl c h =>
    suffices heq : Exp.inl.ι ⁻¹' Cylinder.flatten (.inl c) = Cylinder.flatten c by
      rw [heq]; exact flatten_measurable h
    ext e; simp
  | _ => convert MeasurableSet.empty; ext e; simp

@[fun_prop]
theorem inr.ι.measurable [MeasurableSpace rT] :
    Measurable (Exp.inr.ι (rT := rT)) := by
  apply measurable_generateFrom
  rintro G ⟨c, hc, rfl⟩
  cases hc with
  | @inr c h =>
    suffices heq : Exp.inr.ι ⁻¹' Cylinder.flatten (.inr c) = Cylinder.flatten c by
      rw [heq]; exact flatten_measurable h
    ext e; simp
  | _ => convert MeasurableSet.empty; ext e; simp

@[fun_prop]
theorem alloc.ι.measurable [MeasurableSpace rT] :
    Measurable (Exp.alloc.ι (rT := rT)) := by
  apply measurable_generateFrom
  rintro G ⟨c, hc, rfl⟩
  cases hc with
  | @alloc c h =>
    suffices heq : Exp.alloc.ι ⁻¹' Cylinder.flatten (.alloc c) = Cylinder.flatten c by
      rw [heq]; exact flatten_measurable h
    ext e; simp
  | _ => convert MeasurableSet.empty; ext e; simp

@[fun_prop]
theorem load.ι.measurable [MeasurableSpace rT] :
    Measurable (Exp.load.ι (rT := rT)) := by
  apply measurable_generateFrom
  rintro G ⟨c, hc, rfl⟩
  cases hc with
  | @load c h =>
    suffices heq : Exp.load.ι ⁻¹' Cylinder.flatten (.load c) = Cylinder.flatten c by
      rw [heq]; exact flatten_measurable h
    ext e; simp
  | _ => convert MeasurableSet.empty; ext e; simp

@[fun_prop]
theorem tape.ι.measurable [MeasurableSpace rT] :
    Measurable (Exp.tape.ι (rT := rT)) := by
  apply measurable_generateFrom
  rintro G ⟨c, hc, rfl⟩
  cases hc with
  | @tape c h =>
    suffices heq : Exp.tape.ι ⁻¹' Cylinder.flatten (.tape c) = Cylinder.flatten c by
      rw [heq]; exact flatten_measurable h
    ext e; simp
  | _ => convert MeasurableSet.empty; ext e; simp

@[fun_prop]
theorem pair.ι.measurable [MeasurableSpace rT] :
    Measurable (Exp.pair.ι (rT := rT)) := by
  apply measurable_generateFrom
  rintro G ⟨c, hc, rfl⟩
  cases hc with
  | @pair c₁ c₂ h₁ h₂ =>
    suffices h : Exp.pair.ι ⁻¹' Cylinder.flatten (.pair c₁ c₂)
                = Cylinder.flatten c₁ ×ˢ Cylinder.flatten c₂ by rw [h]; measurability
    ext ⟨_, _⟩; simp
  | _ => convert MeasurableSet.empty; ext ⟨_, _⟩; simp

@[fun_prop]
theorem store.ι.measurable [MeasurableSpace rT] :
    Measurable (Exp.store.ι (rT := rT)) := by
  apply measurable_generateFrom
  rintro G ⟨c, hc, rfl⟩
  cases hc with
  | @store c₁ c₂ h₁ h₂ =>
    suffices h : Exp.store.ι ⁻¹' Cylinder.flatten (.store c₁ c₂)
                = Cylinder.flatten c₁ ×ˢ Cylinder.flatten c₂ by rw [h]; measurability
    ext ⟨_, _⟩; simp
  | _ => convert MeasurableSet.empty; ext ⟨_, _⟩; simp

@[fun_prop]
theorem rand.ι.measurable [MeasurableSpace rT] :
    Measurable (Exp.rand.ι (rT := rT)) := by
  apply measurable_generateFrom
  rintro G ⟨c, hc, rfl⟩
  cases hc with
  | @rand c₁ c₂ h₁ h₂ =>
    suffices h : Exp.rand.ι ⁻¹' Cylinder.flatten (.rand c₁ c₂)
                = Cylinder.flatten c₁ ×ˢ Cylinder.flatten c₂ by rw [h]; measurability
    ext ⟨_, _⟩; simp
  | _ => convert MeasurableSet.empty; ext ⟨_, _⟩; simp

@[fun_prop]
theorem cond.ι.measurable [MeasurableSpace rT] :
    Measurable (Exp.cond.ι (rT := rT)) := by
  apply measurable_generateFrom
  rintro G ⟨c, hc, rfl⟩
  cases hc with
  | @cond cc ct cf hc' ht hf =>
    suffices h : Exp.cond.ι ⁻¹' Cylinder.flatten (.cond cc ct cf)
                = Cylinder.flatten cc ×ˢ Cylinder.flatten ct ×ˢ Cylinder.flatten cf by
      rw [h]; measurability
    ext ⟨_, _, _⟩; simp
  | _ => convert MeasurableSet.empty; ext ⟨_, _, _⟩; simp

@[fun_prop]
theorem case.ι.measurable [MeasurableSpace rT] :
    Measurable (Exp.case.ι (rT := rT)) := by
  apply measurable_generateFrom
  rintro G ⟨c, hc, rfl⟩
  cases hc with
  | @case cc cl cr hc' hl hr =>
    suffices h : Exp.case.ι ⁻¹' Cylinder.flatten (.case cc cl cr)
                = Cylinder.flatten cc ×ˢ Cylinder.flatten cl ×ˢ Cylinder.flatten cr by
      rw [h]; measurability
    ext ⟨_, _, _⟩; simp
  | _ => convert MeasurableSet.empty; ext ⟨_, _, _⟩; simp

@[fun_prop]
theorem unop.ι.measurable [MeasurableSpace rT] :
    Measurable (Exp.unop.ι (rT := rT)) := by
  apply measurable_generateFrom
  rintro G ⟨c, hc, rfl⟩
  cases hc with
  | @unop c u h =>
    suffices heq : Exp.unop.ι ⁻¹' Cylinder.flatten (.unop u c)
                = ({u} : Set UnOp) ×ˢ Cylinder.flatten c by rw [heq]; measurability
    ext ⟨_, _⟩; simp; tauto
  | _ => convert MeasurableSet.empty; ext ⟨_, _⟩; simp

@[fun_prop]
theorem binop.ι.measurable [MeasurableSpace rT] :
    Measurable (Exp.binop.ι (rT := rT)) := by
  apply measurable_generateFrom
  rintro G ⟨c, hc, rfl⟩
  cases hc with
  | @binop c₁ c₂ b h₁ h₂ =>
    suffices heq : Exp.binop.ι ⁻¹' Cylinder.flatten (.binop b c₁ c₂)
                = ({b} : Set BinOp) ×ˢ Cylinder.flatten c₁ ×ˢ Cylinder.flatten c₂ by
      rw [heq]; measurability
    ext ⟨_, _, _⟩; simp; tauto
  | _ => convert MeasurableSet.empty; ext ⟨_, _, _⟩; simp

@[fun_prop]
theorem scrut.ι.measurable [MeasurableSpace rT] :
    Measurable (Exp.scrut.ι (rT := rT)) := by
  apply measurable_generateFrom
  rintro G ⟨c, hc, rfl⟩
  cases hc with
  | @scrut c S h hS =>
    suffices heq : Exp.scrut.ι ⁻¹' Cylinder.flatten (.scrut c S)
                = Cylinder.flatten c ×ˢ S by rw [heq]; measurability
    ext ⟨_, _⟩; simp
  | _ => convert MeasurableSet.empty; ext ⟨_, _⟩; simp

/-! ### Measurable embeddings. -/

macro "solve_discrete_ME" eq_image:term ", " meas:term : tactic => `(tactic|
  (refine ⟨fun _ _ h => by injection h, Measurable.of_discrete, fun S _ => ?_⟩
   rw [← $eq_image S]
   exact $meas S))

theorem bvar.measurableEmbedding [MeasurableSpace rT] :
    MeasurableEmbedding (Exp.bvar : Nat → Exp rT) := by
  solve_discrete_ME cover.bvar_eq_image, cover.bvar.measurable

theorem fvar.measurableEmbedding [MeasurableSpace rT] :
    MeasurableEmbedding (Exp.fvar : Var → Exp rT) := by
  solve_discrete_ME cover.fvar_eq_image, cover.fvar.measurable

theorem fail.measurableEmbedding [MeasurableSpace rT] :
    MeasurableEmbedding (fun _ : Unit => (Exp.fail : Exp rT)) := by
  apply MeasurableEmbedding.of_measurable_inverse (g := fun _ => ())
  · exact measurable_const
  · rw [show Set.range (fun _ : Unit => (Exp.fail : Exp rT)) = cover.fail .univ from by
             rw [cover.fail_eq_image]; ext; simp]
    exact cover.fail.measurable _
  · exact measurable_const
  · intro; rfl

theorem lit.measurableEmbedding [MeasurableSpace rT] :
    MeasurableEmbedding (Exp.lit : BaseLit rT → Exp rT) :=
  ⟨fun _ _ h => by injection h, Exp.lit.ι.measurable,
    fun _ hS => flatten_measurable (.lit _ hS)⟩

theorem lam.measurableEmbedding [MeasurableSpace rT] :
    MeasurableEmbedding (Exp.lam : Exp rT → Exp rT) :=
  measurableEmbedding_of_piSystem₁
    (h_inj := Exp.lam.ι.inj) (h_meas := Exp.lam.ι.measurable)
    (h_gen := rfl) (h_pi := Cylinder.flatten_isPiSystem)
    (h_basic := by rintro _ ⟨c, hc, rfl⟩; exact flatten_measurable (.lam hc))
    (h_cov_meas := cover.lam.measurable _) (h_cov_range := cover.lam_univ_eq_range)

theorem fix.measurableEmbedding [MeasurableSpace rT] :
    MeasurableEmbedding (Exp.fix : Exp rT → Exp rT) :=
  measurableEmbedding_of_piSystem₁
    (h_inj := Exp.fix.ι.inj) (h_meas := Exp.fix.ι.measurable)
    (h_gen := rfl) (h_pi := Cylinder.flatten_isPiSystem)
    (h_basic := by rintro _ ⟨c, hc, rfl⟩; exact flatten_measurable (.fix hc))
    (h_cov_meas := cover.fix.measurable _) (h_cov_range := cover.fix_univ_eq_range)

theorem fst.measurableEmbedding [MeasurableSpace rT] :
    MeasurableEmbedding (Exp.fst : Exp rT → Exp rT) :=
  measurableEmbedding_of_piSystem₁
    (h_inj := Exp.fst.ι.inj) (h_meas := Exp.fst.ι.measurable)
    (h_gen := rfl) (h_pi := Cylinder.flatten_isPiSystem)
    (h_basic := by rintro _ ⟨c, hc, rfl⟩; exact flatten_measurable (.fst hc))
    (h_cov_meas := cover.fst.measurable _) (h_cov_range := cover.fst_univ_eq_range)

theorem snd.measurableEmbedding [MeasurableSpace rT] :
    MeasurableEmbedding (Exp.snd : Exp rT → Exp rT) :=
  measurableEmbedding_of_piSystem₁
    (h_inj := Exp.snd.ι.inj) (h_meas := Exp.snd.ι.measurable)
    (h_gen := rfl) (h_pi := Cylinder.flatten_isPiSystem)
    (h_basic := by rintro _ ⟨c, hc, rfl⟩; exact flatten_measurable (.snd hc))
    (h_cov_meas := cover.snd.measurable _) (h_cov_range := cover.snd_univ_eq_range)

theorem inl.measurableEmbedding [MeasurableSpace rT] :
    MeasurableEmbedding (Exp.inl : Exp rT → Exp rT) :=
  measurableEmbedding_of_piSystem₁
    (h_inj := Exp.inl.ι.inj) (h_meas := Exp.inl.ι.measurable)
    (h_gen := rfl) (h_pi := Cylinder.flatten_isPiSystem)
    (h_basic := by rintro _ ⟨c, hc, rfl⟩; exact flatten_measurable (.inl hc))
    (h_cov_meas := cover.inl.measurable _) (h_cov_range := cover.inl_univ_eq_range)

theorem inr.measurableEmbedding [MeasurableSpace rT] :
    MeasurableEmbedding (Exp.inr : Exp rT → Exp rT) :=
  measurableEmbedding_of_piSystem₁
    (h_inj := Exp.inr.ι.inj) (h_meas := Exp.inr.ι.measurable)
    (h_gen := rfl) (h_pi := Cylinder.flatten_isPiSystem)
    (h_basic := by rintro _ ⟨c, hc, rfl⟩; exact flatten_measurable (.inr hc))
    (h_cov_meas := cover.inr.measurable _) (h_cov_range := cover.inr_univ_eq_range)

theorem alloc.measurableEmbedding [MeasurableSpace rT] :
    MeasurableEmbedding (Exp.alloc : Exp rT → Exp rT) :=
  measurableEmbedding_of_piSystem₁
    (h_inj := Exp.alloc.ι.inj) (h_meas := Exp.alloc.ι.measurable)
    (h_gen := rfl) (h_pi := Cylinder.flatten_isPiSystem)
    (h_basic := by rintro _ ⟨c, hc, rfl⟩; exact flatten_measurable (.alloc hc))
    (h_cov_meas := cover.alloc.measurable _) (h_cov_range := cover.alloc_univ_eq_range)

theorem load.measurableEmbedding [MeasurableSpace rT] :
    MeasurableEmbedding (Exp.load : Exp rT → Exp rT) :=
  measurableEmbedding_of_piSystem₁
    (h_inj := Exp.load.ι.inj) (h_meas := Exp.load.ι.measurable)
    (h_gen := rfl) (h_pi := Cylinder.flatten_isPiSystem)
    (h_basic := by rintro _ ⟨c, hc, rfl⟩; exact flatten_measurable (.load hc))
    (h_cov_meas := cover.load.measurable _) (h_cov_range := cover.load_univ_eq_range)

theorem tape.measurableEmbedding [MeasurableSpace rT] :
    MeasurableEmbedding (Exp.tape : Exp rT → Exp rT) :=
  measurableEmbedding_of_piSystem₁
    (h_inj := Exp.tape.ι.inj) (h_meas := Exp.tape.ι.measurable)
    (h_gen := rfl) (h_pi := Cylinder.flatten_isPiSystem)
    (h_basic := by rintro _ ⟨c, hc, rfl⟩; exact flatten_measurable (.tape hc))
    (h_cov_meas := cover.tape.measurable _) (h_cov_range := cover.tape_univ_eq_range)

theorem app.measurableEmbedding [MeasurableSpace rT] :
    MeasurableEmbedding (Function.uncurry (Exp.app : Exp rT → Exp rT → Exp rT)) :=
  measurableEmbedding_of_piSystem₂
    (h_inj := Exp.app.ι.inj) (h_meas := Exp.app.ι.measurable)
    (h_gen := (generateFrom_eq_prod rfl rfl
                Cylinder.flatten_isCountablySpanning Cylinder.flatten_isCountablySpanning).symm)
    (h_pi := Cylinder.flatten_isPiSystem.prod Cylinder.flatten_isPiSystem)
    (h_basic := by rintro _ ⟨c₁, hc₁, rfl⟩ _ ⟨c₂, hc₂, rfl⟩; exact flatten_measurable (.app hc₁ hc₂))
    (h_cov_meas := cover.app.measurable _) (h_cov_range := cover.app_univ_eq_range)

theorem pair.measurableEmbedding [MeasurableSpace rT] :
    MeasurableEmbedding (Function.uncurry (Exp.pair : Exp rT → Exp rT → Exp rT)) :=
  measurableEmbedding_of_piSystem₂
    (h_inj := Exp.pair.ι.inj) (h_meas := Exp.pair.ι.measurable)
    (h_gen := (generateFrom_eq_prod rfl rfl
                Cylinder.flatten_isCountablySpanning Cylinder.flatten_isCountablySpanning).symm)
    (h_pi := Cylinder.flatten_isPiSystem.prod Cylinder.flatten_isPiSystem)
    (h_basic := by rintro _ ⟨c₁, hc₁, rfl⟩ _ ⟨c₂, hc₂, rfl⟩; exact flatten_measurable (.pair hc₁ hc₂))
    (h_cov_meas := cover.pair.measurable _) (h_cov_range := cover.pair_univ_eq_range)

theorem store.measurableEmbedding [MeasurableSpace rT] :
    MeasurableEmbedding (Function.uncurry (Exp.store : Exp rT → Exp rT → Exp rT)) :=
  measurableEmbedding_of_piSystem₂
    (h_inj := Exp.store.ι.inj) (h_meas := Exp.store.ι.measurable)
    (h_gen := (generateFrom_eq_prod rfl rfl
                Cylinder.flatten_isCountablySpanning Cylinder.flatten_isCountablySpanning).symm)
    (h_pi := Cylinder.flatten_isPiSystem.prod Cylinder.flatten_isPiSystem)
    (h_basic := by rintro _ ⟨c₁, hc₁, rfl⟩ _ ⟨c₂, hc₂, rfl⟩; exact flatten_measurable (.store hc₁ hc₂))
    (h_cov_meas := cover.store.measurable _) (h_cov_range := cover.store_univ_eq_range)

theorem rand.measurableEmbedding [MeasurableSpace rT] :
    MeasurableEmbedding (Function.uncurry (Exp.rand : Exp rT → Exp rT → Exp rT)) :=
  measurableEmbedding_of_piSystem₂
    (h_inj := Exp.rand.ι.inj) (h_meas := Exp.rand.ι.measurable)
    (h_gen := (generateFrom_eq_prod rfl rfl
                Cylinder.flatten_isCountablySpanning Cylinder.flatten_isCountablySpanning).symm)
    (h_pi := Cylinder.flatten_isPiSystem.prod Cylinder.flatten_isPiSystem)
    (h_basic := by rintro _ ⟨c₁, hc₁, rfl⟩ _ ⟨c₂, hc₂, rfl⟩; exact flatten_measurable (.rand hc₁ hc₂))
    (h_cov_meas := cover.rand.measurable _) (h_cov_range := cover.rand_univ_eq_range)

theorem cond.measurableEmbedding [MeasurableSpace rT] :
    MeasurableEmbedding (fun (p : Exp rT × Exp rT × Exp rT) => Exp.cond p.1 p.2.1 p.2.2) :=
  measurableEmbedding_of_piSystem₃
    (h_inj := Exp.cond.ι.inj) (h_meas := Exp.cond.ι.measurable)
    (h_gen := (generateFrom_eq_prod rfl
                (generateFrom_eq_prod rfl rfl
                  Cylinder.flatten_isCountablySpanning Cylinder.flatten_isCountablySpanning)
                Cylinder.flatten_isCountablySpanning
                (Cylinder.flatten_isCountablySpanning.prod Cylinder.flatten_isCountablySpanning)).symm)
    (h_pi := Cylinder.flatten_isPiSystem.prod
              (Cylinder.flatten_isPiSystem.prod Cylinder.flatten_isPiSystem))
    (h_basic := by
      rintro _ ⟨cc, hcc, rfl⟩ _ ⟨ct, hct, rfl⟩ _ ⟨cf, hcf, rfl⟩
      rw [show ((fun p : Exp rT × Exp rT × Exp rT => Exp.cond p.1 p.2.1 p.2.2)
            '' (Cylinder.flatten cc ×ˢ Cylinder.flatten ct ×ˢ Cylinder.flatten cf))
            = Cylinder.flatten (.cond cc ct cf) from by
          ext e; cases e <;> simp]
      exact flatten_measurable (.cond hcc hct hcf))
    (h_cov_meas := cover.cond.measurable _) (h_cov_range := cover.cond_univ_eq_range)

theorem case.measurableEmbedding [MeasurableSpace rT] :
    MeasurableEmbedding (fun (p : Exp rT × Exp rT × Exp rT) => Exp.case p.1 p.2.1 p.2.2) :=
  measurableEmbedding_of_piSystem₃
    (h_inj := Exp.case.ι.inj) (h_meas := Exp.case.ι.measurable)
    (h_gen := (generateFrom_eq_prod rfl
                (generateFrom_eq_prod rfl rfl
                  Cylinder.flatten_isCountablySpanning Cylinder.flatten_isCountablySpanning)
                Cylinder.flatten_isCountablySpanning
                (Cylinder.flatten_isCountablySpanning.prod Cylinder.flatten_isCountablySpanning)).symm)
    (h_pi := Cylinder.flatten_isPiSystem.prod
              (Cylinder.flatten_isPiSystem.prod Cylinder.flatten_isPiSystem))
    (h_basic := by
      rintro _ ⟨cc, hcc, rfl⟩ _ ⟨cl, hcl, rfl⟩ _ ⟨cr, hcr, rfl⟩
      rw [show ((fun p : Exp rT × Exp rT × Exp rT => Exp.case p.1 p.2.1 p.2.2)
            '' (Cylinder.flatten cc ×ˢ Cylinder.flatten cl ×ˢ Cylinder.flatten cr))
            = Cylinder.flatten (.case cc cl cr) from by
          ext e; cases e <;> simp]
      exact flatten_measurable (.case hcc hcl hcr))
    (h_cov_meas := cover.case.measurable _) (h_cov_range := cover.case_univ_eq_range)

theorem unop.measurableEmbedding [MeasurableSpace rT] :
    MeasurableEmbedding (Function.uncurry (Exp.unop : UnOp → Exp rT → Exp rT)) :=
  measurableEmbedding_of_piSystem₂
    (h_inj := Exp.unop.ι.inj) (h_meas := Exp.unop.ι.measurable)
    (h_gen := (generateFrom_eq_prod singletonsAndUniv_generateFrom rfl
                singletonsAndUniv_isCountablySpanning Cylinder.flatten_isCountablySpanning).symm)
    (h_pi := singletonsAndUniv_isPiSystem.prod Cylinder.flatten_isPiSystem)
    (h_basic := by
      rintro A hA _ ⟨c, hc, rfl⟩
      rcases hA with rfl | ⟨u, rfl⟩
      · -- A = univ
        rw [show ((Function.uncurry Exp.unop) '' (Set.univ ×ˢ Cylinder.flatten c) : Set (Exp rT))
              = ⋃ u : UnOp, Exp.unop u '' Cylinder.flatten c from by
            ext e; simp [Function.uncurry]]
        exact .iUnion fun u => flatten_measurable (.unop (u := u) hc)
      · -- A = {u}
        rw [show ((Function.uncurry Exp.unop) '' (({u} : Set UnOp) ×ˢ Cylinder.flatten c) : Set (Exp rT))
              = Cylinder.flatten (.unop u c) from by ext e; cases e <;> simp [Function.uncurry]]
        exact flatten_measurable (.unop hc))
    (h_cov_meas := cover.unop.measurable _) (h_cov_range := cover.unop_univ_eq_range)

theorem binop.measurableEmbedding [MeasurableSpace rT] :
    MeasurableEmbedding (fun (p : BinOp × Exp rT × Exp rT) => Exp.binop p.1 p.2.1 p.2.2) :=
  measurableEmbedding_of_piSystem₃
    (h_inj := Exp.binop.ι.inj) (h_meas := Exp.binop.ι.measurable)
    (h_gen := (generateFrom_eq_prod singletonsAndUniv_generateFrom
                (generateFrom_eq_prod rfl rfl
                  Cylinder.flatten_isCountablySpanning Cylinder.flatten_isCountablySpanning)
                singletonsAndUniv_isCountablySpanning
                (Cylinder.flatten_isCountablySpanning.prod Cylinder.flatten_isCountablySpanning)).symm)
    (h_pi := singletonsAndUniv_isPiSystem.prod
              (Cylinder.flatten_isPiSystem.prod Cylinder.flatten_isPiSystem))
    (h_basic := by
      rintro A hA _ ⟨c₁, hc₁, rfl⟩ _ ⟨c₂, hc₂, rfl⟩
      rcases hA with rfl | ⟨b, rfl⟩
      · rw [show ((fun p : BinOp × Exp rT × Exp rT => Exp.binop p.1 p.2.1 p.2.2)
              '' (Set.univ ×ˢ Cylinder.flatten c₁ ×ˢ Cylinder.flatten c₂))
              = ⋃ b : BinOp, Cylinder.flatten (.binop b c₁ c₂) from by
            ext e; cases e <;> simp <;> tauto]
        exact .iUnion fun b => flatten_measurable (.binop hc₁ hc₂)
      · rw [show ((fun p : BinOp × Exp rT × Exp rT => Exp.binop p.1 p.2.1 p.2.2)
              '' (({b} : Set BinOp) ×ˢ Cylinder.flatten c₁ ×ˢ Cylinder.flatten c₂))
              = Cylinder.flatten (.binop b c₁ c₂) from by
            ext e; cases e <;> simp <;> tauto]
        exact flatten_measurable (.binop hc₁ hc₂))
    (h_cov_meas := cover.binop.measurable _) (h_cov_range := cover.binop_univ_eq_range)

theorem scrut.measurableEmbedding [MeasurableSpace rT] :
    MeasurableEmbedding (Function.uncurry (Exp.scrut : Exp rT → Pat rT → Exp rT)) :=
  measurableEmbedding_of_piSystem₂
    (h_inj := Exp.scrut.ι.inj) (h_meas := Exp.scrut.ι.measurable)
    (h_gen := (generateFrom_eq_prod rfl MeasurableSpace.generateFrom_measurableSet
                Cylinder.flatten_isCountablySpanning isCountablySpanning_measurableSet).symm)
    (h_pi := Cylinder.flatten_isPiSystem.prod
              (fun S (hS : MeasurableSet S) T (hT : MeasurableSet T) _ => hS.inter hT))
    (h_basic := by
      rintro _ ⟨c, hc, rfl⟩ S (hS : MeasurableSet S)
      rw [show ((Function.uncurry Exp.scrut) '' (Cylinder.flatten c ×ˢ S) : Set (Exp rT))
            = Cylinder.flatten (.scrut c S) from by ext e; cases e <;> simp [Function.uncurry]]
      exact flatten_measurable (.scrut _ hc hS))
    (h_cov_meas := cover.scrut.measurable _) (h_cov_range := cover.scrut_univ_eq_range)

theorem casesOn_preimage_decomp
    {rT : Type _} {α : Type _} (S : Set α)
    (f_bvar : Nat → α) (f_fvar : Var → α) (f_lit : BaseLit rT → α)
    (f_lam : Exp rT → α) (f_fix : Exp rT → α)
    (f_app : Exp rT × Exp rT → α)
    (f_unop : UnOp × Exp rT → α) (f_binop : BinOp × Exp rT × Exp rT → α)
    (f_cond : Exp rT × Exp rT × Exp rT → α)
    (f_pair : Exp rT × Exp rT → α)
    (f_fst : Exp rT → α) (f_snd : Exp rT → α)
    (f_inl : Exp rT → α) (f_inr : Exp rT → α)
    (f_case : Exp rT × Exp rT × Exp rT → α)
    (f_alloc : Exp rT → α) (f_load : Exp rT → α) (f_store : Exp rT × Exp rT → α)
    (f_tape : Exp rT → α) (f_rand : Exp rT × Exp rT → α)
    (f_fail : Unit → α) (f_scrut : Exp rT × Pat rT → α) :
    (fun e : Exp rT => Exp.casesOn (motive := fun _ => α) e
        f_bvar f_fvar f_lit f_lam f_fix
        (fun e1 e2 => f_app (e1, e2))
        (fun u e => f_unop (u, e))
        (fun b e1 e2 => f_binop (b, e1, e2))
        (fun ec et ef => f_cond (ec, et, ef))
        (fun e1 e2 => f_pair (e1, e2))
        f_fst f_snd f_inl f_inr
        (fun ec el er => f_case (ec, el, er))
        f_alloc f_load
        (fun e1 e2 => f_store (e1, e2))
        f_tape
        (fun e1 e2 => f_rand (e1, e2))
        (f_fail ())
        (fun e p => f_scrut (e, p))) ⁻¹' S
      = (Exp.bvar.ι  '' (f_bvar  ⁻¹' S))
      ∪ (Exp.fvar.ι  '' (f_fvar  ⁻¹' S))
      ∪ (Exp.lit.ι   '' (f_lit   ⁻¹' S))
      ∪ (Exp.lam.ι   '' (f_lam   ⁻¹' S))
      ∪ (Exp.fix.ι   '' (f_fix   ⁻¹' S))
      ∪ (Exp.app.ι   '' (f_app   ⁻¹' S))
      ∪ (Exp.unop.ι  '' (f_unop  ⁻¹' S))
      ∪ (Exp.binop.ι '' (f_binop ⁻¹' S))
      ∪ (Exp.cond.ι  '' (f_cond  ⁻¹' S))
      ∪ (Exp.pair.ι  '' (f_pair  ⁻¹' S))
      ∪ (Exp.fst.ι   '' (f_fst   ⁻¹' S))
      ∪ (Exp.snd.ι   '' (f_snd   ⁻¹' S))
      ∪ (Exp.inl.ι   '' (f_inl   ⁻¹' S))
      ∪ (Exp.inr.ι   '' (f_inr   ⁻¹' S))
      ∪ (Exp.case.ι  '' (f_case  ⁻¹' S))
      ∪ (Exp.alloc.ι '' (f_alloc ⁻¹' S))
      ∪ (Exp.load.ι  '' (f_load  ⁻¹' S))
      ∪ (Exp.store.ι '' (f_store ⁻¹' S))
      ∪ (Exp.tape.ι  '' (f_tape  ⁻¹' S))
      ∪ (Exp.rand.ι  '' (f_rand  ⁻¹' S))
      ∪ (Exp.fail.ι  '' (f_fail  ⁻¹' S))
      ∪ (Exp.scrut.ι '' (f_scrut ⁻¹' S)) := by
  ext e; cases e <;> aesop

@[fun_prop]
theorem measurable_rec
    {rT : Type _} [MeasurableSpace rT]
    {α : Type _} [MeasurableSpace α]
    (f_bvar : Nat → α) (f_fvar : Var → α) (f_lit : BaseLit rT → α)
    (f_lam : Exp rT → α) (f_fix : Exp rT → α)
    (f_app : Exp rT × Exp rT → α)
    (f_unop : UnOp × Exp rT → α) (f_binop : BinOp × Exp rT × Exp rT → α)
    (f_cond : Exp rT × Exp rT × Exp rT → α)
    (f_pair : Exp rT × Exp rT → α)
    (f_fst : Exp rT → α) (f_snd : Exp rT → α)
    (f_inl : Exp rT → α) (f_inr : Exp rT → α)
    (f_case : Exp rT × Exp rT × Exp rT → α)
    (f_alloc : Exp rT → α) (f_load : Exp rT → α) (f_store : Exp rT × Exp rT → α)
    (f_tape : Exp rT → α) (f_rand : Exp rT × Exp rT → α)
    (f_fail : Unit → α) (f_scrut : Exp rT × Pat rT → α)
    (h_lit : Measurable f_lit)
    (h_lam : Measurable f_lam) (h_fix : Measurable f_fix)
    (h_app : Measurable f_app) (h_unop : Measurable f_unop) (h_binop : Measurable f_binop)
    (h_cond : Measurable f_cond)
    (h_pair : Measurable f_pair) (h_fst : Measurable f_fst) (h_snd : Measurable f_snd)
    (h_inl : Measurable f_inl) (h_inr : Measurable f_inr)
    (h_case : Measurable f_case)
    (h_alloc : Measurable f_alloc) (h_load : Measurable f_load) (h_store : Measurable f_store)
    (h_tape : Measurable f_tape) (h_rand : Measurable f_rand)
    (h_scrut : Measurable f_scrut) :
    Measurable (fun e : Exp rT =>
      Exp.casesOn (motive := fun _ => α) e
        f_bvar f_fvar f_lit f_lam f_fix
        (fun e1 e2 => f_app (e1, e2))
        (fun u e => f_unop (u, e))
        (fun b e1 e2 => f_binop (b, e1, e2))
        (fun ec et ef => f_cond (ec, et, ef))
        (fun e1 e2 => f_pair (e1, e2))
        f_fst f_snd f_inl f_inr
        (fun ec el er => f_case (ec, el, er))
        f_alloc f_load
        (fun e1 e2 => f_store (e1, e2))
        f_tape
        (fun e1 e2 => f_rand (e1, e2))
        (f_fail ())
        (fun e p => f_scrut (e, p))) := by
  intro S hS
  rw [Exp.casesOn_preimage_decomp]
  iterate 21 refine .union ?_ ?_
  · exact bvar.measurableEmbedding.measurableSet_image'  .of_discrete
  · exact fvar.measurableEmbedding.measurableSet_image'  .of_discrete
  · exact lit.measurableEmbedding.measurableSet_image'   (h_lit hS)
  · exact lam.measurableEmbedding.measurableSet_image'   (h_lam hS)
  · exact fix.measurableEmbedding.measurableSet_image'   (h_fix hS)
  · exact app.measurableEmbedding.measurableSet_image'   (h_app hS)
  · exact unop.measurableEmbedding.measurableSet_image'  (h_unop hS)
  · exact binop.measurableEmbedding.measurableSet_image' (h_binop hS)
  · exact cond.measurableEmbedding.measurableSet_image'  (h_cond hS)
  · exact pair.measurableEmbedding.measurableSet_image'  (h_pair hS)
  · exact fst.measurableEmbedding.measurableSet_image'   (h_fst hS)
  · exact snd.measurableEmbedding.measurableSet_image'   (h_snd hS)
  · exact inl.measurableEmbedding.measurableSet_image'   (h_inl hS)
  · exact inr.measurableEmbedding.measurableSet_image'   (h_inr hS)
  · exact case.measurableEmbedding.measurableSet_image'  (h_case hS)
  · exact alloc.measurableEmbedding.measurableSet_image' (h_alloc hS)
  · exact load.measurableEmbedding.measurableSet_image'  (h_load hS)
  · exact store.measurableEmbedding.measurableSet_image' (h_store hS)
  · exact tape.measurableEmbedding.measurableSet_image'  (h_tape hS)
  · exact rand.measurableEmbedding.measurableSet_image'  (h_rand hS)
  · exact fail.measurableEmbedding.measurableSet_image'  .of_discrete
  · exact scrut.measurableEmbedding.measurableSet_image' (h_scrut hS)

end ProbLang.Exp

end Exp -- section

section Val

/-# Measure space on values.

`Val α = (e : Exp α) × IsVal e` is a Sigma type whose witness `IsVal e` is a subsingleton
(see `ProbLang.IsVal.subsingleton`), so the witness carries no information. We give `IsVal`
the discrete (top) σ-algebra, induce the `Sigma` σ-algebra on `Val`, and check that the
constructors and `Exp.toVal?` behave measurably. The σ-algebra ends up being the pullback
through `.fst : Val α → Exp α`. -/

namespace ProbLang

instance instMeasurableSpaceIsVal {α : Type _} {e : Exp α} : MeasurableSpace (IsVal e) := ⊤

instance instMeasurableSpaceVal {α : Type _} [MeasurableSpace α] : MeasurableSpace (Val α) :=
  Sigma.instMeasurableSpace

namespace Val

end Val
end ProbLang

end Val -- section

section EctxItem

/-# Measure space on evaluation-context items.

`EctxItem` has 22 constructors and *no recursion* — each constructor's arguments are
syntax leaves (`UnOp`, `BinOp`) or data leaves (`Val α`, `Exp α`, `Pat α`). This is the
simplest instance of the template: cylinder = `EctxItem`-with-data-leaves-replaced-by-`Set`,
and the cylinder σ-algebra is generated from those flattens. -/

namespace ProbLang.EctxItem

macro "solve_ι_inj" : tactic => `(tactic|
  (intro a b h;
   first
   | (cases h; rfl)
   | (obtain ⟨_, _⟩ := a; obtain ⟨_, _⟩ := b; cases h; rfl)
   | (obtain ⟨_, _, _⟩ := a; obtain ⟨_, _, _⟩ := b; cases h; rfl)))

theorem appL.ι.inj   {α : Type _} : Function.Injective (@EctxItem.appL.ι   α) := by solve_ι_inj
theorem appR.ι.inj   {α : Type _} : Function.Injective (@EctxItem.appR.ι   α) := by solve_ι_inj
theorem unop.ι.inj   {α : Type _} : Function.Injective (@EctxItem.unop.ι   α) := by solve_ι_inj
theorem binopL.ι.inj {α : Type _} : Function.Injective (@EctxItem.binopL.ι α) := by solve_ι_inj
theorem binopR.ι.inj {α : Type _} : Function.Injective (@EctxItem.binopR.ι α) := by solve_ι_inj
theorem condC.ι.inj  {α : Type _} : Function.Injective (@EctxItem.condC.ι  α) := by solve_ι_inj
theorem pairL.ι.inj  {α : Type _} : Function.Injective (@EctxItem.pairL.ι  α) := by solve_ι_inj
theorem pairR.ι.inj  {α : Type _} : Function.Injective (@EctxItem.pairR.ι  α) := by solve_ι_inj
theorem fst.ι.inj    {α : Type _} : Function.Injective (@EctxItem.fst.ι    α) := by solve_ι_inj
theorem snd.ι.inj    {α : Type _} : Function.Injective (@EctxItem.snd.ι    α) := by solve_ι_inj
theorem inl.ι.inj    {α : Type _} : Function.Injective (@EctxItem.inl.ι    α) := by solve_ι_inj
theorem inr.ι.inj    {α : Type _} : Function.Injective (@EctxItem.inr.ι    α) := by solve_ι_inj
theorem case.ι.inj   {α : Type _} : Function.Injective (@EctxItem.case.ι   α) := by solve_ι_inj
theorem alloc.ι.inj  {α : Type _} : Function.Injective (@EctxItem.alloc.ι  α) := by solve_ι_inj
theorem load.ι.inj   {α : Type _} : Function.Injective (@EctxItem.load.ι   α) := by solve_ι_inj
theorem storeL.ι.inj {α : Type _} : Function.Injective (@EctxItem.storeL.ι α) := by solve_ι_inj
theorem storeR.ι.inj {α : Type _} : Function.Injective (@EctxItem.storeR.ι α) := by solve_ι_inj
theorem tape.ι.inj   {α : Type _} : Function.Injective (@EctxItem.tape.ι   α) := by solve_ι_inj
theorem randL.ι.inj  {α : Type _} : Function.Injective (@EctxItem.randL.ι  α) := by solve_ι_inj
theorem randR.ι.inj  {α : Type _} : Function.Injective (@EctxItem.randR.ι  α) := by solve_ι_inj
theorem scrut.ι.inj  {α : Type _} : Function.Injective (@EctxItem.scrut.ι  α) := by solve_ι_inj

/-- A cylinder is an `EctxItem`-shaped value with each data-leaf payload replaced by a
measurable set of that type. Syntax-leaf args (`UnOp`, `BinOp`) are kept as-is. -/
inductive Cylinder (α : Type _)
  | appL   (S : Set (Val α))
  | appR   (S : Set (Exp α))
  | unop   (u : UnOp)
  | binopL (op : BinOp) (S : Set (Val α))
  | binopR (op : BinOp) (S : Set (Exp α))
  | condC  (S1 S2 : Set (Exp α))
  | pairL  (S : Set (Val α))
  | pairR  (S : Set (Exp α))
  | fst
  | snd
  | inl
  | inr
  | case   (S1 S2 : Set (Exp α))
  | alloc
  | load
  | storeL (S : Set (Val α))
  | storeR (S : Set (Exp α))
  | tape
  | randL  (S : Set (Val α))
  | randR  (S : Set (Exp α))
  | scrut  (S : Set (Pat α))

/-- An item with all data-leaf payloads forgotten. Syntax-leaf args are kept. -/
inductive Shape
  | appL
  | appR
  | unop (u : UnOp)
  | binopL (op : BinOp)
  | binopR (op : BinOp)
  | condC
  | pairL
  | pairR
  | fst
  | snd
  | inl
  | inr
  | case
  | alloc
  | load
  | storeL
  | storeR
  | tape
  | randL
  | randR
  | scrut
  deriving Countable

/-- Interpret a cylinder as the set of `EctxItem α` it describes. -/
@[simp] def Cylinder.flatten {α : Type _} : Cylinder α → Set (EctxItem α)
  | .appL S         => EctxItem.appL '' S
  | .appR S         => EctxItem.appR '' S
  | .unop u         => {EctxItem.unop u}
  | .binopL op S    => EctxItem.binopL op '' S
  | .binopR op S    => EctxItem.binopR op '' S
  | .condC S1 S2    => (fun p => EctxItem.condC p.1 p.2) '' (S1 ×ˢ S2)
  | .pairL S        => EctxItem.pairL '' S
  | .pairR S        => EctxItem.pairR '' S
  | .fst            => {EctxItem.fst}
  | .snd            => {EctxItem.snd}
  | .inl            => {EctxItem.inl}
  | .inr            => {EctxItem.inr}
  | .case S1 S2     => (fun p => EctxItem.case p.1 p.2) '' (S1 ×ˢ S2)
  | .alloc          => {EctxItem.alloc}
  | .load           => {EctxItem.load}
  | .storeL S       => EctxItem.storeL '' S
  | .storeR S       => EctxItem.storeR '' S
  | .tape           => {EctxItem.tape}
  | .randL S        => EctxItem.randL '' S
  | .randR S        => EctxItem.randR '' S
  | .scrut S        => EctxItem.scrut '' S

/-- A cylinder has measurable leaves if every data-leaf set is measurable. -/
inductive Cylinder.HasMeasurableLeaves {α : Type _} [MeasurableSpace α] :
    Cylinder α → Prop where
  | appL S   : MeasurableSet S → HasMeasurableLeaves (.appL S)
  | appR S   : MeasurableSet S → HasMeasurableLeaves (.appR S)
  | unop     : HasMeasurableLeaves (.unop u)
  | binopL S : MeasurableSet S → HasMeasurableLeaves (.binopL op S)
  | binopR S : MeasurableSet S → HasMeasurableLeaves (.binopR op S)
  | condC S1 S2 : MeasurableSet S1 → MeasurableSet S2 → HasMeasurableLeaves (.condC S1 S2)
  | pairL S  : MeasurableSet S → HasMeasurableLeaves (.pairL S)
  | pairR S  : MeasurableSet S → HasMeasurableLeaves (.pairR S)
  | fst      : HasMeasurableLeaves .fst
  | snd      : HasMeasurableLeaves .snd
  | inl      : HasMeasurableLeaves .inl
  | inr      : HasMeasurableLeaves .inr
  | case S1 S2 : MeasurableSet S1 → MeasurableSet S2 → HasMeasurableLeaves (.case S1 S2)
  | alloc    : HasMeasurableLeaves .alloc
  | load     : HasMeasurableLeaves .load
  | storeL S : MeasurableSet S → HasMeasurableLeaves (.storeL S)
  | storeR S : MeasurableSet S → HasMeasurableLeaves (.storeR S)
  | tape     : HasMeasurableLeaves .tape
  | randL S  : MeasurableSet S → HasMeasurableLeaves (.randL S)
  | randR S  : MeasurableSet S → HasMeasurableLeaves (.randR S)
  | scrut S  : MeasurableSet S → HasMeasurableLeaves (.scrut S)

instance instMeasurableSpaceEctxItem [MeasurableSpace α] : MeasurableSpace (EctxItem α) :=
  .generateFrom <| Cylinder.flatten '' { c : Cylinder α | c.HasMeasurableLeaves }

@[simp] def shape : EctxItem α → Shape
  | .appL _       => .appL
  | .appR _       => .appR
  | .unop u       => .unop u
  | .binopL op _  => .binopL op
  | .binopR op _  => .binopR op
  | .condC _ _    => .condC
  | .pairL _      => .pairL
  | .pairR _      => .pairR
  | .fst          => .fst
  | .snd          => .snd
  | .inl          => .inl
  | .inr          => .inr
  | .case _ _     => .case
  | .alloc        => .alloc
  | .load         => .load
  | .storeL _     => .storeL
  | .storeR _     => .storeR
  | .tape         => .tape
  | .randL _      => .randL
  | .randR _      => .randR
  | .scrut _      => .scrut

/-- Shape of a cylinder (forgets data leaves). -/
@[simp] def Cylinder.shape {α : Type _} : Cylinder α → Shape
  | .appL _       => .appL
  | .appR _       => .appR
  | .unop u       => .unop u
  | .binopL op _  => .binopL op
  | .binopR op _  => .binopR op
  | .condC _ _    => .condC
  | .pairL _      => .pairL
  | .pairR _      => .pairR
  | .fst          => .fst
  | .snd          => .snd
  | .inl          => .inl
  | .inr          => .inr
  | .case _ _     => .case
  | .alloc        => .alloc
  | .load         => .load
  | .storeL _     => .storeL
  | .storeR _     => .storeR
  | .tape         => .tape
  | .randL _      => .randL
  | .randR _      => .randR
  | .scrut _      => .scrut

/-- The "universe cylinder" for a given shape: `univ` at every data leaf, same skeleton. -/
@[simp] def Shape.cylinder {α : Type _} : Shape → Cylinder α
  | .appL         => .appL Set.univ
  | .appR         => .appR Set.univ
  | .unop u       => .unop u
  | .binopL op    => .binopL op Set.univ
  | .binopR op    => .binopR op Set.univ
  | .condC        => .condC Set.univ Set.univ
  | .pairL        => .pairL Set.univ
  | .pairR        => .pairR Set.univ
  | .fst          => .fst
  | .snd          => .snd
  | .inl          => .inl
  | .inr          => .inr
  | .case         => .case Set.univ Set.univ
  | .alloc        => .alloc
  | .load         => .load
  | .storeL       => .storeL Set.univ
  | .storeR       => .storeR Set.univ
  | .tape         => .tape
  | .randL        => .randL Set.univ
  | .randR        => .randR Set.univ
  | .scrut        => .scrut Set.univ

/-! ### Cylinder intersection. -/

/-- Partial intersection of cylinders. -/
def Cylinder.inter? {α : Type _} : Cylinder α → Cylinder α → Option (Cylinder α)
  | .appL S, .appL S' => some (.appL (S ∩ S'))
  | .appR S, .appR S' => some (.appR (S ∩ S'))
  | .unop u, .unop u' => if u = u' then some (.unop u) else none
  | .binopL op S, .binopL op' S' =>
      if op = op' then some (.binopL op (S ∩ S')) else none
  | .binopR op S, .binopR op' S' =>
      if op = op' then some (.binopR op (S ∩ S')) else none
  | .condC S1 S2, .condC S1' S2' => some (.condC (S1 ∩ S1') (S2 ∩ S2'))
  | .pairL S, .pairL S' => some (.pairL (S ∩ S'))
  | .pairR S, .pairR S' => some (.pairR (S ∩ S'))
  | .fst, .fst => some .fst
  | .snd, .snd => some .snd
  | .inl, .inl => some .inl
  | .inr, .inr => some .inr
  | .case S1 S2, .case S1' S2' => some (.case (S1 ∩ S1') (S2 ∩ S2'))
  | .alloc, .alloc => some .alloc
  | .load, .load => some .load
  | .storeL S, .storeL S' => some (.storeL (S ∩ S'))
  | .storeR S, .storeR S' => some (.storeR (S ∩ S'))
  | .tape, .tape => some .tape
  | .randL S, .randL S' => some (.randL (S ∩ S'))
  | .randR S, .randR S' => some (.randR (S ∩ S'))
  | .scrut S, .scrut S' => some (.scrut (S ∩ S'))
  | _, _ => none

/-- Every element of a cylinder's flatten has that cylinder's shape. -/
theorem Cylinder.shape_of_mem_flatten {α : Type _} {c : Cylinder α} {K : EctxItem α}
    (h : K ∈ Cylinder.flatten c) : EctxItem.shape K = Cylinder.shape c := by
  cases c <;> simp_all <;>
    (first
      | (obtain ⟨_, _, rfl⟩ := h; rfl)
      | (obtain ⟨_, _, _, _, rfl⟩ := h; rfl)
      | rfl)

/-- Flattens of cylinders with different shapes are disjoint. -/
theorem Cylinder.flatten_disjoint_of_shape_ne {α : Type _} {c₁ c₂ : Cylinder α}
    (h : Cylinder.shape c₁ ≠ Cylinder.shape c₂) : Cylinder.flatten c₁ ∩ Cylinder.flatten c₂ = ∅ := by
  ext K
  simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false, not_and]
  intro h₁ h₂
  exact h ((Cylinder.shape_of_mem_flatten h₁).symm.trans (Cylinder.shape_of_mem_flatten h₂))

/-- The cylinder flatten of the intersection equals the intersection of the flattens. -/
theorem Cylinder.flatten_inter {α : Type _} (c₁ c₂ : Cylinder α) :
    Cylinder.flatten c₁ ∩ Cylinder.flatten c₂
      = (Cylinder.inter? c₁ c₂).elim ∅ Cylinder.flatten := sorry

theorem Cylinder.flatten_inter_some {α : Type _} {c₁ c₂ c : Cylinder α}
    (h : Cylinder.inter? c₁ c₂ = some c) :
    Cylinder.flatten c = Cylinder.flatten c₁ ∩ Cylinder.flatten c₂ := by
  rw [Cylinder.flatten_inter, h]; rfl

theorem Cylinder.hasMeasurableLeaves_inter [MeasurableSpace α]
    {c₁ c₂ c : Cylinder α}
    (h₁ : c₁.HasMeasurableLeaves) (h₂ : c₂.HasMeasurableLeaves)
    (h : Cylinder.inter? c₁ c₂ = some c) : c.HasMeasurableLeaves := sorry

/-! ### Per-constructor covers. -/

def cover.appL (S : Set (Val α)) : Set (EctxItem α) := Cylinder.flatten (.appL S)
def cover.appR (S : Set (Exp α)) : Set (EctxItem α) := Cylinder.flatten (.appR S)

def cover.unop (S : Set UnOp) : Set (EctxItem α) :=
  ⋃ u ∈ S, Cylinder.flatten (Cylinder.unop u : Cylinder α)

def cover.binopL (S : Set BinOp) : Set (EctxItem α) :=
  ⋃ op ∈ S, Cylinder.flatten (.binopL op Set.univ)

def cover.binopR (S : Set BinOp) : Set (EctxItem α) :=
  ⋃ op ∈ S, Cylinder.flatten (.binopR op Set.univ)

def cover.condC (S : Set Unit) : Set (EctxItem α) :=
  ⋃ _ ∈ S, Cylinder.flatten (.condC (Set.univ : Set (Exp α)) Set.univ)

def cover.pairL (S : Set (Val α)) : Set (EctxItem α) := Cylinder.flatten (.pairL S)
def cover.pairR (S : Set (Exp α)) : Set (EctxItem α) := Cylinder.flatten (.pairR S)

def cover.fst (S : Set Unit) : Set (EctxItem α) :=
  ⋃ _ ∈ S, Cylinder.flatten (Cylinder.fst : Cylinder α)
def cover.snd (S : Set Unit) : Set (EctxItem α) :=
  ⋃ _ ∈ S, Cylinder.flatten (Cylinder.snd : Cylinder α)
def cover.inl (S : Set Unit) : Set (EctxItem α) :=
  ⋃ _ ∈ S, Cylinder.flatten (Cylinder.inl : Cylinder α)
def cover.inr (S : Set Unit) : Set (EctxItem α) :=
  ⋃ _ ∈ S, Cylinder.flatten (Cylinder.inr : Cylinder α)

def cover.case (S : Set Unit) : Set (EctxItem α) :=
  ⋃ _ ∈ S, Cylinder.flatten (.case (Set.univ : Set (Exp α)) Set.univ)

def cover.alloc (S : Set Unit) : Set (EctxItem α) :=
  ⋃ _ ∈ S, Cylinder.flatten (Cylinder.alloc : Cylinder α)
def cover.load (S : Set Unit) : Set (EctxItem α) :=
  ⋃ _ ∈ S, Cylinder.flatten (Cylinder.load : Cylinder α)

def cover.storeL (S : Set (Val α)) : Set (EctxItem α) := Cylinder.flatten (.storeL S)
def cover.storeR (S : Set (Exp α)) : Set (EctxItem α) := Cylinder.flatten (.storeR S)

def cover.tape (S : Set Unit) : Set (EctxItem α) :=
  ⋃ _ ∈ S, Cylinder.flatten (Cylinder.tape : Cylinder α)

def cover.randL (S : Set (Val α)) : Set (EctxItem α) := Cylinder.flatten (.randL S)
def cover.randR (S : Set (Exp α)) : Set (EctxItem α) := Cylinder.flatten (.randR S)

def cover.scrut (S : Set (Pat α)) : Set (EctxItem α) := Cylinder.flatten (.scrut S)

/-- Cylinder of a given shape has measurable leaves. -/
theorem Shape.cylinder_hasMeasurableLeaves [MeasurableSpace α] (s : Shape) :
    (s.cylinder (α := α)).HasMeasurableLeaves := by
  cases s <;> constructor <;> measurability

/-- Flattening a cylinder of a shape equals set of terms with a given shape. -/
@[simp] theorem Shape.cylinder_preimage_shape (s : Shape) :
    (s.cylinder (α := α)).flatten = EctxItem.shape ⁻¹' {s} := sorry

/-- Flattening a cylinder gives a measurable set. -/
@[measurability]
theorem flatten_measurable [MeasurableSpace α] {c : Cylinder α}
    (hc : c.HasMeasurableLeaves) : MeasurableSet c.flatten :=
  MeasurableSpace.measurableSet_generateFrom ⟨c, hc, rfl⟩

attribute [aesop safe constructors (rule_sets := [Measurable])]
  ProbLang.EctxItem.Cylinder.HasMeasurableLeaves

attribute [aesop safe apply (rule_sets := [Measurable])]
  Shape.cylinder_hasMeasurableLeaves

/-! ### The cylinder flatten family is a π-system that spans `EctxItem α`. -/

theorem Cylinder.flatten_isPiSystem [MeasurableSpace α] :
    IsPiSystem
      ({S : Set (EctxItem α) | ∃ c : Cylinder α, c.HasMeasurableLeaves ∧ Cylinder.flatten c = S}) := by
  rintro _ ⟨c₁, hc₁, rfl⟩ _ ⟨c₂, hc₂, rfl⟩ hne
  have hi : Cylinder.inter? c₁ c₂ ≠ none := by
    intro h
    have : c₁.flatten ∩ c₂.flatten = ∅ := by rw [Cylinder.flatten_inter, h]; rfl
    exact hne.ne_empty this
  obtain ⟨c, hc⟩ : ∃ c, Cylinder.inter? c₁ c₂ = some c := Option.ne_none_iff_exists'.mp hi
  exact ⟨c, Cylinder.hasMeasurableLeaves_inter hc₁ hc₂ hc, Cylinder.flatten_inter_some hc⟩

theorem Cylinder.flatten_isCountablySpanning [MeasurableSpace α] :
    IsCountablySpanning
      ({S : Set (EctxItem α) | ∃ c : Cylinder α, c.HasMeasurableLeaves ∧ Cylinder.flatten c = S}) := by
  obtain ⟨enc⟩ := nonempty_encodable Shape
  refine ⟨fun n =>
    match enc.decode n with
    | some s => Cylinder.flatten (Shape.cylinder s : Cylinder α)
    | none => Cylinder.flatten (.fst : Cylinder α), ?_, ?_⟩
  · intro n
    cases h : enc.decode n with
    | none => exact ⟨.fst, .fst, by simp [h]⟩
    | some s => exact ⟨Shape.cylinder s, Shape.cylinder_hasMeasurableLeaves s, by simp [h]⟩
  · ext K
    simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
    refine ⟨enc.encode (EctxItem.shape K), ?_⟩
    have hd : enc.decode (enc.encode (EctxItem.shape K)) = some (EctxItem.shape K) := enc.encodek _
    rw [hd]
    cases K <;> simp

/-! ### Measurability of the per-constructor covers. -/

macro "solve_cover_measurable" : tactic => `(tactic|
  first
  | exact .biUnion (Set.to_countable _) fun _ _ => flatten_measurable (by measurability)
  | exact flatten_measurable (by measurability))

@[measurability]
theorem cover.appL.measurable [MeasurableSpace α] {S : Set (Val α)} (hS : MeasurableSet S) :
    MeasurableSet (appL (α := α) S) := flatten_measurable (.appL _ hS)

@[measurability]
theorem cover.appR.measurable [MeasurableSpace α] {S : Set (Exp α)} (hS : MeasurableSet S) :
    MeasurableSet (appR (α := α) S) := flatten_measurable (.appR _ hS)

@[measurability]
theorem cover.unop.measurable [MeasurableSpace α] (S : Set UnOp) :
    MeasurableSet (unop (α := α) S) := by solve_cover_measurable

@[measurability]
theorem cover.binopL.measurable [MeasurableSpace α] (S : Set BinOp) :
    MeasurableSet (binopL (α := α) S) := by solve_cover_measurable

@[measurability]
theorem cover.binopR.measurable [MeasurableSpace α] (S : Set BinOp) :
    MeasurableSet (binopR (α := α) S) := by solve_cover_measurable

@[measurability]
theorem cover.condC.measurable [MeasurableSpace α] (S : Set Unit) :
    MeasurableSet (condC (α := α) S) := by solve_cover_measurable

@[measurability]
theorem cover.pairL.measurable [MeasurableSpace α] {S : Set (Val α)} (hS : MeasurableSet S) :
    MeasurableSet (pairL (α := α) S) := flatten_measurable (.pairL _ hS)

@[measurability]
theorem cover.pairR.measurable [MeasurableSpace α] {S : Set (Exp α)} (hS : MeasurableSet S) :
    MeasurableSet (pairR (α := α) S) := flatten_measurable (.pairR _ hS)

@[measurability]
theorem cover.fst.measurable [MeasurableSpace α] (S : Set Unit) :
    MeasurableSet (fst (α := α) S) := by solve_cover_measurable

@[measurability]
theorem cover.snd.measurable [MeasurableSpace α] (S : Set Unit) :
    MeasurableSet (snd (α := α) S) := by solve_cover_measurable

@[measurability]
theorem cover.inl.measurable [MeasurableSpace α] (S : Set Unit) :
    MeasurableSet (inl (α := α) S) := by solve_cover_measurable

@[measurability]
theorem cover.inr.measurable [MeasurableSpace α] (S : Set Unit) :
    MeasurableSet (inr (α := α) S) := by solve_cover_measurable

@[measurability]
theorem cover.case.measurable [MeasurableSpace α] (S : Set Unit) :
    MeasurableSet (case (α := α) S) := by solve_cover_measurable

@[measurability]
theorem cover.alloc.measurable [MeasurableSpace α] (S : Set Unit) :
    MeasurableSet (alloc (α := α) S) := by solve_cover_measurable

@[measurability]
theorem cover.load.measurable [MeasurableSpace α] (S : Set Unit) :
    MeasurableSet (load (α := α) S) := by solve_cover_measurable

@[measurability]
theorem cover.storeL.measurable [MeasurableSpace α] {S : Set (Val α)} (hS : MeasurableSet S) :
    MeasurableSet (storeL (α := α) S) := flatten_measurable (.storeL _ hS)

@[measurability]
theorem cover.storeR.measurable [MeasurableSpace α] {S : Set (Exp α)} (hS : MeasurableSet S) :
    MeasurableSet (storeR (α := α) S) := flatten_measurable (.storeR _ hS)

@[measurability]
theorem cover.tape.measurable [MeasurableSpace α] (S : Set Unit) :
    MeasurableSet (tape (α := α) S) := by solve_cover_measurable

@[measurability]
theorem cover.randL.measurable [MeasurableSpace α] {S : Set (Val α)} (hS : MeasurableSet S) :
    MeasurableSet (randL (α := α) S) := flatten_measurable (.randL _ hS)

@[measurability]
theorem cover.randR.measurable [MeasurableSpace α] {S : Set (Exp α)} (hS : MeasurableSet S) :
    MeasurableSet (randR (α := α) S) := flatten_measurable (.randR _ hS)

@[measurability]
theorem cover.scrut.measurable [MeasurableSpace α] {S : Set (Pat α)} (hS : MeasurableSet S) :
    MeasurableSet (scrut (α := α) S) := flatten_measurable (.scrut _ hS)

macro "solve_cover_eq_image" ctor:ident : tactic => `(tactic|
  (ext K; cases K <;> simp [$ctor:ident]))

theorem cover.appL_eq_image (S : Set (Val α)) :
    cover.appL (α := α) S = EctxItem.appL '' S := by solve_cover_eq_image cover.appL

theorem cover.appR_eq_image (S : Set (Exp α)) :
    cover.appR (α := α) S = EctxItem.appR '' S := by solve_cover_eq_image cover.appR

theorem cover.unop_eq_image (S : Set UnOp) :
    cover.unop (α := α) S = EctxItem.unop '' S := by solve_cover_eq_image cover.unop

theorem cover.binopL_univ_eq_range :
    cover.binopL (α := α) Set.univ = .range (Function.uncurry EctxItem.binopL) := by
  solve_cover_eq_image cover.binopL

theorem cover.binopR_univ_eq_range :
    cover.binopR (α := α) Set.univ = .range (Function.uncurry EctxItem.binopR) := by
  solve_cover_eq_image cover.binopR

theorem cover.condC_univ_eq_range :
    cover.condC (α := α) Set.univ = .range (Function.uncurry EctxItem.condC) := by
  solve_cover_eq_image cover.condC

theorem cover.pairL_eq_image (S : Set (Val α)) :
    cover.pairL (α := α) S = EctxItem.pairL '' S := by solve_cover_eq_image cover.pairL

theorem cover.pairR_eq_image (S : Set (Exp α)) :
    cover.pairR (α := α) S = EctxItem.pairR '' S := by solve_cover_eq_image cover.pairR

theorem cover.fst_eq_image (S : Set Unit) :
    cover.fst (α := α) S = (fun _ : Unit => (EctxItem.fst : EctxItem α)) '' S := by
  solve_cover_eq_image cover.fst

theorem cover.snd_eq_image (S : Set Unit) :
    cover.snd (α := α) S = (fun _ : Unit => (EctxItem.snd : EctxItem α)) '' S := by
  solve_cover_eq_image cover.snd

theorem cover.inl_eq_image (S : Set Unit) :
    cover.inl (α := α) S = (fun _ : Unit => (EctxItem.inl : EctxItem α)) '' S := by
  solve_cover_eq_image cover.inl

theorem cover.inr_eq_image (S : Set Unit) :
    cover.inr (α := α) S = (fun _ : Unit => (EctxItem.inr : EctxItem α)) '' S := by
  solve_cover_eq_image cover.inr

theorem cover.case_univ_eq_range :
    cover.case (α := α) Set.univ = .range (Function.uncurry EctxItem.case) := by
  solve_cover_eq_image cover.case

theorem cover.alloc_eq_image (S : Set Unit) :
    cover.alloc (α := α) S = (fun _ : Unit => (EctxItem.alloc : EctxItem α)) '' S := by
  solve_cover_eq_image cover.alloc

theorem cover.load_eq_image (S : Set Unit) :
    cover.load (α := α) S = (fun _ : Unit => (EctxItem.load : EctxItem α)) '' S := by
  solve_cover_eq_image cover.load

theorem cover.storeL_eq_image (S : Set (Val α)) :
    cover.storeL (α := α) S = EctxItem.storeL '' S := by solve_cover_eq_image cover.storeL

theorem cover.storeR_eq_image (S : Set (Exp α)) :
    cover.storeR (α := α) S = EctxItem.storeR '' S := by solve_cover_eq_image cover.storeR

theorem cover.tape_eq_image (S : Set Unit) :
    cover.tape (α := α) S = (fun _ : Unit => (EctxItem.tape : EctxItem α)) '' S := by
  solve_cover_eq_image cover.tape

theorem cover.randL_eq_image (S : Set (Val α)) :
    cover.randL (α := α) S = EctxItem.randL '' S := by solve_cover_eq_image cover.randL

theorem cover.randR_eq_image (S : Set (Exp α)) :
    cover.randR (α := α) S = EctxItem.randR '' S := by solve_cover_eq_image cover.randR

theorem cover.scrut_eq_image (S : Set (Pat α)) :
    cover.scrut (α := α) S = EctxItem.scrut '' S := by solve_cover_eq_image cover.scrut

/-! ### Measurable constructors. -/

@[fun_prop]
theorem unop.ι.measurable {α : Type _} [MeasurableSpace α] :
    Measurable (EctxItem.unop.ι (α := α)) := Measurable.of_discrete

@[fun_prop]
theorem fst.ι.measurable {α : Type _} [MeasurableSpace α] :
    Measurable (EctxItem.fst.ι (α := α)) := Measurable.of_discrete

@[fun_prop]
theorem snd.ι.measurable {α : Type _} [MeasurableSpace α] :
    Measurable (EctxItem.snd.ι (α := α)) := Measurable.of_discrete

@[fun_prop]
theorem inl.ι.measurable {α : Type _} [MeasurableSpace α] :
    Measurable (EctxItem.inl.ι (α := α)) := Measurable.of_discrete

@[fun_prop]
theorem inr.ι.measurable {α : Type _} [MeasurableSpace α] :
    Measurable (EctxItem.inr.ι (α := α)) := Measurable.of_discrete

@[fun_prop]
theorem alloc.ι.measurable {α : Type _} [MeasurableSpace α] :
    Measurable (EctxItem.alloc.ι (α := α)) := Measurable.of_discrete

@[fun_prop]
theorem load.ι.measurable {α : Type _} [MeasurableSpace α] :
    Measurable (EctxItem.load.ι (α := α)) := Measurable.of_discrete

@[fun_prop]
theorem tape.ι.measurable {α : Type _} [MeasurableSpace α] :
    Measurable (EctxItem.tape.ι (α := α)) := Measurable.of_discrete

@[fun_prop]
theorem appL.ι.measurable [MeasurableSpace α] :
    Measurable (EctxItem.appL.ι (α := α)) := by
  apply measurable_generateFrom
  rintro G ⟨c, hc, rfl⟩
  cases hc with
  | @appL S hS =>
    suffices h : EctxItem.appL.ι ⁻¹' Cylinder.flatten (.appL S) = S by rw [h]; exact hS
    ext v; simp
  | _ => convert MeasurableSet.empty; ext v; simp

@[fun_prop]
theorem appR.ι.measurable [MeasurableSpace α] :
    Measurable (EctxItem.appR.ι (α := α)) := by
  apply measurable_generateFrom
  rintro G ⟨c, hc, rfl⟩
  cases hc with
  | @appR S hS =>
    suffices h : EctxItem.appR.ι ⁻¹' Cylinder.flatten (.appR S) = S by rw [h]; exact hS
    ext e; simp
  | _ => convert MeasurableSet.empty; ext e; simp

@[fun_prop]
theorem pairL.ι.measurable [MeasurableSpace α] :
    Measurable (EctxItem.pairL.ι (α := α)) := by
  apply measurable_generateFrom
  rintro G ⟨c, hc, rfl⟩
  cases hc with
  | @pairL S hS =>
    suffices h : EctxItem.pairL.ι ⁻¹' Cylinder.flatten (.pairL S) = S by rw [h]; exact hS
    ext v; simp
  | _ => convert MeasurableSet.empty; ext v; simp

@[fun_prop]
theorem pairR.ι.measurable [MeasurableSpace α] :
    Measurable (EctxItem.pairR.ι (α := α)) := by
  apply measurable_generateFrom
  rintro G ⟨c, hc, rfl⟩
  cases hc with
  | @pairR S hS =>
    suffices h : EctxItem.pairR.ι ⁻¹' Cylinder.flatten (.pairR S) = S by rw [h]; exact hS
    ext e; simp
  | _ => convert MeasurableSet.empty; ext e; simp

@[fun_prop]
theorem storeL.ι.measurable [MeasurableSpace α] :
    Measurable (EctxItem.storeL.ι (α := α)) := by
  apply measurable_generateFrom
  rintro G ⟨c, hc, rfl⟩
  cases hc with
  | @storeL S hS =>
    suffices h : EctxItem.storeL.ι ⁻¹' Cylinder.flatten (.storeL S) = S by rw [h]; exact hS
    ext v; simp
  | _ => convert MeasurableSet.empty; ext v; simp

@[fun_prop]
theorem storeR.ι.measurable [MeasurableSpace α] :
    Measurable (EctxItem.storeR.ι (α := α)) := by
  apply measurable_generateFrom
  rintro G ⟨c, hc, rfl⟩
  cases hc with
  | @storeR S hS =>
    suffices h : EctxItem.storeR.ι ⁻¹' Cylinder.flatten (.storeR S) = S by rw [h]; exact hS
    ext e; simp
  | _ => convert MeasurableSet.empty; ext e; simp

@[fun_prop]
theorem randL.ι.measurable [MeasurableSpace α] :
    Measurable (EctxItem.randL.ι (α := α)) := by
  apply measurable_generateFrom
  rintro G ⟨c, hc, rfl⟩
  cases hc with
  | @randL S hS =>
    suffices h : EctxItem.randL.ι ⁻¹' Cylinder.flatten (.randL S) = S by rw [h]; exact hS
    ext v; simp
  | _ => convert MeasurableSet.empty; ext v; simp

@[fun_prop]
theorem randR.ι.measurable [MeasurableSpace α] :
    Measurable (EctxItem.randR.ι (α := α)) := by
  apply measurable_generateFrom
  rintro G ⟨c, hc, rfl⟩
  cases hc with
  | @randR S hS =>
    suffices h : EctxItem.randR.ι ⁻¹' Cylinder.flatten (.randR S) = S by rw [h]; exact hS
    ext e; simp
  | _ => convert MeasurableSet.empty; ext e; simp

@[fun_prop]
theorem scrut.ι.measurable [MeasurableSpace α] :
    Measurable (EctxItem.scrut.ι (α := α)) := by
  apply measurable_generateFrom
  rintro G ⟨c, hc, rfl⟩
  cases hc with
  | @scrut S hS =>
    suffices h : EctxItem.scrut.ι ⁻¹' Cylinder.flatten (.scrut S) = S by rw [h]; exact hS
    ext p; simp
  | _ => convert MeasurableSet.empty; ext p; simp

@[fun_prop]
theorem binopL.ι.measurable [MeasurableSpace α] :
    Measurable (EctxItem.binopL.ι (α := α)) := by
  apply measurable_generateFrom
  rintro G ⟨c, hc, rfl⟩
  cases hc with
  | @binopL op S hS =>
    suffices heq : EctxItem.binopL.ι ⁻¹' Cylinder.flatten (.binopL op S)
                = ({op} : Set BinOp) ×ˢ S by rw [heq]; measurability
    ext ⟨_, _⟩; simp; tauto
  | _ => convert MeasurableSet.empty; ext ⟨_, _⟩; simp

@[fun_prop]
theorem binopR.ι.measurable [MeasurableSpace α] :
    Measurable (EctxItem.binopR.ι (α := α)) := by
  apply measurable_generateFrom
  rintro G ⟨c, hc, rfl⟩
  cases hc with
  | @binopR op S hS =>
    suffices heq : EctxItem.binopR.ι ⁻¹' Cylinder.flatten (.binopR op S)
                = ({op} : Set BinOp) ×ˢ S by rw [heq]; measurability
    ext ⟨_, _⟩; simp; tauto
  | _ => convert MeasurableSet.empty; ext ⟨_, _⟩; simp

@[fun_prop]
theorem condC.ι.measurable [MeasurableSpace α] :
    Measurable (EctxItem.condC.ι (α := α)) := by
  apply measurable_generateFrom
  rintro G ⟨c, hc, rfl⟩
  cases hc with
  | @condC S1 S2 hS1 hS2 =>
    suffices h : EctxItem.condC.ι ⁻¹' Cylinder.flatten (.condC S1 S2)
                = S1 ×ˢ S2 by rw [h]; measurability
    ext ⟨_, _⟩; simp
  | _ => convert MeasurableSet.empty; ext ⟨_, _⟩; simp

@[fun_prop]
theorem case.ι.measurable [MeasurableSpace α] :
    Measurable (EctxItem.case.ι (α := α)) := by
  apply measurable_generateFrom
  rintro G ⟨c, hc, rfl⟩
  cases hc with
  | @case S1 S2 hS1 hS2 =>
    suffices h : EctxItem.case.ι ⁻¹' Cylinder.flatten (.case S1 S2)
                = S1 ×ˢ S2 by rw [h]; measurability
    ext ⟨_, _⟩; simp
  | _ => convert MeasurableSet.empty; ext ⟨_, _⟩; simp

/-! ### Measurable embeddings. -/

macro "solve_discrete_ME" eq_image:term ", " meas:term : tactic => `(tactic|
  (refine ⟨fun _ _ h => by injection h, Measurable.of_discrete, fun S _ => ?_⟩
   rw [← $eq_image S]
   exact $meas S))

macro "solve_nullary_ME" eq_image:term ", " meas:term : tactic => `(tactic|
  (apply MeasurableEmbedding.of_measurable_inverse (g := fun _ => ())
   · exact measurable_const
   · rw [show Set.range _ = _ from by rw [← $eq_image Set.univ]; ext; simp]
     exact $meas _
   · exact measurable_const
   · intro; rfl))

theorem unop.measurableEmbedding [MeasurableSpace α] :
    MeasurableEmbedding (EctxItem.unop : UnOp → EctxItem α) := by
  solve_discrete_ME cover.unop_eq_image, cover.unop.measurable

theorem fst.measurableEmbedding [MeasurableSpace α] :
    MeasurableEmbedding (fun _ : Unit => (EctxItem.fst : EctxItem α)) := by
  apply MeasurableEmbedding.of_measurable_inverse (g := fun _ => ())
  · exact measurable_const
  · rw [show Set.range (fun _ : Unit => (EctxItem.fst : EctxItem α)) = cover.fst .univ from by
             rw [cover.fst_eq_image]; ext; simp]
    exact cover.fst.measurable _
  · exact measurable_const
  · intro; rfl

theorem snd.measurableEmbedding [MeasurableSpace α] :
    MeasurableEmbedding (fun _ : Unit => (EctxItem.snd : EctxItem α)) := by
  apply MeasurableEmbedding.of_measurable_inverse (g := fun _ => ())
  · exact measurable_const
  · rw [show Set.range (fun _ : Unit => (EctxItem.snd : EctxItem α)) = cover.snd .univ from by
             rw [cover.snd_eq_image]; ext; simp]
    exact cover.snd.measurable _
  · exact measurable_const
  · intro; rfl

theorem inl.measurableEmbedding [MeasurableSpace α] :
    MeasurableEmbedding (fun _ : Unit => (EctxItem.inl : EctxItem α)) := by
  apply MeasurableEmbedding.of_measurable_inverse (g := fun _ => ())
  · exact measurable_const
  · rw [show Set.range (fun _ : Unit => (EctxItem.inl : EctxItem α)) = cover.inl .univ from by
             rw [cover.inl_eq_image]; ext; simp]
    exact cover.inl.measurable _
  · exact measurable_const
  · intro; rfl

theorem inr.measurableEmbedding [MeasurableSpace α] :
    MeasurableEmbedding (fun _ : Unit => (EctxItem.inr : EctxItem α)) := by
  apply MeasurableEmbedding.of_measurable_inverse (g := fun _ => ())
  · exact measurable_const
  · rw [show Set.range (fun _ : Unit => (EctxItem.inr : EctxItem α)) = cover.inr .univ from by
             rw [cover.inr_eq_image]; ext; simp]
    exact cover.inr.measurable _
  · exact measurable_const
  · intro; rfl

theorem alloc.measurableEmbedding [MeasurableSpace α] :
    MeasurableEmbedding (fun _ : Unit => (EctxItem.alloc : EctxItem α)) := by
  apply MeasurableEmbedding.of_measurable_inverse (g := fun _ => ())
  · exact measurable_const
  · rw [show Set.range (fun _ : Unit => (EctxItem.alloc : EctxItem α)) = cover.alloc .univ from by
             rw [cover.alloc_eq_image]; ext; simp]
    exact cover.alloc.measurable _
  · exact measurable_const
  · intro; rfl

theorem load.measurableEmbedding [MeasurableSpace α] :
    MeasurableEmbedding (fun _ : Unit => (EctxItem.load : EctxItem α)) := by
  apply MeasurableEmbedding.of_measurable_inverse (g := fun _ => ())
  · exact measurable_const
  · rw [show Set.range (fun _ : Unit => (EctxItem.load : EctxItem α)) = cover.load .univ from by
             rw [cover.load_eq_image]; ext; simp]
    exact cover.load.measurable _
  · exact measurable_const
  · intro; rfl

theorem tape.measurableEmbedding [MeasurableSpace α] :
    MeasurableEmbedding (fun _ : Unit => (EctxItem.tape : EctxItem α)) := by
  apply MeasurableEmbedding.of_measurable_inverse (g := fun _ => ())
  · exact measurable_const
  · rw [show Set.range (fun _ : Unit => (EctxItem.tape : EctxItem α)) = cover.tape .univ from by
             rw [cover.tape_eq_image]; ext; simp]
    exact cover.tape.measurable _
  · exact measurable_const
  · intro; rfl

theorem appL.measurableEmbedding [MeasurableSpace α] :
    MeasurableEmbedding (EctxItem.appL : Val α → EctxItem α) :=
  ⟨fun _ _ h => by injection h, EctxItem.appL.ι.measurable,
    fun _ hS => flatten_measurable (.appL _ hS)⟩

theorem appR.measurableEmbedding [MeasurableSpace α] :
    MeasurableEmbedding (EctxItem.appR : Exp α → EctxItem α) :=
  ⟨fun _ _ h => by injection h, EctxItem.appR.ι.measurable,
    fun _ hS => flatten_measurable (.appR _ hS)⟩

theorem pairL.measurableEmbedding [MeasurableSpace α] :
    MeasurableEmbedding (EctxItem.pairL : Val α → EctxItem α) :=
  ⟨fun _ _ h => by injection h, EctxItem.pairL.ι.measurable,
    fun _ hS => flatten_measurable (.pairL _ hS)⟩

theorem pairR.measurableEmbedding [MeasurableSpace α] :
    MeasurableEmbedding (EctxItem.pairR : Exp α → EctxItem α) :=
  ⟨fun _ _ h => by injection h, EctxItem.pairR.ι.measurable,
    fun _ hS => flatten_measurable (.pairR _ hS)⟩

theorem storeL.measurableEmbedding [MeasurableSpace α] :
    MeasurableEmbedding (EctxItem.storeL : Val α → EctxItem α) :=
  ⟨fun _ _ h => by injection h, EctxItem.storeL.ι.measurable,
    fun _ hS => flatten_measurable (.storeL _ hS)⟩

theorem storeR.measurableEmbedding [MeasurableSpace α] :
    MeasurableEmbedding (EctxItem.storeR : Exp α → EctxItem α) :=
  ⟨fun _ _ h => by injection h, EctxItem.storeR.ι.measurable,
    fun _ hS => flatten_measurable (.storeR _ hS)⟩

theorem randL.measurableEmbedding [MeasurableSpace α] :
    MeasurableEmbedding (EctxItem.randL : Val α → EctxItem α) :=
  ⟨fun _ _ h => by injection h, EctxItem.randL.ι.measurable,
    fun _ hS => flatten_measurable (.randL _ hS)⟩

theorem randR.measurableEmbedding [MeasurableSpace α] :
    MeasurableEmbedding (EctxItem.randR : Exp α → EctxItem α) :=
  ⟨fun _ _ h => by injection h, EctxItem.randR.ι.measurable,
    fun _ hS => flatten_measurable (.randR _ hS)⟩

theorem scrut.measurableEmbedding [MeasurableSpace α] :
    MeasurableEmbedding (EctxItem.scrut : Pat α → EctxItem α) :=
  ⟨fun _ _ h => by injection h, EctxItem.scrut.ι.measurable,
    fun _ hS => flatten_measurable (.scrut _ hS)⟩

theorem binopL.measurableEmbedding [MeasurableSpace α] :
    MeasurableEmbedding (Function.uncurry (EctxItem.binopL : BinOp → Val α → EctxItem α)) :=
  measurableEmbedding_of_piSystem₂
    (h_inj := EctxItem.binopL.ι.inj) (h_meas := EctxItem.binopL.ι.measurable)
    (h_gen := (generateFrom_eq_prod singletonsAndUniv_generateFrom
                MeasurableSpace.generateFrom_measurableSet
                singletonsAndUniv_isCountablySpanning isCountablySpanning_measurableSet).symm)
    (h_pi := singletonsAndUniv_isPiSystem.prod
              (fun S (hS : MeasurableSet S) T (hT : MeasurableSet T) _ => hS.inter hT))
    (h_basic := by
      rintro A hA S (hS : MeasurableSet S)
      rcases hA with rfl | ⟨op, rfl⟩
      · rw [show ((Function.uncurry EctxItem.binopL) '' (Set.univ ×ˢ S) : Set (EctxItem α))
              = ⋃ op : BinOp, EctxItem.binopL op '' S from by
            ext K; simp [Function.uncurry]]
        exact .iUnion fun op => flatten_measurable (.binopL (op := op) _ hS)
      · rw [show ((Function.uncurry EctxItem.binopL) '' (({op} : Set BinOp) ×ˢ S) : Set (EctxItem α))
              = Cylinder.flatten (.binopL op S) from by ext K; cases K <;> simp [Function.uncurry]]
        exact flatten_measurable (.binopL _ hS))
    (h_cov_meas := cover.binopL.measurable _) (h_cov_range := cover.binopL_univ_eq_range)

theorem binopR.measurableEmbedding [MeasurableSpace α] :
    MeasurableEmbedding (Function.uncurry (EctxItem.binopR : BinOp → Exp α → EctxItem α)) :=
  measurableEmbedding_of_piSystem₂
    (h_inj := EctxItem.binopR.ι.inj) (h_meas := EctxItem.binopR.ι.measurable)
    (h_gen := (generateFrom_eq_prod singletonsAndUniv_generateFrom
                MeasurableSpace.generateFrom_measurableSet
                singletonsAndUniv_isCountablySpanning isCountablySpanning_measurableSet).symm)
    (h_pi := singletonsAndUniv_isPiSystem.prod
              (fun S (hS : MeasurableSet S) T (hT : MeasurableSet T) _ => hS.inter hT))
    (h_basic := by
      rintro A hA S (hS : MeasurableSet S)
      rcases hA with rfl | ⟨op, rfl⟩
      · rw [show ((Function.uncurry EctxItem.binopR) '' (Set.univ ×ˢ S) : Set (EctxItem α))
              = ⋃ op : BinOp, EctxItem.binopR op '' S from by
            ext K; simp [Function.uncurry]]
        exact .iUnion fun op => flatten_measurable (.binopR (op := op) _ hS)
      · rw [show ((Function.uncurry EctxItem.binopR) '' (({op} : Set BinOp) ×ˢ S) : Set (EctxItem α))
              = Cylinder.flatten (.binopR op S) from by ext K; cases K <;> simp [Function.uncurry]]
        exact flatten_measurable (.binopR _ hS))
    (h_cov_meas := cover.binopR.measurable _) (h_cov_range := cover.binopR_univ_eq_range)

theorem condC.measurableEmbedding [MeasurableSpace α] :
    MeasurableEmbedding (Function.uncurry (EctxItem.condC : Exp α → Exp α → EctxItem α)) :=
  measurableEmbedding_of_piSystem₂
    (h_inj := EctxItem.condC.ι.inj) (h_meas := EctxItem.condC.ι.measurable)
    (h_gen := (generateFrom_eq_prod MeasurableSpace.generateFrom_measurableSet
                MeasurableSpace.generateFrom_measurableSet
                isCountablySpanning_measurableSet isCountablySpanning_measurableSet).symm)
    (h_pi := IsPiSystem.prod
              (fun S (hS : MeasurableSet S) T (hT : MeasurableSet T) _ => hS.inter hT)
              (fun S (hS : MeasurableSet S) T (hT : MeasurableSet T) _ => hS.inter hT))
    (h_basic := by
      rintro S₁ (hS₁ : MeasurableSet S₁) S₂ (hS₂ : MeasurableSet S₂)
      rw [show ((Function.uncurry EctxItem.condC) '' (S₁ ×ˢ S₂) : Set (EctxItem α))
            = Cylinder.flatten (.condC S₁ S₂) from by ext K; cases K <;> simp [Function.uncurry]]
      exact flatten_measurable (.condC _ _ hS₁ hS₂))
    (h_cov_meas := cover.condC.measurable _) (h_cov_range := cover.condC_univ_eq_range)

theorem case.measurableEmbedding [MeasurableSpace α] :
    MeasurableEmbedding (Function.uncurry (EctxItem.case : Exp α → Exp α → EctxItem α)) :=
  measurableEmbedding_of_piSystem₂
    (h_inj := EctxItem.case.ι.inj) (h_meas := EctxItem.case.ι.measurable)
    (h_gen := (generateFrom_eq_prod MeasurableSpace.generateFrom_measurableSet
                MeasurableSpace.generateFrom_measurableSet
                isCountablySpanning_measurableSet isCountablySpanning_measurableSet).symm)
    (h_pi := IsPiSystem.prod
              (fun S (hS : MeasurableSet S) T (hT : MeasurableSet T) _ => hS.inter hT)
              (fun S (hS : MeasurableSet S) T (hT : MeasurableSet T) _ => hS.inter hT))
    (h_basic := by
      rintro S₁ (hS₁ : MeasurableSet S₁) S₂ (hS₂ : MeasurableSet S₂)
      rw [show ((Function.uncurry EctxItem.case) '' (S₁ ×ˢ S₂) : Set (EctxItem α))
            = Cylinder.flatten (.case S₁ S₂) from by ext K; cases K <;> simp [Function.uncurry]]
      exact flatten_measurable (.case _ _ hS₁ hS₂))
    (h_cov_meas := cover.case.measurable _) (h_cov_range := cover.case_univ_eq_range)

theorem casesOn_preimage_decomp
    {α : Type _} {β : Type _} (S : Set β)
    (f_appL : Val α → β) (f_appR : Exp α → β) (f_unop : UnOp → β)
    (f_binopL : BinOp × Val α → β) (f_binopR : BinOp × Exp α → β)
    (f_condC : Exp α × Exp α → β)
    (f_pairL : Val α → β) (f_pairR : Exp α → β)
    (f_fst : Unit → β) (f_snd : Unit → β) (f_inl : Unit → β) (f_inr : Unit → β)
    (f_case : Exp α × Exp α → β)
    (f_alloc : Unit → β) (f_load : Unit → β)
    (f_storeL : Val α → β) (f_storeR : Exp α → β)
    (f_tape : Unit → β)
    (f_randL : Val α → β) (f_randR : Exp α → β)
    (f_scrut : Pat α → β) :
    (fun K : EctxItem α => EctxItem.casesOn (motive := fun _ => β) K
        f_appL f_appR f_unop
        (fun op v => f_binopL (op, v))
        (fun op e => f_binopR (op, e))
        (fun e₁ e₂ => f_condC (e₁, e₂))
        f_pairL f_pairR
        (f_fst ()) (f_snd ()) (f_inl ()) (f_inr ())
        (fun e₁ e₂ => f_case (e₁, e₂))
        (f_alloc ()) (f_load ())
        f_storeL f_storeR
        (f_tape ())
        f_randL f_randR
        f_scrut) ⁻¹' S
      = (EctxItem.appL.ι   '' (f_appL   ⁻¹' S))
      ∪ (EctxItem.appR.ι   '' (f_appR   ⁻¹' S))
      ∪ (EctxItem.unop.ι   '' (f_unop   ⁻¹' S))
      ∪ (EctxItem.binopL.ι '' (f_binopL ⁻¹' S))
      ∪ (EctxItem.binopR.ι '' (f_binopR ⁻¹' S))
      ∪ (EctxItem.condC.ι  '' (f_condC  ⁻¹' S))
      ∪ (EctxItem.pairL.ι  '' (f_pairL  ⁻¹' S))
      ∪ (EctxItem.pairR.ι  '' (f_pairR  ⁻¹' S))
      ∪ (EctxItem.fst.ι    '' (f_fst    ⁻¹' S))
      ∪ (EctxItem.snd.ι    '' (f_snd    ⁻¹' S))
      ∪ (EctxItem.inl.ι    '' (f_inl    ⁻¹' S))
      ∪ (EctxItem.inr.ι    '' (f_inr    ⁻¹' S))
      ∪ (EctxItem.case.ι   '' (f_case   ⁻¹' S))
      ∪ (EctxItem.alloc.ι  '' (f_alloc  ⁻¹' S))
      ∪ (EctxItem.load.ι   '' (f_load   ⁻¹' S))
      ∪ (EctxItem.storeL.ι '' (f_storeL ⁻¹' S))
      ∪ (EctxItem.storeR.ι '' (f_storeR ⁻¹' S))
      ∪ (EctxItem.tape.ι   '' (f_tape   ⁻¹' S))
      ∪ (EctxItem.randL.ι  '' (f_randL  ⁻¹' S))
      ∪ (EctxItem.randR.ι  '' (f_randR  ⁻¹' S))
      ∪ (EctxItem.scrut.ι  '' (f_scrut  ⁻¹' S)) := by
  ext K; cases K <;> aesop

@[fun_prop]
theorem measurable_rec
    {α : Type _} [MeasurableSpace α]
    {β : Type _} [MeasurableSpace β]
    (f_appL : Val α → β) (f_appR : Exp α → β) (f_unop : UnOp → β)
    (f_binopL : BinOp × Val α → β) (f_binopR : BinOp × Exp α → β)
    (f_condC : Exp α × Exp α → β)
    (f_pairL : Val α → β) (f_pairR : Exp α → β)
    (f_fst : Unit → β) (f_snd : Unit → β) (f_inl : Unit → β) (f_inr : Unit → β)
    (f_case : Exp α × Exp α → β)
    (f_alloc : Unit → β) (f_load : Unit → β)
    (f_storeL : Val α → β) (f_storeR : Exp α → β)
    (f_tape : Unit → β)
    (f_randL : Val α → β) (f_randR : Exp α → β)
    (f_scrut : Pat α → β)
    (h_appL : Measurable f_appL) (h_appR : Measurable f_appR)
    (h_binopL : Measurable f_binopL) (h_binopR : Measurable f_binopR)
    (h_condC : Measurable f_condC)
    (h_pairL : Measurable f_pairL) (h_pairR : Measurable f_pairR)
    (h_case : Measurable f_case)
    (h_storeL : Measurable f_storeL) (h_storeR : Measurable f_storeR)
    (h_randL : Measurable f_randL) (h_randR : Measurable f_randR)
    (h_scrut : Measurable f_scrut) :
    Measurable (fun K : EctxItem α => EctxItem.casesOn (motive := fun _ => β) K
        f_appL f_appR f_unop
        (fun op v => f_binopL (op, v))
        (fun op e => f_binopR (op, e))
        (fun e₁ e₂ => f_condC (e₁, e₂))
        f_pairL f_pairR
        (f_fst ()) (f_snd ()) (f_inl ()) (f_inr ())
        (fun e₁ e₂ => f_case (e₁, e₂))
        (f_alloc ()) (f_load ())
        f_storeL f_storeR
        (f_tape ())
        f_randL f_randR
        f_scrut) := by
  intro S hS
  rw [EctxItem.casesOn_preimage_decomp]
  iterate 20 refine .union ?_ ?_
  · exact appL.measurableEmbedding.measurableSet_image'   (h_appL hS)
  · exact appR.measurableEmbedding.measurableSet_image'   (h_appR hS)
  · exact unop.measurableEmbedding.measurableSet_image'   .of_discrete
  · exact binopL.measurableEmbedding.measurableSet_image' (h_binopL hS)
  · exact binopR.measurableEmbedding.measurableSet_image' (h_binopR hS)
  · exact condC.measurableEmbedding.measurableSet_image'  (h_condC hS)
  · exact pairL.measurableEmbedding.measurableSet_image'  (h_pairL hS)
  · exact pairR.measurableEmbedding.measurableSet_image'  (h_pairR hS)
  · exact fst.measurableEmbedding.measurableSet_image'    .of_discrete
  · exact snd.measurableEmbedding.measurableSet_image'    .of_discrete
  · exact inl.measurableEmbedding.measurableSet_image'    .of_discrete
  · exact inr.measurableEmbedding.measurableSet_image'    .of_discrete
  · exact case.measurableEmbedding.measurableSet_image'   (h_case hS)
  · exact alloc.measurableEmbedding.measurableSet_image'  .of_discrete
  · exact load.measurableEmbedding.measurableSet_image'   .of_discrete
  · exact storeL.measurableEmbedding.measurableSet_image' (h_storeL hS)
  · exact storeR.measurableEmbedding.measurableSet_image' (h_storeR hS)
  · exact tape.measurableEmbedding.measurableSet_image'   .of_discrete
  · exact randL.measurableEmbedding.measurableSet_image'  (h_randL hS)
  · exact randR.measurableEmbedding.measurableSet_image'  (h_randR hS)
  · exact scrut.measurableEmbedding.measurableSet_image'  (h_scrut hS)

end ProbLang.EctxItem

end EctxItem -- section

end ProbLangMeasures
