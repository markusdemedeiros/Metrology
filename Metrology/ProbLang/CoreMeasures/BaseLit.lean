module

import all Mathlib.Tactic.DeriveCountable
public import Metrology.ProbLang.Measure
public import Metrology.ProbLang.Syntax.Syntax
public import Metrology.ProbLang.CoreMeasures.Discrete

meta import Metrology.Meta

@[expose] public section

noncomputable section ProbLangMeasures

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

/-- A cylinder is a `BaseLit`-shaped tree whose `rT`-payloads have been replaced by `Set rT`. -/
inductive Cylinder (rT : Type _)
  | int (z : Int)
  | bool (b : Bool)
  | unit
  | loc (l : Loc)
  | lbl (l : Lbl)
  | real (S : Set rT)

/-- A tree with all data forgotten, in order to be countable. -/
inductive Shape
  | int (z : Int)
  | bool (b : Bool)
  | unit
  | loc (l : Loc)
  | lbl (l : Lbl)
  | real
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

/-- A cylinder has measurable leaves if every `Set rT` it carries is measurable. -/
inductive Cylinder.HasMeasurableLeaves {rT : Type _} [MeasurableSpace rT] :
    Cylinder rT → Prop where
  | int     : HasMeasurableLeaves (.int z)
  | bool    : HasMeasurableLeaves (.bool b)
  | unit    : HasMeasurableLeaves .unit
  | loc     : HasMeasurableLeaves (.loc z)
  | lbl     : HasMeasurableLeaves (.lbl z)
  | real Sᵣ : MeasurableSet Sᵣ → HasMeasurableLeaves (.real Sᵣ)

instance instMeasurableSpaceBaseLit [MeasurableSpace rT] : MeasurableSpace (BaseLit rT) :=
  .generateFrom <| Cylinder.flatten '' { c : Cylinder rT | c.HasMeasurableLeaves }

@[simp] def shape : BaseLit rT → Shape
  | .int z        => .int z
  | .bool b       => .bool b
  | .unit         => .unit
  | .loc l        => .loc l
  | .lbl l        => .lbl l
  | .real _       => .real

/-- Shape of a cylinder (forgets data leaves). -/
@[simp] def Cylinder.shape {rT : Type _} : Cylinder rT → Shape
  | .int z        => .int z
  | .bool b       => .bool b
  | .unit         => .unit
  | .loc l        => .loc l
  | .lbl l        => .lbl l
  | .real _       => .real

/-- The "universe cylinder" for a given shape: `univ` at every leaf, same skeleton as the shape. -/
@[simp] def Shape.cylinder {rT : Type _} : Shape → Cylinder rT
  | .int z        => .int z
  | .bool b       => .bool b
  | .unit         => .unit
  | .loc l        => .loc l
  | .lbl l        => .lbl l
  | .real         => .real Set.univ

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
  | _, _ => none

/-- Every element of a cylinder's flatten has that cylinder's shape. -/
theorem Cylinder.shape_of_mem_flatten {rT : Type _} {c : Cylinder rT} {b : BaseLit rT}
    (h : b ∈ Cylinder.flatten c) : BaseLit.shape b = Cylinder.shape c := by
  induction c generalizing b with
  | int _ | bool _ | unit | loc _ | lbl _ => simp_all
  | real _ => obtain ⟨_, _, rfl⟩ := h; rfl

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

/-! Three generic helper lemmas next for provving measurability of a cover -/

/-- Cylinder of a given shape has measurable leaves -/
theorem Shape.cylinder_hasMeasurableLeaves [MeasurableSpace rT] (s : Shape) :
    (s.cylinder (rT := rT)).HasMeasurableLeaves := by
  induction s <;> constructor; measurability

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
    cases b <;> simp

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

theorem casesOn_preimage_decomp
    {rT : Type _} {α : Type _} (S : Set α)
    (f_int  : Int  → α) (f_bool : Bool → α) (f_unit : Unit → α)
    (f_loc  : Loc  → α) (f_lbl  : Lbl  → α) (f_real : rT → α) :
    (fun b : BaseLit rT => BaseLit.casesOn (motive := fun _ => α) b
        f_int f_bool (f_unit ()) f_loc f_lbl f_real) ⁻¹' S
      = (BaseLit.int.ι  '' (f_int  ⁻¹' S))
      ∪ (BaseLit.bool.ι '' (f_bool ⁻¹' S))
      ∪ (BaseLit.unit.ι '' (f_unit ⁻¹' S))
      ∪ (BaseLit.loc.ι  '' (f_loc  ⁻¹' S))
      ∪ (BaseLit.lbl.ι  '' (f_lbl  ⁻¹' S))
      ∪ (BaseLit.real.ι '' (f_real ⁻¹' S)) := by
  ext b; cases b <;> aesop

@[fun_prop]
theorem measurable_rec
    {rT : Type _} [MeasurableSpace rT] [Inhabited rT]
    {α : Type _} [MeasurableSpace α]
    (f_int  : Int  → α) (f_bool : Bool → α) (f_unit : Unit → α)
    (f_loc  : Loc  → α) (f_lbl  : Lbl  → α) (f_real : rT → α)
    (h_real : Measurable f_real) :
    Measurable (fun b : BaseLit rT =>
      BaseLit.casesOn (motive := fun _ => α) b
        f_int f_bool (f_unit ()) f_loc f_lbl f_real) := by
  intro S hS
  rw [BaseLit.casesOn_preimage_decomp]
  iterate 5 refine .union ?_ ?_
  · exact int.measurableEmbedding.measurableSet_image'   .of_discrete
  · exact bool.measurableEmbedding.measurableSet_image'  .of_discrete
  · exact unit.measurableEmbedding.measurableSet_image'  .of_discrete
  · exact loc.measurableEmbedding.measurableSet_image'   .of_discrete
  · exact lbl.measurableEmbedding.measurableSet_image'   .of_discrete
  · exact real.measurableEmbedding.measurableSet_image'  (h_real hS)

end BaseLit
end ProbLang
end ProbLangMeasures
