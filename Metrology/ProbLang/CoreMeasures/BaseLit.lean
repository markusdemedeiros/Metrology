module

import all Mathlib.Tactic.DeriveCountable
public import Metrology.ProbLang.Measure
public import Metrology.ProbLang.Syntax.Syntax
public import Metrology.ProbLang.CoreMeasures.Discrete
public import Metrology.ProbLang.CoreMeasures.Stamp

meta import Metrology.Meta

@[expose] public section

noncomputable section ProbLangMeasures

/-# Measure space on base lits -/

namespace ProbLang.BaseLit

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
@[simp, stamp_simp] def Cylinder.flatten {rT : Type _} : Cylinder rT → Set (BaseLit rT)
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

@[simp, stamp_simp] def shape : BaseLit rT → Shape
  | .int z        => .int z
  | .bool b       => .bool b
  | .unit         => .unit
  | .loc l        => .loc l
  | .lbl l        => .lbl l
  | .real _       => .real

/-- Shape of a cylinder (forgets data leaves). -/
@[simp, stamp_simp] def Cylinder.shape {rT : Type _} : Cylinder rT → Shape
  | .int z        => .int z
  | .bool b       => .bool b
  | .unit         => .unit
  | .loc l        => .loc l
  | .lbl l        => .lbl l
  | .real _       => .real

/-- The "universe cylinder" for a given shape: `univ` at every leaf, same skeleton as the shape. -/
@[simp, stamp_simp] def Shape.cylinder {rT : Type _} : Shape → Cylinder rT
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
    (h : Cylinder.shape c₁ ≠ Cylinder.shape c₂) : Cylinder.flatten c₁ ∩ Cylinder.flatten c₂ = ∅ :=
  Stamp.flatten_disjoint_of_shape_ne (cShape := Cylinder.shape)
    (fun {_ _} h => Cylinder.shape_of_mem_flatten h) h

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
    case real S₂ =>
      simp only [Cylinder.flatten, Cylinder.inter?, Option.elim]
      exact Stamp.flatten_inter_data BaseLit.real.ι.inj
    all_goals (rw [Cylinder.flatten_disjoint_of_shape_ne (by simp [Cylinder.shape])]; rfl)

theorem Cylinder.flatten_inter_some {rT : Type _} {c₁ c₂ c : Cylinder rT}
    (h : Cylinder.inter? c₁ c₂ = some c) :
    Cylinder.flatten c = Cylinder.flatten c₁ ∩ Cylinder.flatten c₂ :=
  Stamp.flatten_inter_some Cylinder.flatten_inter h

/-- Inheritance of `HasMeasurableLeaves` under `Cylinder.inter?`. Per-constructor and
linear in constructor count: `cases c₁`, then `cases c₂` (off-diagonal dies on
`inter? = none ≠ some c`), and the diagonal reduces the `inter?` `some`/`if` and rebuilds
the constructor, with `MeasurableSet.inter` for the sole data leaf (`real`). -/
theorem Cylinder.hasMeasurableLeaves_inter [MeasurableSpace rT]
    {c₁ c₂ c : Cylinder rT}
    (h₁ : c₁.HasMeasurableLeaves) (h₂ : c₂.HasMeasurableLeaves)
    (h : Cylinder.inter? c₁ c₂ = some c) : c.HasMeasurableLeaves := by
  cases c₁ with
  | int z | bool z | unit | loc z | lbl z =>
    cases c₂ <;> simp only [Cylinder.inter?, reduceCtorEq] at h ⊢
    all_goals first | (split at h <;> simp_all) | simp_all
  | real S₁ =>
    cases c₂ <;> simp only [Cylinder.inter?, reduceCtorEq] at h ⊢
    cases h₁; cases h₂; injection h with h; subst h; exact .real _ (MeasurableSet.inter ‹_› ‹_›)


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

@[stamp_simp] def cover.int (S : Set Int) : Set (BaseLit rT) :=
  ⋃ z ∈ S, Cylinder.flatten (.int z)

@[stamp_simp] def cover.bool (S : Set Bool) : Set (BaseLit rT) :=
  ⋃ b ∈ S, Cylinder.flatten (.bool b)

@[stamp_simp] def cover.unit (S : Set Unit) : Set (BaseLit rT) :=
  ⋃ _ ∈ S, Cylinder.flatten (Cylinder.unit : Cylinder rT)

@[stamp_simp] def cover.loc (S : Set Loc) : Set (BaseLit rT) :=
  ⋃ l ∈ S, Cylinder.flatten (.loc l)

@[stamp_simp] def cover.lbl (S : Set Lbl) : Set (BaseLit rT) :=
  ⋃ l ∈ S, Cylinder.flatten (.lbl l)

@[stamp_simp] def cover.real (S : Set rT) : Set (BaseLit rT) :=
  Cylinder.flatten (.real S)

/-! Three generic helper lemmas next for provving measurability of a cover -/

/-- Cylinder of a given shape has measurable leaves -/
theorem Shape.cylinder_hasMeasurableLeaves [MeasurableSpace rT] (s : Shape) :
    (s.cylinder (rT := rT)).HasMeasurableLeaves := by
  induction s <;> (constructor <;> measurability)

/-- Flattening a cylinder of a shape equals set of terms with a given shape -/
@[simp] theorem Shape.cylinder_preimage_shape (s : Shape) :
    (s.cylinder (rT := rT)).flatten = shape ⁻¹' {s} :=
  Stamp.cylinder_preimage_shape (cShape := Cylinder.shape)
    (fun {_ _} h => Cylinder.shape_of_mem_flatten h)
    (fun s => by induction s <;> simp_all)
    (fun b => by induction b <;> simp_all) s

/-- Flattening a cylinder gives a measurable set -/
@[measurability]
theorem flatten_measurable [MeasurableSpace rT] {c : Cylinder rT}
    (hc : c.HasMeasurableLeaves) : MeasurableSet c.flatten :=
  Stamp.flatten_measurable rfl hc

attribute [aesop safe constructors (rule_sets := [Measurable])]
  ProbLang.BaseLit.Cylinder.HasMeasurableLeaves

attribute [aesop safe apply (rule_sets := [Measurable])]
  Shape.cylinder_hasMeasurableLeaves

/-! ### The cylinder flatten family is a π-system that spans `BaseLit rT`. -/

/-- The cylinder flatten family is closed under nonempty intersection. -/
theorem Cylinder.flatten_isPiSystem [MeasurableSpace rT] :
    IsPiSystem
      ({S : Set (BaseLit rT) | ∃ c : Cylinder rT, c.HasMeasurableLeaves ∧ Cylinder.flatten c = S}) :=
  Stamp.flatten_isPiSystem Cylinder.flatten_inter
    (fun {_ _ _} => Cylinder.hasMeasurableLeaves_inter)

/-- The cylinder flatten family is countably spanning. -/
theorem Cylinder.flatten_isCountablySpanning [MeasurableSpace rT] :
    IsCountablySpanning
      ({S : Set (BaseLit rT) | ∃ c : Cylinder rT, c.HasMeasurableLeaves ∧ Cylinder.flatten c = S}) :=
  Stamp.flatten_isCountablySpanning Shape.cylinder_hasMeasurableLeaves
    Shape.cylinder_preimage_shape .unit .unit

/-! ### Measurability of the per-constructor covers. -/

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
    Measurable (BaseLit.int.ι (rT := rT)) := (by measurability)

@[fun_prop]
theorem bool.ι.measurable {rT : Type _} [MeasurableSpace rT] :
    Measurable (BaseLit.bool.ι (rT := rT)) := (by measurability)

@[fun_prop]
theorem unit.ι.measurable {rT : Type _} [MeasurableSpace rT] :
    Measurable (BaseLit.unit.ι (rT := rT)) := (by measurability)

@[fun_prop]
theorem loc.ι.measurable {rT : Type _} [MeasurableSpace rT] :
    Measurable (BaseLit.loc.ι (rT := rT)) := (by measurability)

@[fun_prop]
theorem lbl.ι.measurable {rT : Type _} [MeasurableSpace rT] :
    Measurable (BaseLit.lbl.ι (rT := rT)) := (by measurability)

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

/-! ### Raw-constructor `fun_prop` lemmas. -/

@[fun_prop]
theorem int.measurable {rT : Type _} [MeasurableSpace rT] :
    Measurable (BaseLit.int : Int → BaseLit rT) := int.ι.measurable

@[fun_prop]
theorem bool.measurable {rT : Type _} [MeasurableSpace rT] :
    Measurable (BaseLit.bool : Bool → BaseLit rT) := bool.ι.measurable

@[fun_prop]
theorem loc.measurable {rT : Type _} [MeasurableSpace rT] :
    Measurable (BaseLit.loc : Loc → BaseLit rT) := loc.ι.measurable

@[fun_prop]
theorem lbl.measurable {rT : Type _} [MeasurableSpace rT] :
    Measurable (BaseLit.lbl : Lbl → BaseLit rT) := lbl.ι.measurable

@[fun_prop]
theorem real.measurable {rT : Type _} [MeasurableSpace rT] :
    Measurable (BaseLit.real : rT → BaseLit rT) := real.ι.measurable

/-- Solves `MeasurableEmbedding f` for a discrete-leaf constructor `f`, given the cover's
`_eq_image` lemma and `.measurable` lemma. -/
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

/-- Per-constructor cell family for the `casesOn` preimage decomposition. -/
def decompCell
    {rT : Type _} {α : Type _} (S : Set α)
    (f_int  : Int  → α) (f_bool : Bool → α) (f_unit : Unit → α)
    (f_loc  : Loc  → α) (f_lbl  : Lbl  → α) (f_real : rT → α) : Fin 6 → Set (BaseLit rT) :=
  ![ BaseLit.int.ι  '' (f_int  ⁻¹' S)
   , BaseLit.bool.ι '' (f_bool ⁻¹' S)
   , BaseLit.unit.ι '' (f_unit ⁻¹' S)
   , BaseLit.loc.ι  '' (f_loc  ⁻¹' S)
   , BaseLit.lbl.ι  '' (f_lbl  ⁻¹' S)
   , BaseLit.real.ι '' (f_real ⁻¹' S) ]

theorem casesOn_preimage_decomp
    {rT : Type _} {α : Type _} (S : Set α)
    (f_int  : Int  → α) (f_bool : Bool → α) (f_unit : Unit → α)
    (f_loc  : Loc  → α) (f_lbl  : Lbl  → α) (f_real : rT → α) :
    (fun b : BaseLit rT => BaseLit.casesOn (motive := fun _ => α) b
        f_int f_bool (f_unit ()) f_loc f_lbl f_real) ⁻¹' S
      = ⋃ i, decompCell S f_int f_bool f_unit f_loc f_lbl f_real i := by
  ext b
  simp only [Set.mem_preimage, Set.mem_iUnion, decompCell]
  constructor
  · intro hb; cases b
    · exact ⟨0, _, hb, rfl⟩
    · exact ⟨1, _, hb, rfl⟩
    · exact ⟨2, (), hb, rfl⟩
    · exact ⟨3, _, hb, rfl⟩
    · exact ⟨4, _, hb, rfl⟩
    · exact ⟨5, _, hb, rfl⟩
  · rintro ⟨i, hi⟩; fin_cases i <;>
      · obtain ⟨q, hq, hp⟩ := hi; cases hp; simpa using hq

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
  refine .iUnion fun i => ?_
  fin_cases i
  · exact int.measurableEmbedding.measurableSet_image'   (by measurability)
  · exact bool.measurableEmbedding.measurableSet_image'  (by measurability)
  · exact unit.measurableEmbedding.measurableSet_image'  (by measurability)
  · exact loc.measurableEmbedding.measurableSet_image'   (by measurability)
  · exact lbl.measurableEmbedding.measurableSet_image'   (by measurability)
  · exact real.measurableEmbedding.measurableSet_image'  (h_real hS)

/-- Per-constructor cell family for the `β`-parameterised decomposition. -/
def decompCell_param
    {rT : Type _} {α β : Type _} (S : Set α)
    (f_int  : β × Int  → α) (f_bool : β × Bool → α) (f_unit : β × Unit → α)
    (f_loc  : β × Loc  → α) (f_lbl  : β × Lbl  → α) (f_real : β × rT → α) :
    Fin 6 → Set (BaseLit rT × β) :=
  ![ (fun q : β × Int => (BaseLit.int q.2, q.1))  '' (f_int  ⁻¹' S)
   , (fun q : β × Bool => (BaseLit.bool q.2, q.1)) '' (f_bool ⁻¹' S)
   , (fun q : β × Unit => (BaseLit.unit, q.1))     '' (f_unit ⁻¹' S)
   , (fun q : β × Loc => (BaseLit.loc q.2, q.1))   '' (f_loc  ⁻¹' S)
   , (fun q : β × Lbl => (BaseLit.lbl q.2, q.1))   '' (f_lbl  ⁻¹' S)
   , (fun q : β × rT => (BaseLit.real q.2, q.1))   '' (f_real ⁻¹' S) ]

/-- Joint preimage decomposition for `BaseLit.casesOn` with a `β` parameter. -/
theorem casesOn_preimage_decomp_param
    {rT : Type _} {α β : Type _} (S : Set α)
    (f_int  : β × Int  → α) (f_bool : β × Bool → α) (f_unit : β × Unit → α)
    (f_loc  : β × Loc  → α) (f_lbl  : β × Lbl  → α) (f_real : β × rT → α) :
    (fun p : BaseLit rT × β => BaseLit.casesOn (motive := fun _ => α) p.1
        (fun z => f_int (p.2, z)) (fun b => f_bool (p.2, b))
        (f_unit (p.2, ()))
        (fun l => f_loc (p.2, l)) (fun l => f_lbl (p.2, l))
        (fun r => f_real (p.2, r))) ⁻¹' S
      = ⋃ i, decompCell_param S f_int f_bool f_unit f_loc f_lbl f_real i := by
  ext ⟨b, x⟩
  simp only [Set.mem_preimage, Set.mem_iUnion, decompCell_param]
  constructor
  · intro hb; cases b
    · exact ⟨0, (x, _), hb, rfl⟩
    · exact ⟨1, (x, _), hb, rfl⟩
    · exact ⟨2, (x, ()), hb, rfl⟩
    · exact ⟨3, (x, _), hb, rfl⟩
    · exact ⟨4, (x, _), hb, rfl⟩
    · exact ⟨5, (x, _), hb, rfl⟩
  · rintro ⟨i, hi⟩; fin_cases i <;>
      · obtain ⟨q, hq, hp⟩ := hi; cases hp; simpa using hq

/-- Joint param version of `BaseLit.measurable_rec`. -/
@[fun_prop]
theorem measurable_rec_param
    {rT : Type _} [MeasurableSpace rT] [Inhabited rT]
    {α β : Type _} [MeasurableSpace α] [MeasurableSpace β]
    (c_int  : β × Int  → α) (c_bool : β × Bool → α) (c_unit : β × Unit → α)
    (c_loc  : β × Loc  → α) (c_lbl  : β × Lbl  → α) (c_real : β × rT → α)
    (h_int : Measurable c_int) (h_bool : Measurable c_bool) (h_unit : Measurable c_unit)
    (h_loc : Measurable c_loc) (h_lbl : Measurable c_lbl) (h_real : Measurable c_real) :
    Measurable (fun p : BaseLit rT × β =>
      BaseLit.casesOn (motive := fun _ => α) p.1
        (fun z => c_int (p.2, z)) (fun b => c_bool (p.2, b))
        (c_unit (p.2, ()))
        (fun l => c_loc (p.2, l)) (fun l => c_lbl (p.2, l))
        (fun r => c_real (p.2, r))) := by
  intro S hS
  rw [casesOn_preimage_decomp_param]
  refine .iUnion fun i => ?_
  fin_cases i
  · exact ((int.measurableEmbedding.prodMap (.id (α := β))).comp
      MeasurableEquiv.prodComm.measurableEmbedding).measurableSet_image' (h_int hS)
  · exact ((bool.measurableEmbedding.prodMap (.id (α := β))).comp
      MeasurableEquiv.prodComm.measurableEmbedding).measurableSet_image' (h_bool hS)
  · exact ((unit.measurableEmbedding.prodMap (.id (α := β))).comp
      MeasurableEquiv.prodComm.measurableEmbedding).measurableSet_image' (h_unit hS)
  · exact ((loc.measurableEmbedding.prodMap (.id (α := β))).comp
      MeasurableEquiv.prodComm.measurableEmbedding).measurableSet_image' (h_loc hS)
  · exact ((lbl.measurableEmbedding.prodMap (.id (α := β))).comp
      MeasurableEquiv.prodComm.measurableEmbedding).measurableSet_image' (h_lbl hS)
  · exact ((real.measurableEmbedding.prodMap (.id (α := β))).comp
      MeasurableEquiv.prodComm.measurableEmbedding).measurableSet_image' (h_real hS)

/-! ### Synthetic smoke-test battery

`BaseLit` is non-recursive, so there is no struct-rec keystone; the battery is
phrased through the `casesOn` keystones `measurable_rec` / `measurable_rec_param`.
Each test exercises every constructor slot. -/

/-- Test 1: discrete codomain (`tagDepth : BaseLit rT → Nat`, one tag per constructor;
ignores all payloads, so `f_real` is constant). -/
@[simp] def tagDepth : BaseLit rT → Nat
  | .int _  => 0
  | .bool _ => 1
  | .unit   => 2
  | .loc _  => 3
  | .lbl _  => 4
  | .real _ => 5

theorem tagDepth.measurable [MeasurableSpace rT] [Inhabited rT] :
    Measurable (tagDepth : BaseLit rT → Nat) := by
  have heq : (tagDepth : BaseLit rT → Nat)
    = (fun b : BaseLit rT =>
        BaseLit.casesOn (motive := fun _ => Nat) b
          (fun _ => 0) (fun _ => 1) 2 (fun _ => 3) (fun _ => 4) (fun _ => 5)) := by
    funext b; cases b <;> rfl
  rw [heq]
  apply measurable_rec
    (f_int := fun _ => 0) (f_bool := fun _ => 1)
    (f_unit := fun _ => 2) (f_loc := fun _ => 3) (f_lbl := fun _ => 4)
    (f_real := fun _ => 5)
  fun_prop

/-- Test 2: data-leaf dependent (`countLeaves g`, the `real` payload is mapped through a
measurable `g : rT → Int`; all other constructors return discrete tags). This is the
named equivalent of the original anonymous `measurable_rec` smoke test. -/
@[simp] def countLeaves (g : rT → Int) : BaseLit rT → Int
  | .real r => g r
  | .int n  => n
  | _       => 0

theorem countLeaves.measurable [MeasurableSpace rT] [Inhabited rT] (g : rT → Int)
    (hg : Measurable g) :
    Measurable (countLeaves g : BaseLit rT → Int) := by
  have heq : (countLeaves g : BaseLit rT → Int)
    = (fun b : BaseLit rT =>
        BaseLit.casesOn (motive := fun _ => Int) b
          (fun n => n) (fun _ => 0) 0 (fun _ => 0) (fun _ => 0) g) := by
    funext b; cases b <;> rfl
  rw [heq]
  apply measurable_rec
    (f_int := fun n => n) (f_bool := fun _ => 0)
    (f_unit := fun _ => 0) (f_loc := fun _ => 0) (f_lbl := fun _ => 0)
    (f_real := g)
  exact hg

/-- Test 3: endo-map (`endoMap : BaseLit rT → BaseLit rT`, non-discrete codomain). Since
`BaseLit` is non-recursive this is just a per-constructor relabel via `casesOn`; the
`real` leaf is carried unchanged so the obligation closes through the `real` embedding. -/
@[simp] def endoMap : BaseLit rT → BaseLit rT
  | .int z  => .int z
  | .bool b => .bool b
  | .unit   => .unit
  | .loc l  => .loc l
  | .lbl l  => .lbl l
  | .real r => .real r

theorem endoMap.measurable [MeasurableSpace rT] [Inhabited rT] :
    Measurable (endoMap : BaseLit rT → BaseLit rT) := by
  have heq : (endoMap : BaseLit rT → BaseLit rT)
    = (fun b : BaseLit rT =>
        BaseLit.casesOn (motive := fun _ => BaseLit rT) b
          BaseLit.int BaseLit.bool BaseLit.unit BaseLit.loc BaseLit.lbl BaseLit.real) := by
    funext b; cases b <;> rfl
  rw [heq]
  apply measurable_rec
    (f_int := BaseLit.int) (f_bool := BaseLit.bool)
    (f_unit := fun _ => BaseLit.unit) (f_loc := BaseLit.loc) (f_lbl := BaseLit.lbl)
    (f_real := BaseLit.real)
  exact real.measurable

/-- Test 4: param-threaded (`addAcc : Int → BaseLit rT → Int`, an `Int` accumulator
carried alongside via `measurable_rec_param`; the `int` leaf actually uses both the
payload and the accumulator). -/
@[simp] def addAcc : Int → BaseLit rT → Int
  | acc, .int n  => acc + n
  | acc, _       => acc

theorem addAcc.measurable [MeasurableSpace rT] [Inhabited rT] :
    Measurable (fun p : BaseLit rT × Int => addAcc p.2 p.1) := by
  have heq : (fun p : BaseLit rT × Int => addAcc p.2 p.1)
    = (fun p : BaseLit rT × Int =>
        BaseLit.casesOn (motive := fun _ => Int) p.1
          (fun z => (fun q : Int × Int => q.1 + q.2) (p.2, z))
          (fun b => (fun q : Int × Bool => q.1) (p.2, b))
          ((fun q : Int × Unit => q.1) (p.2, ()))
          (fun l => (fun q : Int × Loc => q.1) (p.2, l))
          (fun l => (fun q : Int × Lbl => q.1) (p.2, l))
          (fun r => (fun q : Int × rT => q.1) (p.2, r))) := by
    funext p; obtain ⟨b, x⟩ := p; cases b <;> rfl
  rw [heq]
  apply measurable_rec_param
    (c_int := fun q : Int × Int => q.1 + q.2)
    (c_bool := fun q : Int × Bool => q.1)
    (c_unit := fun q : Int × Unit => q.1)
    (c_loc := fun q : Int × Loc => q.1)
    (c_lbl := fun q : Int × Lbl => q.1)
    (c_real := fun q : Int × rT => q.1)
  all_goals fun_prop

/-! ### Singleton-class for `BaseLit rT` (lifted from `MeasurableSingletonClass rT`).

This was previously in `Discrete.lean`; moved here so `Recurrences.lean` can use
it for `liftEq.measurable`. -/

/-- Cylinder over `b` that singletons every `real` leaf. -/
@[simp] def singletonCyl {rT : Type _} : BaseLit rT → Cylinder rT
  | .int z      => .int z
  | .bool b     => .bool b
  | .unit       => .unit
  | .loc l      => .loc l
  | .lbl l      => .lbl l
  | .real r     => .real {r}

theorem singletonCyl_flatten {rT : Type _} (b : BaseLit rT) :
    (singletonCyl b).flatten = {b} := by
  induction b with
  | int z => simp
  | bool b => simp
  | unit => simp
  | loc l => simp
  | lbl l => simp
  | real r => simp

theorem singletonCyl_hasMeasurableLeaves
    {rT : Type _} [MeasurableSpace rT] [MeasurableSingletonClass rT] (b : BaseLit rT) :
    (singletonCyl b).HasMeasurableLeaves := by
  induction b with
  | int z => exact .int
  | bool b => exact .bool
  | unit => exact .unit
  | loc l => exact .loc
  | lbl l => exact .lbl
  | real r => exact .real _ (MeasurableSet.singleton r)

instance instMeasurableSingletonClass
    {rT : Type _} [MeasurableSpace rT] [MeasurableSingletonClass rT] :
    MeasurableSingletonClass (BaseLit rT) where
  measurableSet_singleton :=
    Stamp.measurableSet_singleton rfl singletonCyl_flatten singletonCyl_hasMeasurableLeaves

end BaseLit
end ProbLang
end ProbLangMeasures
