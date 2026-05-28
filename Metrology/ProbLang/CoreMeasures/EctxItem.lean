module

import all Mathlib.Tactic.DeriveCountable
public import Metrology.ProbLang.Measure
public import Metrology.ProbLang.Syntax.Syntax
public import Metrology.ProbLang.CoreMeasures.Val

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

/-# Measure space on evaluation-context items. -/

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
      | (obtain ⟨_, _, _, _, rfl⟩ := h; rfl))

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

end EctxItem
end ProbLang
end ProbLangMeasures
