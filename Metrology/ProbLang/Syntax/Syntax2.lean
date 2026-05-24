module

public import Std
public import Std.Data.ExtTreeMap.Lemmas
public import Mathlib.Data.Countable.Basic
public import Mathlib.MeasureTheory.MeasurableSpace.Basic
public import Mathlib.MeasureTheory.MeasurableSpace.Defs
public import Mathlib.Tactic.DeriveCountable
import all Mathlib.Tactic.DeriveCountable
public import Mathlib.Logic.Equiv.List
public import Cslib.Foundations.Data.HasFresh
public import Cslib.Foundations.Syntax.HasSubstitution
public import Mathlib.Probability.ProbabilityMassFunction.Basic
public import Mathlib.Probability.Kernel.Defs
public import Mathlib.Probability.Distributions.Uniform
public import Metrology.ProbLang.Measure

meta import Metrology.Meta

@[expose] public section

open Std
open Cslib

def Std.ExtTreeMap.fresh (t : ExtTreeMap Int V) : Int :=
  match t.maxKey? with | none => 1 | some v => v + 1

theorem Std.ExtTreeMap.fresh_get? (t : ExtTreeMap Int V) :
    t[t.fresh]? = none := by
  unfold ExtTreeMap.fresh
  rcases HM : t.maxKey? with _ | v
  · simp [maxKey?_eq_none_iff.mp HM]
  · apply getElem?_eq_none
    intro hmem
    have hle := ExtTreeMap.le_maxKey?_of_mem hmem (Option.get_of_eq_some (isSome_maxKey?_of_mem hmem) HM)
    simp [compare, compareOfLessAndEq] at hle

-- TODO: PR back to mathlib
instance instCountableChar : Countable Char where
  exists_injective_nat' := by
    exists (·.1.toNat)
    rintro ⟨v1, _⟩ ⟨v2, _⟩
    simp only [Char.mk.injEq]
    exact UInt32.toNat_inj.mp

-- TODO: PR back to mathlib
instance instCountableString : Countable String where
  exists_injective_nat' := by
    have ⟨f, Hf⟩ : Countable (List Char) := by infer_instance
    exists (fun s => f s.toList)
    exact fun _ _ H => String.toList_inj.mp (Hf H)

namespace ProbLang

/-- Free-variable atoms. Strings, when provided by the user, or auto-generated internal
free variables. -/
@[uncurriedProjections, constructors]
inductive Var : Type where
  | named (s : String)
  | internal (n : Nat)
  deriving Inhabited, DecidableEq, Countable, Repr, BEq

instance : Coe String Var := ⟨.named⟩

instance : Coe Nat Var := ⟨.internal⟩

def Var.genId : Var → Nat | .named _ => 0 | .internal n => n

/-- Generate a fresh (internal) free variable. -/
instance : Cslib.HasFresh Var where
  fresh s := .internal <| s.sup (·.genId) + 1
  fresh_notMem L := by
    rw [← Finset.forall_mem_not_eq]
    intro b Hb
    rcases b with (_|n); (· simp)
    simp only [Var.internal.injEq]
    refine Nat.ne_of_gt (Order.lt_add_one_iff.mpr ?_)
    apply Finset.le_sup_of_le Hb
    simp [Var.genId]

abbrev Loc : Type := Int

abbrev Lbl : Type := Int

/-- Type of real numbers equipped with some base sigma algebra.
ProbLang is parameterized by this type, and the type of expressions is discrete
when the type of reals is also discrete.

This allows us to gradually port the development to use a continuous semantics. -/
class ProbLangℝ (T : Type _) extends MeasurableSpace T where

/-- Type of base literals with a given type of reals. Countable etc when rT is. -/
@[uncurriedProjections, curriedProjections, constructors]
inductive BaseLit (rT : Type _)
  | int (z : Int)
  | bool (b : Bool)
  | unit
  | loc (loc : Loc)
  | lbl (lbl : Lbl)
  | real (r : rT)
  -- TEMP for measurability prototyping
  | prod (b1 b2 : BaseLit rT)
  | nest (b : BaseLit rT) (r : rT)
  deriving Countable


end ProbLang

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

-- #synth DiscreteMeasurableSpace Loc

section BaseLit

/-# Measure space on base lits -/

/-- A cylinder is a `BaseLit` whose `rT`-payloads have been replaced by `Set rT`. -/
abbrev BaseLitCyl (rT : Type _) := ProbLang.BaseLit (Set rT)

namespace ProbLang.BaseLit

/-- Interpret a cylinder as the set of `BaseLit rT` it describes. Each branch is the image of
the corresponding constructor over the cartesian product of its arg-sets — singleton sets for
discrete leaves, the carried `Set rT` for real-leaves, and recursive `flatten` for sub-cylinders. -/
@[simp] def flatten {rT : Type _} : BaseLitCyl rT → Set (BaseLit rT)
  | .int z => (BaseLit.int (rT := rT)) '' {z}
  | .bool b => (BaseLit.bool (rT := rT)) '' {b}
  | .unit => (fun _ : Unit => (BaseLit.unit : BaseLit rT)) '' {()}
  | .loc l => (BaseLit.loc (rT := rT)) '' {l}
  | .lbl l => (BaseLit.lbl (rT := rT)) '' {l}
  | .real Sr => (BaseLit.real (rT := rT)) '' Sr
  | .prod c1 c2 =>
      (fun p : BaseLit rT × BaseLit rT => BaseLit.prod p.1 p.2) ''
        (flatten c1 ×ˢ flatten c2)
  | .nest c Sr =>
      (fun p : BaseLit rT × rT => BaseLit.nest p.1 p.2) ''
        (flatten c ×ˢ Sr)

/-- A cylinder has measurable leaves if every `Set rT` it carries is measurable. -/
inductive HasMeasurableLeaves {rT : Type _} [MeasurableSpace rT] :
    BaseLitCyl rT → Prop where
  | int : HasMeasurableLeaves (.int z)
  | bool : HasMeasurableLeaves (.bool b)
  | unit : HasMeasurableLeaves .unit
  | loc : HasMeasurableLeaves (.loc z)
  | lbl : HasMeasurableLeaves (.lbl z)
  | real Sᵣ : MeasurableSet Sᵣ → HasMeasurableLeaves (.real Sᵣ)
  | prod :
    HasMeasurableLeaves c1 →
    HasMeasurableLeaves c2 →
    HasMeasurableLeaves (.prod c1 c2)
  | nest Sᵣ :
    HasMeasurableLeaves c →
    MeasurableSet Sᵣ →
    HasMeasurableLeaves (.nest c Sᵣ)

instance [MeasurableSpace rT] : MeasurableSpace (BaseLit rT) :=
  .generateFrom <| BaseLit.flatten '' { c : BaseLitCyl rT | c.HasMeasurableLeaves }

/-- A shape names which constructor was used at each node of a `BaseLit` tree, with all
`rT`-payloads forgotten. Shapes are `BaseLit Unit`, hence countable. -/
@[simp] def shape : BaseLit rT → BaseLit Unit
  | .int z => .int z
  | .bool b => .bool b
  | .unit => .unit
  | .loc l => .loc l
  | .lbl l => .lbl l
  | .real _ => .real ()
  | .prod b1 b2 => .prod (shape b1) (shape b2)
  | .nest b _ => .nest (shape b) ()

/-- The "universe cylinder" for a given shape: `univ` at every leaf, same skeleton as the shape. -/
@[simp] def shapeCyl : BaseLit Unit → BaseLitCyl rT
  | .int z => .int z
  | .bool b => .bool b
  | .unit => .unit
  | .loc l => .loc l
  | .lbl l => .lbl l
  | .real () => .real Set.univ
  | .prod s1 s2 => .prod (ProbLang.BaseLit.shapeCyl s1) (ProbLang.BaseLit.shapeCyl s2)
  | .nest s () => .nest (ProbLang.BaseLit.shapeCyl s) Set.univ

@[simp] def stratum (s : BaseLit Unit) : Set (BaseLit rT) := shape (rT := rT) ⁻¹' {s}

theorem shapeCyl_HasMeasurableLeaves [MeasurableSpace rT] (s : BaseLit Unit) :
    (shapeCyl (rT := rT) s).HasMeasurableLeaves := by
  induction s <;> constructor <;> measurability

theorem ProbLang.BaseLit.flatten_shapeCyl (s : BaseLit Unit) :
    (shapeCyl (rT := rT) s).flatten = shape ⁻¹' {s} := by
  ext b; induction b generalizing s <;> cases s <;> simp_all

end ProbLang.BaseLit

section Measurability

open ProbLang.BaseLit

theorem BaseLit.flatten_measurable [MeasurableSpace rT] {c : BaseLitCyl rT}
    (hc : c.HasMeasurableLeaves) : MeasurableSet (BaseLit.flatten c) :=
  MeasurableSpace.measurableSet_generateFrom ⟨c, hc, rfl⟩

/-- Each stratum is measurable. -/
theorem ProbLang.BaseLit.stratum_measurable [MeasurableSpace rT] (s : BaseLit Unit) :
    MeasurableSet (shape (rT := rT) ⁻¹' {s}) := by
  rw [← ProbLang.BaseLit.flatten_shapeCyl]
  exact BaseLit.flatten_measurable (shapeCyl_HasMeasurableLeaves s)

/-- Shapes are countable. -/
example : Countable (BaseLit Unit) := inferInstance

/-! ### Covers — sets in `BaseLit rT` cut out by the top-level constructor.

Each cover is defined as a countable union of strata: one stratum per choice of shape for each
recursive sub-`BaseLit` argument of the constructor. Measurability is then immediate. -/

/-- Cover for the `prod` constructor: the union of all `.prod _ _`-shaped strata. -/
def ProbLang.BaseLit.ecov_prod : Set (BaseLit rT) :=
  ⋃ (p : BaseLit Unit × BaseLit Unit), stratum (.prod p.1 p.2)

theorem ProbLang.BaseLit.ecov_prod_measurable [MeasurableSpace rT] :
    MeasurableSet (ProbLang.BaseLit.ecov_prod (rT := rT)) :=
  MeasurableSet.iUnion (fun _ => stratum_measurable _)

/-- The prod-cover is the range of `BaseLit.prod` (derived characterization). -/
theorem ProbLang.BaseLit.ecov_prod_eq_range :
    (ProbLang.BaseLit.ecov_prod (rT := rT))
      = Set.range (fun p : BaseLit rT × BaseLit rT => BaseLit.prod p.1 p.2) := by
  ext b
  simp only [ecov_prod, stratum, Set.mem_iUnion, Set.mem_preimage, Set.mem_singleton_iff,
             Set.mem_range]
  constructor
  · rintro ⟨⟨s1, s2⟩, hb⟩
    cases b with
    | prod b1 b2 => exact ⟨⟨b1, b2⟩, rfl⟩
    | _ => simp [shape] at hb
  · rintro ⟨⟨b1, b2⟩, rfl⟩
    exact ⟨(b1.shape, b2.shape), by simp [shape]⟩

/-- Cover for the `nest` constructor. -/
def ProbLang.BaseLit.ecov_nest : Set (BaseLit rT) :=
  ⋃ (s : BaseLit Unit), stratum (.nest s ())

theorem ProbLang.BaseLit.ecov_nest_measurable [MeasurableSpace rT] :
    MeasurableSet (ProbLang.BaseLit.ecov_nest (rT := rT)) :=
  MeasurableSet.iUnion (fun _ => stratum_measurable _)

/-- The nest-cover is the range of `BaseLit.nest` (derived characterization). -/
theorem ProbLang.BaseLit.ecov_nest_eq_range :
    (ProbLang.BaseLit.ecov_nest (rT := rT))
      = Set.range (fun p : BaseLit rT × rT => BaseLit.nest p.1 p.2) := by
  ext b
  simp only [ecov_nest, stratum, Set.mem_iUnion, Set.mem_preimage, Set.mem_singleton_iff,
             Set.mem_range]
  constructor
  · rintro ⟨s, hb⟩
    cases b with
    | nest b1 r => exact ⟨⟨b1, r⟩, rfl⟩
    | _ => simp [shape] at hb
  · rintro ⟨⟨b1, r⟩, rfl⟩
    exact ⟨b1.shape, by simp [shape]⟩

/-- Default `BaseLit rT` value, used as junk return for off-cover projection cases. -/
instance : Inhabited (BaseLit rT) := ⟨.unit⟩

/-! ### Projections — composed from the metaprogrammed `.π`.
Generic Option-cylinder infrastructure (`OptionCyl`, `Measurable.option_of_cyl_preimages`,
`Set.image_eq_range_inter_preimage_option`, `Measurable.option_map`, `Option.pair`,
`Measurable.option_pair`, `MeasurableEmbedding.some_mk`, `MeasurableSet.singleton_none`)
lives in `Metrology.ProbLang.Measure`. -/

/-- Image of a set under `prod` equals the cover intersected with the projection-preimage. -/
theorem ProbLang.BaseLit.image_prod_eq
    (T : Set (BaseLit rT × BaseLit rT)) :
    (fun p : BaseLit rT × BaseLit rT => BaseLit.prod p.1 p.2) '' T
      = ecov_prod ∩ BaseLit.prod.π ⁻¹' (some '' T) := by
  rw [ecov_prod_eq_range]
  exact Set.image_eq_range_inter_preimage_option _ BaseLit.prod.π (by intro ⟨b1, b2⟩; rfl) T

/-- `BaseLit.prod.π b` agrees with `Option.pair (BaseLit.prod.π.b1 b, BaseLit.prod.π.b2 b)`.

Because `BaseLit.prod.π.b1` and `BaseLit.prod.π.b2` both come from the same underlying `prod.π b`, the joint
function `(BaseLit.prod.π.b1 b, BaseLit.prod.π.b2 b)` is always `(none, none)` or `(some _, some _)` — so the
Option-pairing recovers `BaseLit.prod.π b` exactly. -/
theorem ProbLang.BaseLit.prod_π_eq_pair {rT : Type _} (b : BaseLit rT) :
    BaseLit.prod.π b = Option.pair (BaseLit.prod.π.b1 b, BaseLit.prod.π.b2 b) := by
  cases b with
  | prod b1 b2 =>
    show some (b1, b2) = Option.pair (some b1, some b2)
    rfl
  | int z => rfl
  | bool _ => rfl
  | unit => rfl
  | loc _ => rfl
  | lbl _ => rfl
  | real _ => rfl
  | nest _ _ => rfl

/-- Definitional unfolding of `BaseLit.prod.π.b1` on each constructor. -/
theorem ProbLang.BaseLit.prod_π_b1_def_prod {rT : Type _} (b1 b2 : BaseLit rT) :
    BaseLit.prod.π.b1 (BaseLit.prod b1 b2) = some b1 := rfl
theorem ProbLang.BaseLit.prod_π_b1_def_int {rT : Type _} (z : Int) :
    BaseLit.prod.π.b1 (BaseLit.int z : BaseLit rT) = none := rfl
theorem ProbLang.BaseLit.prod_π_b1_def_bool {rT : Type _} (b : Bool) :
    BaseLit.prod.π.b1 (BaseLit.bool b : BaseLit rT) = none := rfl
theorem ProbLang.BaseLit.prod_π_b1_def_unit {rT : Type _} :
    BaseLit.prod.π.b1 (BaseLit.unit : BaseLit rT) = none := rfl
theorem ProbLang.BaseLit.prod_π_b1_def_loc {rT : Type _} (l : Loc) :
    BaseLit.prod.π.b1 (BaseLit.loc l : BaseLit rT) = none := rfl
theorem ProbLang.BaseLit.prod_π_b1_def_lbl {rT : Type _} (l : Lbl) :
    BaseLit.prod.π.b1 (BaseLit.lbl l : BaseLit rT) = none := rfl
theorem ProbLang.BaseLit.prod_π_b1_def_real {rT : Type _} (r : rT) :
    BaseLit.prod.π.b1 (BaseLit.real r) = none := rfl
theorem ProbLang.BaseLit.prod_π_b1_def_nest {rT : Type _} (b : BaseLit rT) (r : rT) :
    BaseLit.prod.π.b1 (BaseLit.nest b r) = none := rfl

/-- Per-cylinder preimage fact for `BaseLit.prod.π.b1`. -/
theorem ProbLang.BaseLit.prod_π_b1_preimage_some_flatten {rT : Type _}
    (c : BaseLitCyl rT) :
    BaseLit.prod.π.b1 ⁻¹' (some '' BaseLit.flatten c)
      = ⋃ s2 : BaseLit Unit,
          BaseLit.flatten ((BaseLit.prod c (shapeCyl s2)) : BaseLitCyl rT) := by
  ext b
  cases b with
  | prod b1 b2 =>
    rw [Set.mem_preimage, prod_π_b1_def_prod, Set.mem_iUnion]
    constructor
    · rintro ⟨a, ha, heq⟩
      rw [Option.some_inj] at heq
      -- heq : a = b1
      refine ⟨b2.shape, ?_⟩
      simp only [BaseLit.flatten, Set.mem_image, Set.mem_prod]
      refine ⟨(b1, b2), ⟨?_, ?_⟩, rfl⟩
      · rw [← heq]; exact ha
      · rw [ProbLang.BaseLit.flatten_shapeCyl]; rfl
    · rintro ⟨s2, hb2⟩
      simp only [BaseLit.flatten, Set.mem_image, Set.mem_prod] at hb2
      obtain ⟨⟨b1', b2'⟩, ⟨hb1', _⟩, heq⟩ := hb2
      have hp : b1' = b1 ∧ b2' = b2 := by
        have := heq; simp at this; exact this
      obtain ⟨rfl, rfl⟩ := hp
      exact ⟨b1', hb1', rfl⟩
  | int z =>
    rw [Set.mem_preimage, prod_π_b1_def_int, Set.mem_iUnion]
    refine ⟨?_, ?_⟩
    · rintro ⟨a, _, hcontr⟩; exact absurd hcontr (Option.some_ne_none _)
    · rintro ⟨s2, hb2⟩
      simp [BaseLit.flatten] at hb2
  | bool b =>
    rw [Set.mem_preimage, prod_π_b1_def_bool, Set.mem_iUnion]
    refine ⟨?_, ?_⟩
    · rintro ⟨a, _, hcontr⟩; exact absurd hcontr (Option.some_ne_none _)
    · rintro ⟨s2, hb2⟩
      simp [BaseLit.flatten] at hb2
  | unit =>
    rw [Set.mem_preimage, prod_π_b1_def_unit, Set.mem_iUnion]
    refine ⟨?_, ?_⟩
    · rintro ⟨a, _, hcontr⟩; exact absurd hcontr (Option.some_ne_none _)
    · rintro ⟨s2, hb2⟩
      simp [BaseLit.flatten] at hb2
  | loc l =>
    rw [Set.mem_preimage, prod_π_b1_def_loc, Set.mem_iUnion]
    refine ⟨?_, ?_⟩
    · rintro ⟨a, _, hcontr⟩; exact absurd hcontr (Option.some_ne_none _)
    · rintro ⟨s2, hb2⟩
      simp [BaseLit.flatten] at hb2
  | lbl l =>
    rw [Set.mem_preimage, prod_π_b1_def_lbl, Set.mem_iUnion]
    refine ⟨?_, ?_⟩
    · rintro ⟨a, _, hcontr⟩; exact absurd hcontr (Option.some_ne_none _)
    · rintro ⟨s2, hb2⟩
      simp [BaseLit.flatten] at hb2
  | real r =>
    rw [Set.mem_preimage, prod_π_b1_def_real, Set.mem_iUnion]
    refine ⟨?_, ?_⟩
    · rintro ⟨a, _, hcontr⟩; exact absurd hcontr (Option.some_ne_none _)
    · rintro ⟨s2, hb2⟩
      simp [BaseLit.flatten] at hb2
  | nest b r =>
    rw [Set.mem_preimage, prod_π_b1_def_nest, Set.mem_iUnion]
    refine ⟨?_, ?_⟩
    · rintro ⟨a, _, hcontr⟩; exact absurd hcontr (Option.some_ne_none _)
    · rintro ⟨s2, hb2⟩
      simp [BaseLit.flatten] at hb2

/-- Measurability of `BaseLit.prod.π.b1`. Per-cylinder preimage is a countable union of cylinders;
σ-algebra induction extends to arbitrary measurable codomain sets. -/
theorem ProbLang.BaseLit.measurable_prod_π_b1 [MeasurableSpace rT] :
    Measurable (BaseLit.prod.π.b1 : BaseLit rT → Option (BaseLit rT)) := by
  apply Measurable.option_of_cyl_preimages
  rintro (_ | S) hc
  · -- BaseLit.prod.π.b1⁻¹' {none} = ecov_prodᶜ
    have hrw : BaseLit.prod.π.b1 ⁻¹' (OptionCyl.flatten (none : OptionCyl (BaseLit rT)))
             = (ecov_prod : Set (BaseLit rT))ᶜ := by
      ext b
      simp only [OptionCyl.flatten, Set.mem_preimage, Set.mem_singleton_iff,
                 Set.mem_compl_iff, ecov_prod, stratum, Set.mem_iUnion,
                 Set.mem_preimage, Set.mem_singleton_iff]
      cases b with
      | prod b1 b2 =>
        rw [prod_π_b1_def_prod]
        refine ⟨?_, ?_⟩
        · intro hcontr; exact absurd hcontr (Option.some_ne_none _)
        · intro hne
          exfalso; apply hne; exact ⟨(b1.shape, b2.shape), by simp [shape]⟩
      | int z =>
        rw [prod_π_b1_def_int]
        refine ⟨fun _ => ?_, fun _ => rfl⟩
        rintro ⟨⟨s1, s2⟩, hb⟩; simp [shape] at hb
      | bool b =>
        rw [prod_π_b1_def_bool]
        refine ⟨fun _ => ?_, fun _ => rfl⟩
        rintro ⟨⟨s1, s2⟩, hb⟩; simp [shape] at hb
      | unit =>
        rw [prod_π_b1_def_unit]
        refine ⟨fun _ => ?_, fun _ => rfl⟩
        rintro ⟨⟨s1, s2⟩, hb⟩; simp [shape] at hb
      | loc l =>
        rw [prod_π_b1_def_loc]
        refine ⟨fun _ => ?_, fun _ => rfl⟩
        rintro ⟨⟨s1, s2⟩, hb⟩; simp [shape] at hb
      | lbl l =>
        rw [prod_π_b1_def_lbl]
        refine ⟨fun _ => ?_, fun _ => rfl⟩
        rintro ⟨⟨s1, s2⟩, hb⟩; simp [shape] at hb
      | real r =>
        rw [prod_π_b1_def_real]
        refine ⟨fun _ => ?_, fun _ => rfl⟩
        rintro ⟨⟨s1, s2⟩, hb⟩; simp [shape] at hb
      | nest b r =>
        rw [prod_π_b1_def_nest]
        refine ⟨fun _ => ?_, fun _ => rfl⟩
        rintro ⟨⟨s1, s2⟩, hb⟩; simp [shape] at hb
    rw [hrw]; exact ecov_prod_measurable.compl
  · -- BaseLit.prod.π.b1⁻¹' (some '' S) for measurable S ⊆ BaseLit rT.
    -- By σ-algebra induction on S: base case is S = flatten c for c ∈ HasMeasurableLeaves.
    cases hc with
    | some hS =>
      -- Use generic σ-algebra induction: predicate P(S) := MeasurableSet (BaseLit.prod.π.b1⁻¹' (some '' S))
      -- holds on cylinders (load-bearing fact) and is closed under σ-alg operations.
      have P_holds : ∀ S : Set (BaseLit rT), MeasurableSet S →
                       MeasurableSet (BaseLit.prod.π.b1 ⁻¹' (some '' S)) := by
        intro S hS
        induction hS with
        | basic G hG =>
          obtain ⟨c, hc, rfl⟩ := hG
          rw [prod_π_b1_preimage_some_flatten c]
          exact MeasurableSet.iUnion fun s2 =>
            BaseLit.flatten_measurable (.prod hc (shapeCyl_HasMeasurableLeaves s2))
        | empty =>
          simp [Set.image_empty]
        | compl G _ ih =>
          -- BaseLit.prod.π.b1⁻¹' (some '' Gᶜ) = (BaseLit.prod.π.b1⁻¹' (some '' G))ᶜ ∩ (BaseLit.prod.π.b1⁻¹' (range some))
          -- = (BaseLit.prod.π.b1⁻¹' (some '' G))ᶜ ∩ ecov_prod
          have hrange : (some : BaseLit rT → Option (BaseLit rT)) '' Gᶜ
                      = (some '' Set.univ) \ (some '' G) := by
            ext x
            cases x with
            | none => simp
            | some a =>
              simp only [Set.mem_image, Set.mem_diff, Set.mem_univ, Set.mem_compl_iff]
              refine ⟨?_, ?_⟩
              · rintro ⟨a', ha', heq⟩
                refine ⟨⟨a', trivial, heq⟩, ?_⟩
                rintro ⟨a'', ha'', heq2⟩
                rw [Option.some_inj] at heq
                rw [Option.some_inj] at heq2
                rw [← heq2] at heq
                exact ha' (heq ▸ ha'')
              · rintro ⟨_, hne⟩
                refine ⟨a, ?_, rfl⟩
                intro hG
                exact hne ⟨a, hG, rfl⟩
          rw [hrange, Set.preimage_diff]
          have h_univ : MeasurableSet (BaseLit.prod.π.b1 ⁻¹' (some '' (Set.univ : Set (BaseLit rT)))) := by
            -- some '' univ = (singleton none)ᶜ in Option α. Preimage under BaseLit.prod.π.b1 = ecov_prod
            -- (where BaseLit.prod.π.b1 returns some _, i.e., the prod constructor).
            have hrange : (some : BaseLit rT → Option (BaseLit rT)) '' Set.univ
                        = {none}ᶜ := by
              ext x
              cases x with
              | none => simp
              | some a => simp
            rw [hrange]
            rw [Set.preimage_compl]
            -- BaseLit.prod.π.b1⁻¹' {none} = ecov_prodᶜ; complement = ecov_prod.
            have hnone_eq : BaseLit.prod.π.b1 ⁻¹' ({none} : Set (Option (BaseLit rT)))
                          = (ecov_prod : Set (BaseLit rT))ᶜ := by
              ext b
              cases b with
              | prod b1 b2 =>
                rw [Set.mem_preimage, prod_π_b1_def_prod]
                simp only [Set.mem_singleton_iff, Set.mem_compl_iff, ecov_prod, Set.mem_iUnion]
                refine ⟨?_, ?_⟩
                · intro hcontr; exact absurd hcontr (Option.some_ne_none _)
                · intro hne
                  exfalso; apply hne
                  exact ⟨(b1.shape, b2.shape), by simp [stratum, shape]⟩
              | int z =>
                rw [Set.mem_preimage, prod_π_b1_def_int]
                simp only [Set.mem_singleton_iff, Set.mem_compl_iff, ecov_prod, Set.mem_iUnion]
                refine ⟨fun _ => ?_, fun _ => trivial⟩
                rintro ⟨⟨s1, s2⟩, hb⟩; simp [stratum, shape] at hb
              | bool b =>
                rw [Set.mem_preimage, prod_π_b1_def_bool]
                simp only [Set.mem_singleton_iff, Set.mem_compl_iff, ecov_prod, Set.mem_iUnion]
                refine ⟨fun _ => ?_, fun _ => trivial⟩
                rintro ⟨⟨s1, s2⟩, hb⟩; simp [stratum, shape] at hb
              | unit =>
                rw [Set.mem_preimage, prod_π_b1_def_unit]
                simp only [Set.mem_singleton_iff, Set.mem_compl_iff, ecov_prod, Set.mem_iUnion]
                refine ⟨fun _ => ?_, fun _ => trivial⟩
                rintro ⟨⟨s1, s2⟩, hb⟩; simp [stratum, shape] at hb
              | loc l =>
                rw [Set.mem_preimage, prod_π_b1_def_loc]
                simp only [Set.mem_singleton_iff, Set.mem_compl_iff, ecov_prod, Set.mem_iUnion]
                refine ⟨fun _ => ?_, fun _ => trivial⟩
                rintro ⟨⟨s1, s2⟩, hb⟩; simp [stratum, shape] at hb
              | lbl l =>
                rw [Set.mem_preimage, prod_π_b1_def_lbl]
                simp only [Set.mem_singleton_iff, Set.mem_compl_iff, ecov_prod, Set.mem_iUnion]
                refine ⟨fun _ => ?_, fun _ => trivial⟩
                rintro ⟨⟨s1, s2⟩, hb⟩; simp [stratum, shape] at hb
              | real r =>
                rw [Set.mem_preimage, prod_π_b1_def_real]
                simp only [Set.mem_singleton_iff, Set.mem_compl_iff, ecov_prod, Set.mem_iUnion]
                refine ⟨fun _ => ?_, fun _ => trivial⟩
                rintro ⟨⟨s1, s2⟩, hb⟩; simp [stratum, shape] at hb
              | nest b r =>
                rw [Set.mem_preimage, prod_π_b1_def_nest]
                simp only [Set.mem_singleton_iff, Set.mem_compl_iff, ecov_prod, Set.mem_iUnion]
                refine ⟨fun _ => ?_, fun _ => trivial⟩
                rintro ⟨⟨s1, s2⟩, hb⟩; simp [stratum, shape] at hb
            rw [hnone_eq]
            simp
            exact ecov_prod_measurable
          exact h_univ.diff ih
        | iUnion f _ ih =>
          -- some '' (⋃ f) = ⋃ (some '' f)
          rw [Set.image_iUnion, Set.preimage_iUnion]
          exact MeasurableSet.iUnion ih
      exact P_holds S hS

/-- Definitional unfolding of `BaseLit.prod.π.b2` on each constructor. -/
theorem ProbLang.BaseLit.prod_π_b2_def_prod {rT : Type _} (b1 b2 : BaseLit rT) :
    BaseLit.prod.π.b2 (BaseLit.prod b1 b2) = some b2 := rfl
theorem ProbLang.BaseLit.prod_π_b2_def_int {rT : Type _} (z : Int) :
    BaseLit.prod.π.b2 (BaseLit.int z : BaseLit rT) = none := rfl
theorem ProbLang.BaseLit.prod_π_b2_def_bool {rT : Type _} (b : Bool) :
    BaseLit.prod.π.b2 (BaseLit.bool b : BaseLit rT) = none := rfl
theorem ProbLang.BaseLit.prod_π_b2_def_unit {rT : Type _} :
    BaseLit.prod.π.b2 (BaseLit.unit : BaseLit rT) = none := rfl
theorem ProbLang.BaseLit.prod_π_b2_def_loc {rT : Type _} (l : Loc) :
    BaseLit.prod.π.b2 (BaseLit.loc l : BaseLit rT) = none := rfl
theorem ProbLang.BaseLit.prod_π_b2_def_lbl {rT : Type _} (l : Lbl) :
    BaseLit.prod.π.b2 (BaseLit.lbl l : BaseLit rT) = none := rfl
theorem ProbLang.BaseLit.prod_π_b2_def_real {rT : Type _} (r : rT) :
    BaseLit.prod.π.b2 (BaseLit.real r) = none := rfl
theorem ProbLang.BaseLit.prod_π_b2_def_nest {rT : Type _} (b : BaseLit rT) (r : rT) :
    BaseLit.prod.π.b2 (BaseLit.nest b r) = none := rfl

/-- Per-cylinder preimage fact for `BaseLit.prod.π.b2`. -/
theorem ProbLang.BaseLit.prod_π_b2_preimage_some_flatten {rT : Type _}
    (c : BaseLitCyl rT) :
    BaseLit.prod.π.b2 ⁻¹' (some '' BaseLit.flatten c)
      = ⋃ s1 : BaseLit Unit,
          BaseLit.flatten ((BaseLit.prod (shapeCyl s1) c) : BaseLitCyl rT) := by
  ext b
  cases b with
  | prod b1 b2 =>
    rw [Set.mem_preimage, prod_π_b2_def_prod, Set.mem_iUnion]
    constructor
    · rintro ⟨a, ha, heq⟩
      rw [Option.some_inj] at heq
      refine ⟨b1.shape, ?_⟩
      simp only [BaseLit.flatten, Set.mem_image, Set.mem_prod]
      refine ⟨(b1, b2), ⟨?_, ?_⟩, rfl⟩
      · rw [ProbLang.BaseLit.flatten_shapeCyl]; rfl
      · rw [← heq]; exact ha
    · rintro ⟨s1, hb2⟩
      simp only [BaseLit.flatten, Set.mem_image, Set.mem_prod] at hb2
      obtain ⟨⟨b1', b2'⟩, ⟨_, hb2'⟩, heq⟩ := hb2
      have hp : b1' = b1 ∧ b2' = b2 := by
        have := heq; simp at this; exact this
      obtain ⟨rfl, rfl⟩ := hp
      exact ⟨b2', hb2', rfl⟩
  | int z =>
    rw [Set.mem_preimage, prod_π_b2_def_int, Set.mem_iUnion]
    refine ⟨?_, ?_⟩
    · rintro ⟨a, _, hcontr⟩; exact absurd hcontr (Option.some_ne_none _)
    · rintro ⟨s1, hb2⟩; simp [BaseLit.flatten] at hb2
  | bool b =>
    rw [Set.mem_preimage, prod_π_b2_def_bool, Set.mem_iUnion]
    refine ⟨?_, ?_⟩
    · rintro ⟨a, _, hcontr⟩; exact absurd hcontr (Option.some_ne_none _)
    · rintro ⟨s1, hb2⟩; simp [BaseLit.flatten] at hb2
  | unit =>
    rw [Set.mem_preimage, prod_π_b2_def_unit, Set.mem_iUnion]
    refine ⟨?_, ?_⟩
    · rintro ⟨a, _, hcontr⟩; exact absurd hcontr (Option.some_ne_none _)
    · rintro ⟨s1, hb2⟩; simp [BaseLit.flatten] at hb2
  | loc l =>
    rw [Set.mem_preimage, prod_π_b2_def_loc, Set.mem_iUnion]
    refine ⟨?_, ?_⟩
    · rintro ⟨a, _, hcontr⟩; exact absurd hcontr (Option.some_ne_none _)
    · rintro ⟨s1, hb2⟩; simp [BaseLit.flatten] at hb2
  | lbl l =>
    rw [Set.mem_preimage, prod_π_b2_def_lbl, Set.mem_iUnion]
    refine ⟨?_, ?_⟩
    · rintro ⟨a, _, hcontr⟩; exact absurd hcontr (Option.some_ne_none _)
    · rintro ⟨s1, hb2⟩; simp [BaseLit.flatten] at hb2
  | real r =>
    rw [Set.mem_preimage, prod_π_b2_def_real, Set.mem_iUnion]
    refine ⟨?_, ?_⟩
    · rintro ⟨a, _, hcontr⟩; exact absurd hcontr (Option.some_ne_none _)
    · rintro ⟨s1, hb2⟩; simp [BaseLit.flatten] at hb2
  | nest b r =>
    rw [Set.mem_preimage, prod_π_b2_def_nest, Set.mem_iUnion]
    refine ⟨?_, ?_⟩
    · rintro ⟨a, _, hcontr⟩; exact absurd hcontr (Option.some_ne_none _)
    · rintro ⟨s1, hb2⟩; simp [BaseLit.flatten] at hb2

/-- Symmetric for the second projection. -/
theorem ProbLang.BaseLit.measurable_prod_π_b2 [MeasurableSpace rT] :
    Measurable (BaseLit.prod.π.b2 : BaseLit rT → Option (BaseLit rT)) := by
  apply Measurable.option_of_cyl_preimages
  rintro (_ | S) hc
  · -- BaseLit.prod.π.b2⁻¹' {none} = ecov_prodᶜ (same shape as BaseLit.prod.π.b1)
    have hrw : BaseLit.prod.π.b2 ⁻¹' (OptionCyl.flatten (none : OptionCyl (BaseLit rT)))
             = (ecov_prod : Set (BaseLit rT))ᶜ := by
      ext b
      simp only [OptionCyl.flatten, Set.mem_preimage, Set.mem_singleton_iff,
                 Set.mem_compl_iff, ecov_prod, stratum, Set.mem_iUnion,
                 Set.mem_preimage, Set.mem_singleton_iff]
      cases b with
      | prod b1 b2 =>
        rw [prod_π_b2_def_prod]
        refine ⟨?_, ?_⟩
        · intro hcontr; exact absurd hcontr (Option.some_ne_none _)
        · intro hne
          exfalso; apply hne; exact ⟨(b1.shape, b2.shape), by simp [shape]⟩
      | int z =>
        rw [prod_π_b2_def_int]
        refine ⟨fun _ => ?_, fun _ => rfl⟩
        rintro ⟨⟨s1, s2⟩, hb⟩; simp [shape] at hb
      | bool b =>
        rw [prod_π_b2_def_bool]
        refine ⟨fun _ => ?_, fun _ => rfl⟩
        rintro ⟨⟨s1, s2⟩, hb⟩; simp [shape] at hb
      | unit =>
        rw [prod_π_b2_def_unit]
        refine ⟨fun _ => ?_, fun _ => rfl⟩
        rintro ⟨⟨s1, s2⟩, hb⟩; simp [shape] at hb
      | loc l =>
        rw [prod_π_b2_def_loc]
        refine ⟨fun _ => ?_, fun _ => rfl⟩
        rintro ⟨⟨s1, s2⟩, hb⟩; simp [shape] at hb
      | lbl l =>
        rw [prod_π_b2_def_lbl]
        refine ⟨fun _ => ?_, fun _ => rfl⟩
        rintro ⟨⟨s1, s2⟩, hb⟩; simp [shape] at hb
      | real r =>
        rw [prod_π_b2_def_real]
        refine ⟨fun _ => ?_, fun _ => rfl⟩
        rintro ⟨⟨s1, s2⟩, hb⟩; simp [shape] at hb
      | nest b r =>
        rw [prod_π_b2_def_nest]
        refine ⟨fun _ => ?_, fun _ => rfl⟩
        rintro ⟨⟨s1, s2⟩, hb⟩; simp [shape] at hb
    rw [hrw]; exact ecov_prod_measurable.compl
  · -- BaseLit.prod.π.b2⁻¹' (some '' S) for measurable S. Same σ-alg induction shape as BaseLit.prod.π.b1.
    cases hc with
    | some hS =>
      have P_holds : ∀ S : Set (BaseLit rT), MeasurableSet S →
                       MeasurableSet (BaseLit.prod.π.b2 ⁻¹' (some '' S)) := by
        intro S hS
        induction hS with
        | basic G hG =>
          obtain ⟨c, hc, rfl⟩ := hG
          rw [prod_π_b2_preimage_some_flatten c]
          exact MeasurableSet.iUnion fun s1 =>
            BaseLit.flatten_measurable (.prod (shapeCyl_HasMeasurableLeaves s1) hc)
        | empty =>
          simp [Set.image_empty]
        | compl G _ ih =>
          have hrange : (some : BaseLit rT → Option (BaseLit rT)) '' Gᶜ
                      = (some '' Set.univ) \ (some '' G) := by
            ext x
            cases x with
            | none => simp
            | some a =>
              simp only [Set.mem_image, Set.mem_diff, Set.mem_univ, Set.mem_compl_iff]
              refine ⟨?_, ?_⟩
              · rintro ⟨a', ha', heq⟩
                refine ⟨⟨a', trivial, heq⟩, ?_⟩
                rintro ⟨a'', ha'', heq2⟩
                rw [Option.some_inj] at heq
                rw [Option.some_inj] at heq2
                rw [← heq2] at heq
                exact ha' (heq ▸ ha'')
              · rintro ⟨_, hne⟩
                refine ⟨a, ?_, rfl⟩
                intro hG
                exact hne ⟨a, hG, rfl⟩
          rw [hrange, Set.preimage_diff]
          have h_univ : MeasurableSet (BaseLit.prod.π.b2 ⁻¹' (some '' (Set.univ : Set (BaseLit rT)))) := by
            have hrange : (some : BaseLit rT → Option (BaseLit rT)) '' Set.univ
                        = {none}ᶜ := by
              ext x
              cases x with
              | none => simp
              | some a => simp
            rw [hrange]
            rw [Set.preimage_compl]
            have hnone_eq : BaseLit.prod.π.b2 ⁻¹' ({none} : Set (Option (BaseLit rT)))
                          = (ecov_prod : Set (BaseLit rT))ᶜ := by
              ext b
              cases b with
              | prod b1 b2 =>
                rw [Set.mem_preimage, prod_π_b2_def_prod]
                simp only [Set.mem_singleton_iff, Set.mem_compl_iff, ecov_prod, Set.mem_iUnion]
                refine ⟨?_, ?_⟩
                · intro hcontr; exact absurd hcontr (Option.some_ne_none _)
                · intro hne
                  exfalso; apply hne
                  exact ⟨(b1.shape, b2.shape), by simp [stratum, shape]⟩
              | int z =>
                rw [Set.mem_preimage, prod_π_b2_def_int]
                simp only [Set.mem_singleton_iff, Set.mem_compl_iff, ecov_prod, Set.mem_iUnion]
                refine ⟨fun _ => ?_, fun _ => trivial⟩
                rintro ⟨⟨s1, s2⟩, hb⟩; simp [stratum, shape] at hb
              | bool b =>
                rw [Set.mem_preimage, prod_π_b2_def_bool]
                simp only [Set.mem_singleton_iff, Set.mem_compl_iff, ecov_prod, Set.mem_iUnion]
                refine ⟨fun _ => ?_, fun _ => trivial⟩
                rintro ⟨⟨s1, s2⟩, hb⟩; simp [stratum, shape] at hb
              | unit =>
                rw [Set.mem_preimage, prod_π_b2_def_unit]
                simp only [Set.mem_singleton_iff, Set.mem_compl_iff, ecov_prod, Set.mem_iUnion]
                refine ⟨fun _ => ?_, fun _ => trivial⟩
                rintro ⟨⟨s1, s2⟩, hb⟩; simp [stratum, shape] at hb
              | loc l =>
                rw [Set.mem_preimage, prod_π_b2_def_loc]
                simp only [Set.mem_singleton_iff, Set.mem_compl_iff, ecov_prod, Set.mem_iUnion]
                refine ⟨fun _ => ?_, fun _ => trivial⟩
                rintro ⟨⟨s1, s2⟩, hb⟩; simp [stratum, shape] at hb
              | lbl l =>
                rw [Set.mem_preimage, prod_π_b2_def_lbl]
                simp only [Set.mem_singleton_iff, Set.mem_compl_iff, ecov_prod, Set.mem_iUnion]
                refine ⟨fun _ => ?_, fun _ => trivial⟩
                rintro ⟨⟨s1, s2⟩, hb⟩; simp [stratum, shape] at hb
              | real r =>
                rw [Set.mem_preimage, prod_π_b2_def_real]
                simp only [Set.mem_singleton_iff, Set.mem_compl_iff, ecov_prod, Set.mem_iUnion]
                refine ⟨fun _ => ?_, fun _ => trivial⟩
                rintro ⟨⟨s1, s2⟩, hb⟩; simp [stratum, shape] at hb
              | nest b r =>
                rw [Set.mem_preimage, prod_π_b2_def_nest]
                simp only [Set.mem_singleton_iff, Set.mem_compl_iff, ecov_prod, Set.mem_iUnion]
                refine ⟨fun _ => ?_, fun _ => trivial⟩
                rintro ⟨⟨s1, s2⟩, hb⟩; simp [stratum, shape] at hb
            rw [hnone_eq]
            simp
            exact ecov_prod_measurable
          exact h_univ.diff ih
        | iUnion f _ ih =>
          rw [Set.image_iUnion, Set.preimage_iUnion]
          exact MeasurableSet.iUnion ih
      exact P_holds S hS

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
    have hext : cov ∩ f ⁻¹' G'ᶜ = cov \ (cov ∩ f ⁻¹' G') := by
      ext b; constructor
      · rintro ⟨hc, hG'⟩
        exact ⟨hc, fun ⟨_, hG''⟩ => hG' hG''⟩
      · rintro ⟨hc, hne⟩
        exact ⟨hc, fun h => hne ⟨hc, h⟩⟩
    rw [hext]; exact hcov.diff ih
  | iUnion G' _ ih =>
    have hext : cov ∩ f ⁻¹' (⋃ i, G' i) = ⋃ i, cov ∩ f ⁻¹' G' i := by
      ext b; simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_iUnion]
      exact ⟨fun ⟨hc, i, hin⟩ => ⟨i, hc, hin⟩, fun ⟨i, hc, hin⟩ => ⟨hc, i, hin⟩⟩
    rw [hext]; exact .iUnion ih

/-- Specialization to the `BaseLit rT` σ-algebra (a cylinder-generated σ-algebra). -/
theorem ProbLang.BaseLit.cover_meas_of_gen [MeasurableSpace rT]
    (cov : Set (BaseLit rT)) (hcov : MeasurableSet cov)
    (f : BaseLit rT → BaseLit rT)
    (hgen : ∀ c, c.HasMeasurableLeaves → MeasurableSet (cov ∩ f ⁻¹' BaseLit.flatten c)) :
    ∀ G : Set (BaseLit rT), MeasurableSet G → MeasurableSet (cov ∩ f ⁻¹' G) := by
  refine MeasurableSet.cover_inter_preimage_of_gen rfl hcov f ?_
  rintro _ ⟨c, hc, rfl⟩
  exact hgen c hc

/-- **Subtype-restricted measurability from cover-restricted measurability.**

If `cov ⊆ α` is measurable and `cov ∩ f⁻¹' G` is measurable for every measurable `G ⊆ β`,
then the subtype-restricted function `↥cov → β` is measurable. -/
theorem Measurable.of_cover_inter_preimage
    {α β : Type _} [MeasurableSpace α] [MeasurableSpace β]
    {cov : Set α} {f : α → β}
    (h : ∀ G : Set β, MeasurableSet G → MeasurableSet (cov ∩ f ⁻¹' G)) :
    Measurable (fun (b : ↥cov) => f b.val) := by
  intro G hG
  have hext : (fun (b : ↥cov) => f b.val) ⁻¹' G
            = (Subtype.val : ↥cov → α) ⁻¹' (cov ∩ f ⁻¹' G) := by
    ext ⟨b, hb⟩
    simp only [Set.mem_preimage, Set.mem_inter_iff]
    exact ⟨fun h => ⟨hb, h⟩, fun ⟨_, h⟩ => h⟩
  rw [hext]
  exact MeasurableSet.preimage (h G hG) measurable_subtype_coe

/-- **Cover-restricted measurability from subtype-restricted measurability** (the converse). -/
theorem MeasurableSet.cover_inter_preimage_of_subtype
    {α β : Type _} [MeasurableSpace α] [MeasurableSpace β]
    {cov : Set α} (hcov : MeasurableSet cov) {f : α → β}
    (h : Measurable (fun (b : ↥cov) => f b.val)) :
    ∀ G : Set β, MeasurableSet G → MeasurableSet (cov ∩ f ⁻¹' G) := by
  intro G hG
  have hsub : MeasurableSet ((fun (b : ↥cov) => f b.val) ⁻¹' G) := h hG
  have hext : (fun (b : ↥cov) => f b.val) ⁻¹' G
            = (Subtype.val : ↥cov → α) ⁻¹' (cov ∩ f ⁻¹' G) := by
    ext ⟨b, hb⟩
    simp only [Set.mem_preimage, Set.mem_inter_iff]
    exact ⟨fun h => ⟨hb, h⟩, fun ⟨_, h⟩ => h⟩
  rw [hext] at hsub
  rw [show cov ∩ f ⁻¹' G
        = Subtype.val '' ((Subtype.val : ↥cov → α) ⁻¹' (cov ∩ f ⁻¹' G)) by
      rw [Subtype.image_preimage_coe, ← Set.inter_assoc, Set.inter_self]]
  exact MeasurableSet.subtype_image hcov hsub

/-- Global measurability of `BaseLit.prod.π`, derived from per-component measurabilities. -/
theorem ProbLang.BaseLit.measurable_prod_π [MeasurableSpace rT] :
    Measurable (BaseLit.prod.π : BaseLit rT → Option (BaseLit rT × BaseLit rT)) := by
  have hrw : (BaseLit.prod.π : BaseLit rT → Option (BaseLit rT × BaseLit rT))
           = Option.pair ∘ (fun b => (BaseLit.prod.π.b1 b, BaseLit.prod.π.b2 b)) := by
    funext b; exact prod_π_eq_pair b
  rw [hrw]
  exact Measurable.option_pair.comp (Measurable.prodMk measurable_prod_π_b1 measurable_prod_π_b2)

/-- Image of a set under `nest` equals the cover intersected with the projection-preimage. -/
theorem ProbLang.BaseLit.image_nest_eq
    (T : Set (BaseLit rT × rT)) :
    (fun p : BaseLit rT × rT => BaseLit.nest p.1 p.2) '' T
      = ecov_nest ∩ BaseLit.nest.π ⁻¹' (some '' T) := by
  rw [ecov_nest_eq_range]
  exact Set.image_eq_range_inter_preimage_option _ BaseLit.nest.π (by intro ⟨b1, r⟩; rfl) T

/-- Definitional unfolding of `BaseLit.nest.π.b` on each constructor. -/
theorem ProbLang.BaseLit.nest_π_b_def_nest {rT : Type _} (b : BaseLit rT) (r : rT) :
    BaseLit.nest.π.b (BaseLit.nest b r) = some b := rfl
theorem ProbLang.BaseLit.nest_π_b_def_int {rT : Type _} (z : Int) :
    BaseLit.nest.π.b (BaseLit.int z : BaseLit rT) = none := rfl
theorem ProbLang.BaseLit.nest_π_b_def_bool {rT : Type _} (b : Bool) :
    BaseLit.nest.π.b (BaseLit.bool b : BaseLit rT) = none := rfl
theorem ProbLang.BaseLit.nest_π_b_def_unit {rT : Type _} :
    BaseLit.nest.π.b (BaseLit.unit : BaseLit rT) = none := rfl
theorem ProbLang.BaseLit.nest_π_b_def_loc {rT : Type _} (l : Loc) :
    BaseLit.nest.π.b (BaseLit.loc l : BaseLit rT) = none := rfl
theorem ProbLang.BaseLit.nest_π_b_def_lbl {rT : Type _} (l : Lbl) :
    BaseLit.nest.π.b (BaseLit.lbl l : BaseLit rT) = none := rfl
theorem ProbLang.BaseLit.nest_π_b_def_real {rT : Type _} (r : rT) :
    BaseLit.nest.π.b (BaseLit.real r) = none := rfl
theorem ProbLang.BaseLit.nest_π_b_def_prod {rT : Type _} (b1 b2 : BaseLit rT) :
    BaseLit.nest.π.b (BaseLit.prod b1 b2) = none := rfl

/-- Definitional unfolding of `BaseLit.nest.π.r` on each constructor. -/
theorem ProbLang.BaseLit.nest_π_r_def_nest {rT : Type _} (b : BaseLit rT) (r : rT) :
    BaseLit.nest.π.r (BaseLit.nest b r) = some r := rfl
theorem ProbLang.BaseLit.nest_π_r_def_int {rT : Type _} (z : Int) :
    BaseLit.nest.π.r (BaseLit.int z : BaseLit rT) = none := rfl
theorem ProbLang.BaseLit.nest_π_r_def_bool {rT : Type _} (b : Bool) :
    BaseLit.nest.π.r (BaseLit.bool b : BaseLit rT) = none := rfl
theorem ProbLang.BaseLit.nest_π_r_def_unit {rT : Type _} :
    BaseLit.nest.π.r (BaseLit.unit : BaseLit rT) = none := rfl
theorem ProbLang.BaseLit.nest_π_r_def_loc {rT : Type _} (l : Loc) :
    BaseLit.nest.π.r (BaseLit.loc l : BaseLit rT) = none := rfl
theorem ProbLang.BaseLit.nest_π_r_def_lbl {rT : Type _} (l : Lbl) :
    BaseLit.nest.π.r (BaseLit.lbl l : BaseLit rT) = none := rfl
theorem ProbLang.BaseLit.nest_π_r_def_real {rT : Type _} (r : rT) :
    BaseLit.nest.π.r (BaseLit.real r) = none := rfl
theorem ProbLang.BaseLit.nest_π_r_def_prod {rT : Type _} (b1 b2 : BaseLit rT) :
    BaseLit.nest.π.r (BaseLit.prod b1 b2) = none := rfl

/-- Per-cylinder preimage fact for `BaseLit.nest.π.b`. -/
theorem ProbLang.BaseLit.nest_π_b_preimage_some_flatten {rT : Type _}
    (c : BaseLitCyl rT) :
    BaseLit.nest.π.b ⁻¹' (some '' BaseLit.flatten c)
      = BaseLit.flatten ((BaseLit.nest c (Set.univ : Set rT)) : BaseLitCyl rT) := by
  ext b
  cases b with
  | nest b1 r =>
    rw [Set.mem_preimage, nest_π_b_def_nest]
    simp only [BaseLit.flatten, Set.mem_image, Set.mem_prod, Set.mem_univ, and_true]
    constructor
    · rintro ⟨a, ha, heq⟩
      rw [Option.some_inj] at heq
      refine ⟨(b1, r), ?_, rfl⟩
      rw [← heq]; exact ha
    · rintro ⟨⟨b1', r'⟩, hb1', heq⟩
      have hp : b1' = b1 ∧ r' = r := by
        have := heq; simp at this; exact this
      obtain ⟨rfl, rfl⟩ := hp
      exact ⟨b1', hb1', rfl⟩
  | int z =>
    rw [Set.mem_preimage, nest_π_b_def_int]
    simp only [BaseLit.flatten, Set.mem_image, Set.mem_prod]
    refine ⟨?_, ?_⟩
    · rintro ⟨_, _, hcontr⟩; exact absurd hcontr (Option.some_ne_none _)
    · rintro ⟨⟨b1', r'⟩, _, hcontr⟩; simp at hcontr
  | bool b =>
    rw [Set.mem_preimage, nest_π_b_def_bool]
    simp only [BaseLit.flatten, Set.mem_image, Set.mem_prod]
    refine ⟨?_, ?_⟩
    · rintro ⟨_, _, hcontr⟩; exact absurd hcontr (Option.some_ne_none _)
    · rintro ⟨⟨b1', r'⟩, _, hcontr⟩; simp at hcontr
  | unit =>
    rw [Set.mem_preimage, nest_π_b_def_unit]
    simp only [BaseLit.flatten, Set.mem_image, Set.mem_prod]
    refine ⟨?_, ?_⟩
    · rintro ⟨_, _, hcontr⟩; exact absurd hcontr (Option.some_ne_none _)
    · rintro ⟨⟨b1', r'⟩, _, hcontr⟩; simp at hcontr
  | loc l =>
    rw [Set.mem_preimage, nest_π_b_def_loc]
    simp only [BaseLit.flatten, Set.mem_image, Set.mem_prod]
    refine ⟨?_, ?_⟩
    · rintro ⟨_, _, hcontr⟩; exact absurd hcontr (Option.some_ne_none _)
    · rintro ⟨⟨b1', r'⟩, _, hcontr⟩; simp at hcontr
  | lbl l =>
    rw [Set.mem_preimage, nest_π_b_def_lbl]
    simp only [BaseLit.flatten, Set.mem_image, Set.mem_prod]
    refine ⟨?_, ?_⟩
    · rintro ⟨_, _, hcontr⟩; exact absurd hcontr (Option.some_ne_none _)
    · rintro ⟨⟨b1', r'⟩, _, hcontr⟩; simp at hcontr
  | real r =>
    rw [Set.mem_preimage, nest_π_b_def_real]
    simp only [BaseLit.flatten, Set.mem_image, Set.mem_prod]
    refine ⟨?_, ?_⟩
    · rintro ⟨_, _, hcontr⟩; exact absurd hcontr (Option.some_ne_none _)
    · rintro ⟨⟨b1', r'⟩, _, hcontr⟩; simp at hcontr
  | prod b1 b2 =>
    rw [Set.mem_preimage, nest_π_b_def_prod]
    simp only [BaseLit.flatten, Set.mem_image, Set.mem_prod]
    refine ⟨?_, ?_⟩
    · rintro ⟨_, _, hcontr⟩; exact absurd hcontr (Option.some_ne_none _)
    · rintro ⟨⟨b1', r'⟩, _, hcontr⟩; simp at hcontr

/-- Per-cylinder preimage fact for `BaseLit.nest.π.r`: at a measurable set `S ⊆ rT`,
preimage is `⋃ s, flatten (.nest (shapeCyl s) S)`. -/
theorem ProbLang.BaseLit.nest_π_r_preimage_some_S {rT : Type _}
    (S : Set rT) :
    BaseLit.nest.π.r ⁻¹' (some '' S)
      = ⋃ s : BaseLit Unit,
          BaseLit.flatten ((BaseLit.nest (shapeCyl s) S) : BaseLitCyl rT) := by
  ext b
  cases b with
  | nest b1 r =>
    rw [Set.mem_preimage, nest_π_r_def_nest, Set.mem_iUnion]
    constructor
    · rintro ⟨a, ha, heq⟩
      rw [Option.some_inj] at heq
      refine ⟨b1.shape, ?_⟩
      simp only [BaseLit.flatten, Set.mem_image, Set.mem_prod]
      refine ⟨(b1, r), ⟨?_, ?_⟩, rfl⟩
      · rw [ProbLang.BaseLit.flatten_shapeCyl]; rfl
      · rw [← heq]; exact ha
    · rintro ⟨s, hb⟩
      simp only [BaseLit.flatten, Set.mem_image, Set.mem_prod] at hb
      obtain ⟨⟨b1', r'⟩, ⟨_, hr'⟩, heq⟩ := hb
      have hp : b1' = b1 ∧ r' = r := by
        have := heq; simp at this; exact this
      obtain ⟨rfl, rfl⟩ := hp
      exact ⟨r', hr', rfl⟩
  | int z =>
    rw [Set.mem_preimage, nest_π_r_def_int, Set.mem_iUnion]
    refine ⟨?_, ?_⟩
    · rintro ⟨_, _, hcontr⟩; exact absurd hcontr (Option.some_ne_none _)
    · rintro ⟨s, hb⟩; simp [BaseLit.flatten] at hb
  | bool b =>
    rw [Set.mem_preimage, nest_π_r_def_bool, Set.mem_iUnion]
    refine ⟨?_, ?_⟩
    · rintro ⟨_, _, hcontr⟩; exact absurd hcontr (Option.some_ne_none _)
    · rintro ⟨s, hb⟩; simp [BaseLit.flatten] at hb
  | unit =>
    rw [Set.mem_preimage, nest_π_r_def_unit, Set.mem_iUnion]
    refine ⟨?_, ?_⟩
    · rintro ⟨_, _, hcontr⟩; exact absurd hcontr (Option.some_ne_none _)
    · rintro ⟨s, hb⟩; simp [BaseLit.flatten] at hb
  | loc l =>
    rw [Set.mem_preimage, nest_π_r_def_loc, Set.mem_iUnion]
    refine ⟨?_, ?_⟩
    · rintro ⟨_, _, hcontr⟩; exact absurd hcontr (Option.some_ne_none _)
    · rintro ⟨s, hb⟩; simp [BaseLit.flatten] at hb
  | lbl l =>
    rw [Set.mem_preimage, nest_π_r_def_lbl, Set.mem_iUnion]
    refine ⟨?_, ?_⟩
    · rintro ⟨_, _, hcontr⟩; exact absurd hcontr (Option.some_ne_none _)
    · rintro ⟨s, hb⟩; simp [BaseLit.flatten] at hb
  | real r =>
    rw [Set.mem_preimage, nest_π_r_def_real, Set.mem_iUnion]
    refine ⟨?_, ?_⟩
    · rintro ⟨_, _, hcontr⟩; exact absurd hcontr (Option.some_ne_none _)
    · rintro ⟨s, hb⟩; simp [BaseLit.flatten] at hb
  | prod b1 b2 =>
    rw [Set.mem_preimage, nest_π_r_def_prod, Set.mem_iUnion]
    refine ⟨?_, ?_⟩
    · rintro ⟨_, _, hcontr⟩; exact absurd hcontr (Option.some_ne_none _)
    · rintro ⟨s, hb⟩; simp [BaseLit.flatten] at hb

/-- Measurability of `BaseLit.nest.π.b`. -/
theorem ProbLang.BaseLit.measurable_nest_π_b [MeasurableSpace rT] :
    Measurable (BaseLit.nest.π.b : BaseLit rT → Option (BaseLit rT)) := by
  apply Measurable.option_of_cyl_preimages
  rintro (_ | S) hc
  · -- BaseLit.nest.π.b⁻¹' {none} = ecov_nestᶜ
    have hrw : BaseLit.nest.π.b ⁻¹' (OptionCyl.flatten (none : OptionCyl (BaseLit rT)))
             = (ecov_nest : Set (BaseLit rT))ᶜ := by
      ext b
      simp only [OptionCyl.flatten, Set.mem_preimage, Set.mem_singleton_iff,
                 Set.mem_compl_iff, ecov_nest, stratum, Set.mem_iUnion,
                 Set.mem_preimage, Set.mem_singleton_iff]
      cases b with
      | nest b1 r =>
        rw [nest_π_b_def_nest]
        refine ⟨?_, ?_⟩
        · intro hcontr; exact absurd hcontr (Option.some_ne_none _)
        · intro hne; exfalso; apply hne; exact ⟨b1.shape, by simp [shape]⟩
      | int z =>
        rw [nest_π_b_def_int]
        refine ⟨fun _ => ?_, fun _ => rfl⟩
        rintro ⟨s, hb⟩; simp [shape] at hb
      | bool b =>
        rw [nest_π_b_def_bool]
        refine ⟨fun _ => ?_, fun _ => rfl⟩
        rintro ⟨s, hb⟩; simp [shape] at hb
      | unit =>
        rw [nest_π_b_def_unit]
        refine ⟨fun _ => ?_, fun _ => rfl⟩
        rintro ⟨s, hb⟩; simp [shape] at hb
      | loc l =>
        rw [nest_π_b_def_loc]
        refine ⟨fun _ => ?_, fun _ => rfl⟩
        rintro ⟨s, hb⟩; simp [shape] at hb
      | lbl l =>
        rw [nest_π_b_def_lbl]
        refine ⟨fun _ => ?_, fun _ => rfl⟩
        rintro ⟨s, hb⟩; simp [shape] at hb
      | real r =>
        rw [nest_π_b_def_real]
        refine ⟨fun _ => ?_, fun _ => rfl⟩
        rintro ⟨s, hb⟩; simp [shape] at hb
      | prod b1 b2 =>
        rw [nest_π_b_def_prod]
        refine ⟨fun _ => ?_, fun _ => rfl⟩
        rintro ⟨s, hb⟩; simp [shape] at hb
    rw [hrw]; exact ecov_nest_measurable.compl
  · cases hc with
    | some hS =>
      have P_holds : ∀ S : Set (BaseLit rT), MeasurableSet S →
                       MeasurableSet (BaseLit.nest.π.b ⁻¹' (some '' S)) := by
        intro S hS
        induction hS with
        | basic G hG =>
          obtain ⟨c, hc, rfl⟩ := hG
          rw [nest_π_b_preimage_some_flatten c]
          exact BaseLit.flatten_measurable
            (.nest _ hc MeasurableSet.univ)
        | empty => simp [Set.image_empty]
        | compl G _ ih =>
          have hrange : (some : BaseLit rT → Option (BaseLit rT)) '' Gᶜ
                      = (some '' Set.univ) \ (some '' G) := by
            ext x
            cases x with
            | none => simp
            | some a =>
              simp only [Set.mem_image, Set.mem_diff, Set.mem_univ, Set.mem_compl_iff]
              refine ⟨?_, ?_⟩
              · rintro ⟨a', ha', heq⟩
                refine ⟨⟨a', trivial, heq⟩, ?_⟩
                rintro ⟨a'', ha'', heq2⟩
                rw [Option.some_inj] at heq
                rw [Option.some_inj] at heq2
                rw [← heq2] at heq
                exact ha' (heq ▸ ha'')
              · rintro ⟨_, hne⟩
                refine ⟨a, ?_, rfl⟩
                intro hG; exact hne ⟨a, hG, rfl⟩
          rw [hrange, Set.preimage_diff]
          have h_univ : MeasurableSet (BaseLit.nest.π.b ⁻¹' (some '' (Set.univ : Set (BaseLit rT)))) := by
            have hrng : (some : BaseLit rT → Option (BaseLit rT)) '' Set.univ
                      = {none}ᶜ := by
              ext x; cases x with | none => simp | some a => simp
            rw [hrng, Set.preimage_compl]
            have hnone_eq : BaseLit.nest.π.b ⁻¹' ({none} : Set (Option (BaseLit rT)))
                          = (ecov_nest : Set (BaseLit rT))ᶜ := by
              ext b
              cases b with
              | nest b1 r =>
                rw [Set.mem_preimage, nest_π_b_def_nest]
                simp only [Set.mem_singleton_iff, Set.mem_compl_iff, ecov_nest, Set.mem_iUnion]
                refine ⟨?_, ?_⟩
                · intro hcontr; exact absurd hcontr (Option.some_ne_none _)
                · intro hne; exfalso; apply hne
                  exact ⟨b1.shape, by simp [stratum, shape]⟩
              | int z =>
                rw [Set.mem_preimage, nest_π_b_def_int]
                simp only [Set.mem_singleton_iff, Set.mem_compl_iff, ecov_nest, Set.mem_iUnion]
                refine ⟨fun _ => ?_, fun _ => trivial⟩
                rintro ⟨s, hb⟩; simp [stratum, shape] at hb
              | bool b =>
                rw [Set.mem_preimage, nest_π_b_def_bool]
                simp only [Set.mem_singleton_iff, Set.mem_compl_iff, ecov_nest, Set.mem_iUnion]
                refine ⟨fun _ => ?_, fun _ => trivial⟩
                rintro ⟨s, hb⟩; simp [stratum, shape] at hb
              | unit =>
                rw [Set.mem_preimage, nest_π_b_def_unit]
                simp only [Set.mem_singleton_iff, Set.mem_compl_iff, ecov_nest, Set.mem_iUnion]
                refine ⟨fun _ => ?_, fun _ => trivial⟩
                rintro ⟨s, hb⟩; simp [stratum, shape] at hb
              | loc l =>
                rw [Set.mem_preimage, nest_π_b_def_loc]
                simp only [Set.mem_singleton_iff, Set.mem_compl_iff, ecov_nest, Set.mem_iUnion]
                refine ⟨fun _ => ?_, fun _ => trivial⟩
                rintro ⟨s, hb⟩; simp [stratum, shape] at hb
              | lbl l =>
                rw [Set.mem_preimage, nest_π_b_def_lbl]
                simp only [Set.mem_singleton_iff, Set.mem_compl_iff, ecov_nest, Set.mem_iUnion]
                refine ⟨fun _ => ?_, fun _ => trivial⟩
                rintro ⟨s, hb⟩; simp [stratum, shape] at hb
              | real r =>
                rw [Set.mem_preimage, nest_π_b_def_real]
                simp only [Set.mem_singleton_iff, Set.mem_compl_iff, ecov_nest, Set.mem_iUnion]
                refine ⟨fun _ => ?_, fun _ => trivial⟩
                rintro ⟨s, hb⟩; simp [stratum, shape] at hb
              | prod b1 b2 =>
                rw [Set.mem_preimage, nest_π_b_def_prod]
                simp only [Set.mem_singleton_iff, Set.mem_compl_iff, ecov_nest, Set.mem_iUnion]
                refine ⟨fun _ => ?_, fun _ => trivial⟩
                rintro ⟨s, hb⟩; simp [stratum, shape] at hb
            rw [hnone_eq]; simp; exact ecov_nest_measurable
          exact h_univ.diff ih
        | iUnion f _ ih =>
          rw [Set.image_iUnion, Set.preimage_iUnion]
          exact MeasurableSet.iUnion ih
      exact P_holds S hS

/-- Measurability of `BaseLit.nest.π.r` (rT-valued projection). -/
theorem ProbLang.BaseLit.measurable_nest_π_r [MeasurableSpace rT] :
    Measurable (BaseLit.nest.π.r : BaseLit rT → Option rT) := by
  apply Measurable.option_of_cyl_preimages
  rintro (_ | S) hc
  · -- BaseLit.nest.π.r⁻¹' {none} = ecov_nestᶜ
    have hrw : BaseLit.nest.π.r ⁻¹' (OptionCyl.flatten (none : OptionCyl rT))
             = (ecov_nest : Set (BaseLit rT))ᶜ := by
      ext b
      simp only [OptionCyl.flatten, Set.mem_preimage, Set.mem_singleton_iff,
                 Set.mem_compl_iff, ecov_nest, stratum, Set.mem_iUnion,
                 Set.mem_preimage, Set.mem_singleton_iff]
      cases b with
      | nest b1 r =>
        rw [nest_π_r_def_nest]
        refine ⟨?_, ?_⟩
        · intro hcontr; exact absurd hcontr (Option.some_ne_none _)
        · intro hne; exfalso; apply hne; exact ⟨b1.shape, by simp [shape]⟩
      | int z =>
        rw [nest_π_r_def_int]
        refine ⟨fun _ => ?_, fun _ => rfl⟩
        rintro ⟨s, hb⟩; simp [shape] at hb
      | bool b =>
        rw [nest_π_r_def_bool]
        refine ⟨fun _ => ?_, fun _ => rfl⟩
        rintro ⟨s, hb⟩; simp [shape] at hb
      | unit =>
        rw [nest_π_r_def_unit]
        refine ⟨fun _ => ?_, fun _ => rfl⟩
        rintro ⟨s, hb⟩; simp [shape] at hb
      | loc l =>
        rw [nest_π_r_def_loc]
        refine ⟨fun _ => ?_, fun _ => rfl⟩
        rintro ⟨s, hb⟩; simp [shape] at hb
      | lbl l =>
        rw [nest_π_r_def_lbl]
        refine ⟨fun _ => ?_, fun _ => rfl⟩
        rintro ⟨s, hb⟩; simp [shape] at hb
      | real r =>
        rw [nest_π_r_def_real]
        refine ⟨fun _ => ?_, fun _ => rfl⟩
        rintro ⟨s, hb⟩; simp [shape] at hb
      | prod b1 b2 =>
        rw [nest_π_r_def_prod]
        refine ⟨fun _ => ?_, fun _ => rfl⟩
        rintro ⟨s, hb⟩; simp [shape] at hb
    rw [hrw]; exact ecov_nest_measurable.compl
  · cases hc with
    | some hS =>
      -- BaseLit.nest.π.r⁻¹' (some '' S) = ⋃ s, flatten (.nest (shapeCyl s) S). Direct.
      show MeasurableSet (BaseLit.nest.π.r ⁻¹' (some '' S))
      rw [nest_π_r_preimage_some_S]
      exact MeasurableSet.iUnion fun s =>
        BaseLit.flatten_measurable (.nest _ (shapeCyl_HasMeasurableLeaves s) hS)

/-- Joint pairing equation for `BaseLit.nest.π`. -/
theorem ProbLang.BaseLit.nest_π_eq_pair {rT : Type _} (b : BaseLit rT) :
    BaseLit.nest.π b = Option.pair (BaseLit.nest.π.b b, BaseLit.nest.π.r b) := by
  cases b with
  | nest b1 r => show some (b1, r) = Option.pair (some b1, some r); rfl
  | int z => rfl
  | bool _ => rfl
  | unit => rfl
  | loc _ => rfl
  | lbl _ => rfl
  | real _ => rfl
  | prod _ _ => rfl

/-- Global measurability of `BaseLit.nest.π`, derived from per-component measurabilities. -/
theorem ProbLang.BaseLit.measurable_nest_π [MeasurableSpace rT] :
    Measurable (BaseLit.nest.π : BaseLit rT → Option (BaseLit rT × rT)) := by
  have hrw : (BaseLit.nest.π : BaseLit rT → Option (BaseLit rT × rT))
           = Option.pair ∘ (fun b => (BaseLit.nest.π.b b, BaseLit.nest.π.r b)) := by
    funext b; exact nest_π_eq_pair b
  rw [hrw]
  exact Measurable.option_pair.comp (Measurable.prodMk measurable_nest_π_b measurable_nest_π_r)

/-- Cover-restricted measurability for `BaseLit.nest.π` follows from global measurability. -/
theorem ProbLang.BaseLit.cover_meas_nest_π [MeasurableSpace rT]
    {T : Set (Option (BaseLit rT × rT))} (hT : MeasurableSet T) :
    MeasurableSet (ecov_nest ∩ BaseLit.nest.π ⁻¹' T) :=
  ecov_nest_measurable.inter (measurable_nest_π hT)

/-- Cover-restricted measurability for `BaseLit.prod.π` follows from global measurability. -/
theorem ProbLang.BaseLit.cover_meas_prod_π [MeasurableSpace rT]
    {T : Set (Option (BaseLit rT × BaseLit rT))} (hT : MeasurableSet T) :
    MeasurableSet (ecov_prod ∩ BaseLit.prod.π ⁻¹' T) :=
  ecov_prod_measurable.inter (measurable_prod_π hT)

/-- Preimage of `flatten c` under the curried `BaseLit.prod` is empty for non-`.prod` `c`. -/
theorem BaseLit.preimage_flatten_of_ne_prod {rT : Type _} {c : BaseLitCyl rT}
    (h : ∀ c1 c2, c ≠ .prod c1 c2) :
    (fun p : BaseLit rT × BaseLit rT => BaseLit.prod p.1 p.2) ⁻¹' BaseLit.flatten c = ∅ := by
  ext ⟨a, b⟩
  cases c <;> simp_all [BaseLit.flatten]

/-- Measurability of `BaseLit.prod` as a binary function. -/
theorem BaseLit.measurable_prod [MeasurableSpace rT] :
    Measurable (fun p : BaseLit rT × BaseLit rT => BaseLit.prod p.1 p.2) := by
  apply measurable_generateFrom
  rintro G ⟨c, hc, rfl⟩
  cases hc with
  | @prod c1 c2 h1 h2 =>
    have heq : (fun p : BaseLit rT × BaseLit rT => BaseLit.prod p.1 p.2) ⁻¹'
                  BaseLit.flatten (.prod c1 c2)
             = BaseLit.flatten c1 ×ˢ BaseLit.flatten c2 := by
      ext ⟨a, b⟩; simp [BaseLit.flatten]
    rw [heq]
    exact (BaseLit.flatten_measurable h1).prod (BaseLit.flatten_measurable h2)
  | _ =>
    rw [BaseLit.preimage_flatten_of_ne_prod (by intros; nofun)]
    exact MeasurableSet.empty

/-- Preimage of `flatten c` under the curried `BaseLit.nest` is empty for non-`.nest` `c`. -/
theorem BaseLit.preimage_flatten_of_ne_nest {rT : Type _} {c : BaseLitCyl rT}
    (h : ∀ c0 Sr, c ≠ .nest c0 Sr) :
    (fun p : BaseLit rT × rT => BaseLit.nest p.1 p.2) ⁻¹' BaseLit.flatten c = ∅ := by
  ext ⟨a, b⟩
  cases c <;> simp_all [BaseLit.flatten]

/-- Measurability of `BaseLit.nest` as a binary function. -/
theorem BaseLit.measurable_nest [MeasurableSpace rT] :
    Measurable (fun p : BaseLit rT × rT => BaseLit.nest p.1 p.2) := by
  apply measurable_generateFrom
  rintro G ⟨c, hc, rfl⟩
  cases hc with
  | @nest c Sr h hSr =>
    have heq : (fun p : BaseLit rT × rT => BaseLit.nest p.1 p.2) ⁻¹'
                  BaseLit.flatten (.nest c Sr)
             = BaseLit.flatten c ×ˢ Sr := by
      ext ⟨a, b⟩; simp [BaseLit.flatten]
    rw [heq]
    exact (BaseLit.flatten_measurable h).prod hSr
  | _ =>
    rw [BaseLit.preimage_flatten_of_ne_nest (by intros; nofun)]
    exact MeasurableSet.empty

theorem BaseLit.measurable_rec
    {rT : Type _} [MeasurableSpace rT] [Inhabited rT]
    {α : Type _} [MeasurableSpace α]
    (f_int  : Int  → α) (f_bool : Bool → α) (f_unit : Unit → α)
    (f_loc  : Loc  → α) (f_lbl  : Lbl  → α) (f_real : rT → α)
    (f_prod : BaseLit rT × BaseLit rT → α)
    (f_nest : BaseLit rT × rT → α)
    (_h_int  : Measurable f_int)  (_h_bool : Measurable f_bool)
    (_h_unit : Measurable f_unit)
    (_h_loc  : Measurable f_loc)  (_h_lbl  : Measurable f_lbl)
    (h_real : Measurable f_real)
    (h_prod : Measurable f_prod) (h_nest : Measurable f_nest) :
    Measurable (fun b : BaseLit rT =>
      BaseLit.casesOn (motive := fun _ => α) b
        f_int f_bool (f_unit ()) f_loc f_lbl f_real
        (fun b1 b2 => f_prod (b1, b2))
        (fun b r => f_nest (b, r))) := by
  intro S hS
  -- Decompose the preimage uniformly: each summand is `BaseLit.cᵢ '' (f_cᵢ ⁻¹' S)`,
  -- with the nullary `unit` viewed as `Unit → BaseLit rT`, and the multi-arg
  -- constructors viewed as taking a product.
  have hdecomp :
      (fun b : BaseLit rT => BaseLit.casesOn (motive := fun _ => α) b
          f_int f_bool (f_unit ()) f_loc f_lbl f_real
          (fun b1 b2 => f_prod (b1, b2))
          (fun b r => f_nest (b, r))) ⁻¹' S
        = (BaseLit.int   '' (f_int  ⁻¹' S))
        ∪ (BaseLit.bool  '' (f_bool ⁻¹' S))
        ∪ ((fun _ : Unit => (BaseLit.unit : BaseLit rT)) '' (f_unit ⁻¹' S))
        ∪ (BaseLit.loc   '' (f_loc  ⁻¹' S))
        ∪ (BaseLit.lbl   '' (f_lbl  ⁻¹' S))
        ∪ (BaseLit.real  '' (f_real ⁻¹' S))
        ∪ ((fun p : BaseLit rT × BaseLit rT => BaseLit.prod p.1 p.2) ''
            (f_prod ⁻¹' S))
        ∪ ((fun p : BaseLit rT × rT => BaseLit.nest p.1 p.2) ''
            (f_nest ⁻¹' S)) := by
    ext b; cases b <;> simp [Set.mem_preimage]; exact ⟨fun h => ⟨(), h⟩, fun ⟨_, h⟩ => h⟩
  rw [hdecomp]
  refine MeasurableSet.union (MeasurableSet.union (MeasurableSet.union
    (MeasurableSet.union (MeasurableSet.union (MeasurableSet.union
    (MeasurableSet.union ?_ ?_) ?_) ?_) ?_) ?_) ?_) ?_
  -- int branch: countable union of singleton-generators
  · have : (BaseLit.int (rT := rT)) '' (f_int ⁻¹' S)
          = ⋃ z ∈ f_int ⁻¹' S, BaseLit.flatten (rT := rT) (.int z) := by
      ext b; simp [BaseLit.flatten]; tauto
    rw [this]
    exact .biUnion (Set.to_countable _) fun z _ =>
      .basic _ ⟨.int z, .int, rfl⟩
  -- bool branch
  · have : (BaseLit.bool (rT := rT)) '' (f_bool ⁻¹' S)
          = ⋃ b ∈ f_bool ⁻¹' S, BaseLit.flatten (rT := rT) (.bool b) := by
      ext b; simp [BaseLit.flatten]; tauto
    rw [this]
    exact .biUnion (Set.to_countable _) fun b _ =>
      .basic _ ⟨.bool b, .bool, rfl⟩
  -- unit branch: countable union (of one or zero singletons)
  · have : ((fun _ : Unit => (BaseLit.unit : BaseLit rT))) '' (f_unit ⁻¹' S)
          = ⋃ _ ∈ f_unit ⁻¹' S, BaseLit.flatten (rT := rT) (.unit) := by
      ext b; simp [BaseLit.flatten]; tauto
    rw [this]
    exact .biUnion (Set.to_countable _) fun _ _ =>
      .basic _ ⟨.unit, .unit, rfl⟩
  -- loc branch
  · have : (BaseLit.loc (rT := rT)) '' (f_loc ⁻¹' S)
          = ⋃ l ∈ f_loc ⁻¹' S, BaseLit.flatten (rT := rT) (.loc l) := by
      ext b; simp [BaseLit.flatten]; tauto
    rw [this]
    exact .biUnion (Set.to_countable _) fun l _ =>
      .basic _ ⟨.loc l, .loc, rfl⟩
  -- lbl branch
  · have : (BaseLit.lbl (rT := rT)) '' (f_lbl ⁻¹' S)
          = ⋃ l ∈ f_lbl ⁻¹' S, BaseLit.flatten (rT := rT) (.lbl l) := by
      ext b; simp [BaseLit.flatten]; tauto
    rw [this]
    exact .biUnion (Set.to_countable _) fun l _ =>
      .basic _ ⟨.lbl l, .lbl, rfl⟩
  -- real branch: this is *directly* a flattened cylinder
  · have : (BaseLit.real (rT := rT)) '' (f_real ⁻¹' S)
          = BaseLit.flatten (.real (f_real ⁻¹' S)) := by
      simp [BaseLit.flatten]
    rw [this]
    exact .basic _ ⟨.real (f_real ⁻¹' S),
                    .real _ (h_real hS),
                    rfl⟩
  -- prod branch: rewrite image as cover ∩ projection-preimage, then use cover-restricted
  -- measurability of `BaseLit.prod.π`. The Option wrapper goes through `some` (a measurable embedding).
  · rw [ProbLang.BaseLit.image_prod_eq]
    exact ProbLang.BaseLit.cover_meas_prod_π
      (MeasurableEmbedding.some_mk.measurableSet_image' (h_prod hS))
  -- nest branch: same pattern.
  · rw [ProbLang.BaseLit.image_nest_eq]
    exact ProbLang.BaseLit.cover_meas_nest_π
      (MeasurableEmbedding.some_mk.measurableSet_image' (h_nest hS))
end Measurability
end BaseLit








end ProbLangMeasures


/-







theorem BaseLit.beq_self_true (l : BaseLit) : (l == l) = true := by
  cases l with
  | int z =>
    show (Int.decEq z z).decide = true
    exact decide_eq_true rfl
  | bool b => cases b <;> rfl
  | unit => rfl
  | loc l =>
    show decide (l = l) = true
    rw [decide_eq_true rfl]
  | lbl l =>
    show decide (l = l) = true
    rw [decide_eq_true rfl]

inductive UnOp | neg | minus
  deriving Inhabited, Countable, Repr, BEq

inductive BinOp | plus | minus | mult | div | mod | and | or | xor | eq | lt | le | shl | shr
  deriving Inhabited, Countable, Repr, BEq

inductive Ty
  | int | bool | unit
  | prod (τ1 τ2 : Ty)
  | sum (τ1 τ2 : Ty)
  | arrow (τ1 τ2 : Ty)
  | ref (τ : Ty)
  | tape
  | var (n : Nat)
  | rec' (τ : Ty)
  | forall' (τ : Ty)
  | exists' (τ : Ty)
  deriving Inhabited, DecidableEq, Countable, Repr, BEq

inductive Pat
  | wildcard
  | lit (b : BaseLit)
  | pair (p1 p2 : Pat)
  | inl (p : Pat)
  | inr (p : Pat)
  deriving Inhabited, DecidableEq, Countable, Repr, BEq

inductive Exp
  /-- Bound variable -/
  | bvar (n : Nat)
  /-- Free variable -/
  | fvar (x : Var)
  /-- Literal value -/
  | lit (b : BaseLit)
  /-- Lambda: binds its argument -/
  | lam (e : Exp)
  /-- Fixpoint: binds the entire expression -/
  | fix (e : Exp)
  /-- Application -/
  | app (e1 e2 : Exp)
  /-- Base operations -/
  | unop (u : UnOp) (e : Exp)
  | binop (b : BinOp) (e1 e2 : Exp)
  | cond (ec et tf : Exp)
  /-- Pairs -/
  | pair (e1 e2 : Exp)
  | fst (e : Exp)
  | snd (e : Exp)
  /-- Sums -/
  | inl (e : Exp)
  | inr (e : Exp)
  | case (ec el er : Exp)
  /-- Heap -/
  | alloc (e : Exp)
  | load (e : Exp)
  | store (el ev : Exp)
  /-- Allocate random tape, sized as its argument -/
  | tape (e : Exp)
  /-- Unform random sample [0, en), with tape et -/
  | rand (en et : Exp)
  /-- Halt and fail -/
  | fail
  /-- Pattern matching primitive -/
  | scrut (e : Exp) (pat : Pat)
  deriving Inhabited, Countable, Repr, BEq

/-- Phantom constructor: annotate an expression with a type. -/
@[reducible] def Exp.annotated (_τ : Ty) (e : Exp) : Exp := e

namespace Exp

/-- Recursive variable opening. Replace `bvar i` with `sub` at depth `i`. -/
@[simp, scoped grind =] def openRec (i : Nat) (sub : Exp) : Exp → Exp
  | bvar j => if i = j then sub else bvar j
  | fvar x => fvar x
  | lit b => lit b
  | lam e => lam (openRec (i+1) sub e)
  | fix e => fix (openRec (i+1) sub e)
  | app e1 e2 => app (openRec i sub e1) (openRec i sub e2)
  | unop op e => unop op (openRec i sub e)
  | binop op e1 e2 => binop op (openRec i sub e1) (openRec i sub e2)
  | cond ec et ef => cond (openRec i sub ec) (openRec i sub et) (openRec i sub ef)
  | pair e1 e2 => pair (openRec i sub e1) (openRec i sub e2)
  | fst e => fst (openRec i sub e)
  | snd e => snd (openRec i sub e)
  | inl e => inl (openRec i sub e)
  | inr e => inr (openRec i sub e)
  | case ec el er => case (openRec i sub ec) (openRec i sub el) (openRec i sub er)
  | alloc e => alloc (openRec i sub e)
  | load e => load (openRec i sub e)
  | store e1 e2 => store (openRec i sub e1) (openRec i sub e2)
  | tape e => tape (openRec i sub e)
  | rand e1 e2 => rand (openRec i sub e1) (openRec i sub e2)
  | fail => fail
  | scrut e p => scrut (openRec i sub e) p

/-- Open the outermost binder. -/
@[simp, scoped grind =] def open' (e sub : Exp) : Exp := openRec 0 sub e

/-- Recursive variable closing. Replace `fvar x` with `bvar i` at depth `i`. -/
@[simp, scoped grind =] def closeRec (i : Nat) (x : Var) : Exp → Exp
  | bvar j => bvar j
  | fvar y => if x = y then bvar i else fvar y
  | lit b => lit b
  | lam e => lam (closeRec (i+1) x e)
  | fix e => fix (closeRec (i+1) x e)
  | app e1 e2 => app (closeRec i x e1) (closeRec i x e2)
  | unop op e => unop op (closeRec i x e)
  | binop op e1 e2 => binop op (closeRec i x e1) (closeRec i x e2)
  | cond ec et ef => cond (closeRec i x ec) (closeRec i x et) (closeRec i x ef)
  | pair e1 e2 => pair (closeRec i x e1) (closeRec i x e2)
  | fst e => fst (closeRec i x e)
  | snd e => snd (closeRec i x e)
  | inl e => inl (closeRec i x e)
  | inr e => inr (closeRec i x e)
  | case ec el er => case (closeRec i x ec) (closeRec i x el) (closeRec i x er)
  | alloc e => alloc (closeRec i x e)
  | load e => load (closeRec i x e)
  | store e1 e2 => store (closeRec i x e1) (closeRec i x e2)
  | tape e => tape (closeRec i x e)
  | rand e1 e2 => rand (closeRec i x e1) (closeRec i x e2)
  | fail => fail
  | scrut e p => scrut (closeRec i x e) p

/-- Close the x using the outermost binder (bvar 0). -/
@[simp, scoped grind =] def close (e : Exp) (x : Var) : Exp := closeRec 0 x e

/-- Free-variable substitution. -/
@[simp, scoped grind =] def subst (e : Exp) (x : Var) (sub : Exp) : Exp :=
  match e with
  | bvar j => bvar j
  | fvar y => if x = y then sub else fvar y
  | lit b => lit b
  | lam e => lam (subst e x sub)
  | fix e => fix (subst e x sub)
  | app e1 e2 => app (subst e1 x sub) (subst e2 x sub)
  | unop op e => unop op (subst e x sub)
  | binop op e1 e2 => binop op (subst e1 x sub) (subst e2 x sub)
  | cond ec et ef => cond (subst ec x sub) (subst et x sub) (subst ef x sub)
  | pair e1 e2 => pair (subst e1 x sub) (subst e2 x sub)
  | fst e => fst (subst e x sub)
  | snd e => snd (subst e x sub)
  | inl e => inl (subst e x sub)
  | inr e => inr (subst e x sub)
  | case ec el er => case (subst ec x sub) (subst el x sub) (subst er x sub)
  | alloc e => alloc (subst e x sub)
  | load e => load (subst e x sub)
  | store e1 e2 => store (subst e1 x sub) (subst e2 x sub)
  | tape e => tape (subst e x sub)
  | rand e1 e2 => rand (subst e1 x sub) (subst e2 x sub)
  | fail => fail
  | scrut e p => scrut (subst e x sub) p

instance : HasSubstitution Exp Var Exp where
  subst := Exp.subst

/-- Free variables of an expression. -/
@[simp, scoped grind =] def fv : Exp → Finset Var
  | bvar _ => {}
  | fvar x => {x}
  | lit _ => {}
  | lam e => fv e
  | fix e => fv e
  | app e1 e2 => fv e1 ∪ fv e2
  | unop _ e => fv e
  | binop _ e1 e2 => fv e1 ∪ fv e2
  | cond ec et ef => fv ec ∪ fv et ∪ fv ef
  | pair e1 e2 => fv e1 ∪ fv e2
  | fst e => fv e
  | snd e => fv e
  | inl e => fv e
  | inr e => fv e
  | case ec el er => fv ec ∪ fv el ∪ fv er
  | alloc e => fv e
  | load e => fv e
  | store e1 e2 => fv e1 ∪ fv e2
  | tape e => fv e
  | rand e1 e2 => fv e1 ∪ fv e2
  | fail => {}
  | scrut e _ => fv e

/-- An expression is locally closed. -/
inductive IsLocallyClosed : Exp → Prop
  | fvar (x : Var) :
    IsLocallyClosed (fvar x)
  | lit (b : BaseLit) :
    IsLocallyClosed (lit b)
  | lam (L : Finset Var) (e : Exp) :
    (∀ x ∉ L, IsLocallyClosed (open' e (fvar x))) →
    IsLocallyClosed (lam e)
  | fix (L : Finset Var) (e : Exp) :
    (∀ x ∉ L, IsLocallyClosed (open' e (fvar x))) →
    IsLocallyClosed (fix e)
  | app {e1 e2} :
    IsLocallyClosed e1 →
    IsLocallyClosed e2 →
    IsLocallyClosed (app e1 e2)
  | unop (op : UnOp) {e} :
    IsLocallyClosed e →
    IsLocallyClosed (unop op e)
  | binop (op : BinOp) {e1 e2} :
    IsLocallyClosed e1 →
    IsLocallyClosed e2 →
    IsLocallyClosed (binop op e1 e2)
  | cond {ec et ef} :
    IsLocallyClosed ec →
    IsLocallyClosed et →
    IsLocallyClosed ef →
    IsLocallyClosed (cond ec et ef)
  | pair {e1 e2} :
    IsLocallyClosed e1 →
    IsLocallyClosed e2 →
    IsLocallyClosed (pair e1 e2)
  | fst {e} :
    IsLocallyClosed e →
    IsLocallyClosed (fst e)
  | snd {e} :
    IsLocallyClosed e →
    IsLocallyClosed (snd e)
  | inl {e} :
    IsLocallyClosed e →
    IsLocallyClosed (inl e)
  | inr {e} :
    IsLocallyClosed e →
    IsLocallyClosed (inr e)
  | case {ec el er} :
    IsLocallyClosed ec →
    IsLocallyClosed el →
    IsLocallyClosed er →
    IsLocallyClosed (case ec el er)
  | alloc {e} :
    IsLocallyClosed e →
    IsLocallyClosed (alloc e)
  | load {e} :
    IsLocallyClosed e →
    IsLocallyClosed (load e)
  | store {e1 e2} :
    IsLocallyClosed e1 →
    IsLocallyClosed e2 →
    IsLocallyClosed (store e1 e2)
  | tape {e} :
    IsLocallyClosed e →
    IsLocallyClosed (tape e)
  | rand {e1 e2} :
    IsLocallyClosed e1 →
    IsLocallyClosed e2 →
    IsLocallyClosed (rand e1 e2)
  | fail :
    IsLocallyClosed fail
  | scrut {e} (p : Pat) :
    IsLocallyClosed e →
    IsLocallyClosed (scrut e p)

attribute [scoped grind .]
  IsLocallyClosed.fvar
  IsLocallyClosed.lit
  IsLocallyClosed.app
  IsLocallyClosed.unop
  IsLocallyClosed.binop
  IsLocallyClosed.cond
  IsLocallyClosed.pair
  IsLocallyClosed.fst
  IsLocallyClosed.snd
  IsLocallyClosed.inl
  IsLocallyClosed.inr
  IsLocallyClosed.case
  IsLocallyClosed.alloc
  IsLocallyClosed.load
  IsLocallyClosed.store
  IsLocallyClosed.tape
  IsLocallyClosed.rand
  IsLocallyClosed.fail
  IsLocallyClosed.scrut

end Exp

/-- Try to match an expression against a pattern. -/
def Pat.tryMatch : Pat → Exp → Option Exp
  | .wildcard, e => some e
  | .lit b, .lit b' => if b == b' then some (.lit .unit) else none
  | .pair p1 p2, .pair e1 e2 => do
      let b1 ← p1.tryMatch e1
      let b2 ← p2.tryMatch e2
      return .pair b1 b2
  | .inl p, .inl e => p.tryMatch e
  | .inr p, .inr e => p.tryMatch e
  | _, _ => none

/-- `tryMatch (.lit l) (.lit l) = some (.lit .unit)`. -/
theorem Pat.tryMatch_lit_eq (l : BaseLit) :
    Pat.tryMatch (.lit l) (.lit l) = some (.lit .unit) := by
  show (if (l == l) = true then some (Exp.lit BaseLit.unit) else none) = _
  rw [if_pos (BaseLit.beq_self_true l)]

/-- `tryMatch (.lit l1) (.lit l2) = none` when `l1 ≠ l2`. -/
theorem Pat.tryMatch_lit_ne {l1 l2 : BaseLit} (h : ¬ (l1 == l2) = true) :
    Pat.tryMatch (.lit l1) (.lit l2) = none := by
  show (if (l1 == l2) = true then some (Exp.lit BaseLit.unit) else none) = _
  rw [if_neg h]

/- ## Sublanguages -/

abbrev Fragment := Exp → Type

abbrev FragExp (F : Fragment) := (e : Exp) × F e

def Both (F G : Fragment) : Fragment := fun e => F e × G e
def Either (F G : Fragment) : Fragment := fun e => F e ⊕ G e
def Any : Fragment := fun _ => Unit
def None : Fragment := fun _ => Empty
def Overlay (F : Fragment) (M : Exp → Type) : Fragment := fun e => F e × M e

def SubFrag (F G : Fragment) := ∀ e, F e → G e
scoped infixr:25 " ⊆f " => SubFrag

def SubFrag.id : F ⊆f F := fun _ x => x
def SubFrag.comp (f : F ⊆f G) (g : G ⊆f H) : F ⊆f H := fun e x => g e (f e x)
def SubFrag.map (f : F ⊆f G) : FragExp F → FragExp G
  | ⟨e, w⟩ => ⟨e, f e w⟩

def FragExp.erase : FragExp F → Exp := Sigma.fst

class Checkable (F : Fragment) where
  check? : (e : Exp) → Option (F e)

def FragExp.mk? [Checkable F] (e : Exp) : Option (FragExp F) :=
  (Checkable.check? e).map (⟨e, ·⟩)

instance [Checkable F] [Checkable G] : Checkable (Both F G) where
  check? e := do return (← Checkable.check? e, ← Checkable.check? e)

/- ## Values -/

/-- Type-valued witness that an expression is a value. Values are:
    literals, lambda abstractions (which are closed-over functions), fixpoints
    (also functions), and pair/inl/inr of values. -/
inductive IsVal : Exp → Type
  | lit  : IsVal (.lit b)
  | lam  : IsVal (.lam e)
  | fix  : IsVal (.fix e)
  | pair : IsVal e1 → IsVal e2 → IsVal (.pair e1 e2)
  | inl  : IsVal e → IsVal (.inl e)
  | inr  : IsVal e → IsVal (.inr e)

/-- A value is an expression paired with a Type-valued witness. -/
@[expose] def Val := (e : Exp) × IsVal e

namespace IsVal

/-- Decidable check. -/
def check? : (e : Exp) → Option (IsVal e)
  | .lit _ => some .lit
  | .lam _ => some .lam
  | .fix _ => some .fix
  | .pair e1 e2 => do return .pair (← check? e1) (← check? e2)
  | .inl e => do return .inl (← check? e)
  | .inr e => do return .inr (← check? e)
  | _ => none

theorem subsingleton : (w1 w2 : IsVal e) → w1 = w2
  | .lit, .lit => rfl
  | .lam, .lam => rfl
  | .fix, .fix => rfl
  | .pair h1 h2, .pair h1' h2' => by rw [subsingleton h1 h1', subsingleton h2 h2']
  | .inl h, .inl h' => by rw [subsingleton h h']
  | .inr h, .inr h' => by rw [subsingleton h h']

instance : Subsingleton (IsVal e) := ⟨subsingleton⟩

end IsVal

instance : Checkable IsVal where check? := IsVal.check?

def Exp.isValue (e : Exp) : Prop := Nonempty (IsVal e)

def IsVal.toIsValue (w : IsVal e) : e.isValue := ⟨w⟩

noncomputable def IsVal.ofIsValue (h : e.isValue) : IsVal e := h.some

theorem IsVal.check?_some : (w : IsVal e) → ∃ w', IsVal.check? e = some w'
  | .lit => ⟨.lit, rfl⟩
  | .lam => ⟨.lam, rfl⟩
  | .fix => ⟨.fix, rfl⟩
  | .pair h1 h2 => by
      obtain ⟨w1, hw1⟩ := check?_some h1; obtain ⟨w2, hw2⟩ := check?_some h2
      exact ⟨.pair w1 w2, by simp [check?, hw1, hw2]⟩
  | .inl h => by obtain ⟨w, hw⟩ := check?_some h; exact ⟨.inl w, by simp [check?, hw]⟩
  | .inr h => by obtain ⟨w, hw⟩ := check?_some h; exact ⟨.inr w, by simp [check?, hw]⟩

/-- Recursive Prop-valued value predicate. -/
@[simp] def Exp.isValueR : Exp → Prop
  | .lit _ | .lam _ | .fix _ => True
  | .pair e1 e2 => e1.isValueR ∧ e2.isValueR
  | .inl e | .inr e => e.isValueR
  | _ => False

theorem Exp.isValue_iff_isValueR {e : Exp} : e.isValue ↔ e.isValueR := by
  constructor
  · rintro ⟨w⟩; induction w with
    | lit | lam | fix => trivial
    | pair _ _ ih1 ih2 => exact ⟨ih1, ih2⟩
    | inl _ ih | inr _ ih => exact ih
  · intro h; induction e with
    | lit | lam | fix => exact ⟨by constructor⟩
    | pair _ _ ih1 ih2 =>
      obtain ⟨h1, h2⟩ := h; exact ⟨.pair (ih1 h1).some (ih2 h2).some⟩
    | inl _ ih => exact ⟨.inl (ih h).some⟩
    | inr _ ih => exact ⟨.inr (ih h).some⟩
    | _ => exact absurd h id

theorem IsVal.not_isValue_of_check?_none {e : Exp} (h : IsVal.check? e = none) : ¬e.isValue :=
  fun ⟨w⟩ => by obtain ⟨_, hw⟩ := w.check?_some; simp_all

theorem IsVal.check?_eq_none {e : Exp} (h : ¬e.isValue) : IsVal.check? e = none := by
  cases hc : IsVal.check? e with
  | none => rfl
  | some w => exact absurd ⟨w⟩ h

instance Exp.decIsValue (e : Exp) : Decidable e.isValue :=
  match hc : IsVal.check? e with
  | some w => isTrue ⟨w⟩
  | none => isFalse (IsVal.not_isValue_of_check?_none hc)

@[simp] theorem Val.isValue (v : Val) : v.1.isValue := ⟨v.2⟩

@[ext]
theorem Val.ext {v1 v2 : Val} (h : v1.1 = v2.1) : v1 = v2 := by
  obtain ⟨e1, w1⟩ := v1; obtain ⟨e2, w2⟩ := v2
  simp at h; subst h; congr 1; exact IsVal.subsingleton w1 w2

instance : Countable Val := by
  unfold Val; exact instCountableSigma

instance instCountableExtTreeMapLoc {V : Type _} [Countable V] :
    Countable (ExtTreeMap Loc V compare) := by
  obtain ⟨f_v, Hf_v⟩ : Countable (List (Loc × V)) := by infer_instance
  let f_items : ExtTreeMap Loc V compare → List (Loc × V) := ExtTreeMap.toList
  have Hf_items : Function.Injective f_items := by
    simp [f_items]
    intro H1 H2 He
    exact ExtTreeMap.toList_inj.mp (Hf_v (congrArg f_v (Hf_v (congrArg f_v He))))
  exists (fun t => f_v <| f_items t)
  intro H1 H2 He
  exact ExtTreeMap.ext_getElem? (congrFun (congrArg getElem? (Hf_items (Hf_v He))))

def Exp.toVal? (e : Exp) : Option Val :=
  match IsVal.check? e with
  | some w => some ⟨e, w⟩
  | none => none

@[simp] theorem Exp.toVal?_eq_none {e : Exp} : e.toVal? = none ↔ ¬e.isValue := by
  constructor
  · intro h
    simp only [toVal?] at h
    exact IsVal.not_isValue_of_check?_none (by cases hc : IsVal.check? e <;> simp_all)
  · intro h; simp [toVal?, IsVal.check?_eq_none h]

def Exp.ofVal (v : Val) : Exp := v.1

structure Tape where
  bound : Int
  presamples : List { z : Int // 0 ≤ z ∧ z < bound}
  deriving Inhabited, Countable

def Tape.empty (z : Int) : Tape := ⟨z, []⟩

/-- Loc → V heaps. This data structure encapsulates the underlying representation,
  and allows for better typeclass inference. -/
@[reducible] def LocHeap (V : Type _) : Type _ := ExtTreeMap Loc V compare

instance : Inhabited (LocHeap V) := inferInstanceAs (Inhabited (ExtTreeMap _ _ _))

instance [Countable V] : Countable (LocHeap V) :=
  inferInstanceAs (Countable (ExtTreeMap _ _ _))

instance : GetElem? (LocHeap V) Loc V (fun (m : ExtTreeMap Loc V compare) k => k ∈ m) :=
  inferInstanceAs (GetElem? (ExtTreeMap Loc V compare) _ _ _)

structure State where
  heap  : LocHeap Val
  tapes : LocHeap Tape
  deriving Inhabited, Countable

theorem Exp.toVal?_ofVal (v : Val) : (Exp.ofVal v).toVal? = some v := by
  obtain ⟨e, w⟩ := v
  simp only [Exp.ofVal, Exp.toVal?]
  cases hc : IsVal.check? e with
  | none => exact absurd w.toIsValue (IsVal.not_isValue_of_check?_none hc)
  | some w' => exact congrArg some (Val.ext rfl)

theorem Exp.ofVal_of_toVal_some {e : Exp} {v : Val} (h : e.toVal? = some v) : Exp.ofVal v = e := by
  simp only [toVal?] at h
  split at h
  · simp at h; exact congrArg Sigma.fst h.symm
  · simp at h

theorem Exp.ofVal_injective : Function.Injective Exp.ofVal :=
  fun _ _ h => Val.ext h

/- ## Evaluation contexts -/

inductive EctxItem
  | appL (v2 : Val)
  | appR (e1 : Exp)
  | unop (op : UnOp)
  | binopL (op : BinOp) (v2 : Val)
  | binopR (op : BinOp) (e1 : Exp)
  | condC (e1 e2 : Exp)
  | pairL (v2 : Val)
  | pairR (e1 : Exp)
  | fst
  | snd
  | inl
  | inr
  | case (e1 e2 : Exp)
  | alloc
  | load
  | storeL (v2 : Val)
  | storeR (e1 : Exp)
  | tape
  | randL (v2 : Val)
  | randR (e1 : Exp)
  | scrut (p : Pat)

@[simp] def EctxItem.fillItem (Ki : EctxItem) (e : Exp) : Exp :=
  match Ki with
  | appL v2 => .app e (.ofVal v2)
  | appR e1 => .app e1 e
  | unop op => .unop op e
  | binopL op v2 => .binop op e (.ofVal v2)
  | binopR op e1 => .binop op e1 e
  | condC e1 e2 => .cond e e1 e2
  | .pairL v2 => .pair e (.ofVal v2)
  | .pairR e1 => .pair e1 e
  | .fst => .fst e
  | .snd => .snd e
  | .inl => .inl e
  | .inr => .inr e
  | .case e1 e2 => .case e e1 e2
  | .alloc => .alloc e
  | .load => .load e
  | .storeL v2 => .store e (.ofVal v2)
  | .storeR e1 => .store e1 e
  | .tape => .tape e
  | .randL v2 => .rand e (.ofVal v2)
  | .randR e1 => .rand e1 e
  | .scrut p => .scrut e p

def Exp.decompItem (e : Exp) : Option (EctxItem × Exp) :=
  match e with
  | app e1 e2 =>
    e2.toVal?.casesOn (some (.appR e1, e2)) fun v2 =>
    e1.toVal?.casesOn (some (.appL v2, e1)) fun _ => none
  | unop op e1 =>
    e1.toVal?.casesOn (some (.unop op, e1)) fun _ => none
  | binop op e1 e2 =>
    e2.toVal?.casesOn (some (.binopR op e1, e2)) fun v2 =>
    e1.toVal?.casesOn (some (.binopL op v2, e1)) fun _ => none
  | .cond ec et ef =>
    ec.toVal?.casesOn (some (.condC et ef, ec)) fun _ => none
  | pair e1 e2 =>
    e2.toVal?.casesOn (some (.pairR e1, e2)) fun v2 =>
    e1.toVal?.casesOn (some (.pairL v2, e1)) fun _ => none
  | fst e1 =>
    e1.toVal?.casesOn (some (.fst, e1)) fun _ => none
  | snd e1 =>
    e1.toVal?.casesOn (some (.snd, e1)) fun _ => none
  | inl e1 =>
    e1.toVal?.casesOn (some (.inl, e1)) fun _ => none
  | inr e1 =>
    e1.toVal?.casesOn (some (.inr, e1)) fun _ => none
  | alloc e1 =>
    e1.toVal?.casesOn (some (.alloc, e1)) fun _ => none
  | load e1 =>
    e1.toVal?.casesOn (some (.load, e1)) fun _ => none
  | store e1 e2 =>
    e2.toVal?.casesOn (some (.storeR e1, e2)) fun v2 =>
    e1.toVal?.casesOn (some (.storeL v2, e1)) fun _ => none
  | rand e1 e2 =>
    e2.toVal?.casesOn (some (.randR e1, e2)) fun v2 =>
    e1.toVal?.casesOn (some (.randL v2, e1)) fun _ => none
  | .case ec el er =>
    ec.toVal?.casesOn (some (.case el er, ec)) fun _ => none
  | tape e1 =>
    e1.toVal?.casesOn (some (.tape, e1)) fun _ => none
  | scrut e1 p =>
    e1.toVal?.casesOn (some (.scrut p, e1)) fun _ => none
  | _ => none

/- ## Deterministic evaluation helpers -/

def UnOp.eval (op : UnOp) (v : Exp) : Option Exp :=
  match op, v with
  | neg, .lit (.bool b) => some <| .lit <| .bool <| ¬ b
  | minus, .lit (.int z) => some <| .lit <| .int <| z.neg
  | _, _ => none

def BinOp.eval (op : BinOp) (v1 v2 : Exp) : Option Exp :=
  match op, v1, v2 with
  | plus,  .lit (.int z1),  .lit (.int z2)  => some <| .lit <| .int (z1 + z2)
  | minus, .lit (.int z1),  .lit (.int z2)  => some <| .lit <| .int (z1 - z2)
  | mult,  .lit (.int z1),  .lit (.int z2)  => some <| .lit <| .int (z1 * z2)
  -- Division and modulus on integers are total in Lean (n / 0 = 0, n % 0 = n)
  -- and Rocq's `Z.quot`/`Z.rem` agree, so we follow the same convention rather
  -- than getting stuck on a zero divisor.
  | div,   .lit (.int z1),  .lit (.int z2)  => some <| .lit <| .int (z1 / z2)
  | mod,   .lit (.int z1),  .lit (.int z2)  => some <| .lit <| .int (z1 % z2)
  | and,   .lit (.bool b1), .lit (.bool b2) => some <| .lit <| .bool (b1 && b2)
  | or,    .lit (.bool b1), .lit (.bool b2) => some <| .lit <| .bool (b1 || b2)
  | xor,   .lit (.bool b1), .lit (.bool b2) => some <| .lit <| .bool (b1 ^^ b2)
  | eq,    .lit l1,         .lit l2         => some <| .lit <| .bool (decide (l1 = l2))
  -- Equality on tagged unboxed values (inl/inr of literals): tags differ → false;
  -- tags match → recurse on payload literals.
  | eq,    .inl (.lit l1),  .inl (.lit l2)  => some <| .lit <| .bool (decide (l1 = l2))
  | eq,    .inr (.lit l1),  .inr (.lit l2)  => some <| .lit <| .bool (decide (l1 = l2))
  | eq,    .inl (.lit _),   .inr (.lit _)   => some <| .lit <| .bool false
  | eq,    .inr (.lit _),   .inl (.lit _)   => some <| .lit <| .bool false
  | lt,    .lit (.int z1),  .lit (.int z2)  => some <| .lit <| .bool (decide (z1 < z2))
  | le,    .lit (.int z1),  .lit (.int z2)  => some <| .lit <| .bool (decide (z1 ≤ z2))
  -- Bit shifts on integers. Shift amount is converted to Nat via `toNat`
  -- (negative shift amounts treat as 0 — caller's responsibility to ensure non-negative).
  | shl,   .lit (.int z1),  .lit (.int z2)  => some <| .lit <| .int (z1 * 2 ^ z2.toNat)
  | shr,   .lit (.int z1),  .lit (.int z2)  => some <| .lit <| .int (z1 / 2 ^ z2.toNat)
  |_,      _,        _        => none

def State.update_heap (σ : State) (f : ExtTreeMap Loc Val → ExtTreeMap Loc Val) : State :=
  ⟨f σ.heap, σ.tapes⟩

def State.update_tapes (σ : State) (f : ExtTreeMap Loc Tape → ExtTreeMap Loc Tape) : State :=
  ⟨σ.heap, f σ.tapes⟩

theorem State.update_tapes_twice (σ : State) (l : Loc) (ys xs : Tape) :
    (σ.update_tapes (·.insert l xs)).update_tapes (·.insert l ys) =
    σ.update_tapes (·.insert l ys) := by
  unfold State.update_tapes; simp; grind

theorem State.update_tapes_same {σ σ' : State}
    (h : σ.update_tapes (·.insert l xs) = σ'.update_tapes (·.insert l ys)) :
    xs = ys := by
  have key := congrArg (·.tapes[l]?) h
  simp [State.update_tapes, LocHeap] at key
  exact key

theorem State.update_tapes_no_change {σ : State} (h : σ.tapes[l]? = some ys) :
    σ.update_tapes (·.insert l ys) = σ := by
  unfold State.update_tapes; congr 2; grind

theorem State.update_tapes_same' {σ σ' : State} {xs : List { z : Int // 0 ≤ z ∧ z < n }}
    {x y : { z : Int // 0 ≤ z ∧ z < n }}
    (h : σ.update_tapes (·.insert l ⟨n, xs ++ [x]⟩) = σ'.update_tapes (·.insert l ⟨n, xs ++ [y]⟩)) :
    x = y := by
  have heq := State.update_tapes_same h
  simp [Tape.mk.injEq] at heq
  exact heq

theorem State.update_tapes_neq' {σ σ' : State} {xs : List { z : Int // 0 ≤ z ∧ z < n }}
    {x y : { z : Int // 0 ≤ z ∧ z < n }} (hne : x ≠ y) :
    σ.update_tapes (·.insert l ⟨n, xs ++ [x]⟩) ≠ σ'.update_tapes (·.insert l ⟨n, xs ++ [y]⟩) :=
  (hne <| State.update_tapes_same' ·)

structure Cfg where
  expr : Exp
  state : State
  deriving Countable

theorem Ectx.fillItem_injective : Function.Injective (EctxItem.fillItem K) := by
  cases K <;> simp [Function.Injective, EctxItem.fillItem]

theorem EctxItem.fillItem_isValue {K : EctxItem} : (K.fillItem e).isValue → e.isValue := by
  rintro ⟨w⟩
  cases K <;> (simp only [EctxItem.fillItem] at w; cases w) <;> exact ‹IsVal e›.toIsValue

theorem EctxItem.fillItem_noVal_inj {Ki1 Ki2 : EctxItem} {e1 e2 : Exp}
    (hv1 : ¬e1.isValue) (hv2 : ¬e2.isValue)
    (h : Ki1.fillItem e1 = Ki2.fillItem e2) : Ki1 = Ki2 := by
  cases Ki1 <;> cases Ki2 <;> simp_all [EctxItem.fillItem, Exp.ofVal] <;>
    grind [Val.ext_iff, Val.isValue, Exp.isValue_iff_isValueR]

@[simp]
def Exp.height : Exp → Nat
  | bvar _ | fvar _ | lit _ => 1
  | lam e => 1 + e.height
  | fix e => 1 + e.height
  | app e1 e2 => 1 + e1.height + e2.height
  | binop _ e1 e2 => 1 + e1.height + e2.height
  | pair e1 e2 => 1 + e1.height + e2.height
  | store e1 e2 => 1 + e1.height + e2.height
  | rand e1 e2 => 1 + e1.height + e2.height
  | unop _ e => 1 + e.height
  | fst e => 1 + e.height
  | snd e => 1 + e.height
  | inl e => 1 + e.height
  | inr e => 1 + e.height
  | alloc e => 1 + e.height
  | load e => 1 + e.height
  | tape e => 1 + e.height
  | .cond e0 e1 e2 => 1 + e0.height + e1.height + e2.height
  | .case e0 e1 e2 => 1 + e0.height + e1.height + e2.height
  | scrut e _ => 1 + e.height
  | fail => 1

private theorem Exp.toVal?_of_isVal {e : Exp} (w : IsVal e) : ∃ v : Val, e.toVal? = some v ∧ v.1 = e :=
  let ⟨w', hw'⟩ := w.check?_some; ⟨⟨e, w'⟩, by simp [toVal?, hw'], rfl⟩

theorem EctxItem.decompItem_fillItem (Ki : EctxItem) {e : Exp} (hv : ¬e.isValue) :
    (Ki.fillItem e).decompItem = some (Ki, e) := by
  cases Ki with
  | appL v2 | binopL _ v2 | pairL v2 | storeL v2 | randL v2 =>
    obtain ⟨val, hval⟩ := v2
    obtain ⟨v', hv', hv'e⟩ := Exp.toVal?_of_isVal hval
    simp [EctxItem.fillItem, Exp.decompItem, Exp.toVal?_eq_none.mpr hv,
         hv', Exp.ofVal, Val.ext_iff, hv'e]
  | _ => simp [EctxItem.fillItem, Exp.decompItem, Exp.toVal?_eq_none.mpr hv]

theorem Exp.decompItem_fill {e e' : Exp} {Ki : EctxItem}
    (h : e.decompItem = some (Ki, e')) : Ki.fillItem e' = e ∧ ¬e'.isValue := by
  simp only [decompItem, toVal?] at h
  have aux : ∀ x, IsVal.check? x = none → ¬Exp.isValue x :=
    fun x h => IsVal.not_isValue_of_check?_none h
  cases e <;> simp_all [Exp.ofVal] <;>
    (split at h <;> simp_all <;> (try obtain ⟨rfl, rfl⟩ := h; simp_all)) <;>
    (split at h <;> simp_all <;> (try obtain ⟨rfl, rfl⟩ := h; simp_all))

theorem EctxItem.fillItem_noVal {Ki : EctxItem} {e : Exp} (hv : ¬e.isValue) :
    ¬(Ki.fillItem e).isValue := (hv <| EctxItem.fillItem_isValue ·)

abbrev Ectx := List EctxItem

theorem List.eq_nil_or_snoc (l : List α) : l = [] ∨ ∃ l' x, l = l' ++ [x] := by
  rcases List.eq_nil_or_concat l with h | ⟨l', x, h⟩
  · exact .inl h
  · exact .inr ⟨l', x, List.concat_eq_append .. ▸ h⟩

def Ectx.empty : Ectx := []

def Ectx.comp (e1 e2 : Ectx) : Ectx := e2 ++ e1

def Ectx.fill (K : Ectx) (e : Exp) : Exp := K.foldl (flip EctxItem.fillItem) e

theorem fill_app (K1 K2 : Ectx) e : (K1 ++ K2).fill e = K2.fill (K1.fill e) :=
  List.foldl_append

@[simp] theorem Ectx.fill_snoc (K : Ectx) (Ki : EctxItem) (e : Exp) :
    Ectx.fill (K ++ [Ki]) e = Ki.fillItem (K.fill e) :=
  List.foldl_append

theorem Ectx.fill_comp (K1 K2 : Ectx) (e : Exp) :
    K1.fill (K2.fill e) = (K1.comp K2).fill e := by
  simp [Ectx.comp, fill_app]

theorem Ectx.fill_injective (K : Ectx) : Function.Injective K.fill := by
  induction K with
  | nil => intro _ _ h; exact h
  | cons Ki K ih => exact fun _ _ h => Ectx.fillItem_injective (ih h)

theorem Ectx.fill_noVal {K : Ectx} {e : Exp} (hv : ¬e.isValue) : ¬(K.fill e).isValue := by
  induction K generalizing e with
  | nil => exact hv
  | cons Ki K ih => exact ih (EctxItem.fillItem_noVal hv)

theorem Ectx.fill_isValue {K : Ectx} {e : Exp} (hv : (K.fill e).isValue) : e.isValue :=
  if h : e.isValue then h else absurd hv (Ectx.fill_noVal h)

theorem Exp.decompItem_height {e : Exp} (h : e.decompItem = some (Ki, e')) :
    e'.height < e.height := by
  simp only [decompItem, toVal?] at h
  cases e <;> simp_all <;>
    (split at h <;> simp_all <;> try omega) <;>
    (split at h <;> simp_all <;> try omega)

def Exp.decomp (e : Exp) : Ectx × Exp :=
  match _h : e.decompItem with
  | some (Ki, e') =>
      let (K, e'') := decomp e'
      (K ++ [Ki], e'')
  | none => ([], e)
  termination_by e.height
  decreasing_by exact Exp.decompItem_height _h

theorem Exp.decomp_unfold (e : Exp) :
    e.decomp =
      match _ : e.decompItem with
      | some (Ki, e') => let (K, e'') := e'.decomp; (K ++ [Ki], e'')
      | none => ([], e) :=
  Exp.decomp.eq_1 e

theorem Exp.decomp_inv_nil {e e' : Exp} (h : e.decomp = ([], e')) :
    e.decompItem = none ∧ e = e' := by
  rw [Exp.decomp] at h
  split at h
  · simp_all [List.append_eq_nil_iff]
  · exact ⟨by assumption, (Prod.mk.inj h).2⟩

theorem Exp.decomp_inv_cons {Ki : EctxItem} {K : Ectx} {e e'' : Exp}
    (h : e.decomp = (K ++ [Ki], e'')) :
    ∃ e', e.decompItem = some (Ki, e') ∧ e'.decomp = (K, e'') := by
  rw [decomp_unfold] at h
  split at h
  · next Ki' e' hd =>
    simp only at h
    obtain ⟨hK, he⟩ := Prod.mk.inj h
    have hlen : e'.decomp.1.length = K.length := by
      have := congrArg List.length hK
      simp at this
      omega
    obtain ⟨hK', hKi⟩ := List.append_inj hK hlen
    rw [List.singleton_inj.mp hKi] at hd
    exact ⟨e', hd, Prod.ext hK' (by simp [he])⟩
  · simp_all [List.append_eq_nil_iff]

theorem Exp.decomp_fill {K : Ectx} {e e' : Exp} (h : e.decomp = (K, e')) :
    K.fill e' = e := by
  suffices ∀ n K (e e' : Exp), K.length = n → e.decomp = (K, e') → K.fill e' = e by
    exact this K.length K e e' rfl h
  intro n
  induction n with
  | zero =>
    intro _ _ _ hlen hd
    obtain rfl := List.eq_nil_of_length_eq_zero hlen
    exact (decomp_inv_nil hd).2.symm
  | succ n ih =>
    intro K e e' hlen hd
    have hne : K ≠ [] := by intro hK; simp [hK] at hlen
    obtain ⟨K'', Ki, rfl⟩ : ∃ K'' Ki, K = K'' ++ [Ki] :=
      ⟨K.dropLast, K.getLast hne, (List.dropLast_concat_getLast hne).symm⟩
    obtain ⟨e'', hKi, hK''⟩ := decomp_inv_cons hd
    simp only [Ectx.fill, List.foldl_append, List.foldl_cons, List.foldl_nil] at *
    rw [ih K'' e'' e' (by simp at hlen; omega) hK'']
    exact (decompItem_fill hKi).1

theorem Exp.decomp_val_empty {K : Ectx} {e e' : Exp}
    (hd : e.decomp = (K, e')) (hv : e'.isValue) : K = [] := by
  suffices ∀ n K (e e' : Exp), K.length = n → e.decomp = (K, e') → e'.isValue → K = [] by
    exact this K.length K e e' rfl hd hv
  intro n
  induction n with
  | zero =>
    intros
    exact List.eq_nil_of_length_eq_zero ‹_›
  | succ n ih =>
    intro K e e' hlen hd hv
    have hne : K ≠ [] := by intro hK; simp [hK] at hlen
    obtain ⟨K'', Ki, rfl⟩ : ∃ K'' Ki, K = K'' ++ [Ki] :=
      ⟨K.dropLast, K.getLast hne, (List.dropLast_concat_getLast hne).symm⟩
    obtain ⟨e'', hKi, hK''⟩ := decomp_inv_cons hd
    rw [ih K'' e'' e' (by simp at hlen; omega) hK'' hv] at hK''
    rw [(decomp_inv_nil hK'').2] at hKi
    exact absurd hv (decompItem_fill hKi).2

theorem Exp.decomp_fill_comp {e e' : Exp} {K K' : Ectx}
    (hv : ¬e.isValue) (hd : e.decomp = (K', e')) :
    (K.fill e).decomp = (K' ++ K, e') := by
  suffices ∀ n K, K.length = n → (K.fill e).decomp = (K' ++ K, e') by
    exact this K.length K rfl
  intro n
  induction n with
  | zero =>
    intro K hlen
    obtain rfl := List.eq_nil_of_length_eq_zero hlen
    simpa
  | succ n ih =>
    intro K hlen
    have hne : K ≠ [] := by intro hK; simp [hK] at hlen
    obtain ⟨K'', Ki, rfl⟩ : ∃ K'' Ki, K = K'' ++ [Ki] :=
      ⟨K.dropLast, K.getLast hne, (List.dropLast_concat_getLast hne).symm⟩
    simp only [Ectx.fill_snoc]
    rw [decomp_unfold, EctxItem.decompItem_fillItem Ki (Ectx.fill_noVal hv)]
    simp only [ih K'' (by simp at hlen; omega), List.append_assoc]

/-- `x ∉ fv e` — LN replacement for the old string-based Fresh predicate. -/
def Exp.Fresh (x : Var) (e : Exp) : Prop := x ∉ e.fv
-/
