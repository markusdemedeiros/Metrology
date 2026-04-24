import Mathlib.Data.ENNReal.Basic
import Iris
import Iris.Algebra.HeapView
import Iris.Instances.IProp.Instance
import Iris.Std.HeapInstances
import Metrology.Iris.Algebra
import Metrology.Iris.SpecProgram
import Metrology.ProbLang.Syntax.Syntax
import Metrology.ProbLang.Syntax.Notation

/-!
# Program-side ghost state

Concrete ghost-state for the **program** side of the Approxis WP. Mirrors
`Metrology/Iris/SpecProgram.lean` but owns *program* heap and tapes rather
than spec-side ones.

## Rocq source

`clutch/theories/approxis/primitive_laws.v` — the `approxisGS` class bundles
program-side heap/tape ghost-maps with the spec resources.

Here we separate concerns:
- `AppPreGS` / `AppGS` own *program* heap and tape γ-names.
- `SpecGS` owns spec-side γ-names (already in `SpecProgram.lean`).
- The Approxis "combined" instance is the union `[AppGS GF] [SpecGS GF] [ecGS GF]`.

The CMRAs (`SpecHeap = HeapView ℕ+ Loc (Agree Val) LocHeap`, etc.) are reused
verbatim from `SpecProgram.lean` — nothing spec-specific about them, just
"ghost-map over Loc".
-/

section AppProgramRA
open Std Iris Iris.Std COFE ProbLang

/-! ## Ghost-state classes -/

/-- The preGS bundle: which CMRAs live in `GF`. Reuses `SpecHeap`/`SpecTapes`
from `SpecProgram.lean` — the algebra is identical for program and spec. -/
class AppPreGS (GF : BundledGFunctors) where
  heap : ElemG GF (constOF SpecHeap)
  tapes : ElemG GF (constOF SpecTapes)

attribute [reducible, instance] AppPreGS.heap AppPreGS.tapes

/-- The full GS: picks concrete γ names for the program-side heap and tapes. -/
class AppGS (GF : BundledGFunctors) extends AppPreGS GF where
  γheap : GName
  γtapes : GName

/-! ## Resources (authoritative + fragments) -/

section Resources

variable {GF : BundledGFunctors} [IApp : AppGS GF]

/-- Authoritative program heap. -/
def appHeapAuth (σ : LocHeap Val) : IProp GF :=
  iOwn (E := IApp.heap) IApp.γheap (HeapView.Auth (.own 1) (LocHeap.asAgree σ))

/-- Fragment witnessing `l ↦ v` on the program heap. -/
def appHeapFrag (ℓ : Loc) (v : Val) : IProp GF :=
  iOwn (E := IApp.heap) IApp.γheap (HeapView.Frag ℓ (.own 1) (toAgree v))

/-- Authoritative program tapes. -/
def appTapesAuth (σ : LocHeap Tape) : IProp GF :=
  iOwn (E := IApp.tapes) IApp.γtapes (HeapView.Auth (.own 1) (LocHeap.asAgree σ))

/-- Fragment witnessing `l ↪ₐ t` on the program tapes. -/
def appTapesFrag (ℓ : Loc) (t : Tape) : IProp GF :=
  iOwn (E := IApp.tapes) IApp.γtapes (HeapView.Frag ℓ (.own 1) (toAgree t))

/-- Bundled state interpretation: both heap and tapes at once. -/
def appStateAuth (σ : State) : IProp GF :=
  iprop(appHeapAuth σ.heap ∗ appTapesAuth σ.tapes)

end Resources

/-! ## Points-to notation

Lives in namespace `AppGS`. Users write `open scoped AppGS` to bring `↦`/`↪`
into scope for the program-side ghost-state. Scoped to avoid shadowing
Mathlib's `Function.Embedding` (`↪`) globally. -/

namespace AppGS
scoped notation:51 l:51 " ↦ " v:51 => appHeapFrag l v
end AppGS
-- Tape points-to uses subscripted `↪ₐ` to avoid Mathlib's `Function.Embedding`
-- (which binds `↪` globally). Heap points-to `↦` lives in scope `AppGS`.
notation:51 l:51 " ↪ₐ " v:51 => appTapesFrag l v

/-! ## Algebra: lookup, update, alloc

These mirror `spec_auth_lookup_heap`, `spec_auth_update_heap`,
`spec_auth_heap_alloc` (and tape analogues) from `SpecProgram.lean`, but
act on the program-side γ names. -/

section Algebra
open scoped AppGS

variable {GF : BundledGFunctors} [IApp : AppGS GF]

theorem app_state_lookup_heap {σ : State} {l : Loc} {v : Val} :
    ⊢@{IProp GF} appStateAuth σ -∗ l ↦ v -∗ ⌜σ.heap[l]? = some v⌝ := by
  unfold appStateAuth appHeapAuth appHeapFrag
  iintro ⟨Hh, -⟩ Hf
  ihave Hv := iOwn_cmraValid_op (E := IApp.heap) $$ [Hh Hf]
  · isplitl [Hh] <;> iassumption
  ihave %hv := internalCmraValid_discrete (A := SpecHeap) (PROP := IProp GF) $$ Hv
  ipure_intro
  obtain ⟨v', _, _, Hlookup, _, Hinc⟩ := HeapView.auth_op_frag_valid_total_discrete_iff hv
  rw [LocHeap.asAgree_get?] at Hlookup
  show PartialMap.get? σ.heap l = some v
  cases Hcase : PartialMap.get? σ.heap l with
  | none => rw [Hcase] at Hlookup; simp at Hlookup
  | some w =>
    rw [Hcase] at Hlookup
    simp only [Option.map_some, Option.some.injEq] at Hlookup
    have Hinc' : toAgree v ≼ toAgree w := Hlookup ▸ Hinc
    have : v = w := Agree.toAgree_included_L.mp Hinc'
    exact this ▸ rfl

theorem app_state_update_heap {σ : State} {l : Loc} {v w : Val} :
    ⊢@{IProp GF} appStateAuth σ -∗ l ↦ v ==∗
      appStateAuth (σ.update_heap (fun h : LocHeap Val => PartialMap.insert h l w)) ∗
        l ↦ w := by
  iintro Ha Hf
  ihave %Hlk := app_state_lookup_heap (GF := GF) $$ Ha Hf
  unfold appStateAuth appHeapAuth appHeapFrag
  ihave ⟨Hh, Ht⟩ := Ha
  have Hval_toAgree : ✓ (toAgree w : Agree Val) := by
    intro n; simp [Agree.validN_iff, toAgree]
  have Hupd :
      HeapView.Auth (F := ℕ+) (.own 1) (LocHeap.asAgree σ.heap) •
        HeapView.Frag (F := ℕ+) (H := LocHeap) l (.own 1) (toAgree v) ~~>
      HeapView.Auth (F := ℕ+) (.own 1)
          (PartialMap.insert (LocHeap.asAgree σ.heap) l (toAgree w)) •
        HeapView.Frag (F := ℕ+) l (.own 1) (toAgree w) :=
    HeapView.update_replace Hval_toAgree
  ihave Hu := iOwn_update_op (E := IApp.heap) $$ [Hh Hf]
  · exact Hupd
  · isplitl [Hh] <;> iassumption
  imod Hu
  imodintro
  ihave ⟨Hh, Hf⟩ := iOwn_op (E := IApp.heap) $$ Hu
  simp only [State.update_heap, LocHeap.asAgree_insert]
  isplitr [Hf] <;> try iassumption
  isplitl [Hh] <;> try iassumption

theorem app_state_heap_alloc {σ : State} (v : Val) :
    ⊢@{IProp GF} appStateAuth σ ==∗
      appStateAuth (σ.update_heap
          (fun h : LocHeap Val => PartialMap.insert h σ.heap.fresh v)) ∗
        σ.heap.fresh ↦ v := by
  iintro Ha
  unfold appStateAuth appHeapAuth appHeapFrag
  ihave ⟨Hh, Ht⟩ := Ha
  have Hfresh : PartialMap.get? (LocHeap.asAgree σ.heap) σ.heap.fresh = none := by
    rw [LocHeap.asAgree_get?]
    show (σ.heap[σ.heap.fresh]?).map toAgree = none
    rw [ExtTreeMap.fresh_get?]; rfl
  have Hval_toAgree : ✓ (toAgree v : Agree Val) := by
    intro n; simp [Agree.validN_iff, toAgree]
  have Hupd :
      HeapView.Auth (F := ℕ+) (.own 1) (LocHeap.asAgree σ.heap) ~~>
      HeapView.Auth (F := ℕ+) (.own 1)
          (PartialMap.insert (LocHeap.asAgree σ.heap) σ.heap.fresh (toAgree v)) •
        HeapView.Frag (F := ℕ+) σ.heap.fresh (.own 1) (toAgree v) :=
    HeapView.update_one_alloc Hfresh DFrac.valid_own_one Hval_toAgree
  ihave Hu := iOwn_update (E := IApp.heap) $$ Hh
  · exact Hupd
  imod Hu
  imodintro
  ihave ⟨Hh, Hf⟩ := iOwn_op (E := IApp.heap) $$ Hu
  simp only [State.update_heap, LocHeap.asAgree_insert]
  isplitr [Hf] <;> try iassumption
  isplitl [Hh] <;> try iassumption

theorem app_state_lookup_tape {σ : State} {l : Loc} {t : Tape} :
    ⊢@{IProp GF} appStateAuth σ -∗ l ↪ₐ t -∗ ⌜σ.tapes[l]? = some t⌝ := by
  unfold appStateAuth appTapesAuth appTapesFrag
  iintro ⟨-, Ht⟩ Hf
  ihave Hv := iOwn_cmraValid_op (E := IApp.tapes) $$ [Ht Hf]
  · isplitl [Ht] <;> iassumption
  ihave %hv := internalCmraValid_discrete (A := SpecTapes) (PROP := IProp GF) $$ Hv
  ipure_intro
  obtain ⟨v', _, _, Hlookup, _, Hinc⟩ := HeapView.auth_op_frag_valid_total_discrete_iff hv
  rw [LocHeap.asAgree_get?] at Hlookup
  show PartialMap.get? σ.tapes l = some t
  cases Hcase : PartialMap.get? σ.tapes l with
  | none => rw [Hcase] at Hlookup; simp at Hlookup
  | some w =>
    rw [Hcase] at Hlookup
    simp only [Option.map_some, Option.some.injEq] at Hlookup
    have Hinc' : toAgree t ≼ toAgree w := Hlookup ▸ Hinc
    have : t = w := Agree.toAgree_included_L.mp Hinc'
    exact this ▸ rfl

theorem app_state_update_tape {σ : State} {l : Loc} {t s : Tape} :
    ⊢@{IProp GF} appStateAuth σ -∗ l ↪ₐ t ==∗
      appStateAuth (σ.update_tapes (fun h : LocHeap Tape => PartialMap.insert h l s)) ∗
        l ↪ₐ s := by
  iintro Ha Hf
  ihave %Hlk := app_state_lookup_tape (GF := GF) $$ Ha Hf
  unfold appStateAuth appTapesAuth appTapesFrag
  ihave ⟨Hh, Ht⟩ := Ha
  have Hval_toAgree : ✓ (toAgree s : Agree Tape) := by
    intro n; simp [Agree.validN_iff, toAgree]
  have Hupd :
      HeapView.Auth (F := ℕ+) (.own 1) (LocHeap.asAgree σ.tapes) •
        HeapView.Frag (F := ℕ+) (H := LocHeap) l (.own 1) (toAgree t) ~~>
      HeapView.Auth (F := ℕ+) (.own 1)
          (PartialMap.insert (LocHeap.asAgree σ.tapes) l (toAgree s)) •
        HeapView.Frag (F := ℕ+) l (.own 1) (toAgree s) :=
    HeapView.update_replace Hval_toAgree
  ihave Hu := iOwn_update_op (E := IApp.tapes) $$ [Ht Hf]
  · exact Hupd
  · isplitl [Ht] <;> iassumption
  imod Hu
  imodintro
  ihave ⟨Ht, Hf⟩ := iOwn_op (E := IApp.tapes) $$ Hu
  simp only [State.update_tapes, LocHeap.asAgree_insert]
  isplitr [Hf] <;> try iassumption
  isplitl [Hh] <;> try iassumption

theorem app_state_tape_alloc {σ : State} (t : Tape) :
    ⊢@{IProp GF} appStateAuth σ ==∗
      appStateAuth (σ.update_tapes
          (fun h : LocHeap Tape => PartialMap.insert h σ.tapes.fresh t)) ∗
        σ.tapes.fresh ↪ₐ t := by
  iintro Ha
  unfold appStateAuth appTapesAuth appTapesFrag
  ihave ⟨Hh, Ht⟩ := Ha
  have Hfresh : PartialMap.get? (LocHeap.asAgree σ.tapes) σ.tapes.fresh = none := by
    rw [LocHeap.asAgree_get?]
    show (σ.tapes[σ.tapes.fresh]?).map toAgree = none
    rw [ExtTreeMap.fresh_get?]; rfl
  have Hval_toAgree : ✓ (toAgree t : Agree Tape) := by
    intro n; simp [Agree.validN_iff, toAgree]
  have Hupd :
      HeapView.Auth (F := ℕ+) (.own 1) (LocHeap.asAgree σ.tapes) ~~>
      HeapView.Auth (F := ℕ+) (.own 1)
          (PartialMap.insert (LocHeap.asAgree σ.tapes) σ.tapes.fresh (toAgree t)) •
        HeapView.Frag (F := ℕ+) σ.tapes.fresh (.own 1) (toAgree t) :=
    HeapView.update_one_alloc Hfresh DFrac.valid_own_one Hval_toAgree
  ihave Hu := iOwn_update (E := IApp.tapes) $$ Ht
  · exact Hupd
  imod Hu
  imodintro
  ihave ⟨Ht, Hf⟩ := iOwn_op (E := IApp.tapes) $$ Hu
  simp only [State.update_tapes, LocHeap.asAgree_insert]
  isplitr [Hf] <;> try iassumption
  isplitl [Hh] <;> try iassumption

end Algebra

/-! ## `natTape` — user-level tape wrapper

Rocq's `nat_tape l N (ns : list nat)` hides the backend `list (fin (S N))`
behind an `∃ fs, fin_to_nat <$> fs = ns`. Our backend tape is already
`List {z : Int // 0 ≤ z < bound}` — a bounded-subtype list — so the
analogous wrapper existentially quantifies the subtype list and asserts
its underlying `Int` projection matches the user-supplied `ns : List Int`.

The Rocq `↪N` and `↪ₛN` notations become `↪Nₐ` and `↪Nₛ` here, avoiding
the `↪`/`Function.Embedding` collision. -/

section NatTape
open scoped AppGS

variable {GF : BundledGFunctors} [AppGS GF]

/-- Predicate: every element of `ns : List Int` lies in `[0, z)`. -/
def Tape.inBounds (z : Int) (ns : List Int) : Prop :=
  ∀ n ∈ ns, 0 ≤ n ∧ n < z

/-- User-level tape: `l` points to a tape of bound `z` whose contents, as
plain integers, match `ns`. -/
noncomputable def appNatTape (l : Loc) (z : Int) (ns : List Int) : IProp GF :=
  iprop(∃ fs : List { z' : Int // 0 ≤ z' ∧ z' < z },
    (⌜fs.map (fun x => x.val) = ns⌝) ∗ l ↪ₐ ⟨z, fs⟩)

end NatTape

namespace AppGS
/-- `l ↪N⟨z; ns⟩` — user-level tape points-to with `ns : List Int`. -/
scoped notation:51 l:51 " ↪N⟨" z:51 "; " ns:51 "⟩" => appNatTape l z ns
end AppGS

section NatTapeInterface
open scoped AppGS

variable {GF : BundledGFunctors} [AppGS GF]

/-- Empty user-level tape collapses to the backend empty tape. -/
theorem app_natTape_to_empty {l : Loc} {z : Int} :
    appNatTape (GF := GF) l z [] ⊢ l ↪ₐ ⟨z, []⟩ := by
  unfold appNatTape
  iintro ⟨%fs, %Hmap, Hl⟩
  -- `fs.map (·.val) = []` implies `fs = []`
  have : fs = [] := List.map_eq_nil_iff.mp Hmap
  subst this
  iexact Hl

/-- Backend empty tape embeds into user-level empty tape. -/
theorem app_empty_to_natTape {l : Loc} {z : Int} :
    (l ↪ₐ ⟨z, ([] : List { z' : Int // 0 ≤ z' ∧ z' < z })⟩) ⊢@{IProp GF}
      appNatTape l z [] := by
  iintro Hl
  unfold appNatTape
  iexists []
  isplitr; · ipure_intro; rfl
  iexact Hl

/-- Read the head of a user-level tape: get the head as a subtype element,
with a bijection back to the user form. -/
theorem app_read_natTape_head {l : Loc} {z : Int} {n : Int} {ns : List Int} :
    appNatTape (GF := GF) l z (n :: ns) ⊢
      iprop(∃ (x : { z' : Int // 0 ≤ z' ∧ z' < z })
              (xs : List { z' : Int // 0 ≤ z' ∧ z' < z }),
        l ↪ₐ ⟨z, x :: xs⟩ ∗ (⌜x.val = n⌝) ∗
        (l ↪ₐ ⟨z, xs⟩ -∗ appNatTape l z ns)) := by
  unfold appNatTape
  iintro ⟨%fs, %Hmap, Hl⟩
  -- `(fs.map (·.val)) = n :: ns` forces `fs = x :: xs` with `x.val = n`,
  -- `xs.map (·.val) = ns`.
  have ⟨x, xs, hfs, hx, hxs⟩ := List.map_eq_cons_iff.mp Hmap
  subst hfs
  iexists x, xs
  isplitl [Hl]; · iexact Hl
  isplitr; · ipure_intro; exact hx
  iintro Hl'
  iexists xs
  isplitr; · ipure_intro; exact hxs
  iexact Hl'

end NatTapeInterface

/-! ## Allocation

Allocates a fresh `AppGS GF` instance, producing the authoritative program
state `appStateAuth σ`. Analogue of `spec_ra_init` restricted to the
program-side (no prog-exclusive component — the program heap/tape γ-names
live separately from the spec ones). -/
theorem app_ra_init {GF : BundledGFunctors} [IAPre : AppPreGS GF]
    (σ : State) :
    ⊢@{IProp GF} |==> ∃ IA : AppGS GF,
      @appStateAuth _ IA σ := by
  imod (iOwn_alloc (E := IAPre.heap)
    (HeapView.Auth (F := ℕ+) (.own 1) (LocHeap.asAgree σ.heap))
    HeapView.auth_one_valid) with ⟨%γH, HH⟩
  imod (iOwn_alloc (E := IAPre.tapes)
    (HeapView.Auth (F := ℕ+) (.own 1) (LocHeap.asAgree σ.tapes))
    HeapView.auth_one_valid) with ⟨%γT, HT⟩
  imodintro
  let IA : AppGS GF := {
    toAppPreGS := IAPre
    γheap := γH
    γtapes := γT }
  iexists IA
  unfold appStateAuth appHeapAuth appTapesAuth
  isplitl [HH] <;> iassumption

/-! ## Validity helpers for two heap/tape fragments at the same location

Two full-fraction `↦` fragments at the same location are inconsistent
(combined fraction `1 + 1 = 2 > 1`). Needed by `lrel_ref`/`lrel_tape`
functionality/injectivity proofs in `Metrology/Approxis/Model.lean`. -/

section ValidHelpers
variable {GF : BundledGFunctors} [IApp : AppGS GF]

theorem appHeapFrag_valid_2 {l : Loc} {v1 v2 : Val} :
    ⊢@{IProp GF} appHeapFrag l v1 -∗ appHeapFrag l v2 -∗ False := by
  iintro H1 H2
  unfold appHeapFrag
  ihave Hv := iOwn_cmraValid_op (E := IApp.heap) $$ [H1 H2]
  · isplitl [H1] <;> iassumption
  ihave %hv := internalCmraValid_discrete $$ Hv
  exfalso
  rw [HeapView.frag_op_valid_iff] at hv
  obtain ⟨hdq, _⟩ := hv
  -- `hdq : ✓ (DFrac.own 1 • DFrac.own 1 : DFrac ℕ+)` unfolds to `(1 + 1 : ℕ+) ≤ 1`.
  -- PNat: `(1 + 1).1 = 2`, `2 ≤ 1` is false.
  show False
  have : ¬ ((1 : Iris.PNat) + 1).1 ≤ (1 : Iris.PNat).1 := by
    show ¬ (1 + 1 : Nat) ≤ 1; omega
  exact this hdq

theorem appTapesFrag_valid_2 {l : Loc} {t1 t2 : Tape} :
    ⊢@{IProp GF} appTapesFrag l t1 -∗ appTapesFrag l t2 -∗ False := by
  iintro H1 H2
  unfold appTapesFrag
  ihave Hv := iOwn_cmraValid_op (E := IApp.tapes) $$ [H1 H2]
  · isplitl [H1] <;> iassumption
  ihave %hv := internalCmraValid_discrete $$ Hv
  exfalso
  rw [HeapView.frag_op_valid_iff] at hv
  obtain ⟨hdq, _⟩ := hv
  -- `hdq : ✓ (DFrac.own 1 • DFrac.own 1 : DFrac ℕ+)` unfolds to `(1 + 1 : ℕ+) ≤ 1`.
  -- PNat: `(1 + 1).1 = 2`, `2 ≤ 1` is false.
  show False
  have : ¬ ((1 : Iris.PNat) + 1).1 ≤ (1 : Iris.PNat).1 := by
    show ¬ (1 + 1 : Nat) ≤ 1; omega
  exact this hdq

end ValidHelpers

end AppProgramRA
