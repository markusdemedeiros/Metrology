module

public import Mathlib.Data.ENNReal.Basic
public import Iris
public import Iris.Algebra.HeapView
public import Iris.Instances.IProp.Instance
public import Iris.Std.HeapInstances
public import Metrology.Iris.Algebra
public import Metrology.ProbLang.Syntax.Syntax
public import Metrology.ProbLang.Syntax.Notation
public import Metrology.ProbLang.Discrete

@[expose] public section

section SpecRA
open Std Iris Iris.Std COFE ProbLang

variable {rT : Type _} [ProbLang.LawfulProbLangℝ rT]

instance : COFE (Exp rT) := COFE.ofDiscrete _
instance : OFE.Discrete (Exp rT) := ⟨id⟩
instance (x : Exp rT) : OFE.DiscreteE x := ⟨OFE.Discrete.discrete_0⟩

instance : COFE Tape := COFE.ofDiscrete _
instance : OFE.Discrete Tape := ⟨id⟩
instance (x : Tape) : OFE.DiscreteE x := ⟨OFE.Discrete.discrete_0⟩

instance : COFE (Val rT) := COFE.ofDiscrete _
instance : OFE.Discrete (Val rT) := ⟨id⟩
instance (x : Val rT) : OFE.DiscreteE x := ⟨OFE.Discrete.discrete_0⟩

abbrev SpecProg (α : Type _) [ProbLang.LawfulProbLangℝ α] :=
  Auth (Option (Excl (Exp α)))
abbrev SpecHeap (rT : Type _) [ProbLang.LawfulProbLangℝ rT] :=
  HeapView Loc (Agree (Val rT)) LocHeap
abbrev SpecTapes := HeapView Loc (Agree Tape) LocHeap

def SpecProg.auth (e : Exp rT) : SpecProg rT := ● (some <| .excl e)
def SpecProg.frag (e : Exp rT) : SpecProg rT := ◯ (some <| .excl e)

def LocHeap.asAgree [OFE V] (h : LocHeap V) : LocHeap (Agree V) :=
  PartialMap.map LocHeap toAgree h

theorem LocHeap.asAgree_get? [OFE V] (h : LocHeap V) (l : Loc) :
    PartialMap.get? (LocHeap.asAgree h) l = (PartialMap.get? h l).map toAgree := by
  show PartialMap.get? _ _ = _
  simp only [LocHeap.asAgree, PartialMap.map, LawfulPartialMap.get?_bindAlter]
  cases PartialMap.get? h l <;> rfl

theorem LocHeap.asAgree_insert [OFE V] (h : LocHeap V) (l : Loc) (v : V) :
    LocHeap.asAgree (PartialMap.insert h l v) =
      PartialMap.insert (LocHeap.asAgree h) l (toAgree v) := by
  refine LawfulPartialMap.equiv_iff_eq.mp fun k => ?_
  by_cases hk : l = k
  · subst hk
    rw [LocHeap.asAgree_get?, LawfulPartialMap.get?_insert_eq rfl,
        LawfulPartialMap.get?_insert_eq rfl]
    rfl
  · rw [LocHeap.asAgree_get?, LawfulPartialMap.get?_insert_ne hk,
        LawfulPartialMap.get?_insert_ne hk, LocHeap.asAgree_get?]

class SpecPreGS (rT : outParam (Type _)) [ProbLang.LawfulProbLangℝ rT] (GF : BundledGFunctors) where
  prog : ElemG GF (constOF (SpecProg rT))
  heap : ElemG GF (constOF (SpecHeap rT))
  tapes : ElemG GF (constOF SpecTapes)

attribute [reducible, instance] SpecPreGS.prog SpecPreGS.heap SpecPreGS.tapes

class SpecGS (rT : outParam (Type _)) [ProbLang.LawfulProbLangℝ rT] (GF : BundledGFunctors)
   extends SpecPreGS rT GF where
  γprog : GName
  γheap : GName
  γtapes : GName

section Resources

variable {GF : BundledGFunctors} [ISpec : SpecGS rT GF]

def specProgAuth (e : Exp rT) : IProp GF := iOwn (E := ISpec.prog) ISpec.γprog (.auth e)
def specProgFrag (e : Exp rT) : IProp GF := iOwn (E := ISpec.prog) ISpec.γprog (.frag e)

def specHeapAuth (σ : LocHeap (Val rT)) : IProp GF :=
  iOwn (E := ISpec.heap) ISpec.γheap (HeapView.Auth (.own 1) (LocHeap.asAgree σ))
def specHeapFrag (ℓ : Loc) (v : Val rT) : IProp GF :=
  iOwn (E := ISpec.heap) ISpec.γheap (HeapView.Frag ℓ (.own 1) (toAgree v))

def specTapesAuth (σ : LocHeap Tape) : IProp GF :=
  iOwn (E := ISpec.tapes) ISpec.γtapes (HeapView.Auth (.own 1) (LocHeap.asAgree σ))
def specTapesFrag (ℓ : Loc) (t : Tape) : IProp GF :=
  iOwn (E := ISpec.tapes) ISpec.γtapes (HeapView.Frag ℓ (.own 1) (toAgree t))

def ProbLang.Cfg.specAuth (c : Cfg rT) : IProp GF :=
  let ⟨e, ⟨σ, τ⟩⟩ := c
  iprop(specProgAuth e ∗ specHeapAuth σ ∗ specTapesAuth τ)

-- TODO: Add ⤇ to my Lean4 emacs mode (lol)
-- TODO: Make ↪ less annoying to type too
notation "⤇ " t:50 => specProgFrag t
notation l:50 " ↦ₛ " v:50 => specHeapFrag l v
notation l:50 " ↪ₛ " τ:50 => specTapesFrag l τ

end Resources

section Algebra

variable {GF : BundledGFunctors} [ISpec : SpecGS rT GF]

open ProbLang.Cfg

omit [LawfulProbLangℝ rT] in
theorem some_excl_inc_excl_exp_eq {e1 e2 : Exp rT} (H : some (Excl.excl e1) ≼ some (Excl.excl e2)) :
    e1 = e2 := by
  have H' := Option.inc_iff.mp H
  simp at H'
  rcases H' with (H'|H')
  · exact H'
  · have H'' := Excl.inc_iff.mp H'
    simp at H''

theorem specAuth_specFrag_agree {e1 e2 : Exp rT} {σ : State rT} :
    ⊢@{IProp GF} specAuth ⟨e1, σ⟩ -∗ ⤇ e2 -∗ ⌜e1 = e2⌝ := by
  unfold specAuth specProgAuth specProgFrag
  iintro ⟨He, -, -⟩ Hf
  icombine He Hf gives Hv
  ihave %hv := internalCmraValid_discrete (A := SpecProg rT) $$ Hv
  ipureintro
  obtain ⟨hinc, _⟩ := Auth.auth_both_valid_discrete.mp hv
  exact some_excl_inc_excl_exp_eq hinc |>.symm

theorem specProg_update {e1 e2 e3 : Exp rT} {σ : State rT} :
    ⊢@{IProp GF} specAuth ⟨e1, σ⟩ -∗ ⤇ e2 ==∗ specAuth ⟨e3, σ⟩ ∗ ⤇ e3 := by
  iintro Ha Hf
  ihave %he := specAuth_specFrag_agree $$ Ha Hf
  subst he
  unfold specAuth specProgAuth specProgFrag; simp only []
  ihave ⟨He, Hh, Ht⟩ := Ha
  have Hupd : SpecProg.frag e1 • SpecProg.auth e1 ~~> SpecProg.frag e3 • SpecProg.auth e3 :=
    Auth.auth_update (.option (.exclusive trivial))
  ihave Hu := iOwn_update_op (E := ISpec.prog) $$ [$Hf $He]
  · exact Hupd
  imod Hu
  imodintro
  ihave ⟨Hf, Ha⟩ := iOwn_op $$ Hu
  isplitr [Hf] <;> try iassumption
  isplitl [Ha] <;> try iassumption
  isplitl [Hh] <;> try iassumption


theorem spec_auth_lookup_heap {e : Exp rT} {σ : State rT} {l : Loc} {v : Val rT} :
    ⊢@{IProp GF} specAuth ⟨e, σ⟩ -∗ l ↦ₛ v -∗ ⌜σ.heap[l]? = some v⌝ := by
  unfold specAuth specHeapAuth specHeapFrag
  iintro ⟨-, Hh, -⟩ Hf
  icombine Hh Hf gives Hv
  ihave %hv := internalCmraValid_discrete $$ Hv
  ipureintro
  obtain ⟨v', _, _, Hlookup, _, Hinc⟩ := HeapView.auth_op_frag_valid_total_discrete_iff hv
  -- Hlookup : PartialMap.get? (asAgree σ.heap) l = some v'
  -- Hinc : toAgree v ≼ v'
  rw [LocHeap.asAgree_get?] at Hlookup
  -- Hlookup : Option.map toAgree (PartialMap.get? σ.heap l) = some v'
  -- But goal uses σ.heap[l]?; these are defeq (PartialMap.get? on ExtTreeMap = [·]?)
  show PartialMap.get? σ.heap l = some v
  cases Hcase : PartialMap.get? σ.heap l with
  | none => rw [Hcase] at Hlookup; simp at Hlookup
  | some w =>
    rw [Hcase] at Hlookup
    simp only [Option.map_some, Option.some.injEq] at Hlookup
    -- Hlookup : toAgree w = v'
    have Hinc' : toAgree v ≼ toAgree w := Hlookup ▸ Hinc
    have : v = w := Agree.toAgree_included.mp Hinc'
    exact this ▸ rfl

theorem spec_auth_update_heap {e : Exp rT} {σ : State rT} {l : Loc} {v w : Val rT} :
    ⊢@{IProp GF} specAuth ⟨e, σ⟩ -∗ l ↦ₛ v ==∗
      specAuth ⟨e, σ.update_heap (fun h : LocHeap (Val rT) => PartialMap.insert h l w)⟩ ∗
        l ↦ₛ w := by
  iintro Ha Hf
  ihave %Hlk := spec_auth_lookup_heap $$ Ha Hf
  unfold specAuth specHeapAuth specHeapFrag
  ihave ⟨He, Hh, Ht⟩ := Ha
  have Hval_toAgree : ✓ (toAgree w : Agree (Val rT)) := by
    intro n; simp
  have Hupd :
      HeapView.Auth (.own 1) (LocHeap.asAgree σ.heap) •
        HeapView.Frag l (.own 1) (toAgree v) ~~>
      HeapView.Auth (.own 1)
          (PartialMap.insert (LocHeap.asAgree σ.heap) l (toAgree w)) •
        HeapView.Frag l (.own 1) (toAgree w) :=
    HeapView.update_replace Hval_toAgree
  ihave Hu := iOwn_update_op (E := ISpec.heap) $$ [$Hh $Hf]
  · exact Hupd
  imod Hu
  imodintro
  ihave ⟨Hh, Hf⟩ := iOwn_op $$ Hu
  -- Goal: specAuth ⟨e, σ.update_heap(insert l w)⟩ ∗ l ↦ₛ w
  -- After unfold: specProgAuth e ∗ specHeapAuth (insert l w σ.heap) ∗ specTapesAuth _ ∗ Frag
  simp only [State.update_heap, LocHeap.asAgree_insert]
  isplitr [Hf] <;> try iassumption
  isplitl [He] <;> try iassumption
  isplitl [Hh] <;> try iassumption

theorem spec_auth_heap_alloc {e : Exp rT} {σ : State rT} (v : Val rT) :
    ⊢@{IProp GF} specAuth ⟨e, σ⟩ ==∗
      specAuth ⟨e, σ.update_heap
          (fun h : LocHeap (Val rT) => PartialMap.insert h σ.heap.fresh v)⟩ ∗
        σ.heap.fresh ↦ₛ v := by
  iintro Ha
  unfold specAuth specHeapAuth specHeapFrag
  ihave ⟨He, Hh, Ht⟩ := Ha
  have Hfresh : PartialMap.get? (LocHeap.asAgree σ.heap) σ.heap.fresh = none := by
    rw [LocHeap.asAgree_get?]
    show (σ.heap[σ.heap.fresh]?).map toAgree = none
    rw [ExtTreeMap.fresh_get?]; rfl
  have Hval_toAgree : ✓ (toAgree v : Agree (Val rT)) := by
    intro n; simp
  have Hupd :
      HeapView.Auth (.own 1) (LocHeap.asAgree σ.heap) ~~>
      HeapView.Auth (.own 1)
          (PartialMap.insert (LocHeap.asAgree σ.heap) σ.heap.fresh (toAgree v)) •
        HeapView.Frag σ.heap.fresh (.own 1) (toAgree v) :=
    HeapView.update_one_alloc Hfresh DFrac.valid_own_one Hval_toAgree
  ihave Hu := iOwn_update $$ Hh
  · exact Hupd
  imod Hu
  imodintro
  ihave ⟨Hh, Hf⟩ := iOwn_op $$ Hu
  simp only [State.update_heap, LocHeap.asAgree_insert]
  isplitr [Hf] <;> try iassumption
  isplitl [He] <;> try iassumption
  isplitl [Hh] <;> try iassumption

theorem spec_auth_lookup_tape {e : Exp rT} {σ : State rT} {l : Loc} {t : Tape} :
    ⊢@{IProp GF} specAuth ⟨e, σ⟩ -∗ l ↪ₛ t -∗ ⌜σ.tapes[l]? = some t⌝ := by
  unfold specAuth specTapesAuth specTapesFrag
  iintro ⟨-, -, Ht⟩ Hf
  icombine Ht Hf gives Hv
  ihave %hv := internalCmraValid_discrete $$ Hv
  ipureintro
  obtain ⟨v', _, _, Hlookup, _, Hinc⟩ := HeapView.auth_op_frag_valid_total_discrete_iff hv
  rw [LocHeap.asAgree_get?] at Hlookup
  show PartialMap.get? σ.tapes l = some t
  cases Hcase : PartialMap.get? σ.tapes l with
  | none => rw [Hcase] at Hlookup; simp at Hlookup
  | some w =>
    rw [Hcase] at Hlookup
    simp only [Option.map_some, Option.some.injEq] at Hlookup
    have Hinc' : toAgree t ≼ toAgree w := Hlookup ▸ Hinc
    have : t = w := Agree.toAgree_included.mp Hinc'
    exact this ▸ rfl

theorem spec_auth_update_tape {e : Exp rT} {σ : State rT} {l : Loc} {t s : Tape} :
    ⊢@{IProp GF} specAuth ⟨e, σ⟩ -∗ l ↪ₛ t ==∗
      specAuth ⟨e, σ.update_tapes (fun h : LocHeap Tape => PartialMap.insert h l s)⟩ ∗
        l ↪ₛ s := by
  iintro Ha Hf
  ihave %Hlk := spec_auth_lookup_tape $$ Ha Hf
  unfold specAuth specTapesAuth specTapesFrag
  ihave ⟨He, Hh, Ht⟩ := Ha
  have Hval_toAgree : ✓ (toAgree s : Agree Tape) := by
    intro n; simp
  have Hupd :
      HeapView.Auth (.own 1) (LocHeap.asAgree σ.tapes) •
        HeapView.Frag l (.own 1) (toAgree t) ~~>
      HeapView.Auth (.own 1)
          (PartialMap.insert (LocHeap.asAgree σ.tapes) l (toAgree s)) •
        HeapView.Frag l (.own 1) (toAgree s) :=
    HeapView.update_replace Hval_toAgree
  ihave Hu := iOwn_update_op (E := ISpec.tapes) $$ [$Ht $Hf]
  · exact Hupd
  imod Hu
  imodintro
  ihave ⟨Ht, Hf⟩ := iOwn_op $$ Hu
  simp only [State.update_tapes, LocHeap.asAgree_insert]
  isplitr [Hf] <;> try iassumption
  isplitl [He] <;> try iassumption
  isplitl [Hh] <;> try iassumption

theorem spec_auth_tape_alloc {e : Exp rT} {σ : State rT} (t : Tape) :
    ⊢@{IProp GF} specAuth ⟨e, σ⟩ ==∗
      specAuth ⟨e, σ.update_tapes
          (fun h : LocHeap Tape => PartialMap.insert h σ.tapes.fresh t)⟩ ∗
        σ.tapes.fresh ↪ₛ t := by
  iintro Ha
  unfold specAuth specTapesAuth specTapesFrag
  ihave ⟨He, Hh, Ht⟩ := Ha
  have Hfresh : PartialMap.get? (LocHeap.asAgree σ.tapes) σ.tapes.fresh = none := by
    rw [LocHeap.asAgree_get?]
    show (σ.tapes[σ.tapes.fresh]?).map toAgree = none
    rw [ExtTreeMap.fresh_get?]; rfl
  have Hval_toAgree : ✓ (toAgree t : Agree Tape) := by
    intro n; simp
  have Hupd :
      HeapView.Auth (.own 1) (LocHeap.asAgree σ.tapes) ~~>
      HeapView.Auth (.own 1)
          (PartialMap.insert (LocHeap.asAgree σ.tapes) σ.tapes.fresh (toAgree t)) •
        HeapView.Frag σ.tapes.fresh (.own 1) (toAgree t) :=
    HeapView.update_one_alloc Hfresh DFrac.valid_own_one Hval_toAgree
  ihave Hu := iOwn_update $$ Ht
  · exact Hupd
  imod Hu
  imodintro
  ihave ⟨Ht, Hf⟩ := iOwn_op $$ Hu
  simp only [State.update_tapes, LocHeap.asAgree_insert]
  isplitr [Hf] <;> try iassumption
  isplitl [He] <;> try iassumption
  isplitl [Hh] <;> try iassumption

/-! ## Allocation

Allocates a fresh `SpecGS rT GF` instance, producing the authoritative spec state `specAuth ⟨e, σ⟩` paired
with the program fragment `⤇ e`. Heap/tape fragments are *not* produced by
this version (the adequacy use-site discards them via `_`). -/
theorem spec_ra_init {GF : BundledGFunctors} [ISPre : SpecPreGS rT GF]
    (e : Exp rT) (σ : State rT) :
    ⊢@{IProp GF} |==> ∃ IS : SpecGS rT GF,
      Cfg.specAuth (ISpec := IS) ⟨e, σ⟩ ∗ specProgFrag (ISpec := IS) e := by
  imod (iOwn_alloc (E := ISPre.prog) (SpecProg.auth e • SpecProg.frag e)
    (Auth.auth_both_valid_2 trivial .rfl)) with ⟨%γp, Hp⟩
  imod (iOwn_alloc (E := ISPre.heap)
    (HeapView.Auth (.own 1) (LocHeap.asAgree σ.heap))
    HeapView.auth_one_valid) with ⟨%γH, HH⟩
  imod (iOwn_alloc (E := ISPre.tapes)
    (HeapView.Auth (.own 1) (LocHeap.asAgree σ.tapes))
    HeapView.auth_one_valid) with ⟨%γT, HT⟩
  imodintro
  let IS : SpecGS rT GF := {
    toSpecPreGS := ISPre
    γprog := γp
    γheap := γH
    γtapes := γT }
  iexists IS
  unfold ProbLang.Cfg.specAuth specProgAuth specHeapAuth specTapesAuth specProgFrag
  ihave ⟨Hpa, Hpf⟩ := iOwn_op $$ Hp
  isplitl [Hpa HH HT]
  · isplitl [Hpa] <;> try iassumption
    isplitl [HH] <;> iassumption
  · iexact Hpf


end Algebra

/-! ## `natSpecTape` — user-level spec-side tape wrapper

Spec-side analogue of `appNatTape`. Hides the backend subtype-list tape
behind an existential, presenting `ns : List Int` to callers. -/

section NatSpecTape

variable {GF : BundledGFunctors} [ISpec : SpecGS rT GF]

/-- Spec-side user-level tape: `l` points to a tape of bound `z` whose
contents, as plain integers, match `ns`. -/
noncomputable def specNatTape (l : Loc) (z : Int) (ns : List Int) : IProp GF :=
  iprop(∃ fs : List { z' : Int // 0 ≤ z' ∧ z' < z },
    (⌜fs.map (fun x => x.val) = ns⌝) ∗ specTapesFrag l ⟨z, fs⟩)

/-- `l ↪ₛN⟨z; ns⟩` — spec-side user-level tape points-to. -/
notation:51 l:51 " ↪ₛN⟨" z:51 "; " ns:51 "⟩" => specNatTape l z ns

/-- Empty user-level spec tape collapses to the backend empty tape. -/
theorem spec_natTape_to_empty {l : Loc} {z : Int} :
    specNatTape (GF := GF) l z [] ⊢ l ↪ₛ ⟨z, []⟩ := by
  unfold specNatTape
  iintro ⟨%fs, %Hmap, Hl⟩
  have : fs = [] := List.map_eq_nil_iff.mp Hmap
  subst this
  iexact Hl

/-- Backend empty spec tape embeds into user-level empty spec tape. -/
theorem spec_empty_to_natTape {l : Loc} {z : Int} :
    (l ↪ₛ ⟨z, ([] : List { z' : Int // 0 ≤ z' ∧ z' < z })⟩) ⊢@{IProp GF}
      specNatTape l z [] := by
  iintro Hl
  unfold specNatTape
  iexists []
  isplitr; · ipureintro; rfl
  iexact Hl

/-- Read the head of a user-level spec tape. -/
theorem spec_read_natTape_head {l : Loc} {z : Int} {n : Int} {ns : List Int} :
    specNatTape (GF := GF) l z (n :: ns) ⊢
      iprop(∃ (x : { z' : Int // 0 ≤ z' ∧ z' < z })
              (xs : List { z' : Int // 0 ≤ z' ∧ z' < z }),
        l ↪ₛ ⟨z, x :: xs⟩ ∗ (⌜x.val = n⌝) ∗
        (l ↪ₛ ⟨z, xs⟩ -∗ specNatTape l z ns)) := by
  unfold specNatTape
  iintro ⟨%fs, %Hmap, Hl⟩
  have ⟨x, xs, hfs, hx, hxs⟩ := List.map_eq_cons_iff.mp Hmap
  subst hfs
  iexists x, xs
  isplitl [Hl]; · iexact Hl
  isplitr; · ipureintro; exact hx
  iintro Hl'
  iexists xs
  isplitr; · ipureintro; exact hxs
  iexact Hl'

end NatSpecTape

/-! ## Validity helpers for two spec-side heap/tape fragments at the same location

Two full-fraction `↦ₛ` fragments at the same spec location are inconsistent.
Needed by `lrel_ref`/`lrel_tape` functionality/injectivity proofs in
`Metrology/Approxis/Model.lean`. -/

section ValidHelpers
variable {GF : BundledGFunctors} [ISpec : SpecGS rT GF]

theorem specHeapFrag_valid_2 {l : Loc} {v1 v2 : Val rT} :
    ⊢@{IProp GF} specHeapFrag l v1 -∗ specHeapFrag l v2 -∗ False := by
  iintro H1 H2
  unfold specHeapFrag
  icombine H1 H2 gives Hv
  ihave %hv := internalCmraValid_discrete $$ Hv
  exfalso
  rw [HeapView.frag_op_valid_iff] at hv
  obtain ⟨hdq, _⟩ := hv
  -- `hdq : ✓ (DFrac.own 1 • DFrac.own 1)`; `valid_own_op` gives `(1 : Qp).val < 1`.
  exact absurd (DFrac.valid_own_op hdq) (lt_irrefl _)

theorem specTapesFrag_valid_2 {l : Loc} {t1 t2 : Tape} :
    ⊢@{IProp GF} specTapesFrag l t1 -∗ specTapesFrag l t2 -∗ False := by
  iintro H1 H2
  unfold specTapesFrag
  icombine H1 H2 gives Hv
  ihave %hv := internalCmraValid_discrete $$ Hv
  exfalso
  rw [HeapView.frag_op_valid_iff] at hv
  obtain ⟨hdq, _⟩ := hv
  -- `hdq : ✓ (DFrac.own 1 • DFrac.own 1)`; `valid_own_op` gives `(1 : Qp).val < 1`.
  exact absurd (DFrac.valid_own_op hdq) (lt_irrefl _)

end ValidHelpers

end SpecRA
