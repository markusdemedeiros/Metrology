import Mathlib.Data.ENNReal.Basic
import Iris
import Iris.Algebra.HeapView
import Iris.Instances.IProp.Instance
import Iris.Std.HeapInstances
import Metrology.Iris.Algebra
import Metrology.ProbLang.Syntax.Syntax
import Metrology.ProbLang.Syntax.Notation

section SpecRA
open Std Iris Iris.Std COFE ProbLang

instance : COFE Exp := COFE.ofDiscrete _ Eq_Equivalence
instance : OFE.Discrete Exp := ⟨id⟩
instance (x : Exp) : OFE.DiscreteE x := ⟨OFE.Discrete.discrete_0⟩

instance : COFE Tape := COFE.ofDiscrete _ Eq_Equivalence
instance : OFE.Discrete Tape := ⟨id⟩
instance (x : Tape) : OFE.DiscreteE x := ⟨OFE.Discrete.discrete_0⟩

instance : COFE Val := COFE.ofDiscrete _ Eq_Equivalence
instance : OFE.Discrete Val := ⟨id⟩
instance (x : Val) : OFE.DiscreteE x := ⟨OFE.Discrete.discrete_0⟩

instance : OFE.Leibniz Exp := ⟨id⟩
instance : OFE.Leibniz Tape := ⟨id⟩
instance : OFE.Leibniz Val := ⟨id⟩

abbrev SpecProg := Auth ℕ+ (Option (Excl Exp))
abbrev SpecHeap := HeapView ℕ+ Loc (Agree Val) LocHeap
abbrev SpecTapes := HeapView ℕ+ Loc (Agree Tape) LocHeap

def SpecProg.auth (e : Exp) : SpecProg := ● (some <| .excl e)
def SpecProg.frag (e : Exp) : SpecProg := ◯ (some <| .excl e)

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
  apply ExtensionalPartialMap.equiv_iff_eq.mp
  intro k
  by_cases hk : l = k
  · subst hk
    rw [LocHeap.asAgree_get?, LawfulPartialMap.get?_insert_eq rfl,
        LawfulPartialMap.get?_insert_eq rfl]
    rfl
  · rw [LocHeap.asAgree_get?, LawfulPartialMap.get?_insert_ne hk,
        LawfulPartialMap.get?_insert_ne hk, LocHeap.asAgree_get?]

class SpecPreGS (GF : BundledGFunctors) where
  prog : ElemG GF (constOF SpecProg)
  heap : ElemG GF (constOF SpecHeap)
  tapes : ElemG GF (constOF SpecTapes)

attribute [reducible, instance] SpecPreGS.prog SpecPreGS.heap SpecPreGS.tapes

class SpecGS (GF : BundledGFunctors) extends SpecPreGS GF where
  γprog : GName
  γheap : GName
  γtapes : GName

section Resources

variable {GF : BundledGFunctors} [ISpec : SpecGS GF]

def specProgAuth (e : Exp) : IProp GF := iOwn (E := ISpec.prog) ISpec.γprog (.auth e)
def specProgFrag (e : Exp) : IProp GF := iOwn (E := ISpec.prog) ISpec.γprog (.frag e)

def specHeapAuth (σ : LocHeap Val) : IProp GF :=
  iOwn (E := ISpec.heap) ISpec.γheap (HeapView.Auth (.own 1) (LocHeap.asAgree σ))
def specHeapFrag (ℓ : Loc) (v : Val) : IProp GF :=
  iOwn (E := ISpec.heap) ISpec.γheap (HeapView.Frag ℓ (.own 1) (toAgree v))

def specTapesAuth (σ : LocHeap Tape) : IProp GF :=
  iOwn (E := ISpec.tapes) ISpec.γtapes (HeapView.Auth (.own 1) (LocHeap.asAgree σ))
def specTapesFrag (ℓ : Loc) (t : Tape) : IProp GF :=
  iOwn (E := ISpec.tapes) ISpec.γtapes (HeapView.Frag ℓ (.own 1) (toAgree t))

def ProbLang.Cfg.specAuth (c : Cfg) : IProp GF :=
  let ⟨e, ⟨σ, τ⟩⟩ := c
  iprop(specProgAuth e ∗ specHeapAuth σ ∗ specTapesAuth τ)

-- TODO: Add ⤇ to my Lean4 emacs mode (lol)
-- TODO: Make ↪ less annoying to type too
notation "⤇ " t:50 => specProgFrag t
notation l:50 " ↦ₛ " v:50 => specHeapFrag l v
notation l:50 " ↪ₛ " τ:50 => specTapesFrag l τ

end Resources

section Algebra

variable {GF : BundledGFunctors} [ISpec : SpecGS GF]

open ProbLang Cfg

theorem some_excl_inc_excl_exp_eq {e1 e2 : Exp} (H : some (Excl.excl e1) ≼ some (Excl.excl e2)) :
    e1 = e2 := by
  have H' := Option.inc_iff.mp H
  simp at H'
  rcases H' with (H'|H')
  · exact H'
  · have H'' := excl_included.mp H'
    simp at H''

theorem specAuth_specFrag_agree {e1 e2 : Exp} {σ : State} :
    ⊢@{IProp GF} specAuth ⟨e1, σ⟩ -∗ ⤇ e2 -∗ ⌜e1 = e2⌝ := by
  unfold specAuth specProgAuth specProgFrag
  iintro ⟨He, -, -⟩ Hf
  ihave Hv := iOwn_cmraValid_op (E := ISpec.prog) $$ [He Hf]
  · isplitl [He] <;> iassumption
  ihave %hv := internalCmraValid_discrete (A := SpecProg) (PROP := IProp GF) $$ Hv
  ipure_intro
  obtain ⟨hinc, _⟩ := Auth.auth_both_valid_discrete.mp hv
  exact some_excl_inc_excl_exp_eq hinc |>.symm

theorem specProg_update {e1 e2 e3 : Exp} {σ : State} :
    ⊢@{IProp GF} specAuth ⟨e1, σ⟩ -∗ ⤇ e2 ==∗ specAuth ⟨e3, σ⟩ ∗ ⤇ e3 := by
  iintro Ha Hf
  ihave %he := specAuth_specFrag_agree (GF := GF) $$ Ha Hf
  subst he
  unfold specAuth specProgAuth specProgFrag; simp only []
  ihave ⟨He, Hh, Ht⟩ := Ha
  have Hupd : SpecProg.frag e1 • SpecProg.auth e1 ~~> SpecProg.frag e3 • SpecProg.auth e3 :=
    Auth.auth_update (.option (.exclusive trivial))
  ihave Hu := iOwn_update_op (E := ISpec.prog) $$ [Hf He]
  · exact Hupd
  · isplitl [Hf] <;> iassumption
  imod Hu
  imodintro
  ihave ⟨Hf, Ha⟩ := iOwn_op (E := ISpec.prog) $$ Hu
  isplitr [Hf] <;> try iassumption
  isplitl [Ha] <;> try iassumption
  isplitl [Hh] <;> try iassumption


theorem spec_auth_lookup_heap {e : Exp} {σ : State} {l : Loc} {v : Val} :
    ⊢@{IProp GF} specAuth ⟨e, σ⟩ -∗ l ↦ₛ v -∗ ⌜σ.heap[l]? = some v⌝ := by
  unfold specAuth specHeapAuth specHeapFrag
  iintro ⟨-, Hh, -⟩ Hf
  ihave Hv := iOwn_cmraValid_op (E := ISpec.heap) $$ [Hh Hf]
  · isplitl [Hh] <;> iassumption
  ihave %hv := internalCmraValid_discrete (A := SpecHeap) (PROP := IProp GF) $$ Hv
  ipure_intro
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
    have : v = w := Agree.toAgree_included_L.mp Hinc'
    exact this ▸ rfl

theorem spec_auth_update_heap {e : Exp} {σ : State} {l : Loc} {v w : Val} :
    ⊢@{IProp GF} specAuth ⟨e, σ⟩ -∗ l ↦ₛ v ==∗
      specAuth ⟨e, σ.update_heap (fun h : LocHeap Val => PartialMap.insert h l w)⟩ ∗
        l ↦ₛ w := by
  iintro Ha Hf
  ihave %Hlk := spec_auth_lookup_heap (GF := GF) $$ Ha Hf
  unfold specAuth specHeapAuth specHeapFrag
  ihave ⟨He, Hh, Ht⟩ := Ha
  have Hval_toAgree : ✓ (toAgree w : Agree Val) := by
    intro n; simp [Agree.validN_iff, toAgree]
  have Hupd :
      HeapView.Auth (F := ℕ+) (.own 1) (LocHeap.asAgree σ.heap) •
        HeapView.Frag (F := ℕ+) (H := LocHeap) l (.own 1) (toAgree v) ~~>
      HeapView.Auth (F := ℕ+) (.own 1)
          (PartialMap.insert (LocHeap.asAgree σ.heap) l (toAgree w)) •
        HeapView.Frag (F := ℕ+) l (.own 1) (toAgree w) :=
    HeapView.update_replace Hval_toAgree
  ihave Hu := iOwn_update_op (E := ISpec.heap) $$ [Hh Hf]
  · exact Hupd
  · isplitl [Hh] <;> iassumption
  imod Hu
  imodintro
  ihave ⟨Hh, Hf⟩ := iOwn_op (E := ISpec.heap) $$ Hu
  -- Goal: specAuth ⟨e, σ.update_heap(insert l w)⟩ ∗ l ↦ₛ w
  -- After unfold: specProgAuth e ∗ specHeapAuth (insert l w σ.heap) ∗ specTapesAuth _ ∗ Frag
  simp only [State.update_heap, LocHeap.asAgree_insert]
  isplitr [Hf] <;> try iassumption
  isplitl [He] <;> try iassumption
  isplitl [Hh] <;> try iassumption

theorem spec_auth_heap_alloc {e : Exp} {σ : State} (v : Val) :
    ⊢@{IProp GF} specAuth ⟨e, σ⟩ ==∗
      specAuth ⟨e, σ.update_heap
          (fun h : LocHeap Val => PartialMap.insert h σ.heap.fresh v)⟩ ∗
        σ.heap.fresh ↦ₛ v := by
  iintro Ha
  unfold specAuth specHeapAuth specHeapFrag
  ihave ⟨He, Hh, Ht⟩ := Ha
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
  ihave Hu := iOwn_update (E := ISpec.heap) $$ Hh
  · exact Hupd
  imod Hu
  imodintro
  ihave ⟨Hh, Hf⟩ := iOwn_op (E := ISpec.heap) $$ Hu
  simp only [State.update_heap, LocHeap.asAgree_insert]
  isplitr [Hf] <;> try iassumption
  isplitl [He] <;> try iassumption
  isplitl [Hh] <;> try iassumption

theorem spec_auth_lookup_tape {e : Exp} {σ : State} {l : Loc} {t : Tape} :
    ⊢@{IProp GF} specAuth ⟨e, σ⟩ -∗ l ↪ₛ t -∗ ⌜σ.tapes[l]? = some t⌝ := by
  unfold specAuth specTapesAuth specTapesFrag
  iintro ⟨-, -, Ht⟩ Hf
  ihave Hv := iOwn_cmraValid_op (E := ISpec.tapes) $$ [Ht Hf]
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

theorem spec_auth_update_tape {e : Exp} {σ : State} {l : Loc} {t s : Tape} :
    ⊢@{IProp GF} specAuth ⟨e, σ⟩ -∗ l ↪ₛ t ==∗
      specAuth ⟨e, σ.update_tapes (fun h : LocHeap Tape => PartialMap.insert h l s)⟩ ∗
        l ↪ₛ s := by
  iintro Ha Hf
  ihave %Hlk := spec_auth_lookup_tape (GF := GF) $$ Ha Hf
  unfold specAuth specTapesAuth specTapesFrag
  ihave ⟨He, Hh, Ht⟩ := Ha
  have Hval_toAgree : ✓ (toAgree s : Agree Tape) := by
    intro n; simp [Agree.validN_iff, toAgree]
  have Hupd :
      HeapView.Auth (F := ℕ+) (.own 1) (LocHeap.asAgree σ.tapes) •
        HeapView.Frag (F := ℕ+) (H := LocHeap) l (.own 1) (toAgree t) ~~>
      HeapView.Auth (F := ℕ+) (.own 1)
          (PartialMap.insert (LocHeap.asAgree σ.tapes) l (toAgree s)) •
        HeapView.Frag (F := ℕ+) l (.own 1) (toAgree s) :=
    HeapView.update_replace Hval_toAgree
  ihave Hu := iOwn_update_op (E := ISpec.tapes) $$ [Ht Hf]
  · exact Hupd
  · isplitl [Ht] <;> iassumption
  imod Hu
  imodintro
  ihave ⟨Ht, Hf⟩ := iOwn_op (E := ISpec.tapes) $$ Hu
  simp only [State.update_tapes, LocHeap.asAgree_insert]
  isplitr [Hf] <;> try iassumption
  isplitl [He] <;> try iassumption
  isplitl [Hh] <;> try iassumption

theorem spec_auth_tape_alloc {e : Exp} {σ : State} (t : Tape) :
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
    intro n; simp [Agree.validN_iff, toAgree]
  have Hupd :
      HeapView.Auth (F := ℕ+) (.own 1) (LocHeap.asAgree σ.tapes) ~~>
      HeapView.Auth (F := ℕ+) (.own 1)
          (PartialMap.insert (LocHeap.asAgree σ.tapes) σ.tapes.fresh (toAgree t)) •
        HeapView.Frag (F := ℕ+) σ.tapes.fresh (.own 1) (toAgree t) :=
    HeapView.update_one_alloc Hfresh DFrac.valid_own_one Hval_toAgree
  ihave Hu := iOwn_update (E := ISpec.tapes) $$ Ht
  · exact Hupd
  imod Hu
  imodintro
  ihave ⟨Ht, Hf⟩ := iOwn_op (E := ISpec.tapes) $$ Hu
  simp only [State.update_tapes, LocHeap.asAgree_insert]
  isplitr [Hf] <;> try iassumption
  isplitl [He] <;> try iassumption
  isplitl [Hh] <;> try iassumption

/-
  (** Laplace Tapes *)

  Lemma spec_auth_lookup_tape_laplace e1 σ1 l v dq :
    spec_auth (e1, σ1) -∗ l ↪Lₛ{dq} v -∗ ⌜σ1.(tapes_laplace) !! l = Some v⌝.
  Proof. iIntros "(_&_&_&H) H'/=". iApply (ghost_map_lookup with "H H'"). Qed.

  Lemma spec_auth_update_tape_laplace w e1 σ1 l v :
    spec_auth (e1, σ1) -∗ l ↪Lₛ{#1} v ==∗
    spec_auth (e1, state_upd_tapes_laplace <[l:=w]> σ1) ∗ l ↪Lₛ{#1} w.
  Proof.
    iIntros "(?&?&?&H) H'/=".
    iMod (ghost_map_update with "H H'") as "?".
    iModIntro. by iFrame.
  Qed.

  Lemma spec_auth_tape_laplace_alloc e σ num den mean :
    spec_auth (e, σ) ==∗
    spec_auth (e, state_upd_tapes_laplace <[fresh_loc σ.(tapes_laplace) := (Tape_Laplace num den mean [])]> σ) ∗ fresh_loc σ.(tapes_laplace) ↪Lₛ (num, den, mean; []).
  Proof.
    iIntros "(? & ? & ?&Htapes) /=".
    iMod (ghost_map_insert (fresh_loc σ.(tapes_laplace)) with "Htapes") as "[H Hl]".
    { apply not_elem_of_dom, fresh_loc_is_fresh. }
    by iFrame.
  Qed.

End theory.

Lemma spec_ra_init e σ `{specGpreS Σ} :
  ⊢ |==> ∃ _ : specG_prob_lang Σ,
      spec_auth (e, σ) ∗ ⤇ e ∗ ([∗ map] l ↦ v ∈ σ.(heap), l ↦ₛ v) ∗ ([∗ map] α ↦ t ∈ σ.(tapes), α ↪ₛ t) ∗ ([∗ map] α ↦ t ∈ σ.(tapes_laplace), α ↪Lₛ t).
Proof.
  iMod (own_alloc ((● (Excl' e)) ⋅ (◯ (Excl' e)))) as "(%γp & Hprog_auth & Hprog_frag)".
  { by apply auth_both_valid_discrete. }
  iMod (ghost_map_alloc σ.(heap)) as "[%γH [Hh Hls]]".
  iMod (ghost_map_alloc σ.(tapes)) as "[%γT [Ht Hαs]]".
  iMod (ghost_map_alloc σ.(tapes_laplace)) as "[%γTL [Htl Hαs']]".
  iExists (SpecGS _ _ γp _ _ _ γH γT γTL).
  by iFrame.
Qed.

(** Tapes containing natural numbers defined as a wrapper over backend tapes *)
Definition nat_spec_tape `{specG_prob_lang Σ} l (N : nat) (ns : list nat) : iProp Σ :=
  ∃ (fs : list (fin (S N))), ⌜fin_to_nat <$> fs = ns⌝ ∗ l ↪ₛ (N; fs).

Notation "l ↪ₛN ( M ; ns )" := (nat_spec_tape l M ns)%I
       (at level 20, format "l ↪ₛN ( M ; ns )") : bi_scope.

Section spec_tape_interface.
  Context `{!specG_prob_lang Σ}.

  (** Helper lemmas to go back and forth between the user-level representation
      of tapes (using nat) and the backend (using fin) *)

  Lemma spec_tapeN_to_empty l M :
    (l ↪ₛN ( M ; [] ) -∗ l ↪ₛ ( M ; [] )).
  Proof.
    iIntros "Hl".
    iDestruct "Hl" as (?) "(%Hmap & Hl')".
    by destruct (fmap_nil_inv _ _ Hmap).
  Qed.


  Lemma empty_to_spec_tapeN l M :
    (l ↪ₛ ( M ; [] ) -∗ l ↪ₛN ( M ; [] )).
  Proof.
    iIntros "Hl".
    iExists []. auto.
  Qed.

  Lemma read_spec_tape_head l M n ns :
    (l ↪ₛN ( M ; n :: ns ) -∗
      ∃ x xs, l ↪ₛ ( M ; x :: xs ) ∗ ⌜ fin_to_nat x = n ⌝ ∗
              ( l ↪ₛ ( M ; xs ) -∗l ↪ₛN ( M ; ns ) )).
  Proof.
    iIntros "Hl".
    iDestruct "Hl" as (xss) "(%Hmap & Hl')".
    destruct (fmap_cons_inv _ _ _ _ Hmap) as (x&xs&->&Hxs&->).
    iExists x, xs.
    iFrame.
    iSplit; auto.
    iIntros.
    iExists xs; auto.
  Qed.

End spec_tape_interface.

-/

end Algebra
end SpecRA
