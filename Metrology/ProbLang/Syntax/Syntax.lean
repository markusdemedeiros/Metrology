module

public import Std
public import Std.Data.ExtTreeMap.Lemmas
public import Mathlib.Data.Countable.Basic
public import Mathlib.Tactic.DeriveCountable
import all Mathlib.Tactic.DeriveCountable
public import Mathlib.Logic.Equiv.List
public import Cslib.Foundations.Data.HasFresh
public import Cslib.Foundations.Syntax.HasSubstitution

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

inductive BaseLit | int (z : Int) | bool (b : Bool) | unit | loc (loc : Loc) | lbl (lbl : Lbl)
  deriving Inhabited, DecidableEq, Countable, Repr, BEq

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

end ProbLang
