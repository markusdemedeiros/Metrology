-- import Mathlib

def Ident : Type := String

inductive Lit (B Z R : Type _) where
| bool (b : B)
| int  (z : Z)
| real (r : R)

inductive BinOp where
| add
| mul
| lt

inductive Expr (B Z R : Type _) where
-- Literals
| elit (l : Lit B Z R)
-- Functions
| evar (s : Ident)
| erec (f x : Ident) (e : Expr B Z R)
| eapp (e1 e2 : Expr B Z R)
-- Operations
| ebinop (op : BinOp) (e1 e2 : Expr B Z R)
| econd (e et ef : Expr B Z R)
-- Products
| epair (e1 e2 : Expr B Z R)
| efst (e : Expr B Z R)
| esnd (e : Expr B Z R)
-- Sums
| eleft (e : Expr B Z R)
| eright (e : Expr B Z R)
| ecase (e el er : Expr B Z R)
-- Memory
| ealloc (ev : Expr B Z R)
| eset (el ev : Expr B Z R)
| eload (e1 : Expr B Z R)
-- Probability
| etape (en : Expr B Z R)
| erand (et en : Expr B Z R)


/-
Inductive expr :=
  (* Values *)
  | Val (v : val)
  (* Base lambda calculus *)
  | Var (x : string)
  | Rec (f x : binder) (e : expr)
  | App (e1 e2 : expr)
  (* Base types and their operations *)
  | UnOp (op : un_op) (e : expr)
  | BinOp (op : bin_op) (e1 e2 : expr)
  | If (e0 e1 e2 : expr)
  (* Products *)
  | Pair (e1 e2 : expr)
  | Fst (e : expr)
  | Snd (e : expr)
  (* Sums *)
  | InjL (e : expr)
  | InjR (e : expr)
  | Case (e0 : expr) (e1 : expr) (e2 : expr)
  (* Heap *)
  | AllocN (e1 e2 : expr) (* Array length and initial value *)
  | Load (e : expr)
  | Store (e1 : expr) (e2 : expr)
  (* Probabilistic choice *)
  | AllocTape (e : expr)
  | Rand (e1 e2 : expr)
  (* No-op operator used for cost *)
  | Tick (e : expr)
with val :=
  | LitV (l : base_lit)
  | RecV (f x : binder) (e : expr)
  | PairV (v1 v2 : val)
  | InjLV (v : val)
  | InjRV (v : val).
-/









/-

import Mathlib.MeasureTheory.Constructions.Cylinders
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.Data.Real.Basic

-- Operational semantics of continuous PPL
-- Doing it first "by hand", then changing to the automated stuff




abbrev Ident : Type _ := String

mutual

inductive Expr where
| val (v : Val)
| var (x : Ident)
| app (rator rand : Expr)

inductive Val where
| lit (l : Lit)

end

abbrev Lit.ProjTypes : Lit → Type _
| .bool b => Bool
| .int  z => Int
| .real r => Real

def Lit.Projections : (i : Lit) → Lit.ProjTypes i
| .bool b => b
| .int  z => z
| .real r => r

instance : (i : Lit) → MeasurableSpace i.ProjTypes := by
  intro i; cases i <;> infer_instance

#check @MeasureTheory.cylinderEvents Lit Lit.ProjTypes _
-- (Set.univ : Set Lit)

/-

--
--
-- #synth (∀ (i : Lit), MeasurableSpace i.ProjTypes)
--


inductive Ectx where


-/-/
