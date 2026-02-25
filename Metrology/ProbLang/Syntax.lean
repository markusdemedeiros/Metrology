import Std
import Std.Data.TreeMap.Lemmas

open Std

def Std.TreeMap.fresh [Ord K] [Add K] [One K] (t : TreeMap K V) : K :=
  match t.maxKey? with | none => 1 | some v => v + 1

theorem Std.TreeMap.fresh_get? (t : TreeMap Int V) :
    t[t.fresh]? = none := by
  unfold TreeMap.fresh
  rcases HM : t.maxKey? with _ | v
  · exact getElem?_of_isEmpty <| maxKey?_eq_none_iff.mp HM
  · rw [getElem?_eq_none_iff]
    intro hmem
    have hle := TreeMap.le_maxKey?_of_mem hmem (Option.get_of_eq_some (isSome_maxKey?_of_mem hmem) HM)
    simp [compare, compareOfLessAndEq] at hle
    split at hle; grind
    split at hle; grind
    simp at hle

abbrev Loc : Type := Int

abbrev Lbl : Type := Int

inductive Binder | anon | named (s : String)
  deriving Inhabited, DecidableEq

inductive BaseLit | int (z : Int) | bool (b : Bool) | unit | loc (loc : Loc) | lbl (lbl : Lbl)
  deriving Inhabited, DecidableEq

inductive UnOp | neg | minus
  deriving Inhabited

inductive BinOp | plus | minus | mult | and | or | xor | eq
  deriving Inhabited

inductive Expr
| lit (b : BaseLit)
| var (x : String)
| letrec (f x : Binder) (e : Expr)
| app (e1 e2 : Expr)
| unop (u : UnOp) (e : Expr)
| binop (b : BinOp) (e1 e2 : Expr)
| bif (ec et tf : Expr)
| pair (e1 e2 : Expr)
| fst (e : Expr)
| snd (e : Expr)
| inl (e : Expr)
| inr (e : Expr)
| case (ec el er : Expr)
| alloc (e : Expr) -- Initial value
| load (e : Expr)
| store (el ev : Expr)
| allocTape (e : Expr)
| rand (en et : Expr)
  deriving Inhabited

@[simp]
def Expr.isValue : Expr → Prop
| lit _ | letrec _ _ _ => True
| inl e | inr e => e.isValue
| pair e1 e2 => e1.isValue ∧ e2.isValue
| _ => False

@[simp]
def Expr.noValue (e : Expr) : Prop := ¬ e.isValue

def Val := { e : Expr // e.isValue }

open Classical in
noncomputable def Expr.toVal? (e : Expr) : Option Val :=
  if H : e.isValue then some ⟨e, H⟩ else none

def Expr.ofVal (v : Val) : Expr := v.1

structure Tape where
  bound : Int
  presamples : List { z : Int // 0 ≤ z ∧ z < bound}
  deriving Inhabited

def Tape.empty (z : Int) : Tape := ⟨z, []⟩

structure State where
  heap  : TreeMap Loc Val
  tapes : TreeMap Loc Tape
  deriving Inhabited

theorem Expr.toVal?_ofVal (v : Val) : (Expr.ofVal v).toVal? = some v := by
  obtain ⟨e, He⟩ := v
  revert He
  induction e <;> simp_all [isValue, Expr.ofVal, Expr.toVal?]

theorem Expr.ofVal_of_toVal_some {e : Expr} : ∀ {v}, e.toVal? = some v → Expr.ofVal v = e := by
  induction e <;> simp [toVal?, ofVal]

theorem ofVal_injective : Function.Injective Expr.ofVal :=
  fun ⟨_, _⟩ _ _ => by congr

inductive EctxItem
| appL (v2 : Val)
| appR (e1 : Expr)
| unop (op : UnOp)
| binopL (op : BinOp) (v2 : Val)
| binopR (op : BinOp) (e1 : Expr)
| bifC (e1 e2 : Expr)
| pairL (v2 : Val)
| pairR (e1 : Expr)
| fst
| snd
| inl
| inr
| case (e1 e2 : Expr)
| alloc
| load
| storeL (v2 : Val)
| storeR (e1 : Expr)
| allocTape
| randL (v2 : Val)
| randR (e1 : Expr)

def EctxItem.FillItem (Ki : EctxItem) (e : Expr) : Expr :=
  match Ki with
  | appL v2 => .app e (.ofVal v2)
  | appR e1 => .app e1 e
  | unop op => .unop op e
  | binopL op v2 => .binop op e (.ofVal v2)
  | binopR op e1 => .binop op e1 e
  | bifC e1 e2 => .bif e e1 e2
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
  | .allocTape => .allocTape e
  | .randL v2 => .rand e (.ofVal v2)
  | .randR e1 => .rand e1 e

noncomputable def Expr.DecompItem (e : Expr) : Option (EctxItem × Expr) :=
  match e with
  | app e1 e2 =>
    e2.toVal?.casesOn (some (.appR e1, e2)) fun v2 =>
    e1.toVal?.casesOn (some (.appL v2, e1)) fun _ => none
  | unop op e1 =>
    e.toVal?.casesOn (some (.unop op, e1)) fun _ => none
  | binop op e1 e2 =>
    e2.toVal?.casesOn (some (.binopR op e1, e2)) fun v2 =>
    e1.toVal?.casesOn (some (.binopL op v2, e1)) fun _ => none
  | .bif ec et ef =>
    ec.toVal?.casesOn (some (.bifC et ef, ec)) fun _ => none
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
  | _ => none

def Expr.subst (e : Expr) (x : String) (v : Expr) : Expr :=
  match e with
  | lit l => lit l
  | var y =>
    if x = y
    then v
    else var y
  | letrec f y e =>
    if .named x ≠ f ∧ .named x ≠ y
    then letrec f y (e.subst x v)
    else letrec f y e
  | app e1 e2 => app (e1.subst x v) (e2.subst x v)
  | unop op e => unop op (e.subst x v)
  | binop op e1 e2 => binop op (e1.subst x v) (e2.subst x v)
  | .bif ec et ef => .bif (ec.subst x v) (et.subst x v) (ef.subst x v)
  | pair e1 e2 => pair (e1.subst x v) (e2.subst x v)
  | fst e => fst (e.subst x v)
  | snd e => snd (e.subst x v)
  | inl e => inl (e.subst x v)
  | inr e => inr (e.subst x v)
  | case ec el er => case (ec.subst x v) (el.subst x v) (er.subst x v)
  | alloc e => alloc (e.subst x v)
  | load e => load (e.subst x v)
  | store e1 e2 => store (e1.subst x v) (e2.subst x v)
  | rand e1 e2 => rand (e1.subst x v) (e2.subst x v)
  | allocTape e => allocTape (e.subst x v)

def Expr.subst' (mx : Binder) (v e : Expr) : Expr :=
  match mx with | .named x => e.subst x v | .anon => e

def UnOp.eval (op : UnOp) (v : Expr) : Option Expr :=
  match op, v with
  | neg, .lit (.bool b) => some <| .lit <| .bool <| ¬ b
  | minus, .lit (.int z) => some <| .lit <| .int <| z.neg
  | _, _ => none

def BinOp.eval (op : BinOp) (v1 v2 : Expr) : Option Expr :=
  match op, v1, v2 with
  | plus,  .lit (.int z1),  .lit (.int z2)  => some <| .lit <| .int (z1 + z2)
  | minus, .lit (.int z1),  .lit (.int z2)  => some <| .lit <| .int (z1 - z2)
  | mult,  .lit (.int z1),  .lit (.int z2)  => some <| .lit <| .int (z1 * z2)
  | and,   .lit (.bool b1), .lit (.bool b2) => some <| .lit <| .bool (b1 && b2)
  | or,    .lit (.bool b1), .lit (.bool b2) => some <| .lit <| .bool (b1 || b2)
  | xor,   .lit (.bool b1), .lit (.bool b2) => some <| .lit <| .bool (b1 ^^ b2)
  | eq,    .lit l1,         .lit l2         => some <| .lit <| .bool (decide (l1 = l2))
  |_,      _,        _        => none

def State.update_heap (σ : State) (f : TreeMap Loc Val → TreeMap Loc Val) : State :=
  ⟨f σ.heap, σ.tapes⟩

def State.update_tapes (σ : State) (f : TreeMap Loc Tape → TreeMap Loc Tape) : State :=
  ⟨σ.heap, f σ.tapes⟩

-- PORTING NOTE: Ignore for now
-- Lemma state_upd_tapes_twice σ l n xs ys :
--   state_upd_tapes <[l:=(n; ys)]> (state_upd_tapes <[l:=(n; xs)]> σ) = state_upd_tapes <[l:=(n; ys)]> σ.
-- Proof. rewrite /state_upd_tapes /=. f_equal. apply insert_insert. Qed.

-- PORTING NOTE: Ignore for now
-- Lemma state_upd_tapes_same σ σ' l n xs ys :
--   state_upd_tapes <[l:=(n; ys)]> σ = state_upd_tapes <[l:=(n; xs)]> σ' -> xs = ys.
-- Proof. rewrite /state_upd_tapes /=. intros K. simplify_eq.
--        rewrite map_eq_iff in H.
--        specialize (H l).
--        rewrite !lookup_insert in H.
--        by simplify_eq.
-- Qed.

-- PORTING NOTE: Ignore for now
-- Lemma state_upd_tapes_no_change σ l n ys :
--   tapes σ !! l = Some (n; ys)->
--   state_upd_tapes <[l:=(n; ys)]> σ = σ .
-- Proof.
--   destruct σ as [? t]. simpl.
--   intros Ht.
--   f_equal.
--   apply insert_id. done.
-- Qed.

-- PORTING NOTE: Ignore for now
-- Lemma state_upd_tapes_same' σ σ' l n xs (x y : fin (S n)) :
--   state_upd_tapes <[l:=(n; xs++[x])]> σ = state_upd_tapes <[l:=(n; xs++[y])]> σ' -> x = y.
-- Proof. intros H. apply state_upd_tapes_same in H.
--        by simplify_eq.
-- Qed.

-- PORTING NOTE: Ignore for now
-- Lemma state_upd_tapes_neq' σ σ' l n xs (x y : fin (S n)) :
--   x≠y -> state_upd_tapes <[l:=(n; xs++[x])]> σ ≠ state_upd_tapes <[l:=(n; xs++[y])]> σ'.
-- Proof. move => H /state_upd_tapes_same ?. simplify_eq.
-- Qed.

-- PORTING NOTE: Ignore for now
-- Lemma state_upd_heap_singleton l v σ :
--   state_upd_heap_N l 1 v σ = state_upd_heap <[l:= v]> σ.
-- Proof.
--   destruct σ as [h p]. rewrite /state_upd_heap_N /=. f_equiv.
--   rewrite right_id insert_union_singleton_l. done.
-- Qed.

-- PORTING NOTE: Ignore for now
-- Lemma state_upd_tapes_heap σ l1 l2 n xs m v :
--   state_upd_tapes <[l2:=(n; xs)]> (state_upd_heap_N l1 m v σ) =
--   state_upd_heap_N l1 m v (state_upd_tapes <[l2:=(n; xs)]> σ).
-- Proof.
--   by rewrite /state_upd_tapes /state_upd_heap_N /=.
-- Qed.

structure Cfg where
  expr : Expr
  state : State

theorem Ectx.FillItem_injective : Function.Injective (EctxItem.FillItem K) := by
  cases K <;> simp [Function.Injective, EctxItem.FillItem]

theorem FillItem_isValue {K : EctxItem} : (K.FillItem e).isValue → e.isValue := by
  cases K <;> simp [EctxItem.FillItem] <;> grind

-- Lemma fill_item_no_val_inj Ki1 Ki2 e1 e2 :
--   to_val e1 = None → to_val e2 = None →
--   fill_item Ki1 e1 = fill_item Ki2 e2 → Ki1 = Ki2.
-- Proof. destruct Ki2, Ki1; naive_solver eauto with f_equal. Qed.

-- Fixpoint height (e : expr) : nat :=
--   match e with
--   | Val _ => 1
--   | Var _ => 1
--   | Rec _ _ e => 1 + height e
--   | App e1 e2 => 1 + height e1 + height e2
--   | UnOp _ e => 1 + height e
--   | BinOp _ e1 e2 => 1 + height e1 + height e2
--   | If e0 e1 e2 => 1 + height e0 + height e1 + height e2
--   | Pair e1 e2 => 1 + height e1 + height e2
--   | Fst e => 1 + height e
--   | Snd e => 1 + height e
--   | InjL e => 1 + height e
--   | InjR e => 1 + height e
--   | Case e0 e1 e2 => 1 + height e0 + height e1 + height e2
--   | AllocN e1 e2 => 1 + height e1 + height e2
--   | Load e => 1 + height e
--   | Store e1 e2 => 1 + height e1 + height e2
--   | AllocTape e => 1 + height e
--   | Rand e1 e2 => 1 + height e1 + height e2
--   | Laplace e1 e2 e3 => 1 + height e1 + height e2 + height e3
--   | Tick e => 1 + height e
--   end.
--
-- Definition expr_ord (e1 e2 : expr) : Prop := (height e1 < height e2)%nat.
--
-- Lemma expr_ord_wf' h e : (height e ≤ h)%nat → Acc expr_ord e.
-- Proof.
--   rewrite /expr_ord. revert e; induction h.
--   { destruct e; simpl; lia. }
--   intros []; simpl;
--     constructor; simpl; intros []; eauto with lia.
-- Defined.
--
-- Lemma expr_ord_wf : well_founded expr_ord.
-- Proof. red; intro; eapply expr_ord_wf'; eauto. Defined.
--
-- Lemma decomp_expr_ord Ki e e' : decomp_item e = Some (Ki, e') → expr_ord e' e.
-- Proof.
--   rewrite /expr_ord /decomp_item.
--   destruct Ki ; repeat destruct_match ; intros [=] ; subst ; cbn ; lia.
-- Qed.
--
-- Lemma decomp_fill_item Ki e :
--   to_val e = None → decomp_item (fill_item Ki e) = Some (Ki, e).
-- Proof. destruct Ki ; simpl ; by repeat destruct_match. Qed.

-- Lemma decomp_fill_item_2 e e' Ki :
--   decomp_item e = Some (Ki, e') → fill_item Ki e' = e ∧ to_val e' = None.
-- Proof.
--   rewrite /decomp_item ;
--     destruct e ; try done ;
--     destruct Ki ; cbn ; repeat destruct_match ; intros [=] ; subst ; auto.
-- Qed.
