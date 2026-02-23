import Std

open Std

abbrev Loc : Type _ := Int

abbrev Lbl : Type _ := Int

inductive Binder | anon | named (s : String)
  deriving Inhabited

inductive BaseLit | int (z : ℤ) | bool (b : Bool) | unit | loc (loc : Loc) | lbl (lbl : Lbl)
  deriving Inhabited

inductive UnOp | neg | minus
  deriving Inhabited

inductive BinOp | plus | minus | mult | and | or | xor | eq
  deriving Inhabited

inductive Expr
| lit (b : BaseLit)
| letrec (f x : Binder) (e : Expr)
| app (e1 e2 : Expr)
| unop (u : UnOp) (e : Expr)
| binop (b : BinOp) (e1 e2 : Expr)
| bif (ec et tf : BiNOp)
| pair (e1 e2 : Expr)
| fst (e : Expr)
| snd (e : Expr)
| inl (e : Expr)
| inr (e : Expr)
| case (ec el er : Expr)
| alloc (e : Expr) -- Initial value
| load (e : Expr)
| store (el ev : Expr)
| alloctape (e : Expr)
| rand (en et : Expr)
  deriving Inhabited

@[simp]
def Expr.isValue : Expr → Prop
| lit _ | letrec _ _ _ => True
| inl e | inr e => e.isValue
| pair e1 e2 => e1.isValue ∧ e2.isValue
| _ => False

def Val := { e : Expr // e.isValue }

def Expr.toVal? : Expr → Option Val 
| letrec f x e' => some ⟨letrec f x e', trivial⟩
| lit l => some ⟨lit l, trivial⟩
| inl e' => e'.toVal?.bind fun ⟨v, Hv⟩ => some ⟨inl v, Hv⟩
| inr e' => e'.toVal?.bind fun ⟨v, Hv⟩ => some ⟨inr v, Hv⟩
| pair e1 e2 =>
  e1.toVal?.bind fun ⟨v1, H1⟩ =>
  e2.toVal?.bind fun ⟨v2, H2⟩ =>
  some ⟨pair v1 v2, ⟨H1, H2⟩⟩
| _ => none

def Expr.ofVal (v : Val) : Expr := v.1

structure Tape where
  bound : Nat
  presamples : List (Fin bound.succ)

structure State where
  heap  : TreeMap Loc Val
  tapes : TreeMap Loc Tape




-- Lemma to_of_val v : to_val (of_val v) = Some v.
-- Proof. by destruct v. Qed.

-- Lemma of_to_val e v : to_val e = Some v → of_val v = e.
-- Proof. destruct e=>//=. by intros [= <-]. Qed.

-- Global Instance of_val_inj : Inj (=) (=) of_val.
-- Proof. intros ??. congruence. Qed.

-- Global Instance state_inhabited : Inhabited state :=
--   populate {| heap := inhabitant; tapes := inhabitant |}.
-- Global Instance val_inhabited : Inhabited val := populate (LitV LitUnit).
-- Global Instance expr_inhabited : Inhabited expr := populate (Val inhabitant).

-- Inductive ectx_item :=
--   | AppLCtx (v2 : val)
--   | AppRCtx (e1 : expr)
--   | UnOpCtx (op : un_op)
--   | BinOpLCtx (op : bin_op) (v2 : val)
--   | BinOpRCtx (op : bin_op) (e1 : expr)
--   | IfCtx (e1 e2 : expr)
--   | PairLCtx (v2 : val)
--   | PairRCtx (e1 : expr)
--   | FstCtx
--   | SndCtx
--   | InjLCtx
--   | InjRCtx
--   | CaseCtx (e1 : expr) (e2 : expr)
--   | AllocNLCtx (v2 : val)
--   | AllocNRCtx (e1 : expr)
--   | LoadCtx
--   | StoreLCtx (v2 : val)
--   | StoreRCtx (e1 : expr)
--   | AllocTapeCtx
--   | RandLCtx (v2 : val)
--   | RandRCtx (e1 : expr)
--   | LaplaceNumCtx (v2 : val) (v3 : val)
--   | LaplaceDenCtx (e1 : expr) (v3 : val)
--   | LaplaceLocCtx (e1 : expr) (e2 : expr)
--   | TickCtx.

-- Definition fill_item (Ki : ectx_item) (e : expr) : expr :=
--   match Ki with
--   | AppLCtx v2 => App e (of_val v2)
--   | AppRCtx e1 => App e1 e
--   | UnOpCtx op => UnOp op e
--   | BinOpLCtx op v2 => BinOp op e (Val v2)
--   | BinOpRCtx op e1 => BinOp op e1 e
--   | IfCtx e1 e2 => If e e1 e2
--   | PairLCtx v2 => Pair e (Val v2)
--   | PairRCtx e1 => Pair e1 e
--   | FstCtx => Fst e
--   | SndCtx => Snd e
--   | InjLCtx => InjL e
--   | InjRCtx => InjR e
--   | CaseCtx e1 e2 => Case e e1 e2
--   | AllocNLCtx v2 => AllocN e (Val v2)
--   | AllocNRCtx e1 => AllocN e1 e
--   | LoadCtx => Load e
--   | StoreLCtx v2 => Store e (Val v2)
--   | StoreRCtx e1 => Store e1 e
--   | AllocTapeCtx => AllocTape e
--   | RandLCtx v2 => Rand e (Val v2)
--   | RandRCtx e1 => Rand e1 e
--   | LaplaceNumCtx v2 v3 => Laplace e (Val v2) (Val v3)
--   | LaplaceDenCtx e1 v3 => Laplace e1 e (Val v3)
--   | LaplaceLocCtx e1 e2 => Laplace e1 e2 e
--   | TickCtx => Tick e
--   end.

-- Definition decomp_item (e : expr) : option (ectx_item * expr) :=
--   let noval (e : expr) (ei : ectx_item) :=
--     match e with Val _ => None | _ => Some (ei, e) end in
--   match e with
--   | App e1 e2      =>
--       match e2 with
--       | (Val v)    => noval e1 (AppLCtx v)
--       | _          => Some (AppRCtx e1, e2)
--       end
--   | UnOp op e      => noval e (UnOpCtx op)
--   | BinOp op e1 e2 =>
--       match e2 with
--       | Val v      => noval e1 (BinOpLCtx op v)
--       | _          => Some (BinOpRCtx op e1, e2)
--       end
--   | If e0 e1 e2    => noval e0 (IfCtx e1 e2)
--   | Pair e1 e2     =>
--       match e2 with
--       | Val v      => noval e1 (PairLCtx v)
--       | _          => Some (PairRCtx e1, e2)
--       end
--   | Fst e          => noval e FstCtx
--   | Snd e          => noval e SndCtx
--   | InjL e         => noval e InjLCtx
--   | InjR e         => noval e InjRCtx
--   | Case e0 e1 e2  => noval e0 (CaseCtx e1 e2)
--   | AllocN e1 e2        =>
--       match e2 with
--       | Val v      => noval e1 (AllocNLCtx v)
--       | _          => Some (AllocNRCtx e1, e2)
--       end
--
--   | Load e         => noval e LoadCtx
--   | Store e1 e2    =>
--       match e2 with
--       | Val v      => noval e1 (StoreLCtx v)
--       | _          => Some (StoreRCtx e1, e2)
--       end
--   | AllocTape e    => noval e AllocTapeCtx
--   | Rand e1 e2     =>
--       match e2 with
--       | Val v      => noval e1 (RandLCtx v)
--       | _          => Some (RandRCtx e1, e2)
--       end
--   | Laplace e1 e2 e3 =>
--       match e3 with
--       | Val v3 =>
--           match e2 with
--           | Val v2 => noval e1 (LaplaceNumCtx v2 v3)
--           | _ => Some (LaplaceDenCtx e1 v3, e2)
--           end
--       | _ => Some (LaplaceLocCtx e1 e2, e3)
--       end
--   | Tick e         => noval e TickCtx
--   | _              => None
--   end.

-- Fixpoint subst (x : string) (v : val) (e : expr)  : expr :=
--   match e with
--   | Val _ => e
--   | Var y => if decide (x = y) then Val v else Var y
--   | Rec f y e =>
--      Rec f y $ if decide (BNamed x ≠ f ∧ BNamed x ≠ y) then subst x v e else e
--   | App e1 e2 => App (subst x v e1) (subst x v e2)
--   | UnOp op e => UnOp op (subst x v e)
--   | BinOp op e1 e2 => BinOp op (subst x v e1) (subst x v e2)
--   | If e0 e1 e2 => If (subst x v e0) (subst x v e1) (subst x v e2)
--   | Pair e1 e2 => Pair (subst x v e1) (subst x v e2)
--   | Fst e => Fst (subst x v e)
--   | Snd e => Snd (subst x v e)
--   | InjL e => InjL (subst x v e)
--   | InjR e => InjR (subst x v e)
--   | Case e0 e1 e2 => Case (subst x v e0) (subst x v e1) (subst x v e2)
--   | AllocN e1 e2 => AllocN (subst x v e1) (subst x v e2)
--   | Load e => Load (subst x v e)
--   | Store e1 e2 => Store (subst x v e1) (subst x v e2)
--   | AllocTape e => AllocTape (subst x v e)
--   | Rand e1 e2 => Rand (subst x v e1) (subst x v e2)
--   | Laplace e1 e2 e3 => Laplace (subst x v e1) (subst x v e2) (subst x v e3)
--   | Tick e => Tick (subst x v e)
--   end.

-- Definition subst' (mx : binder) (v : val) : expr → expr :=
--   match mx with BNamed x => subst x v | BAnon => λ x, x end.

-- Definition un_op_eval (op : un_op) (v : val) : option val :=
--   match op, v with
--   | NegOp, LitV (LitBool b) => Some $ LitV $ LitBool (negb b)
--   | NegOp, LitV (LitInt z) => Some $ LitV $ LitInt (Z.lnot z)
--   | MinusUnOp, LitV (LitInt z) => Some $ LitV $ LitInt (- z)
--   | _, _ => None
--   end.

-- Definition bin_op_eval_int (op : bin_op) (n1 n2 : Z) : base_lit :=
--   match op with
--   | PlusOp => LitInt (n1 + n2)
--   | MinusOp => LitInt (n1 - n2)
--   | MultOp => LitInt (n1 * n2)
--   | QuotOp => LitInt (n1 `quot` n2)
--   | RemOp => LitInt (n1 `rem` n2)
--   | AndOp => LitInt (Z.land n1 n2)
--   | OrOp => LitInt (Z.lor n1 n2)
--   | XorOp => LitInt (Z.lxor n1 n2)
--   | ShiftLOp => LitInt (n1 ≪ n2)
--   | ShiftROp => LitInt (n1 ≫ n2)
--   | LeOp => LitBool (bool_decide (n1 ≤ n2))
--   | LtOp => LitBool (bool_decide (n1 < n2))
--   | EqOp => LitBool (bool_decide (n1 = n2))
--   | OffsetOp => LitInt (n1 + n2) (* Treat offsets as ints *)
--   end%Z.

-- Definition bin_op_eval_bool (op : bin_op) (b1 b2 : bool) : option base_lit :=
--   match op with
--   | PlusOp | MinusOp | MultOp | QuotOp | RemOp => None (* Arithmetic *)
--   | AndOp => Some (LitBool (b1 && b2))
--   | OrOp => Some (LitBool (b1 || b2))
--   | XorOp => Some (LitBool (xorb b1 b2))
--   | ShiftLOp | ShiftROp => None (* Shifts *)
--   | LeOp | LtOp => None (* InEquality *)
--   | EqOp => Some (LitBool (bool_decide (b1 = b2)))
--   | OffsetOp => None
--   end.

-- Definition bin_op_eval_loc (op : bin_op) (l1 : loc) (v2 : base_lit) : option base_lit :=
--   match op, v2 with
--   | OffsetOp, LitInt off => Some $ LitLoc (l1 +ₗ off)
--   | LeOp, LitLoc l2 => Some $ LitBool (bool_decide (l1 ≤ₗ l2))
--   | LtOp, LitLoc l2 => Some $ LitBool (bool_decide (l1 <ₗ l2))
--   | _, _ => None
--   end.

-- Definition bin_op_eval (op : bin_op) (v1 v2 : val) : option val :=
--   if decide (op = EqOp) then
--     if decide (vals_compare_safe v1 v2) then
--       Some $ LitV $ LitBool $ bool_decide (v1 = v2)
--     else
--       None
--   else
--     match v1, v2 with
--     | LitV (LitInt n1), LitV (LitInt n2) => Some $ LitV $ bin_op_eval_int op n1 n2
--     | LitV (LitBool b1), LitV (LitBool b2) => LitV <$> bin_op_eval_bool op b1 b2
--     | LitV (LitLoc l1), LitV v2 => LitV <$> bin_op_eval_loc op l1 v2
--     | _, _ => None
--     end.

-- Definition state_upd_heap (f : gmap loc val → gmap loc val) (σ : state) : state :=
--   {| heap := f σ.(heap); tapes := σ.(tapes) |}.
-- Global Arguments state_upd_heap _ !_ /.

-- Definition state_upd_tapes (f : gmap loc tape → gmap loc tape) (σ : state) : state :=
--   {| heap := σ.(heap); tapes := f σ.(tapes) |}.
-- Global Arguments state_upd_tapes _ !_ /.

-- Lemma state_upd_tapes_twice σ l n xs ys :
--   state_upd_tapes <[l:=(n; ys)]> (state_upd_tapes <[l:=(n; xs)]> σ) = state_upd_tapes <[l:=(n; ys)]> σ.
-- Proof. rewrite /state_upd_tapes /=. f_equal. apply insert_insert. Qed.
--
-- Lemma state_upd_tapes_same σ σ' l n xs ys :
--   state_upd_tapes <[l:=(n; ys)]> σ = state_upd_tapes <[l:=(n; xs)]> σ' -> xs = ys.
-- Proof. rewrite /state_upd_tapes /=. intros K. simplify_eq.
--        rewrite map_eq_iff in H.
--        specialize (H l).
--        rewrite !lookup_insert in H.
--        by simplify_eq.
-- Qed.

-- Lemma state_upd_tapes_no_change σ l n ys :
--   tapes σ !! l = Some (n; ys)->
--   state_upd_tapes <[l:=(n; ys)]> σ = σ .
-- Proof.
--   destruct σ as [? t]. simpl.
--   intros Ht.
--   f_equal.
--   apply insert_id. done.
-- Qed.

-- Lemma state_upd_tapes_same' σ σ' l n xs (x y : fin (S n)) :
--   state_upd_tapes <[l:=(n; xs++[x])]> σ = state_upd_tapes <[l:=(n; xs++[y])]> σ' -> x = y.
-- Proof. intros H. apply state_upd_tapes_same in H.
--        by simplify_eq.
-- Qed.

-- Lemma state_upd_tapes_neq' σ σ' l n xs (x y : fin (S n)) :
--   x≠y -> state_upd_tapes <[l:=(n; xs++[x])]> σ ≠ state_upd_tapes <[l:=(n; xs++[y])]> σ'.
-- Proof. move => H /state_upd_tapes_same ?. simplify_eq.
-- Qed.

-- Lemma state_upd_heap_singleton l v σ :
--   state_upd_heap_N l 1 v σ = state_upd_heap <[l:= v]> σ.
-- Proof.
--   destruct σ as [h p]. rewrite /state_upd_heap_N /=. f_equiv.
--   rewrite right_id insert_union_singleton_l. done.
-- Qed.

-- Lemma state_upd_tapes_heap σ l1 l2 n xs m v :
--   state_upd_tapes <[l2:=(n; xs)]> (state_upd_heap_N l1 m v σ) =
--   state_upd_heap_N l1 m v (state_upd_tapes <[l2:=(n; xs)]> σ).
-- Proof.
--   by rewrite /state_upd_tapes /state_upd_heap_N /=.
-- Qed.
--
-- Lemma heap_array_replicate_S_end l v n :
--   heap_array l (replicate (S n) v) = heap_array l (replicate n v) ∪ {[l +ₗ n:= v]}.
-- Proof.
--   induction n.
--   - simpl.
--     rewrite map_union_empty.
--     rewrite map_empty_union.
--     by rewrite loc_add_0.
--   - rewrite replicate_S_end
--      heap_array_app
--      IHn /=.
--     rewrite map_union_empty length_replicate //.
-- Qed.
