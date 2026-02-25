import Std
import Std.Data.ExtTreeMap.Lemmas

open Std

def Std.ExtTreeMap.fresh (t : ExtTreeMap Int V) : Int :=
  match t.maxKey? with | none => 1 | some v => v + 1

theorem Std.ExtTreeMap.fresh_get? (t : ExtTreeMap Int V) :
    t[t.fresh]? = none := by
  unfold ExtTreeMap.fresh
  rcases HM : t.maxKey? with _ | v
  · have hemp : t = ∅ := maxKey?_eq_none_iff.mp HM
    simp [hemp]
  · apply getElem?_eq_none
    intro hmem
    have hle := ExtTreeMap.le_maxKey?_of_mem hmem (Option.get_of_eq_some (isSome_maxKey?_of_mem hmem) HM)
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
  heap  : ExtTreeMap Loc Val
  tapes : ExtTreeMap Loc Tape
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

def State.update_heap (σ : State) (f : ExtTreeMap Loc Val → ExtTreeMap Loc Val) : State :=
  ⟨f σ.heap, σ.tapes⟩

def State.update_tapes (σ : State) (f : ExtTreeMap Loc Tape → ExtTreeMap Loc Tape) : State :=
  ⟨σ.heap, f σ.tapes⟩

theorem State.update_tapes_twice (σ : State) (l : Loc) (ys xs : Tape) :
    (σ.update_tapes (·.insert l xs)).update_tapes (·.insert l ys) =
    σ.update_tapes (·.insert l ys) := by
  unfold State.update_tapes; congr 1; grind

theorem State.update_tapes_same {σ σ' : State}
    (h : σ.update_tapes (·.insert l xs) = σ'.update_tapes (·.insert l ys)) :
    xs = ys := by
  have key := congrArg (·.tapes[l]?) h
  simp [State.update_tapes] at key
  exact key

theorem State.update_tapes_no_change {σ : State} (h : σ.tapes[l]? = some ys) :
    σ.update_tapes (·.insert l ys) = σ := by
  unfold State.update_tapes; congr 1; grind

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
  expr : Expr
  state : State

theorem Ectx.FillItem_injective : Function.Injective (EctxItem.FillItem K) := by
  cases K <;> simp [Function.Injective, EctxItem.FillItem]

theorem FillItem_isValue {K : EctxItem} : (K.FillItem e).isValue → e.isValue := by
  cases K <;> simp [EctxItem.FillItem] <;> grind

theorem EctxItem.FillItem_noVal_inj {Ki1 Ki2 : EctxItem} {e1 e2 : Expr}
    (hv1 : ¬e1.isValue) (hv2 : ¬e2.isValue)
    (h : Ki1.FillItem e1 = Ki2.FillItem e2) : Ki1 = Ki2 := by
  sorry
-- Lemma fill_item_no_val_inj Ki1 Ki2 e1 e2 :
--   to_val e1 = None → to_val e2 = None →
--   fill_item Ki1 e1 = fill_item Ki2 e2 → Ki1 = Ki2.
-- Proof. destruct Ki2, Ki1; naive_solver eauto with f_equal. Qed.

@[simp]
def Expr.height : Expr → Nat
  | lit _ | var _ => 1
  | letrec _ _ e => 1 + e.height
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
  | allocTape e => 1 + e.height
  | .bif e0 e1 e2 => 1 + e0.height + e1.height + e2.height
  | .case e0 e1 e2 => 1 + e0.height + e1.height + e2.height

-- Lemma decomp_expr_ord Ki e e' : decomp_item e = Some (Ki, e') → expr_ord e' e.
-- Proof.
--   rewrite /expr_ord /decomp_item.
--   destruct Ki ; repeat destruct_match ; intros [=] ; subst ; cbn ; lia.
-- Qed.
--
theorem EctxItem.DecompItem_FillItem (Ki : EctxItem) {e : Expr} (hv : ¬e.isValue) :
    (Ki.FillItem e).DecompItem = some (Ki, e) := by
  sorry
-- Lemma decomp_fill_item Ki e :
--   to_val e = None → decomp_item (fill_item Ki e) = Some (Ki, e).
-- Proof. destruct Ki ; simpl ; by repeat destruct_match. Qed.

theorem Expr.DecompItem_fill {e e' : Expr} {Ki : EctxItem}
    (h : e.DecompItem = some (Ki, e')) : Ki.FillItem e' = e ∧ ¬e'.isValue := by
  sorry
-- Lemma decomp_fill_item_2 e e' Ki :
--   decomp_item e = Some (Ki, e') → fill_item Ki e' = e ∧ to_val e' = None.
-- Proof.
--   rewrite /decomp_item ;
--     destruct e ; try done ;
--     destruct Ki ; cbn ; repeat destruct_match ; intros [=] ; subst ; auto.
-- Qed.

theorem EctxItem.FillItem_noVal {Ki : EctxItem} {e : Expr} (hv : ¬e.isValue) :
    ¬(Ki.FillItem e).isValue := by
  sorry
-- Lemma fill_item_not_val K e : to_val e = None → to_val (fill_item K e) = None.
-- Proof. rewrite !eq_None_not_Some. eauto using fill_item_val. Qed.

abbrev Ectx := List EctxItem

def Ectx.empty : Ectx := []

def Ectx.comp (e1 e2 : Ectx) : Ectx := e2 ++ e1

def Ectx.fill (K : Ectx) (e : Expr) : Expr := K.foldl (flip EctxItem.FillItem) e

theorem fill_app (K1 K2 : Ectx) e : (K1 ++ K2).fill e = K2.fill (K1.fill e) :=
  List.foldl_append

theorem Ectx.fill_comp (K1 K2 : Ectx) (e : Expr) :
    K1.fill (K2.fill e) = (K2.comp K1).fill e := by
  sorry
-- Lemma fill_comp : ∀ (K1 K2 : ectx) e, fill K1 (fill K2 e) = fill (flip app K1 K2) e
--     - intros K1 K2 e. by rewrite /fill /= foldl_app.

theorem Ectx.fill_injective (K : Ectx) : Function.Injective K.fill := by
  sorry
-- Lemma fill_inj : ∀ K : ectx, Inj eq eq (fill K)
--     - intros K; induction K as [|Ki K IH]; rewrite /Inj; naive_solver.

theorem Ectx.fill_isValue {K : Ectx} {e : Expr} (hv : (K.fill e).isValue) : e.isValue := by
  sorry
--     assert (fill_val : ∀ K e, is_Some (to_val (fill K e)) → is_Some (to_val e)).
--     { intros K. induction K as [|Ki K IH]=> e //=. by intros ?%IH%fill_item_val. }

theorem Ectx.fill_noVal {K : Ectx} {e : Expr} (hv : ¬e.isValue) : ¬(K.fill e).isValue := by
  sorry
--   Lemma fill_not_val K e : to_val e = None → to_val (fill K e) = None.
--   Proof. rewrite !eq_None_not_Some. eauto using fill_val. Qed.

theorem Expr.DecompItem_height {e : Expr} (h : e.DecompItem = some (Ki, e')) :
    e'.height < e.height := by
  simp only [DecompItem, toVal?] at h
  split at h
  all_goals simp_all
  all_goals (split at h <;> simp_all <;> try omega)
  all_goals (split at h <;> simp_all <;> omega)

noncomputable def Expr.decomp (e : Expr) : Ectx × Expr :=
  match _h : e.DecompItem with
  | some (Ki, e') =>
      let (K, e'') := decomp e'
      (K ++ [Ki], e'')
  | none => ([], e)
  termination_by e.height
  decreasing_by exact Expr.DecompItem_height _h

theorem Expr.decomp_unfold (e : Expr) :
    e.decomp =
      match e.DecompItem with
      | some (Ki, e') => let (K, e'') := e'.decomp; (K ++ [Ki], e'')
      | none => ([], e) := by
  sorry
--   Lemma decomp_unfold e :
--     decomp e =
--       match decomp_item e with
--       | Some (Ki, e') => let '(K, e'') := decomp e' in (K ++ [Ki], e'')
--       | None => ([], e)
--       end.
--   Proof.
--     rewrite /decomp WfExtensionality.fix_sub_eq_ext /= -/decomp.
--     repeat case_match; try done.
--   Qed.

theorem Expr.decomp_inv_nil {e e' : Expr} (h : e.decomp = ([], e')) :
    e.DecompItem = none ∧ e = e' := by
  sorry
--   Lemma decomp_inv_nil e e' :
--     decomp e = ([], e') → decomp_item e = None ∧ e = e'.
--   Proof.
--     rewrite decomp_unfold.
--     destruct (decomp_item e) as [[Ki e'']|] eqn:Heq; [|by intros [=]].
--     destruct (decomp e''). intros [= Hl He].
--     assert (l = []) as ->.
--     { destruct l; inversion Hl. }
--     inversion Hl.
--   Qed.

theorem Expr.decomp_inv_cons {Ki : EctxItem} {K : Ectx} {e e'' : Expr}
    (h : e.decomp = (K ++ [Ki], e'')) :
    ∃ e', e.DecompItem = some (Ki, e') ∧ e'.decomp = (K, e'') := by
  sorry
--   Lemma decomp_inv_cons Ki K e e'' :
--     decomp e = (K ++ [Ki], e'') → ∃ e', decomp_item e = Some (Ki, e') ∧ decomp e' = (K, e'').
--   Proof.
--     rewrite decomp_unfold.
--     destruct (decomp_item e) as [[Ki' e']|] eqn:Heq'.
--     2 : { intros [=]. by destruct K. }
--     destruct (decomp e') as [K' e'''] eqn:Heq.
--     intros [= [<- <-]%list_snoc_singleton_inv ->].
--     eauto.
--   Qed.

theorem Expr.decomp_fill {K : Ectx} {e e' : Expr} (h : e.decomp = (K, e')) :
    K.fill e' = e := by
  sorry
-- Lemma decomp_fill  : ∀ (K : ectx) e e', decomp e = (K, e') → fill K e' = e
--     - induction K as [|Ki K] using rev_ind; intros e e'.
--       { intros [? ->]%decomp_inv_nil=>//. }
--       intros (e'' & Hrei & Hre)%decomp_inv_cons.
--       rewrite fill_app /= (IHK e'') //.
--       by apply decomp_fill_item_2.

theorem Expr.decomp_val_empty {K : Ectx} {e e' : Expr}
    (hd : e.decomp = (K, e')) (hv : e'.isValue) : K = [] := by
  sorry
-- Lemma decomp_val_empty : ∀ (K : ectx) e e', decomp e = (K, e') → is_Some (to_val e') → K = []
--     - intros K. induction K as [|Ki K] using rev_ind; [done|].
--       intros ?? (e'' & Hrei & Hre)%decomp_inv_cons Hv.
--       specialize (IHK _ _ Hre Hv). simplify_eq.
--       apply decomp_inv_nil in Hre as [? ?]; simplify_eq.
--       by apply decomp_fill_item_2 in Hrei as [_ ?%eq_None_not_Some].

theorem Expr.decomp_fill_comp {e e' : Expr} {K K' : Ectx}
    (hv : ¬e.isValue) (hd : e.decomp = (K', e')) :
    (K.fill e).decomp = (K' ++ K, e') := by
  sorry
-- Lemma decomp_fill_comp  : ∀ e e' (K K' : ectx), to_val e = None → decomp e = (K', e') → decomp (fill K e) = (flip app K K', e')
--     - intros e e' K K'. revert K' e e'.
--       induction K as [|Ki K] using rev_ind.
--       { intros ??? =>/=. rewrite app_nil_r //. }
--       intros K' e e' Hval Hre. rewrite fill_app /=.
--       rewrite decomp_unfold.
--       rewrite decomp_fill_item; [|auto using fill_item_not_val].
--       rewrite (IHK K' _ e') //=.
--       rewrite !app_assoc //.
