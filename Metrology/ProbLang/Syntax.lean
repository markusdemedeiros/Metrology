import Std
import Std.Data.ExtTreeMap.Lemmas
import Mathlib.Data.Countable.Basic
import Mathlib.Tactic.DeriveCountable
import Mathlib.Logic.Equiv.List

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

abbrev Loc : Type := Int

abbrev Lbl : Type := Int
inductive Binder | anon | named (s : String)
  deriving Inhabited, DecidableEq, Countable, Repr, BEq

inductive BaseLit | int (z : Int) | bool (b : Bool) | unit | loc (loc : Loc) | lbl (lbl : Lbl)
  deriving Inhabited, DecidableEq, Countable, Repr, BEq

inductive UnOp | neg | minus
  deriving Inhabited, Countable, Repr, BEq

inductive BinOp | plus | minus | mult | and | or | xor | eq
  deriving Inhabited, Countable, Repr, BEq

inductive Exp
| lit (b : BaseLit)
| var (x : String)
| letrec (f x : Binder) (e : Exp)
| app (e1 e2 : Exp)
| unop (u : UnOp) (e : Exp)
| binop (b : BinOp) (e1 e2 : Exp)
| cond (ec et tf : Exp)
| pair (e1 e2 : Exp)
| fst (e : Exp)
| snd (e : Exp)
| inl (e : Exp)
| inr (e : Exp)
| case (ec el er : Exp)
| alloc (e : Exp) -- Initial value
| load (e : Exp)
| store (el ev : Exp)
| tape (e : Exp)
| rand (en et : Exp)
| fail
  deriving Inhabited, Countable, Repr, BEq

@[simp]
def Exp.isValue : Exp → Prop
| lit _ | letrec _ _ _ => True
| inl e | inr e => e.isValue
| pair e1 e2 => e1.isValue ∧ e2.isValue
| _ => False

def Exp.isValueB : Exp → Bool
  | .lit _ | .letrec _ _ _ => true
  | .inl e | .inr e => e.isValueB
  | .pair e1 e2 => e1.isValueB && e2.isValueB
  | _ => false

theorem Exp.isValueB_iff (e : Exp) : e.isValueB = true ↔ e.isValue := by
  induction e <;> simp_all [isValueB, isValue, Bool.and_eq_true]

theorem Exp.isValueB_false_iff (e : Exp) : e.isValueB = false ↔ ¬e.isValue := by
  simp [← isValueB_iff, Bool.not_eq_true]

@[simp]
def Exp.noValue (e : Exp) : Prop := ¬ e.isValue

def Val := { e : Exp // e.isValue }

instance : Countable Val := Subtype.countable

instance instCountableTreeMapLocVal : Countable (ExtTreeMap Loc Val compare) := by
  obtain ⟨f_v, Hf_v⟩ : Countable (List (Loc × Val)) := by infer_instance
  let f_items : ExtTreeMap Loc Val compare → List (Loc × Val) := ExtTreeMap.toList
  have Hf_items : Function.Injective f_items := by
    simp [f_items]
    intro H1 H2 He
    exact ExtTreeMap.toList_inj.mp (Hf_v (congrArg f_v (Hf_v (congrArg f_v He))))
  exists (fun t => f_v <| f_items t)
  intro H1 H2 He
  exact ExtTreeMap.ext_getElem? (congrFun (congrArg getElem? (Hf_items (Hf_v He))))


open Classical in
noncomputable def Exp.toVal? (e : Exp) : Option Val :=
  if H : e.isValue then some ⟨e, H⟩ else none

def Exp.toValB? (e : Exp) : Option Val :=
  if H : e.isValueB = true then some ⟨e, e.isValueB_iff.mp H⟩ else none

theorem Exp.toValB?_eq_toVal? (e : Exp) : e.toValB? = e.toVal? := by
  simp only [toValB?, toVal?]
  by_cases H : e.isValue
  · have hB : e.isValueB = true := (isValueB_iff e).mpr H
    simp [hB, H]
  · have hB : e.isValueB = false := by simp [(isValueB_iff e).not.mpr H]
    simp [hB, H]

def Exp.ofVal (v : Val) : Exp := v.1

structure Tape where
  bound : Int
  presamples : List { z : Int // 0 ≤ z ∧ z < bound}
  deriving Inhabited, Countable

instance instCountableTreeMapLocTape : Countable (ExtTreeMap Loc Tape compare) := by
  obtain ⟨f_v, Hf_v⟩ : Countable (List (Loc × Tape)) := by infer_instance
  let f_items : ExtTreeMap Loc Tape compare → List (Loc × Tape) := ExtTreeMap.toList
  have Hf_items : Function.Injective f_items := by
    simp [f_items]
    intro H1 H2 He
    exact ExtTreeMap.toList_inj.mp (Hf_v (congrArg f_v (Hf_v (congrArg f_v He))))
  exists (fun t => f_v <| f_items t)
  intro H1 H2 He
  exact ExtTreeMap.ext_getElem? (congrFun (congrArg getElem? (Hf_items (Hf_v He))))

def Tape.empty (z : Int) : Tape := ⟨z, []⟩

structure State where
  heap  : ExtTreeMap Loc Val
  tapes : ExtTreeMap Loc Tape
  deriving Inhabited, Countable

theorem Exp.toVal?_ofVal (v : Val) : (Exp.ofVal v).toVal? = some v := by
  obtain ⟨e, He⟩ := v
  revert He
  induction e <;> simp_all [isValue, Exp.ofVal, Exp.toVal?]

theorem Exp.ofVal_of_toVal_some {e : Exp} : ∀ {v}, e.toVal? = some v → Exp.ofVal v = e := by
  induction e <;> simp [toVal?, ofVal]
  intros _ _ _ h
  rw [← h]

theorem ofVal_injective : Function.Injective Exp.ofVal :=
  fun ⟨_, _⟩ _ _ => by congr

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

def EctxItem.FillItem (Ki : EctxItem) (e : Exp) : Exp :=
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

def Exp.DecompItem (e : Exp) : Option (EctxItem × Exp) :=
  match e with
  | app e1 e2 =>
    e2.toValB?.casesOn (some (.appR e1, e2)) fun v2 =>
    e1.toValB?.casesOn (some (.appL v2, e1)) fun _ => none
  | unop op e1 =>
    e1.toValB?.casesOn (some (.unop op, e1)) fun _ => none
  | binop op e1 e2 =>
    e2.toValB?.casesOn (some (.binopR op e1, e2)) fun v2 =>
    e1.toValB?.casesOn (some (.binopL op v2, e1)) fun _ => none
  | .cond ec et ef =>
    ec.toValB?.casesOn (some (.condC et ef, ec)) fun _ => none
  | pair e1 e2 =>
    e2.toValB?.casesOn (some (.pairR e1, e2)) fun v2 =>
    e1.toValB?.casesOn (some (.pairL v2, e1)) fun _ => none
  | fst e1 =>
    e1.toValB?.casesOn (some (.fst, e1)) fun _ => none
  | snd e1 =>
    e1.toValB?.casesOn (some (.snd, e1)) fun _ => none
  | inl e1 =>
    e1.toValB?.casesOn (some (.inl, e1)) fun _ => none
  | inr e1 =>
    e1.toValB?.casesOn (some (.inr, e1)) fun _ => none
  | alloc e1 =>
    e1.toValB?.casesOn (some (.alloc, e1)) fun _ => none
  | load e1 =>
    e1.toValB?.casesOn (some (.load, e1)) fun _ => none
  | store e1 e2 =>
    e2.toValB?.casesOn (some (.storeR e1, e2)) fun v2 =>
    e1.toValB?.casesOn (some (.storeL v2, e1)) fun _ => none
  | rand e1 e2 =>
    e2.toValB?.casesOn (some (.randR e1, e2)) fun v2 =>
    e1.toValB?.casesOn (some (.randL v2, e1)) fun _ => none
  | .case ec el er =>
    ec.toValB?.casesOn (some (.case el er, ec)) fun _ => none
  | tape e1 =>
    e1.toValB?.casesOn (some (.tape, e1)) fun _ => none
  | _ => none

def Exp.subst (e : Exp) (x : String) (v : Exp) : Exp :=
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
  | .cond ec et ef => .cond (ec.subst x v) (et.subst x v) (ef.subst x v)
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
  | tape e => tape (e.subst x v)
  | fail => fail

def Exp.subst' (mx : Binder) (v e : Exp) : Exp :=
  match mx with | .named x => e.subst x v | .anon => e

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
  expr : Exp
  state : State
  deriving Countable

theorem Ectx.FillItem_injective : Function.Injective (EctxItem.FillItem K) := by
  cases K <;> simp [Function.Injective, EctxItem.FillItem]

theorem FillItem_isValue {K : EctxItem} : (K.FillItem e).isValue → e.isValue := by
  cases K <;> simp [EctxItem.FillItem]; grind

theorem EctxItem.FillItem_noVal_inj {Ki1 Ki2 : EctxItem} {e1 e2 : Exp}
    (hv1 : ¬e1.isValue) (hv2 : ¬e2.isValue)
    (h : Ki1.FillItem e1 = Ki2.FillItem e2) : Ki1 = Ki2 := by
  cases Ki1 <;> cases Ki2 <;>
    simp_all [EctxItem.FillItem, Exp.ofVal] <;>
    -- (try (obtain ⟨_, hval⟩ := ‹Val›; simp_all [Exp.isValue])) <;>
    grind [ofVal_injective, Subtype.ext_iff]

@[simp]
def Exp.height : Exp → Nat
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
  | tape e => 1 + e.height
  | .cond e0 e1 e2 => 1 + e0.height + e1.height + e2.height
  | .case e0 e1 e2 => 1 + e0.height + e1.height + e2.height
  | fail => 1

theorem EctxItem.DecompItem_FillItem (Ki : EctxItem) {e : Exp} (hv : ¬e.isValue) :
    (Ki.FillItem e).DecompItem = some (Ki, e) := by
  have hvB : e.isValueB = false := by simp [(Exp.isValueB_iff e).not.mpr hv]
  cases Ki with
  | appL v2 | binopL _ v2 | pairL v2 | storeL v2 | randL v2 =>
    obtain ⟨val, hval⟩ := v2
    have hvalB : val.isValueB = true := (Exp.isValueB_iff val).mpr hval
    simp [EctxItem.FillItem, Exp.DecompItem, Exp.toValB?, hvB, hvalB, Exp.ofVal]
  | _ => simp [EctxItem.FillItem, Exp.DecompItem, Exp.toValB?, hvB]

theorem Exp.DecompItem_fill {e e' : Exp} {Ki : EctxItem}
    (h : e.DecompItem = some (Ki, e')) : Ki.FillItem e' = e ∧ ¬e'.isValue := by
  simp only [DecompItem, toValB?, isValueB_iff] at h
  cases e <;> simp_all [EctxItem.FillItem, ofVal] <;>
    (split at h <;> simp_all [Option.some.injEq, Prod.mk.injEq, isValueB_false_iff]) <;>
    (try (split at h <;> simp_all [Option.some.injEq, Prod.mk.injEq, isValueB_false_iff])) <;>
    (try (obtain ⟨rfl, rfl⟩ := h; simp_all))

theorem EctxItem.FillItem_noVal {Ki : EctxItem} {e : Exp} (hv : ¬e.isValue) :
    ¬(Ki.FillItem e).isValue :=
  fun h => hv (FillItem_isValue h)

abbrev Ectx := List EctxItem

def Ectx.empty : Ectx := []

def Ectx.comp (e1 e2 : Ectx) : Ectx := e2 ++ e1

def Ectx.fill (K : Ectx) (e : Exp) : Exp := K.foldl (flip EctxItem.FillItem) e

theorem fill_app (K1 K2 : Ectx) e : (K1 ++ K2).fill e = K2.fill (K1.fill e) :=
  List.foldl_append

theorem Ectx.fill_comp (K1 K2 : Ectx) (e : Exp) :
    K1.fill (K2.fill e) = (K1.comp K2).fill e := by
  simp [Ectx.comp, fill_app]

theorem Ectx.fill_injective (K : Ectx) : Function.Injective K.fill := by
  induction K with
  | nil => intro _ _ h; exact h
  | cons Ki K ih => exact fun _ _ h => Ectx.FillItem_injective (ih h)

theorem Ectx.fill_noVal {K : Ectx} {e : Exp} (hv : ¬e.isValue) : ¬(K.fill e).isValue := by
  induction K generalizing e with
  | nil => exact hv
  | cons Ki K ih => exact ih (EctxItem.FillItem_noVal hv)

theorem Ectx.fill_isValue {K : Ectx} {e : Exp} (hv : (K.fill e).isValue) : e.isValue :=
  Classical.byContradiction fun h => absurd hv (Ectx.fill_noVal h)

theorem Exp.DecompItem_height {e : Exp} (h : e.DecompItem = some (Ki, e')) :
    e'.height < e.height := by
  simp only [DecompItem, toValB?, isValueB_iff] at h
  split at h
  all_goals simp_all
  all_goals (split at h <;> simp_all <;> try omega)
  all_goals (split at h <;> simp_all <;> omega)

def Exp.decomp (e : Exp) : Ectx × Exp :=
  match _h : e.DecompItem with
  | some (Ki, e') =>
      let (K, e'') := decomp e'
      (K ++ [Ki], e'')
  | none => ([], e)
  termination_by e.height
  decreasing_by exact Exp.DecompItem_height _h

theorem Exp.decomp_unfold (e : Exp) :
    e.decomp =
      match _h : e.DecompItem with
      | some (Ki, e') => let (K, e'') := e'.decomp; (K ++ [Ki], e'')
      | none => ([], e) :=
  Exp.decomp.eq_1 e

theorem Exp.decomp_inv_nil {e e' : Exp} (h : e.decomp = ([], e')) :
    e.DecompItem = none ∧ e = e' := by
  rw [Exp.decomp] at h
  split at h
  · obtain ⟨K, e''⟩ := e.decomp
    simp_all [List.append_eq_nil_iff]
  · exact ⟨by assumption, by simp_all⟩

theorem Exp.decomp_inv_cons {Ki : EctxItem} {K : Ectx} {e e'' : Exp}
    (h : e.decomp = (K ++ [Ki], e'')) :
    ∃ e', e.DecompItem = some (Ki, e') ∧ e'.decomp = (K, e'') := by
  rw [decomp_unfold] at h
  split at h
  · rename_i Ki' e' hd
    simp only at h
    obtain ⟨hK, he⟩ := Prod.mk.inj h
    have hlen : (e'.decomp.1).length = K.length := by
      have := congrArg List.length hK; simp at this; omega
    obtain ⟨hK', hKi⟩ := List.append_inj hK hlen
    have hKi' : Ki' = Ki := List.singleton_inj.mp hKi
    exact ⟨e', hd.symm ▸ hKi' ▸ rfl,
           Prod.ext hK' (by simp [he])⟩
  · simp_all [List.append_eq_nil_iff]

theorem Exp.decomp_fill {K : Ectx} {e e' : Exp} (h : e.decomp = (K, e')) :
    K.fill e' = e := by
  suffices ∀ n K (e e' : Exp), K.length = n → e.decomp = (K, e') → K.fill e' = e by
    exact this K.length K e e' rfl h
  intro n
  induction n with
  | zero =>
    intro K e e' hlen hd
    have : K = [] := List.eq_nil_of_length_eq_zero hlen
    subst this; exact (decomp_inv_nil hd).2.symm
  | succ n ih =>
    intro K e e' hlen hd
    have hne : K ≠ [] := by intro hK; simp [hK] at hlen
    obtain ⟨K'', Ki, rfl⟩ : ∃ K'' Ki, K = K'' ++ [Ki] :=
      ⟨K.dropLast, K.getLast hne, (List.dropLast_concat_getLast hne).symm⟩
    obtain ⟨e'', hKi, hK''⟩ := decomp_inv_cons hd
    have hlen'' : K''.length = n := by simp at hlen; omega
    -- (K'' ++ [Ki]).fill e' = Ki.FillItem (K''.fill e') = Ki.FillItem e'' = e
    have hfill := ih K'' e'' e' hlen'' hK''
    have hitem := (DecompItem_fill hKi).1
    simp only [Ectx.fill, List.foldl_append, List.foldl_cons, List.foldl_nil] at *
    show Ki.FillItem (List.foldl (flip EctxItem.FillItem) e' K'') = e
    rw [hfill]
    exact hitem

-- TODO: Cleanup
theorem Exp.decomp_val_empty {K : Ectx} {e e' : Exp}
    (hd : e.decomp = (K, e')) (hv : e'.isValue) : K = [] := by
  suffices ∀ n K (e e' : Exp), K.length = n → e.decomp = (K, e') → e'.isValue → K = [] by
    exact this K.length K e e' rfl hd hv
  intro n
  induction n with
  | zero => intros; exact List.eq_nil_of_length_eq_zero ‹_›
  | succ n ih =>
    intro K e e' hlen hd hv
    have hne : K ≠ [] := by intro hK; simp [hK] at hlen
    obtain ⟨K'', Ki, rfl⟩ : ∃ K'' Ki, K = K'' ++ [Ki] :=
      ⟨K.dropLast, K.getLast hne, (List.dropLast_concat_getLast hne).symm⟩
    obtain ⟨e'', hKi, hK''⟩ := decomp_inv_cons hd
    have hlen'' : K''.length = n := by simp at hlen; omega
    have hK''nil : K'' = [] := ih K'' e'' e' hlen'' hK'' hv
    subst hK''nil
    obtain ⟨_, he''⟩ := decomp_inv_nil hK''
    subst he''
    exact absurd hv (DecompItem_fill hKi).2

-- TODO: Cleanup
theorem Exp.decomp_fill_comp {e e' : Exp} {K K' : Ectx}
    (hv : ¬e.isValue) (hd : e.decomp = (K', e')) :
    (K.fill e).decomp = (K' ++ K, e') := by
  suffices ∀ n K, K.length = n →
      (K.fill e).decomp = (K' ++ K, e') by
    exact this K.length K rfl
  intro n
  induction n with
  | zero =>
    intro K hlen
    have : K = [] := List.eq_nil_of_length_eq_zero hlen
    subst this; simpa
  | succ n ih =>
    intro K hlen
    have hne : K ≠ [] := by intro hK; simp [hK] at hlen
    obtain ⟨K'', Ki, rfl⟩ : ∃ K'' Ki, K = K'' ++ [Ki] :=
      ⟨K.dropLast, K.getLast hne, (List.dropLast_concat_getLast hne).symm⟩
    have hlen'' : K''.length = n := by simp at hlen; omega
    have hfill_eq : Ectx.fill (K'' ++ [Ki]) e =
        Ki.FillItem (Ectx.fill K'' e) := by
      simp only [Ectx.fill, List.foldl_append, List.foldl_cons, List.foldl_nil]; rfl
    rw [hfill_eq]
    have hfill_noVal : ¬(Ectx.fill K'' e).isValue := Ectx.fill_noVal hv
    rw [decomp_unfold, EctxItem.DecompItem_FillItem Ki hfill_noVal]
    have ih_applied : (Ectx.fill K'' e).decomp = (K' ++ K'', e') := ih K'' hlen''
    simp only [ih_applied, List.append_assoc]

end ProbLang
