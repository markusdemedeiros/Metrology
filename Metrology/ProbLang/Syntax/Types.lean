import Metrology.ProbLang.Syntax.Syntax
import Metrology.ProbLang.Syntax.Properties

/-!
# Syntactic typing for ProbLang (System F_μ_ref with tapes) — LN edition

Port of `theories/prob_lang/typing/types.v` from Clutch (logsem/clutch),
adapted to the locally-nameless encoding. Typing contexts now map atoms
(`Var = Nat`) to types. Binder rules use cofinite quantification: `Γ ⊢
lam e : τ1 → τ2` iff for every fresh atom `x ∉ L`, `Γ, x : τ1 ⊢ e^x : τ2`.

Type-level de-Bruijn (`Ty.var`, `Ty.rec'`, `Ty.forall'`, `Ty.exists'`) is
unchanged from Clutch — types were de-Bruijn already.
-/

namespace ProbLang
open Cslib Exp

/-! ## Ty renaming / substitution (de Bruijn) — unchanged from the old Types -/

@[simp] def upren (ξ : Nat → Nat) : Nat → Nat
  | 0     => 0
  | n + 1 => ξ n + 1

def Ty.rename (ξ : Nat → Nat) : Ty → Ty
  | .int        => .int
  | .bool       => .bool
  | .unit       => .unit
  | .tape       => .tape
  | .prod τ1 τ2 => .prod (τ1.rename ξ) (τ2.rename ξ)
  | .sum  τ1 τ2 => .sum  (τ1.rename ξ) (τ2.rename ξ)
  | .arrow τ1 τ2 => .arrow (τ1.rename ξ) (τ2.rename ξ)
  | .ref τ      => .ref (τ.rename ξ)
  | .var n      => .var (ξ n)
  | .rec' τ     => .rec'    (τ.rename (upren ξ))
  | .forall' τ  => .forall' (τ.rename (upren ξ))
  | .exists' τ  => .exists' (τ.rename (upren ξ))

def up (σ : Nat → Ty) : Nat → Ty
  | 0     => .var 0
  | n + 1 => (σ n).rename (· + 1)

def Ty.subst (σ : Nat → Ty) : Ty → Ty
  | .int        => .int
  | .bool       => .bool
  | .unit       => .unit
  | .tape       => .tape
  | .prod τ1 τ2 => .prod (τ1.subst σ) (τ2.subst σ)
  | .sum  τ1 τ2 => .sum  (τ1.subst σ) (τ2.subst σ)
  | .arrow τ1 τ2 => .arrow (τ1.subst σ) (τ2.subst σ)
  | .ref τ      => .ref (τ.subst σ)
  | .var n      => σ n
  | .rec' τ     => .rec'    (τ.subst (up σ))
  | .forall' τ  => .forall' (τ.subst (up σ))
  | .exists' τ  => .exists' (τ.subst (up σ))

def Ty.single (τ' τ : Ty) : Ty :=
  τ.subst (fun n => match n with | 0 => τ' | k + 1 => .var k)

def Ty.shift (τ : Ty) : Ty := τ.rename (· + 1)

def Ty.renameSubst (ξ : Nat → Nat) (σ : Nat → Ty) : Nat → Ty :=
  fun n => (σ n).rename ξ

def Ty.substComp (σ₂ σ₁ : Nat → Ty) : Nat → Ty :=
  fun n => (σ₁ n).subst σ₂

@[simp] def upN : Nat → (Nat → Ty) → (Nat → Ty)
  | 0,     σ => σ
  | k + 1, σ => up (upN k σ)

theorem upren_id : ∀ n, upren id n = n
  | 0     => rfl
  | _ + 1 => rfl

theorem upren_comp (ξ₁ ξ₂ : Nat → Nat) : ∀ n,
    upren ξ₁ (upren ξ₂ n) = upren (ξ₁ ∘ ξ₂) n
  | 0     => rfl
  | _ + 1 => rfl

theorem Ty.rename_id (τ : Ty) : τ.rename id = τ := by
  induction τ with
  | var n => rfl
  | rec' τ ih | forall' τ ih | exists' τ ih =>
    simp only [Ty.rename]
    rw [show upren id = id from funext upren_id, ih]
  | _ => simp only [Ty.rename, *]

theorem Ty.rename_rename (ξ₁ ξ₂ : Nat → Nat) (τ : Ty) :
    (τ.rename ξ₂).rename ξ₁ = τ.rename (ξ₁ ∘ ξ₂) := by
  induction τ generalizing ξ₁ ξ₂ with
  | var n => rfl
  | rec' τ ih | forall' τ ih | exists' τ ih =>
    simp only [Ty.rename, ih]
    rw [show upren ξ₁ ∘ upren ξ₂ = upren (ξ₁ ∘ ξ₂) from funext (upren_comp _ _)]
  | _ => simp only [Ty.rename, *]

theorem up_upren (ξ : Nat → Nat) : ∀ n,
    up (fun k => .var (ξ k)) n = .var (upren ξ n)
  | 0     => rfl
  | _ + 1 => rfl

theorem Ty.rename_eq_subst (ξ : Nat → Nat) (τ : Ty) :
    τ.rename ξ = τ.subst (fun n => .var (ξ n)) := by
  induction τ generalizing ξ with
  | var n => rfl
  | rec' τ ih | forall' τ ih | exists' τ ih =>
    simp only [Ty.rename, Ty.subst, ih,
      show (fun n => Ty.var (upren ξ n)) = up (fun k => .var (ξ k))
        from funext fun n => (up_upren ξ n).symm]
  | _ => simp only [Ty.rename, Ty.subst, *]

theorem up_var : ∀ n, up .var n = .var n
  | 0     => rfl
  | _ + 1 => rfl

theorem Ty.subst_id (τ : Ty) : τ.subst .var = τ := by
  induction τ with
  | var n => rfl
  | rec' τ ih | forall' τ ih | exists' τ ih =>
    simp only [Ty.subst]
    rw [show up .var = .var from funext up_var, ih]
  | _ => simp only [Ty.subst, *]

theorem up_subst_upren (σ : Nat → Ty) (ξ : Nat → Nat) : ∀ n,
    up (σ ∘ ξ) n = up σ (upren ξ n)
  | 0     => rfl
  | _ + 1 => rfl

theorem Ty.subst_rename (σ : Nat → Ty) (ξ : Nat → Nat) (τ : Ty) :
    (τ.rename ξ).subst σ = τ.subst (σ ∘ ξ) := by
  induction τ generalizing σ ξ with
  | var n => rfl
  | rec' τ ih | forall' τ ih | exists' τ ih =>
    simp only [Ty.rename, Ty.subst, ih,
      show up σ ∘ upren ξ = up (σ ∘ ξ) from funext fun n => (up_subst_upren σ ξ n).symm]
  | _ => simp only [Ty.rename, Ty.subst, *]

theorem up_renameSubst (ξ : Nat → Nat) (σ : Nat → Ty) : ∀ n,
    up (Ty.renameSubst ξ σ) n = Ty.renameSubst (upren ξ) (up σ) n
  | 0     => rfl
  | n + 1 => by
    simp only [up, Ty.renameSubst, Ty.rename_rename]; rfl

theorem Ty.rename_subst (ξ : Nat → Nat) (σ : Nat → Ty) (τ : Ty) :
    (τ.subst σ).rename ξ = τ.subst (Ty.renameSubst ξ σ) := by
  induction τ generalizing ξ σ with
  | var n => rfl
  | rec' τ ih | forall' τ ih | exists' τ ih =>
    simp only [Ty.subst, Ty.rename, ih,
      show Ty.renameSubst (upren ξ) (up σ) = up (Ty.renameSubst ξ σ)
        from funext fun n => (up_renameSubst ξ σ n).symm]
  | _ => simp only [Ty.subst, Ty.rename, *]

theorem up_substComp (σ₁ σ₂ : Nat → Ty) : ∀ n,
    up (Ty.substComp σ₂ σ₁) n = Ty.substComp (up σ₂) (up σ₁) n
  | 0     => rfl
  | n + 1 => by
    simp only [up, Ty.substComp, Ty.rename_subst, Ty.subst_rename]; rfl

theorem Ty.subst_subst (σ₁ σ₂ : Nat → Ty) (τ : Ty) :
    (τ.subst σ₁).subst σ₂ = τ.subst (Ty.substComp σ₂ σ₁) := by
  induction τ generalizing σ₁ σ₂ with
  | var n => rfl
  | rec' τ ih | forall' τ ih | exists' τ ih =>
    simp only [Ty.subst, ih,
      show Ty.substComp (up σ₂) (up σ₁) = up (Ty.substComp σ₂ σ₁)
        from funext fun n => (up_substComp σ₁ σ₂ n).symm]
  | _ => simp only [Ty.subst, *]

theorem Ty.single_shift (τ τ' : Ty) :
    Ty.single τ' τ.shift = τ := by
  simp only [Ty.single, Ty.shift, Ty.subst_rename]
  exact τ.subst_id

theorem upN_var : ∀ (k n : Nat), upN k .var n = .var n
  | 0,     _ => rfl
  | k + 1, n => by
    show up (upN k .var) n = _
    rw [funext (upN_var k), up_var]

theorem upN_lt : ∀ {k n : Nat} (σ : Nat → Ty), n < k → upN k σ n = .var n
  | _ + 1, 0,     _, _ => rfl
  | k + 1, n + 1, σ, h => by
    show up (upN k σ) (n + 1) = .var (n + 1)
    simp only [up, upN_lt σ (Nat.lt_of_succ_lt_succ h), Ty.rename]

theorem upN_ge : ∀ {k n : Nat} (σ : Nat → Ty), k ≤ n →
    upN k σ n = (σ (n - k)).rename (· + k)
  | 0,     n,     σ, _ => by
    show σ n = _
    rw [← Ty.rename_id (σ n)]; rfl
  | k + 1, n + 1, σ, h => by
    show up (upN k σ) (n + 1) = _
    simp only [up, upN_ge σ (Nat.le_of_succ_le_succ h), Ty.rename_rename,
               Nat.add_sub_add_right]
    rfl
  | _ + 1, 0,     _, h => absurd h (by omega)

/-! ## Value classes -/

inductive UnboxedType : Ty → Prop
  | unit                           : UnboxedType .unit
  | int                            : UnboxedType .int
  | bool                           : UnboxedType .bool
  | ref (τ : Ty)                   : UnboxedType (.ref τ)

inductive EqType : Ty → Prop
  | unit                           : EqType .unit
  | int                            : EqType .int
  | bool                           : EqType .bool
  | prod {τ τ'}                    : EqType τ → EqType τ' → EqType (.prod τ τ')
  | sum  {τ τ'}                    : EqType τ → EqType τ' → EqType (.sum τ τ')

theorem unboxed_type_ref_or_eqtype {τ : Ty} (h : UnboxedType τ) :
    EqType τ ∨ (∃ τ', τ = .ref τ') ∨ τ = .tape := by
  cases h with
  | unit  => exact .inl .unit
  | int   => exact .inl .int
  | bool  => exact .inl .bool
  | ref τ => exact .inr (.inl ⟨τ, rfl⟩)

def BinOp.intResTy : BinOp → Option Ty
  | .plus | .minus | .mult  => some .int
  | .and  | .or    | .xor   => none
  | .eq                     => some .bool

def BinOp.boolResTy : BinOp → Option Ty
  | .plus | .minus | .mult  => none
  | .and  | .or    | .xor   => some .bool
  | .eq                     => some .bool

def UnOp.intResTy : UnOp → Option Ty
  | .neg   => none
  | .minus => some .int

def UnOp.boolResTy : UnOp → Option Ty
  | .neg   => some .bool
  | .minus => none

/-! ## Typing contexts

A typing context `Tctx` maps atoms (`Var = Nat`) to types. -/

abbrev Tctx := Var → Option Ty

namespace Tctx

def empty : Tctx := fun _ => none

/-- Insert at an atom. -/
def insert (Γ : Tctx) (x : Var) (τ : Ty) : Tctx :=
  fun y => if y = x then some τ else Γ y

/-- Pointwise shift on type-level de-Bruijn. -/
def shift (Γ : Tctx) : Tctx := fun x => (Γ x).map Ty.shift

end Tctx

/-! ## The `rec_unfold` value: `λ x, x` = `lam (bvar 0)` -/

/-- Wrapping `unfold` in this identity makes unfolding a recursive type take a
    real computation step. Under LN, `λ x. x` is `lam (bvar 0)`. -/
def recUnfold : Exp := .lam (.bvar 0)

/-! ## Pattern typing -/

/-- `PatTyped τs p τb` — pattern `p` matched against a scrutinee of type `τs`
    yields bindings of type `τb`. The LN `.wildcard` pattern binds the whole
    scrutinee (there is no separate `.var` pattern since bindings live outside
    `Pat`). -/
inductive PatTyped : Ty → Pat → Ty → Prop
  | wildcard {τ}        : PatTyped τ .wildcard τ
  | lit_int {z}        : PatTyped .int  (.lit (.int z))  .unit
  | lit_bool {b}       : PatTyped .bool (.lit (.bool b)) .unit
  | lit_unit           : PatTyped .unit (.lit .unit)     .unit
  | pair {τ1 τ2 p1 p2 b1 b2} :
      PatTyped τ1 p1 b1 → PatTyped τ2 p2 b2 →
      PatTyped (.prod τ1 τ2) (.pair p1 p2) (.prod b1 b2)
  | inl {τ1 τ2 p b}    : PatTyped τ1 p b → PatTyped (.sum τ1 τ2) (.inl p) b
  | inr {τ1 τ2 p b}    : PatTyped τ2 p b → PatTyped (.sum τ1 τ2) (.inr p) b

/-! ## Typing judgment

Binder rules use cofinite quantification over finite sets of atoms.

`.lam e` : introduce a `λ`. Under LN, `e` has a dangling `bvar 0`; to type
it we open with a fresh atom.

`.fix e` : introduce a fixpoint (the body binds its recursive self).

The old Clutch `letrec f x body` corresponds to `fix (lam body)` in LN;
there's no dedicated `Typed.letrec` rule — derive it from `fix` + `lam`.
-/

inductive Typed : Tctx → Exp → Ty → Prop
  | fvar {Γ x τ} :
      Γ x = some τ →
      Typed Γ (.fvar x) τ
  | lit_int  {Γ z} : Typed Γ (.lit (.int z)) .int
  | lit_bool {Γ b} : Typed Γ (.lit (.bool b)) .bool
  | lit_unit {Γ}   : Typed Γ (.lit .unit)     .unit
  | binop_int {Γ op e1 e2 τ} :
      Typed Γ e1 .int → Typed Γ e2 .int →
      op.intResTy = some τ →
      Typed Γ (.binop op e1 e2) τ
  | binop_bool {Γ op e1 e2 τ} :
      Typed Γ e1 .bool → Typed Γ e2 .bool →
      op.boolResTy = some τ →
      Typed Γ (.binop op e1 e2) τ
  | unop_int {Γ op e τ} :
      Typed Γ e .int → op.intResTy = some τ →
      Typed Γ (.unop op e) τ
  | unop_bool {Γ op e τ} :
      Typed Γ e .bool → op.boolResTy = some τ →
      Typed Γ (.unop op e) τ
  | unboxed_eq {Γ e1 e2 τ} :
      UnboxedType τ →
      Typed Γ e1 τ → Typed Γ e2 τ →
      Typed Γ (.binop .eq e1 e2) .bool
  | pair {Γ e1 e2 τ1 τ2} :
      Typed Γ e1 τ1 → Typed Γ e2 τ2 →
      Typed Γ (.pair e1 e2) (.prod τ1 τ2)
  | fst {Γ e τ1 τ2} :
      Typed Γ e (.prod τ1 τ2) → Typed Γ (.fst e) τ1
  | snd {Γ e τ1 τ2} :
      Typed Γ e (.prod τ1 τ2) → Typed Γ (.snd e) τ2
  | inl {Γ e τ1 τ2} :
      Typed Γ e τ1 → Typed Γ (.inl e) (.sum τ1 τ2)
  | inr {Γ e τ1 τ2} :
      Typed Γ e τ2 → Typed Γ (.inr e) (.sum τ1 τ2)
  | case {Γ e0 e1 e2 τ1 τ2 τ3} :
      Typed Γ e0 (.sum τ1 τ2) →
      Typed Γ e1 (.arrow τ1 τ3) →
      Typed Γ e2 (.arrow τ2 τ3) →
      Typed Γ (.case e0 e1 e2) τ3
  | cond {Γ e0 e1 e2 τ} :
      Typed Γ e0 .bool →
      Typed Γ e1 τ → Typed Γ e2 τ →
      Typed Γ (.cond e0 e1 e2) τ
  | lam (L : Finset Var) {Γ e τ1 τ2} :
      (∀ x ∉ L, Typed (Γ.insert x τ1) (Exp.open' e (.fvar x)) τ2) →
      Typed Γ (.lam e) (.arrow τ1 τ2)
  | fix (L : Finset Var) {Γ e τ1 τ2} :
      (∀ f ∉ L, Typed (Γ.insert f (.arrow τ1 τ2)) (Exp.open' e (.fvar f)) (.arrow τ1 τ2)) →
      Typed Γ (.fix e) (.arrow τ1 τ2)
  | app {Γ e1 e2 τ1 τ2} :
      Typed Γ e1 (.arrow τ1 τ2) →
      Typed Γ e2 τ1 →
      Typed Γ (.app e1 e2) τ2
  | tlam {Γ e τ} :
      Typed Γ.shift e τ →
      Typed Γ (.lam e) (.forall' τ)
  | tapp {Γ e τ τ'} :
      Typed Γ e (.forall' τ) →
      Typed Γ (.app e (.lit .unit)) (τ.single τ')
  | tfold {Γ e τ} :
      Typed Γ e (τ.single (.rec' τ)) →
      Typed Γ e (.rec' τ)
  | tunfold {Γ e τ} :
      Typed Γ e (.rec' τ) →
      Typed Γ (.app recUnfold e) (τ.single (.rec' τ))
  | tpack {Γ e τ τ'} :
      Typed Γ e (τ.single τ') →
      Typed Γ e (.exists' τ)
  | tunpack (L : Finset Var) {Γ e1 e2 τ τ2} :
      Typed Γ e1 (.exists' τ) →
      (∀ x ∉ L, Typed ((Γ.shift).insert x τ) (Exp.open' e2 (.fvar x)) τ2.shift) →
      Typed Γ (.app (.lam e2) e1) τ2
  | alloc {Γ e τ} :
      Typed Γ e τ → Typed Γ (.alloc e) (.ref τ)
  | load {Γ e τ} :
      Typed Γ e (.ref τ) → Typed Γ (.load e) τ
  | store {Γ e e' τ} :
      Typed Γ e (.ref τ) → Typed Γ e' τ →
      Typed Γ (.store e e') .unit
  | alloc_tape {Γ e} :
      Typed Γ e .int → Typed Γ (.tape e) .tape
  | rand {Γ e1 e2} :
      Typed Γ e1 .int → Typed Γ e2 .tape →
      Typed Γ (.rand e1 e2) .int
  | rand_unit {Γ e1 e2} :
      Typed Γ e1 .int → Typed Γ e2 .unit →
      Typed Γ (.rand e1 e2) .int
  | scrut {Γ e p τs τb} :
      Typed Γ e τs → PatTyped τs p τb →
      Typed Γ (.scrut e p) (.sum τb .unit)
  | fail {Γ τ} : Typed Γ .fail τ

@[inherit_doc] scoped notation Γ " ⊢ₜ " e " : " τ => Typed Γ e τ

end ProbLang
