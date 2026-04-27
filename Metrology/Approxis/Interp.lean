import Metrology.Approxis.PrimitiveLaws
import Metrology.Approxis.Model
import Metrology.ProbLang.Metatheory
import Metrology.ProbLang.Syntax.Types

/-!
# Type Interpretation

Interpretation of syntactic types as semantic types: a nonexpansive map
`interp : Ty → TyEnv GF → lrel GF` sending each syntactic type to its
logical relation under a type-variable environment.

**Representation choice.** Rocq uses `listO (lrelC Σ)` for the
type-variable environment. We instead use a function `Nat → lrel GF`
(`TyEnv GF`) so the OFE comes for free via the pi instance on the
function space.

**Design note.** We define `interp` via `Ty.rec` on a **bundled motive**
`fun τ => {f : TyEnv GF → lrel GF // NonExpansiveEnv f}` where
`NonExpansiveEnv` is pointwise nonexpansiveness in the environment.
Bundling the nonexpansiveness witness with the function lets the `.rec'`
case of the recursion feed `lrel_rec`'s `Hom` constructor a genuine
(non-`sorry`) ne-proof via the induction hypothesis. `interp` and
`interp_ne_env` are then the two projections of this bundle. No sorries.

## Rocq source
`clutch/theories/approxis/interp.v`
-/

open Std Iris Iris.Std Iris.BI Iris.ProofMode OFE COFE ProbLang ProbLang.ApproxisWpGS

namespace ProbLang

section TyEnvSetup
variable {GF : BundledGFunctors}

/-- Type-variable environment: `Nat → lrel GF`. -/
abbrev TyEnv (GF : BundledGFunctors) := Nat → lrel GF

/-- Prepend a semantic type to a type-variable environment. -/
def TyEnv.cons (X : lrel GF) (Δ : TyEnv GF) : TyEnv GF
  | 0 => X
  | n + 1 => Δ n

/-- `cons X` is nonexpansive in `X`. -/
theorem TyEnv.cons_ne_head {n : Nat} {X Y : lrel GF} {Δ : TyEnv GF}
    (h : X ≡{n}≡ Y) : (TyEnv.cons X Δ) ≡{n}≡ (TyEnv.cons Y Δ) := by
  intro k
  cases k with
  | zero => exact h
  | succ m => exact Dist.rfl

/-- `cons` is nonexpansive in the tail. -/
theorem TyEnv.cons_ne_tail {n : Nat} {X : lrel GF} {Δ Δ' : TyEnv GF}
    (h : Δ ≡{n}≡ Δ') : (TyEnv.cons X Δ) ≡{n}≡ (TyEnv.cons X Δ') := by
  intro k
  cases k with
  | zero => exact Dist.rfl
  | succ m => exact h m

/-- Context lookup for type variables. Mirrors `ctx_lookup`. -/
@[reducible] def ctxLookup (x : Nat) (Δ : TyEnv GF) : lrel GF := Δ x

end TyEnvSetup

section interp
variable {hlc : Bool} {GF : BundledGFunctors} [ApproxisRGS hlc GF]

/-- A function `TyEnv GF → lrel GF` paired with its pointwise
nonexpansiveness witness. This is the motive we recurse on, so that the
`.rec'` case can directly feed `lrel_rec`'s `Hom` using the IH. -/
structure NEFun (GF : BundledGFunctors) where
  fn  : TyEnv GF → lrel GF
  ne  : ∀ {n : Nat} {Δ Δ' : TyEnv GF}, Δ ≡{n}≡ Δ' → fn Δ ≡{n}≡ fn Δ'

namespace NEFun
variable {GF : BundledGFunctors} [ApproxisRGS hlc GF]

/-- The constant `NEFun`. -/
@[reducible] noncomputable def const (L : lrel GF) : NEFun GF :=
  { fn := fun _ => L, ne := fun _ => Dist.rfl }

/-- `NEFun` factory for `ctxLookup`. -/
@[reducible] def ofCtx (x : Nat) : NEFun GF :=
  { fn := fun Δ => ctxLookup x Δ, ne := fun h => h x }

/-- Lift a binary `NonExpansive₂` combinator to `NEFun`s. -/
@[reducible] noncomputable def map2 (F : lrel GF → lrel GF → lrel GF)
    [OFE.NonExpansive₂ F] (A B : NEFun GF) : NEFun GF :=
  { fn := fun Δ => F (A.fn Δ) (B.fn Δ)
    ne := fun h => OFE.NonExpansive₂.ne (A.ne h) (B.ne h) }

/-- Lift a unary `NonExpansive` combinator to `NEFun`s. -/
@[reducible] noncomputable def map1 (F : lrel GF → lrel GF)
    [OFE.NonExpansive F] (A : NEFun GF) : NEFun GF :=
  { fn := fun Δ => F (A.fn Δ)
    ne := fun h => OFE.NonExpansive.ne (f := F) (A.ne h) }

/-- The recursive-type combinator at the `NEFun` level. Given a `NEFun`
on the extended environment, produce a `NEFun` on the current one. The
ne-witness is a direct use of `lrel_rec_ne`. -/
@[reducible] noncomputable def rec' (A : NEFun GF) : NEFun GF :=
  { fn := fun Δ => lrel_rec
      { f := fun X => A.fn (TyEnv.cons X Δ)
        ne := ⟨fun {_ _ _} hXY => A.ne (TyEnv.cons_ne_head hXY)⟩ }
    ne := fun h => lrel_rec_ne (fun _ => A.ne (TyEnv.cons_ne_tail h)) }

/-- The `∀`-type combinator at the `NEFun` level. -/
@[reducible] noncomputable def forall' (A : NEFun GF) : NEFun GF :=
  { fn := fun Δ => lrel_forall (fun X => A.fn (TyEnv.cons X Δ))
    ne := fun h => lrel_forall_ne (fun _ => A.ne (TyEnv.cons_ne_tail h)) }

/-- The `∃`-type combinator at the `NEFun` level. -/
@[reducible] noncomputable def exists' (A : NEFun GF) : NEFun GF :=
  { fn := fun Δ => lrel_exists (fun X => A.fn (TyEnv.cons X Δ))
    ne := fun h => lrel_exists_ne (fun _ => A.ne (TyEnv.cons_ne_tail h)) }

end NEFun

/-- Bundled interpretation: `interpNE τ` is a function `TyEnv → lrel`
together with its pointwise ne-witness in the environment. Defined by
structural recursion on `τ`. -/
noncomputable def interpNE : Ty → NEFun GF
  | .unit         => NEFun.const lrel_unit
  | .int          => NEFun.const lrel_int
  | .bool         => NEFun.const lrel_bool
  | .tape         => NEFun.const lrel_tape
  | .var x        => NEFun.ofCtx x
  | .prod τ1 τ2   => NEFun.map2 lrel_prod (interpNE τ1) (interpNE τ2)
  | .sum  τ1 τ2   => NEFun.map2 lrel_sum  (interpNE τ1) (interpNE τ2)
  | .arrow τ1 τ2  => NEFun.map2 lrel_arr  (interpNE τ1) (interpNE τ2)
  | .ref τ        => NEFun.map1 lrel_ref (interpNE τ)
  | .rec' τ'      => NEFun.rec'    (interpNE τ')
  | .forall' τ'   => NEFun.forall' (interpNE τ')
  | .exists' τ'   => NEFun.exists' (interpNE τ')

/-- Unbundled interpretation: the function component of `interpNE`. -/
noncomputable def interp (τ : Ty) (Δ : TyEnv GF) : lrel GF :=
  (interpNE (GF := GF) τ).fn Δ

/-- Public API: `interp τ` is nonexpansive in its environment. -/
theorem interp_ne_env (τ : Ty) {n : Nat} {Δ Δ' : TyEnv GF}
    (h : Δ ≡{n}≡ Δ') : interp τ Δ ≡{n}≡ interp τ Δ' :=
  (interpNE (GF := GF) τ).ne h

end interp

/-! ## Closedness of related values

Every value related by `interp τ Δ` is closed (no free variables, locally
closed). This is a port-specific property — Rocq's intrinsic `val` carries
closedness for free; we need to track it explicitly. The proof is by
structural induction on `τ`, using each lrel's value-form constraint
(literals are closed; arrow/forall/exists carry an explicit closedness
conjunct; ref/tape values are locations/labels). -/

section interp_closed
variable {hlc : Bool} {GF : BundledGFunctors} [ApproxisRGS hlc GF]

/-- `IsClosedRespecting Δ`: every lrel in `Δ` only relates closed values.
A side condition for `interp_closed` to handle the type-variable case.
Made a typeclass so it propagates implicitly to every `interp_closed` call. -/
class TyEnv.IsClosedRespecting (Δ : TyEnv GF) : Prop where
  closed : ∀ (n : Nat) (v v' : Val), (Δ n).car v v' ⊢@{IProp GF}
    iprop(⌜v.1.isClosedEmpty ∧ v'.1.isClosedEmpty⌝)

/-- Helper: a literal value is closed. -/
theorem Exp.lit_isClosedEmpty (b : BaseLit) : (Exp.lit b).isClosedEmpty :=
  ⟨IsLocallyClosed.lit b, by simp [Exp.fv]⟩

/-- The constant-`lrel_unit` environment is closed-respecting: it relates only
`(.lit .unit, .lit .unit)`, both closed. Useful as a base case. -/
instance TyEnv.constUnit_IsClosedRespecting :
    TyEnv.IsClosedRespecting ((fun _ => lrel_unit) : TyEnv GF) where
  closed n v v' := by
    show iprop(⌜v.1 = .lit .unit ∧ v'.1 = .lit .unit⌝) ⊢ _
    iintro %h
    ipure_intro
    exact ⟨h.1 ▸ Exp.lit_isClosedEmpty _, h.2 ▸ Exp.lit_isClosedEmpty _⟩

/-- An lrel `X` is "closed-respecting" if it only relates closed values.
Used as a side condition for extending closed-respecting environments. -/
class lrel.IsClosedRespecting (X : lrel GF) : Prop where
  closed : ∀ (v v' : Val), X.car v v' ⊢@{IProp GF}
    iprop(⌜v.1.isClosedEmpty ∧ v'.1.isClosedEmpty⌝)

/-- Extending a closed-respecting `Δ` with a closed-respecting `X` is closed-respecting. -/
instance TyEnv.cons_IsClosedRespecting (X : lrel GF) (Δ : TyEnv GF)
    [hX : X.IsClosedRespecting] [hΔ : Δ.IsClosedRespecting] :
    (TyEnv.cons X Δ).IsClosedRespecting where
  closed n v v' := by
    cases n with
    | zero => exact hX.closed v v'
    | succ k => exact hΔ.closed k v v'

/-- Every `interp τ Δ` value-relation only relates closed values, provided
`Δ` is closed-respecting. Proof by structural induction on `τ`. The `rec'`
case requires Löb induction; we wrap the whole statement in `loeb_wand`. -/
theorem interp_closed {Δ : TyEnv GF} [hΔ : Δ.IsClosedRespecting]
    (τ : Ty) (v v' : Val) :
    (interp τ Δ).car v v' ⊢@{IProp GF}
      iprop(⌜v.1.isClosedEmpty ∧ v'.1.isClosedEmpty⌝) := by
  induction τ generalizing Δ v v'
  · -- int
    show iprop(∃ n : Int, ⌜v.1 = .lit (.int n) ∧ v'.1 = .lit (.int n)⌝) ⊢
      iprop(⌜_ ∧ _⌝ : IProp GF)
    iintro ⟨%n, %h⟩
    ipure_intro
    exact ⟨h.1 ▸ Exp.lit_isClosedEmpty _, h.2 ▸ Exp.lit_isClosedEmpty _⟩
  · -- bool
    show iprop(∃ b : Bool, ⌜v.1 = .lit (.bool b) ∧ v'.1 = .lit (.bool b)⌝) ⊢
      iprop(⌜_ ∧ _⌝ : IProp GF)
    iintro ⟨%b, %h⟩
    ipure_intro
    exact ⟨h.1 ▸ Exp.lit_isClosedEmpty _, h.2 ▸ Exp.lit_isClosedEmpty _⟩
  · -- unit
    show iprop(⌜v.1 = .lit .unit ∧ v'.1 = .lit .unit⌝) ⊢
      iprop(⌜_ ∧ _⌝ : IProp GF)
    iintro %h
    obtain ⟨h1, h2⟩ := h
    ipure_intro
    exact ⟨h1 ▸ Exp.lit_isClosedEmpty _, h2 ▸ Exp.lit_isClosedEmpty _⟩
  · -- prod
    rename_i τ1 τ2 ih1 ih2
    show iprop(∃ (a1 a2 b1 b2 : Val),
        (⌜v.1 = .pair a1.1 b1.1⌝) ∗ (⌜v'.1 = .pair a2.1 b2.1⌝) ∗
        (interp τ1 Δ).car a1 a2 ∗ (interp τ2 Δ).car b1 b2) ⊢ _
    iintro ⟨%a1, %a2, %b1, %b2, %hv1, %hv2, HA, HB⟩
    ihave %hac := ih1 a1 a2 $$ HA
    ihave %hbc := ih2 b1 b2 $$ HB
    ipure_intro
    refine ⟨hv1 ▸ ?_, hv2 ▸ ?_⟩
    · refine ⟨Exp.IsLocallyClosed.pair hac.1.1 hbc.1.1, ?_⟩
      simp [Exp.fv, hac.1.2, hbc.1.2]
    · refine ⟨Exp.IsLocallyClosed.pair hac.2.1 hbc.2.1, ?_⟩
      simp [Exp.fv, hac.2.2, hbc.2.2]
  · -- sum
    rename_i τ1 τ2 ih1 ih2
    show iprop(∃ (w1 w2 : Val),
        (⌜v.1 = .inl w1.1⌝ ∗ ⌜v'.1 = .inl w2.1⌝ ∗ (interp τ1 Δ).car w1 w2) ∨
        (⌜v.1 = .inr w1.1⌝ ∗ ⌜v'.1 = .inr w2.1⌝ ∗ (interp τ2 Δ).car w1 w2)) ⊢ _
    iintro ⟨%w1, %w2, Hor⟩
    icases Hor with (⟨%hv1, %hv2, HA⟩ | ⟨%hv1, %hv2, HB⟩)
    · ihave %hwc := ih1 w1 w2 $$ HA
      ipure_intro
      refine ⟨hv1 ▸ ?_, hv2 ▸ ?_⟩
      · exact ⟨Exp.IsLocallyClosed.inl hwc.1.1, by simp [Exp.fv]; exact hwc.1.2⟩
      · exact ⟨Exp.IsLocallyClosed.inl hwc.2.1, by simp [Exp.fv]; exact hwc.2.2⟩
    · ihave %hwc := ih2 w1 w2 $$ HB
      ipure_intro
      refine ⟨hv1 ▸ ?_, hv2 ▸ ?_⟩
      · exact ⟨Exp.IsLocallyClosed.inr hwc.1.1, by simp [Exp.fv]; exact hwc.1.2⟩
      · exact ⟨Exp.IsLocallyClosed.inr hwc.2.1, by simp [Exp.fv]; exact hwc.2.2⟩
  · -- arrow: lrel_arr's first conjunct is closedness
    rename_i τ1 τ2 _ _
    show iprop(_ ∗ □ _) ⊢ iprop(⌜_ ∧ _⌝ : IProp GF)
    iintro ⟨%h, _⟩
    ipure_intro; exact h
  · -- ref
    rename_i τ' _
    show iprop(∃ (l1 l2 : Loc), (⌜v.1 = .lit (.loc l1)⌝) ∗
        (⌜v'.1 = .lit (.loc l2)⌝) ∗ _) ⊢ _
    iintro ⟨%l1, %l2, %hv1, %hv2, _⟩
    ipure_intro
    exact ⟨hv1 ▸ Exp.lit_isClosedEmpty _, hv2 ▸ Exp.lit_isClosedEmpty _⟩
  · -- tape
    show iprop(∃ (α1 α2 : Loc) (z : Int), (⌜v.1 = .lit (.lbl α1)⌝) ∗
        (⌜v'.1 = .lit (.lbl α2)⌝) ∗ _) ⊢ _
    iintro ⟨%α1, %α2, %z, %hv1, %hv2, _⟩
    ipure_intro
    exact ⟨hv1 ▸ Exp.lit_isClosedEmpty _, hv2 ▸ Exp.lit_isClosedEmpty _⟩
  · -- var
    rename_i n
    show (Δ n).car v v' ⊢ _
    exact hΔ.closed n v v'
  · -- rec': (lrel_rec C).car v v' ≡ ⌜v.closed ∧ v'.closed⌝ ∗ ▷ (C ...).car v v'.
    -- Closedness is the first conjunct (option C uniformly applied to lrel_rec).
    rename_i τ' _
    let CRec : lrel GF -n> lrel GF :=
      { f := fun X => interp τ' (TyEnv.cons X Δ)
        ne := ⟨fun {_ _ _} hXY => (interpNE τ').ne (TyEnv.cons_ne_head hXY)⟩ }
    have hequiv : (interp (Ty.rec' τ') Δ : lrel GF) ≡ lrelRec1 CRec (interp (Ty.rec' τ') Δ) :=
      lrel_rec_unfold CRec
    have hunfold : (interp (Ty.rec' τ') Δ : lrel GF) = lrelRec1 CRec (interp (Ty.rec' τ') Δ) :=
      OFE.Leibniz.eq_of_eqv (α := lrel GF) hequiv
    rw [hunfold]
    show iprop((⌜_⌝) ∗ _) ⊢ _
    iintro ⟨%hcl, _⟩
    ipure_intro
    exact hcl
  · -- forall'
    rename_i τ' _
    show iprop(∀ (A : lrel GF),
        (lrel_arr lrel_unit (interp τ' (TyEnv.cons A Δ))).car v v') ⊢ _
    iintro Hall
    -- Instantiate at A := lrel_unit (any specific lrel will do).
    ihave Hinst := Hall $$ %lrel_unit
    -- Hinst : (lrel_arr lrel_unit (interp τ' (cons lrel_unit Δ))).car v v'.
    -- The lrel_arr's first conjunct is closedness; project it.
    ihave Hclosed : iprop(⌜v.1.isClosedEmpty ∧ v'.1.isClosedEmpty⌝ : IProp GF) $$ [Hinst]
    · show iprop(_ ∗ □ _) ⊢ _
      iintro ⟨%h, _⟩
      ipure_intro; exact h
    iexact Hclosed
  · -- exists': lrel_exists's first conjunct is closedness
    rename_i τ' _
    show iprop(_ ∗ ∃ _, _) ⊢ iprop(⌜_ ∧ _⌝ : IProp GF)
    iintro ⟨%h, _⟩
    ipure_intro; exact h

/-- For any `τ` and any closed-respecting `Δ`, the resulting lrel `interp τ Δ`
is itself closed-respecting. -/
instance interp_IsClosedRespecting {Δ : TyEnv GF} [Δ.IsClosedRespecting] (τ : Ty) :
    (interp τ Δ).IsClosedRespecting where
  closed v v' := interp_closed τ v v'

end interp_closed

/-! ## Unboxed-value predicate

Ports `val_is_unboxed` (clutch/theories/prob_lang/lang.v). A value is
"unboxed" if it's a literal (int/bool/unit/loc/lbl) or a tagged literal
via `inl`/`inr`. -/

/-- A value-level expression is unboxed. -/
@[simp] def Exp.isUnboxedV : Exp → Prop
  | .lit _ => True
  | .inl (.lit _) => True
  | .inr (.lit _) => True
  | _ => False

/-- `Val.isUnboxed v` holds iff `v.1` is unboxed. -/
@[reducible] def Val.isUnboxed (v : Val) : Prop := v.1.isUnboxedV

/-! ## Soundness of the semantic type interpretation -/

section interp_sound
variable {hlc : Bool} {GF : BundledGFunctors} [ApproxisRGS hlc GF]

/-- Unboxed-type values are unboxed. Mirrors `unboxed_type_sound`
(interp.v:49–58). -/
theorem unboxed_type_sound {τ : Ty} {Δ : TyEnv GF} {v v' : Val}
    (H : UnboxedType τ) :
    (interp τ Δ).car v v' ⊢@{IProp GF} ⌜ Val.isUnboxed v ∧ Val.isUnboxed v' ⌝ := by
  cases H
  -- unit
  · show iprop(⌜ _ ⌝) ⊢ _
    iintro ⟨%h1, %h2⟩
    ipure_intro
    exact ⟨by simp [Val.isUnboxed, h1], by simp [Val.isUnboxed, h2]⟩
  -- int
  · show iprop(∃ _, _) ⊢ _
    iintro ⟨%n, %h1, %h2⟩
    ipure_intro
    exact ⟨by simp [Val.isUnboxed, h1], by simp [Val.isUnboxed, h2]⟩
  -- bool
  · show iprop(∃ _, _) ⊢ _
    iintro ⟨%b, %h1, %h2⟩
    ipure_intro
    exact ⟨by simp [Val.isUnboxed, h1], by simp [Val.isUnboxed, h2]⟩
  -- ref τ'
  · show iprop(∃ _ _, _) ⊢ _
    iintro ⟨%l1, %l2, %h1, %h2, _⟩
    ipure_intro
    exact ⟨by simp [Val.isUnboxed, h1], by simp [Val.isUnboxed, h2]⟩

/-- At an unboxed type, both related values are bare literals (`.lit _`).
Stronger than `unboxed_type_sound` (which allows `inl/inr` shapes too) because
`UnboxedType` doesn't include sums. Used by `bin_log_related_unboxed_eq` to
β-step `BinOp.eval .eq` on the underlying literals. -/
theorem unboxed_type_lit_shape {τ : Ty} {Δ : TyEnv GF} {v v' : Val}
    (H : UnboxedType τ) :
    (interp τ Δ).car v v' ⊢@{IProp GF}
      ⌜∃ l l' : BaseLit, v.1 = .lit l ∧ v'.1 = .lit l'⌝ := by
  cases H
  -- unit
  · show iprop(⌜ _ ⌝) ⊢ _
    iintro ⟨%h1, %h2⟩
    ipure_intro
    exact ⟨_, _, h1, h2⟩
  -- int
  · show iprop(∃ _, _) ⊢ _
    iintro ⟨%n, %h1, %h2⟩
    ipure_intro
    exact ⟨_, _, h1, h2⟩
  -- bool
  · show iprop(∃ _, _) ⊢ _
    iintro ⟨%b, %h1, %h2⟩
    ipure_intro
    exact ⟨_, _, h1, h2⟩
  -- ref τ'
  · show iprop(∃ _ _, _) ⊢ _
    iintro ⟨%l1, %l2, %h1, %h2, _⟩
    ipure_intro
    exact ⟨_, _, h1, h2⟩

/-- At equality-types, both related values are pointwise equal. Mirrors
`eq_type_sound` (interp.v:60–77). -/
theorem eq_type_sound {τ : Ty} {Δ : TyEnv GF} {v v' : Val} (H : EqType τ) :
    (interp τ Δ).car v v' ⊢@{IProp GF} ⌜ v = v' ⌝ := by
  induction H generalizing v v'
  -- unit
  · show iprop(⌜ _ ⌝) ⊢ _
    iintro ⟨%h1, %h2⟩
    ipure_intro
    apply Val.ext
    rw [h1, h2]
  -- int
  · show iprop(∃ _, _) ⊢ _
    iintro ⟨%n, %h1, %h2⟩
    ipure_intro
    apply Val.ext
    rw [h1, h2]
  -- bool
  · show iprop(∃ _, _) ⊢ _
    iintro ⟨%b, %h1, %h2⟩
    ipure_intro
    apply Val.ext
    rw [h1, h2]
  -- prod
  · rename_i τ1 τ2 Hτ1 Hτ2 ih1 ih2
    show iprop(∃ _ _ _ _, _) ⊢ _
    iintro ⟨%a1, %a2, %b1, %b2, %h1, %h2, HA, HB⟩
    unfold interp at ih1 ih2
    ihave %heq1 := ih1 (v := a1) (v' := a2) $$ HA
    ihave %heq2 := ih2 (v := b1) (v' := b2) $$ HB
    ipure_intro
    apply Val.ext
    rw [h1, h2, heq1, heq2]
  -- sum
  · rename_i τ1 τ2 Hτ1 Hτ2 ih1 ih2
    unfold interp at ih1 ih2
    show iprop(∃ _ _, _) ⊢ _
    iintro ⟨%w1, %w2, Hd⟩
    icases Hd with (⟨%h1, %h2, HA⟩ | ⟨%h1, %h2, HB⟩)
    · ihave %heq := ih1 (v := w1) (v' := w2) $$ HA
      ipure_intro
      apply Val.ext
      rw [h1, h2, heq]
    · ihave %heq := ih2 (v := w1) (v' := w2) $$ HB
      ipure_intro
      apply Val.ext
      rw [h1, h2, heq]

/-- Decidable equality at unboxed types. Mirrors `unboxed_type_eq`
(interp.v:79–118). Sketch:

1. By `unboxed_type_ref_or_eqtype`, `τ` is `EqType` or `ref τ'` or `tape`.
2. `EqType` case: `eq_type_sound` on both hyps gives `v1 = v2` and
   `w1 = w2`, then the biconditional follows pure-logically.
3. `ref τ'` case: destructure both `lrel_ref` hyps. Case-split on
   `l1 = r1` and `l2 = r2`. Three of the four subcases are either
   trivial (both equal → both sides equal) or pure-logic (one equal
   and the other not → both sides false). The fourth subcase (`l1 = r1`
   but `l2 ≠ r2`, or vice versa) opens two invariants to derive
   `False` from two `appHeapFrag`/`specHeapFrag` at the same location.
4. `tape` case: analogous using `appTapesFrag`/`specTapesFrag`.

The invariant-opening pattern mirrors `interp_ref_funct`/`inj`,
`interp_tape_funct`/`inj` from Model.lean. -/
theorem unboxed_type_eq {τ : Ty} {Δ : TyEnv GF} {v1 v2 w1 w2 : Val}
    (H : UnboxedType τ) :
    (interp τ Δ).car v1 v2 ⊢@{IProp GF}
      (interp τ Δ).car w1 w2 -∗ |={⊤}=> ⌜ v1 = w1 ↔ v2 = w2 ⌝ := by
  -- Classify `τ` into EqType, TRef, or TTape.
  rcases unboxed_type_ref_or_eqtype H with Hτ | ⟨τ', rfl⟩ | rfl
  · -- EqType case: v1 = v2 and w1 = w2 both equalities, so the biconditional is pure.
    iintro H1 H2
    ihave %heq1 := eq_type_sound Hτ $$ H1
    ihave %heq2 := eq_type_sound Hτ $$ H2
    imodintro
    ipure_intro
    refine ⟨fun h => ?_, fun h => ?_⟩
    · rw [← heq1, ← heq2, h]
    · rw [heq1, heq2, h]
  · -- TRef τ' case.
    unfold interp
    show (lrel_ref ((interpNE τ').fn Δ)).car _ _ ⊢
      (lrel_ref ((interpNE τ').fn Δ)).car _ _ -∗ _
    unfold lrel_ref
    iintro H1 H2
    icases H1 with ⟨%l1, %l2, %he1, %he1', Hinv1⟩
    icases H2 with ⟨%r1, %r2, %he2, %he2', Hinv2⟩
    -- v1.1 = .lit (.loc l1), v2.1 = .lit (.loc l2), w1.1 = .lit (.loc r1), w2.1 = .lit (.loc r2).
    by_cases h_l1_r1 : l1 = r1
    · by_cases h_l2_r2 : l2 = r2
      · -- l1 = r1 and l2 = r2: both `v = w` equalities hold.
        imodintro
        ipure_intro
        subst h_l1_r1 h_l2_r2
        refine ⟨fun _ => ?_, fun _ => ?_⟩
        · apply Val.ext; rw [he1', he2']
        · apply Val.ext; rw [he1, he2]
      · -- l1 = r1 but l2 ≠ r2: derive False from two specHeapFrag at l2 (= r2 would
        -- be required for equality, but l2 ≠ r2 case... wait this is subtle).
        subst h_l1_r1
        -- After subst: r1 replaced by l1. Derive False.
        have hN_disj : logN.@ ((l1, l2) : Loc × Loc) ## logN.@ ((l1, r2) : Loc × Loc) :=
          ndot_ne_disjoint _ (fun heq => h_l2_r2 (by injection heq))
        have h1 : (↑(logN.@ ((l1, l2) : Loc × Loc)) : CoPset) ⊆ ⊤ :=
          fun _ _ => CoPset.mem_full
        have h2' : (↑(logN.@ ((l1, r2) : Loc × Loc)) : CoPset) ⊆
                   ⊤ \ (↑(logN.@ ((l1, l2) : Loc × Loc)) : CoPset) := by
          intro p hp
          rw [CoPset.in_diff]
          exact ⟨CoPset.mem_full, fun hp1 => hN_disj p ⟨hp1, hp⟩⟩
        imod Iris.inv_acc ⊤ _ _ h1 $$ Hinv1 with ⟨HP1, _⟩
        imod Iris.inv_acc _ _ _ h2' $$ Hinv2 with ⟨HP2, _⟩
        ihave HbotLater : iprop(▷ False) $$ [HP1 HP2]
        · ihave HP1a := later_exists.mpr $$ HP1
          icases HP1a with ⟨%wa1, HP1b⟩
          ihave HP1c := later_exists.mpr $$ HP1b
          icases HP1c with ⟨%ws1, HP1d⟩
          ihave HP1e := later_sep.mp $$ HP1d
          icases HP1e with ⟨Hl1L, _⟩
          ihave HP2a := later_exists.mpr $$ HP2
          icases HP2a with ⟨%wa2, HP2b⟩
          ihave HP2c := later_exists.mpr $$ HP2b
          icases HP2c with ⟨%ws2, HP2d⟩
          ihave HP2e := later_sep.mp $$ HP2d
          icases HP2e with ⟨Hl2L, _⟩
          inext
          iapply appHeapFrag_valid_2 $$ Hl1L Hl2L
        iapply IsExcept0.is_except0
        unfold BIBase.except0
        iapply BI.or_intro_l
        iexact HbotLater
    · by_cases h_l2_r2 : l2 = r2
      · -- l1 ≠ r1 but l2 = r2: derive False from two specHeapFrag at r2.
        subst h_l2_r2
        have hN_disj : logN.@ ((l1, l2) : Loc × Loc) ## logN.@ ((r1, l2) : Loc × Loc) :=
          ndot_ne_disjoint _ (fun heq => h_l1_r1 (by injection heq))
        have h1 : (↑(logN.@ ((l1, l2) : Loc × Loc)) : CoPset) ⊆ ⊤ :=
          fun _ _ => CoPset.mem_full
        have h2' : (↑(logN.@ ((r1, l2) : Loc × Loc)) : CoPset) ⊆
                   ⊤ \ (↑(logN.@ ((l1, l2) : Loc × Loc)) : CoPset) := by
          intro p hp
          rw [CoPset.in_diff]
          exact ⟨CoPset.mem_full, fun hp1 => hN_disj p ⟨hp1, hp⟩⟩
        imod Iris.inv_acc ⊤ _ _ h1 $$ Hinv1 with ⟨HP1, _⟩
        imod Iris.inv_acc _ _ _ h2' $$ Hinv2 with ⟨HP2, _⟩
        ihave HbotLater : iprop(▷ False) $$ [HP1 HP2]
        · ihave HP1a := later_exists.mpr $$ HP1
          icases HP1a with ⟨%wa1, HP1b⟩
          ihave HP1c := later_exists.mpr $$ HP1b
          icases HP1c with ⟨%ws1, HP1d⟩
          ihave HP1e := later_sep.mp $$ HP1d
          icases HP1e with ⟨_, HP1f⟩
          ihave HP1g := later_sep.mp $$ HP1f
          icases HP1g with ⟨Hs1L, _⟩
          ihave HP2a := later_exists.mpr $$ HP2
          icases HP2a with ⟨%wa2, HP2b⟩
          ihave HP2c := later_exists.mpr $$ HP2b
          icases HP2c with ⟨%ws2, HP2d⟩
          ihave HP2e := later_sep.mp $$ HP2d
          icases HP2e with ⟨_, HP2f⟩
          ihave HP2g := later_sep.mp $$ HP2f
          icases HP2g with ⟨Hs2L, _⟩
          inext
          iapply specHeapFrag_valid_2 $$ Hs1L Hs2L
        iapply IsExcept0.is_except0
        unfold BIBase.except0
        iapply BI.or_intro_l
        iexact HbotLater
      · -- l1 ≠ r1 and l2 ≠ r2: both `v = w` inequalities hold.
        imodintro
        ipure_intro
        refine ⟨fun h => ?_, fun h => ?_⟩
        · exfalso; apply h_l1_r1
          have := congrArg Sigma.fst h; rw [he1, he2] at this
          injection this with this; injection this
        · exfalso; apply h_l2_r2
          have := congrArg Sigma.fst h; rw [he1', he2'] at this
          injection this with this; injection this
  · -- TTape case.
    unfold interp
    show (lrel_tape (GF := GF)).car _ _ ⊢
      (lrel_tape (GF := GF)).car _ _ -∗ _
    unfold lrel_tape
    iintro H1 H2
    icases H1 with ⟨%α1, %α2, %z1, %he1, %he1', Hinv1⟩
    icases H2 with ⟨%β1, %β2, %z2, %he2, %he2', Hinv2⟩
    by_cases h_α1_β1 : α1 = β1
    · by_cases h_α2_β2 : α2 = β2
      · imodintro
        ipure_intro
        subst h_α1_β1 h_α2_β2
        refine ⟨fun _ => ?_, fun _ => ?_⟩
        · apply Val.ext; rw [he1', he2']
        · apply Val.ext; rw [he1, he2]
      · subst h_α1_β1
        have hN_disj : logN.@ ((α1, α2) : Loc × Loc) ## logN.@ ((α1, β2) : Loc × Loc) :=
          ndot_ne_disjoint _ (fun heq => h_α2_β2 (by injection heq))
        have h1 : (↑(logN.@ ((α1, α2) : Loc × Loc)) : CoPset) ⊆ ⊤ :=
          fun _ _ => CoPset.mem_full
        have h2' : (↑(logN.@ ((α1, β2) : Loc × Loc)) : CoPset) ⊆
                   ⊤ \ (↑(logN.@ ((α1, α2) : Loc × Loc)) : CoPset) := by
          intro p hp
          rw [CoPset.in_diff]
          exact ⟨CoPset.mem_full, fun hp1 => hN_disj p ⟨hp1, hp⟩⟩
        imod Iris.inv_acc ⊤ _ _ h1 $$ Hinv1 with ⟨HP1, _⟩
        imod Iris.inv_acc _ _ _ h2' $$ Hinv2 with ⟨HP2, _⟩
        ihave HbotLater : iprop(▷ False) $$ [HP1 HP2]
        · ihave HP1e := later_sep.mp $$ HP1
          icases HP1e with ⟨Ha1L, _⟩
          ihave HP2e := later_sep.mp $$ HP2
          icases HP2e with ⟨Ha2L, _⟩
          inext
          iapply appTapesFrag_valid_2 $$ Ha1L Ha2L
        iapply IsExcept0.is_except0
        unfold BIBase.except0
        iapply BI.or_intro_l
        iexact HbotLater
    · by_cases h_α2_β2 : α2 = β2
      · subst h_α2_β2
        have hN_disj : logN.@ ((α1, α2) : Loc × Loc) ## logN.@ ((β1, α2) : Loc × Loc) :=
          ndot_ne_disjoint _ (fun heq => h_α1_β1 (by injection heq))
        have h1 : (↑(logN.@ ((α1, α2) : Loc × Loc)) : CoPset) ⊆ ⊤ :=
          fun _ _ => CoPset.mem_full
        have h2' : (↑(logN.@ ((β1, α2) : Loc × Loc)) : CoPset) ⊆
                   ⊤ \ (↑(logN.@ ((α1, α2) : Loc × Loc)) : CoPset) := by
          intro p hp
          rw [CoPset.in_diff]
          exact ⟨CoPset.mem_full, fun hp1 => hN_disj p ⟨hp1, hp⟩⟩
        imod Iris.inv_acc ⊤ _ _ h1 $$ Hinv1 with ⟨HP1, _⟩
        imod Iris.inv_acc _ _ _ h2' $$ Hinv2 with ⟨HP2, _⟩
        ihave HbotLater : iprop(▷ False) $$ [HP1 HP2]
        · ihave HP1e := later_sep.mp $$ HP1
          icases HP1e with ⟨_, Hs1L⟩
          ihave HP2e := later_sep.mp $$ HP2
          icases HP2e with ⟨_, Hs2L⟩
          inext
          iapply specTapesFrag_valid_2 $$ Hs1L Hs2L
        iapply IsExcept0.is_except0
        unfold BIBase.except0
        iapply BI.or_intro_l
        iexact HbotLater
      · imodintro
        ipure_intro
        refine ⟨fun h => ?_, fun h => ?_⟩
        · exfalso; apply h_α1_β1
          have := congrArg Sigma.fst h; rw [he1, he2] at this
          injection this with this; injection this
        · exfalso; apply h_α2_β2
          have := congrArg Sigma.fst h; rw [he1', he2'] at this
          injection this with this; injection this

end interp_sound

/-! ## Relational environment typing

`env_ltyped2 Γ vs` asserts that the value-substitution `vs` is related to
itself by the relational context `Γ` at every bound variable. Mirrors
Rocq's `env_ltyped2` (interp.v:222–225), which uses `big_sepM2` on
gmaps. We use Metrology's list-of-pairs `SubstMap` representation and
phrase the property with explicit domain equality + a pointwise
quantified conjunction, matching Rocq's unfolded `big_sepM2`
semantics (see `iris/bi/big_op.v`: `big_sepM2_def := ⌜dom m1 = dom m2⌝ ∧
[∗ map] k ↦ xy ∈ map_zip m1 m2, Φ k xy.1 xy.2`). -/

/-- Relational typing context: atoms → (persistent) relation. -/
abbrev RelCtx (GF : BundledGFunctors) := List (Var × lrel GF)

/-- Value substitution: atoms → pairs of values. -/
abbrev ValSubstMap := List (Var × (Val × Val))

namespace RelCtx
variable {GF : BundledGFunctors}

/-- Lookup in a relational context. **Rightmost** binding wins (matching
`Exp.substMap`'s foldr semantics: rightmost is applied first / wins). -/
def lookup : RelCtx GF → Var → Option (lrel GF)
  | [], _ => none
  | (y, A) :: rest, x =>
    match lookup rest x with
    | some B => some B
    | none => if x = y then some A else none

/-- An entry's existence in `Γ` implies the lookup at its key is some. -/
theorem lookup_isSome_of_mem {Γ : RelCtx GF} {p : Var × lrel GF}
    (h : p ∈ Γ) : (Γ.lookup p.1).isSome := by
  induction Γ with
  | nil => cases h
  | cons q rest ih =>
    rcases List.mem_cons.mp h with rfl | hRest
    · -- q = p.
      simp only [RelCtx.lookup]
      cases hr : RelCtx.lookup rest p.1 with
      | some _ => simp
      | none => simp
    · simp only [RelCtx.lookup]
      have := ih hRest
      cases hr : RelCtx.lookup rest p.1 with
      | some _ => simp
      | none => rw [hr] at this; simp at this

end RelCtx

namespace ValSubstMap

/-- Lookup in a value substitution. **Rightmost** binding wins. -/
def lookup : ValSubstMap → Var → Option (Val × Val)
  | [], _ => none
  | (y, p) :: rest, x =>
    match lookup rest x with
    | some q => some q
    | none => if x = y then some p else none

/-- Left projection as a `SubstMap`. -/
def fst (vs : ValSubstMap) : SubstMap := vs.map (fun p => (p.1, p.2.1.1))

/-- Right projection as a `SubstMap`. -/
def snd (vs : ValSubstMap) : SubstMap := vs.map (fun p => (p.1, p.2.2.1))

/-- Lookup commutes with `.fst` projection. -/
theorem fst_lookup (vs : ValSubstMap) (x : Var) :
    SubstMap.lookup vs.fst x = (vs.lookup x).map (fun p => p.1.1) := by
  induction vs with
  | nil => rfl
  | cons p rest ih =>
    obtain ⟨y, v1, v2⟩ := p
    show SubstMap.lookup ((y, v1.1) :: ValSubstMap.fst rest) x =
      (ValSubstMap.lookup ((y, v1, v2) :: rest) x).map (fun p => p.1.1)
    simp only [SubstMap.lookup, ValSubstMap.lookup, ih]
    cases ValSubstMap.lookup rest x with
    | some q => simp
    | none => simp

/-- Lookup commutes with `.snd` projection. -/
theorem snd_lookup (vs : ValSubstMap) (x : Var) :
    SubstMap.lookup vs.snd x = (vs.lookup x).map (fun p => p.2.1) := by
  induction vs with
  | nil => rfl
  | cons p rest ih =>
    obtain ⟨y, v1, v2⟩ := p
    show SubstMap.lookup ((y, v2.1) :: ValSubstMap.snd rest) x =
      (ValSubstMap.lookup ((y, v1, v2) :: rest) x).map (fun p => p.2.1)
    simp only [SubstMap.lookup, ValSubstMap.lookup, ih]
    cases ValSubstMap.lookup rest x with
    | some q => simp
    | none => simp

/-- A lookup that returns `some` implies the key appears in the list. -/
theorem mem_of_lookup_isSome {vs : ValSubstMap} {x : Var}
    (h : (vs.lookup x).isSome) : ∃ p ∈ vs, p.1 = x := by
  induction vs with
  | nil => simp [ValSubstMap.lookup] at h
  | cons p rest ih =>
    obtain ⟨z, w⟩ := p
    simp only [ValSubstMap.lookup] at h
    cases hr : ValSubstMap.lookup rest x with
    | some w' =>
      simp only [hr] at h
      have hsome : (ValSubstMap.lookup rest x).isSome := by rw [hr]; rfl
      obtain ⟨p', hp'mem, hp'eq⟩ := ih hsome
      exact ⟨p', List.mem_cons.mpr (.inr hp'mem), hp'eq⟩
    | none =>
      simp only [hr] at h
      split_ifs at h with hxz
      · subst hxz
        exact ⟨(x, w), List.mem_cons.mpr (.inl rfl), rfl⟩
      · simp at h

end ValSubstMap

section env_typed
variable {hlc : Bool} {GF : BundledGFunctors} [ApproxisRGS hlc GF]

/-- The relational typing assertion on value substitutions.

Pointwise property: for every variable `x`, either both `Γ` and `vs` are
undefined at `x`, or both are defined and the pair in `vs x` lies in the
relation assigned by `Γ x`. Matches the unfolded semantics of Rocq's
`big_sepM2`. -/
noncomputable def env_ltyped2 (Γ : RelCtx GF) (vs : ValSubstMap) : IProp GF :=
  iprop((⌜∀ x, (Γ.lookup x).isSome ↔ (vs.lookup x).isSome⌝) ∗
    (⌜∀ p ∈ vs, p.2.1.1.isClosed .empty ∧ p.2.2.1.isClosed .empty⌝) ∗
    (∀ (x : Var) (A : lrel GF) (v1 v2 : Val),
      (⌜Γ.lookup x = some A⌝) -∗
      (⌜vs.lookup x = some (v1, v2)⌝) -∗
      A v1 v2))

/-- `env_ltyped2` is persistent: both conjuncts are persistent (pure
propositions and a forall of persistent lrels). -/
instance env_ltyped2_persistent (Γ : RelCtx GF) (vs : ValSubstMap) :
    Persistent (env_ltyped2 Γ vs) := by
  unfold env_ltyped2
  infer_instance

/-- Domain agreement: `Γ.lookup x = some _ ↔ vs.lookup x = some _`. -/
theorem env_ltyped2_domEq (Γ : RelCtx GF) (vs : ValSubstMap) :
    env_ltyped2 Γ vs ⊢@{IProp GF}
      iprop(⌜∀ x, (Γ.lookup x).isSome ↔ (vs.lookup x).isSome⌝) := by
  unfold env_ltyped2
  iintro ⟨%H, _, _⟩
  ipure_intro; exact H

/-- Closedness: every binding in `vs` is closed. -/
theorem env_ltyped2_allClosed (Γ : RelCtx GF) (vs : ValSubstMap) :
    env_ltyped2 Γ vs ⊢@{IProp GF}
      iprop(⌜∀ p ∈ vs, p.2.1.1.isClosed .empty ∧ p.2.2.1.isClosed .empty⌝) := by
  unfold env_ltyped2
  iintro ⟨_, %Hc, _⟩
  ipure_intro; exact Hc

/-- Lookup-by-Γ: if `Γ x = some A`, the substitution has a matching pair
and the pair is in `A`. -/
theorem env_ltyped2_lookup (Γ : RelCtx GF) (vs : ValSubstMap) (x : Var) (A : lrel GF)
    (hΓ : Γ.lookup x = some A) :
    env_ltyped2 Γ vs ⊢@{IProp GF}
      iprop(∃ (v1 v2 : Val), (⌜vs.lookup x = some (v1, v2)⌝) ∗ A v1 v2) := by
  unfold env_ltyped2
  iintro ⟨%Hdom, %Hclosed, Hall⟩
  have hvs : (vs.lookup x).isSome := (Hdom x).mp (by rw [hΓ]; rfl)
  obtain ⟨⟨v1, v2⟩, hvs_eq⟩ := Option.isSome_iff_exists.mp hvs
  iexists v1, v2
  isplitr; · ipure_intro; exact hvs_eq
  iapply Hall $$ %x %A %v1 %v2
  · ipure_intro; exact hΓ
  · ipure_intro; exact hvs_eq

/-- Empty-Γ empty-vs. -/
theorem env_ltyped2_empty : ⊢@{IProp GF} env_ltyped2 ([] : RelCtx GF) [] := by
  unfold env_ltyped2
  isplitr
  · ipure_intro; intro x; simp [RelCtx.lookup, ValSubstMap.lookup]
  isplitr
  · ipure_intro; intro p hp; cases hp
  iintro %x %A %v1 %v2 %hΓ %hvs
  simp [RelCtx.lookup] at hΓ

/-- Empty-Γ forces vs empty. -/
theorem env_ltyped2_empty_inv (vs : ValSubstMap) :
    env_ltyped2 ([] : RelCtx GF) vs ⊢@{IProp GF} ⌜vs = []⌝ := by
  unfold env_ltyped2
  iintro ⟨%Hdom, _, _⟩
  ipure_intro
  cases vs with
  | nil => rfl
  | cons p rest =>
    exfalso
    have hsome : (ValSubstMap.lookup (p :: rest) p.1).isSome := by
      simp only [ValSubstMap.lookup]
      cases ValSubstMap.lookup rest p.1 with
      | some _ => simp
      | none => simp
    have := (Hdom p.1).mpr hsome
    simp [RelCtx.lookup] at this

/-- Extending both contexts preserves `env_ltyped2`. Requires the new values
to be closed (since `env_ltyped2` records closedness of all bindings). -/
theorem env_ltyped2_insert (Γ : RelCtx GF) (vs : ValSubstMap)
    (x : Var) (A : lrel GF) (v1 v2 : Val)
    (hv1c : v1.1.isClosed .empty) (hv2c : v2.1.isClosed .empty) :
    iprop(A v1 v2 ∗ env_ltyped2 Γ vs) ⊢@{IProp GF}
      env_ltyped2 ((x, A) :: Γ) ((x, (v1, v2)) :: vs) := by
  iintro ⟨HA, HΓ⟩
  unfold env_ltyped2
  icases HΓ with ⟨%Hdom, %Hclosed, #Hall⟩
  isplitr
  · ipure_intro
    intro y
    simp only [RelCtx.lookup, ValSubstMap.lookup]
    have hdom_y := Hdom y
    cases hΓy : Γ.lookup y with
    | some B =>
      have : (vs.lookup y).isSome := hdom_y.mp (by rw [hΓy]; rfl)
      obtain ⟨q, hvy⟩ := Option.isSome_iff_exists.mp this
      rw [hvy]; simp
    | none =>
      have : ¬ (vs.lookup y).isSome := fun h => by
        have := hdom_y.mpr h
        rw [hΓy] at this; exact absurd this (by simp)
      have hvy : vs.lookup y = none := Option.not_isSome_iff_eq_none.mp this
      rw [hvy]; simp
  isplitr
  · ipure_intro
    intro p hp
    rcases List.mem_cons.mp hp with rfl | hpm
    · exact ⟨hv1c, hv2c⟩
    · exact Hclosed p hpm
  iintro %y %B %w1 %w2 %hΓ' %hvs'
  simp only [RelCtx.lookup] at hΓ'
  simp only [ValSubstMap.lookup] at hvs'
  cases hΓy : Γ.lookup y with
  | some Bold =>
    rw [hΓy] at hΓ'; injection hΓ' with hBeq; subst hBeq
    have hsome_vs : (vs.lookup y).isSome := (Hdom y).mp (by rw [hΓy]; rfl)
    obtain ⟨⟨w1', w2'⟩, hvy⟩ := Option.isSome_iff_exists.mp hsome_vs
    rw [hvy] at hvs'; injection hvs' with heq; obtain ⟨rfl, rfl⟩ := heq
    iapply Hall $$ %y %Bold %w1 %w2
    · ipure_intro; exact hΓy
    · ipure_intro; exact hvy
  | none =>
    rw [hΓy] at hΓ'
    simp only at hΓ'
    split_ifs at hΓ' with hxy
    injection hΓ' with hBeq; subst hBeq; subst hxy
    cases hvy : vs.lookup y with
    | some q =>
      have := (Hdom y).mpr (by rw [hvy]; rfl)
      rw [hΓy] at this; exact absurd this (by simp)
    | none =>
      rw [hvy] at hvs'
      simp only [if_pos rfl] at hvs'
      injection hvs' with heq
      obtain ⟨rfl, rfl⟩ := heq
      iexact HA

end env_typed

/-! ## The semantic typing judgement

Mirrors `bin_log_related` (interp.v:274–279). Takes an already-lifted
relational context `Γ : RelCtx GF` (clients holding a syntactic `Tctx`
can lift via `fun x => (Γ.lookupTy x).map (fun τ => interp τ Δ)` or a
list analogue). -/

section bin_log_related
variable {hlc : Bool} {GF : BundledGFunctors} [ApproxisRGS hlc GF]

noncomputable def bin_log_related (E : CoPset) (Γ : RelCtx GF)
    (e e' : Exp) (A : lrel GF) : IProp GF :=
  iprop(∀ (vs : ValSubstMap),
    env_ltyped2 Γ vs -∗
    refines E (Exp.substMap vs.fst e) (Exp.substMap vs.snd e') A)

/-- Convenience wrapper: take a syntactic type `τ` and a type-env `Δ`,
and use `interp τ Δ` as the relation. -/
noncomputable abbrev bin_log_related_ty (E : CoPset) (Δ : TyEnv GF)
    (Γ : RelCtx GF) (e e' : Exp) (τ : Ty) : IProp GF :=
  bin_log_related E Γ e e' (interp τ Δ)

end bin_log_related

/-! ## Notation for the semantic typing judgement -/

scoped notation:100 E "; " Δ "; " Γ " ⊨ " e " ≤log≤ " e' " : " τ =>
  bin_log_related_ty E Δ Γ e e' τ

scoped notation:100 Δ "; " Γ " ⊨ " e " ≤log≤ " e' " : " τ =>
  bin_log_related_ty (⊤ : CoPset) Δ Γ e e' τ

/-! ## Substitution lemmas on `interp`

Ports the two load-bearing lemmas from `interp.v` that `fundamental.v`
actually consumes. The stepping-stone lemmas (`interp_ren_up`,
`interp_weaken`, `interp_subst_up`) are not ported — we prove
`interp_ren` and `interp_subst` by direct structural induction on `τ`,
going through a general renaming-equivariance lemma
(`interp_rename`) and a general substitution-equivariance lemma
(`interp_substComp`) as internal tools. -/

section interp_subst
variable {hlc : Bool} {GF : BundledGFunctors} [ApproxisRGS hlc GF]

/-- Composing a `TyEnv` with a renaming. -/
@[reducible] def TyEnv.comp (Δ : TyEnv GF) (ξ : Nat → Nat) : TyEnv GF :=
  fun n => Δ (ξ n)

/-- `cons X (Δ ∘ ξ) = cons X Δ ∘ upren ξ`. -/
theorem TyEnv.comp_upren (X : lrel GF) (Δ : TyEnv GF) (ξ : Nat → Nat) :
    TyEnv.cons X (TyEnv.comp Δ ξ) = TyEnv.comp (TyEnv.cons X Δ) (upren ξ) := by
  funext n; cases n with
  | zero => rfl
  | succ m => rfl

/-- **Renaming equivariance.** Renaming `τ` by `ξ` syntactically is
equivalent to composing the environment with `ξ` semantically. -/
theorem interp_rename (τ : Ty) (ξ : Nat → Nat) (Δ : TyEnv GF) :
    interp (τ.rename ξ) Δ ≡ interp τ (TyEnv.comp Δ ξ) := by
  induction τ generalizing ξ Δ
  -- int, bool, unit, tape: all rfl
  · intro _ _; rfl
  · intro _ _; rfl
  · intro _ _; rfl
  -- prod
  · rename_i τ1 τ2 ih1 ih2
    intro v1 v2
    show (lrel_prod _ _).car v1 v2 ≡ (lrel_prod _ _).car v1 v2
    have h1 := ih1 ξ Δ
    have h2 := ih2 ξ Δ
    exact (NonExpansive₂.eqv (f := lrel_prod) h1 h2) v1 v2
  -- sum
  · rename_i τ1 τ2 ih1 ih2
    intro v1 v2
    have h1 := ih1 ξ Δ
    have h2 := ih2 ξ Δ
    exact (NonExpansive₂.eqv (f := lrel_sum) h1 h2) v1 v2
  -- arrow
  · rename_i τ1 τ2 ih1 ih2
    intro v1 v2
    have h1 := ih1 ξ Δ
    have h2 := ih2 ξ Δ
    exact (NonExpansive₂.eqv (f := lrel_arr) h1 h2) v1 v2
  -- ref
  · rename_i τ ih
    intro v1 v2
    have h := ih ξ Δ
    exact (NonExpansive.eqv (f := lrel_ref) h) v1 v2
  -- tape
  · intro _ _; rfl
  -- var
  · intro v1 v2; rfl
  -- rec'
  · rename_i τ' ih
    intro v1 v2
    show (lrel_rec _).car v1 v2 ≡ (lrel_rec _).car v1 v2
    refine OFE.equiv_dist.mpr fun n => ?_
    refine lrel_rec_ne (fun X => ?_) v1 v2
    have hih : interp (τ'.rename (upren ξ)) (TyEnv.cons X Δ) ≡
               interp τ' (TyEnv.comp (TyEnv.cons X Δ) (upren ξ)) := ih (upren ξ) _
    have hcomp : TyEnv.comp (TyEnv.cons X Δ) (upren ξ) = TyEnv.cons X (TyEnv.comp Δ ξ) :=
      (TyEnv.comp_upren X Δ ξ).symm
    rw [hcomp] at hih
    exact OFE.Equiv.dist hih
  -- forall'
  · rename_i τ' ih
    intro v1 v2
    show (lrel_forall _).car v1 v2 ≡ (lrel_forall _).car v1 v2
    refine OFE.equiv_dist.mpr fun n => ?_
    refine lrel_forall_ne (fun X => ?_) v1 v2
    have hih : interp (τ'.rename (upren ξ)) (TyEnv.cons X Δ) ≡
               interp τ' (TyEnv.comp (TyEnv.cons X Δ) (upren ξ)) := ih (upren ξ) _
    have hcomp : TyEnv.comp (TyEnv.cons X Δ) (upren ξ) = TyEnv.cons X (TyEnv.comp Δ ξ) :=
      (TyEnv.comp_upren X Δ ξ).symm
    rw [hcomp] at hih
    exact OFE.Equiv.dist hih
  -- exists'
  · rename_i τ' ih
    intro v1 v2
    show (lrel_exists _).car v1 v2 ≡ (lrel_exists _).car v1 v2
    refine OFE.equiv_dist.mpr fun n => ?_
    refine lrel_exists_ne (fun X => ?_) v1 v2
    have hih : interp (τ'.rename (upren ξ)) (TyEnv.cons X Δ) ≡
               interp τ' (TyEnv.comp (TyEnv.cons X Δ) (upren ξ)) := ih (upren ξ) _
    have hcomp : TyEnv.comp (TyEnv.cons X Δ) (upren ξ) = TyEnv.cons X (TyEnv.comp Δ ξ) :=
      (TyEnv.comp_upren X Δ ξ).symm
    rw [hcomp] at hih
    exact OFE.Equiv.dist hih

/-- **`interp_ren`**: shifting `τ` and consing the env preserves
interpretation. -/
theorem interp_ren (τ : Ty) (X : lrel GF) (Δ : TyEnv GF) :
    interp (Ty.shift τ) (TyEnv.cons X Δ) ≡ interp τ Δ := by
  unfold Ty.shift
  have h := interp_rename τ (· + 1) (TyEnv.cons X Δ)
  have hcomp : TyEnv.comp (TyEnv.cons X Δ) (· + 1) = Δ := by
    funext n; rfl
  rw [hcomp] at h
  exact h

/-- Lift a syntactic substitution to a semantic env by interpreting each
image type under `Δ`. -/
@[reducible] noncomputable def semSubst (σ : Nat → Ty) (Δ : TyEnv GF) : TyEnv GF :=
  fun n => interp (σ n) Δ

/-- Commutation of `up σ` with `cons X`: `semSubst (up σ) (cons X Δ) = cons X (semSubst σ Δ)`,
up to pointwise equivalence. (Equality would require extensionality on `lrel`.) -/
theorem semSubst_up (σ : Nat → Ty) (X : lrel GF) (Δ : TyEnv GF) :
    ∀ n, semSubst (up σ) (TyEnv.cons X Δ) n ≡ TyEnv.cons X (semSubst σ Δ) n
  | 0 => by unfold semSubst up; rfl
  | k + 1 => by
    unfold semSubst up TyEnv.cons
    -- ((σ k).rename (· + 1)).interp (cons X Δ) ≡ (σ k).interp Δ
    exact interp_ren (σ k) X Δ

/-- **Substitution equivariance.** Substituting in `τ` syntactically is
equivalent to evaluating under the semantic environment obtained by
interpreting each substitution image. -/
theorem interp_substG (τ : Ty) (σ : Nat → Ty) (Δ : TyEnv GF) :
    interp (τ.subst σ) Δ ≡ interp τ (semSubst σ Δ) := by
  induction τ generalizing σ Δ
  · intro _ _; rfl
  · intro _ _; rfl
  · intro _ _; rfl
  -- prod
  · rename_i τ1 τ2 ih1 ih2
    intro v1 v2
    show (lrel_prod _ _).car v1 v2 ≡ (lrel_prod _ _).car v1 v2
    exact (NonExpansive₂.eqv (f := lrel_prod) (ih1 σ Δ) (ih2 σ Δ)) v1 v2
  -- sum
  · rename_i τ1 τ2 ih1 ih2
    intro v1 v2
    exact (NonExpansive₂.eqv (f := lrel_sum) (ih1 σ Δ) (ih2 σ Δ)) v1 v2
  -- arrow
  · rename_i τ1 τ2 ih1 ih2
    intro v1 v2
    exact (NonExpansive₂.eqv (f := lrel_arr) (ih1 σ Δ) (ih2 σ Δ)) v1 v2
  -- ref
  · rename_i τ ih
    intro v1 v2
    exact (NonExpansive.eqv (f := lrel_ref) (ih σ Δ)) v1 v2
  -- tape
  · intro _ _; rfl
  -- var
  · intro v1 v2; rfl
  -- rec'
  · rename_i τ' ih
    intro v1 v2
    show (lrel_rec _).car v1 v2 ≡ (lrel_rec _).car v1 v2
    refine OFE.equiv_dist.mpr fun n => ?_
    refine lrel_rec_ne (fun X => ?_) v1 v2
    have hih : interp (τ'.subst (up σ)) (TyEnv.cons X Δ) ≡
               interp τ' (semSubst (up σ) (TyEnv.cons X Δ)) := ih (up σ) _
    -- Need to transport through semSubst_up to `cons X (semSubst σ Δ)`.
    have hne : interp τ' (semSubst (up σ) (TyEnv.cons X Δ)) ≡
               interp τ' (TyEnv.cons X (semSubst σ Δ)) := by
      refine OFE.equiv_dist.mpr fun m => ?_
      exact interp_ne_env τ' (fun k => (semSubst_up σ X Δ k).dist)
    exact (hih.trans hne).dist
  -- forall'
  · rename_i τ' ih
    intro v1 v2
    show (lrel_forall _).car v1 v2 ≡ (lrel_forall _).car v1 v2
    refine OFE.equiv_dist.mpr fun n => ?_
    refine lrel_forall_ne (fun X => ?_) v1 v2
    have hih : interp (τ'.subst (up σ)) (TyEnv.cons X Δ) ≡
               interp τ' (semSubst (up σ) (TyEnv.cons X Δ)) := ih (up σ) _
    have hne : interp τ' (semSubst (up σ) (TyEnv.cons X Δ)) ≡
               interp τ' (TyEnv.cons X (semSubst σ Δ)) := by
      refine OFE.equiv_dist.mpr fun m => ?_
      exact interp_ne_env τ' (fun k => (semSubst_up σ X Δ k).dist)
    exact (hih.trans hne).dist
  -- exists'
  · rename_i τ' ih
    intro v1 v2
    show (lrel_exists _).car v1 v2 ≡ (lrel_exists _).car v1 v2
    refine OFE.equiv_dist.mpr fun n => ?_
    refine lrel_exists_ne (fun X => ?_) v1 v2
    have hih : interp (τ'.subst (up σ)) (TyEnv.cons X Δ) ≡
               interp τ' (semSubst (up σ) (TyEnv.cons X Δ)) := ih (up σ) _
    have hne : interp τ' (semSubst (up σ) (TyEnv.cons X Δ)) ≡
               interp τ' (TyEnv.cons X (semSubst σ Δ)) := by
      refine OFE.equiv_dist.mpr fun m => ?_
      exact interp_ne_env τ' (fun k => (semSubst_up σ X Δ k).dist)
    exact (hih.trans hne).dist

/-- **`interp_subst`**: single substitution at the head. Mirrors
`interp.v:210–212`. With `Ty.single τ τ' = τ[τ'/0]`, this reads:
interpreting `τ[τ'/0]` is the same as interpreting `τ` under an
environment extended with the interpretation of `τ'`. -/
theorem interp_subst (τ' τ : Ty) (Δ : TyEnv GF) :
    interp (Ty.single τ τ') Δ ≡ interp τ (TyEnv.cons (interp τ' Δ) Δ) := by
  unfold Ty.single
  have h := interp_substG τ (fun n => match n with | 0 => τ' | k + 1 => .var k) Δ
  -- semSubst of that σ is `cons (interp τ' Δ) Δ` up to pointwise equiv.
  have hcong : interp τ (semSubst (fun n => match n with | 0 => τ' | k + 1 => .var k) Δ) ≡
               interp τ (TyEnv.cons (interp τ' Δ) Δ) := by
    refine OFE.equiv_dist.mpr fun m => ?_
    refine interp_ne_env τ (fun k => ?_)
    cases k with
    | zero => exact Dist.rfl
    | succ j => exact Dist.rfl
  exact h.trans hcong

end interp_subst

end ProbLang
