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

/-! ### `interp_closed`: closedness of values at any `interp τ Δ`

Now trivial: closedness is built into `lrel`'s structure (option D, 2026-04-27).
This was previously a substantial inductive proof requiring `IsClosedRespecting`
typeclass infrastructure. -/

section interp_closed
variable {hlc : Bool} {GF : BundledGFunctors} [ApproxisRGS hlc GF]

/-- Every `interp τ Δ` value-relation only relates closed values. Trivial via
`lrel.closed` field. -/
theorem interp_closed {Δ : TyEnv GF} (τ : Ty) (v v' : Val) :
    (interp τ Δ).car v v' ⊢@{IProp GF}
      iprop(⌜v.1.isClosedEmpty ∧ v'.1.isClosedEmpty⌝) :=
  (interp τ Δ).closed v v'

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

/-- If a key appears in vs, lookup is some. -/
theorem lookup_isSome_of_mem {vs : ValSubstMap} {x : Var}
    (hmem : ∃ w, (x, w) ∈ vs) : (vs.lookup x).isSome := by
  obtain ⟨w, hmem⟩ := hmem
  induction vs with
  | nil => exact absurd hmem (by simp)
  | cons q rest ih =>
    obtain ⟨k, v⟩ := q
    rcases List.mem_cons.mp hmem with hp_eq | hpm
    · injection hp_eq with hkx _
      subst hkx
      simp only [ValSubstMap.lookup]
      cases ValSubstMap.lookup rest x with
      | some _ => simp
      | none => simp
    · simp only [ValSubstMap.lookup]
      cases hrr : ValSubstMap.lookup rest x with
      | some _ => simp
      | none =>
        have := ih hpm
        rw [hrr] at this
        cases this

/-- Delete all entries with key `x` from a value substitution map. -/
def delete (vs : ValSubstMap) (x : Var) : ValSubstMap :=
  vs.filter (fun p => !decide (p.1 = x))

/-- After deleting `x`, lookup at `x` returns `none`. -/
theorem lookup_delete_self (vs : ValSubstMap) (x : Var) :
    (vs.delete x).lookup x = none := by
  induction vs with
  | nil => rfl
  | cons p rest ih =>
    obtain ⟨z, w⟩ := p
    show ValSubstMap.lookup
        (List.filter (fun p => !decide (p.1 = x)) ((z, w) :: rest)) x = none
    rw [List.filter_cons]
    by_cases hzx : z = x
    · simp [hzx]; show (delete rest x).lookup x = none; exact ih
    · have hcond : (!decide ((z, w).1 = x)) = true := by simp [hzx]
      rw [if_pos hcond]
      show (match ValSubstMap.lookup (delete rest x) x with
            | some q => some q
            | none => if x = z then some w else none) = none
      rw [ih]
      simp [Ne.symm hzx]

/-- After deleting `x`, lookup at any other key is unchanged. -/
theorem lookup_delete_other (vs : ValSubstMap) (x z : Var) (hxz : z ≠ x) :
    (vs.delete x).lookup z = vs.lookup z := by
  induction vs with
  | nil => rfl
  | cons p rest ih =>
    obtain ⟨w, v⟩ := p
    show ValSubstMap.lookup
        (List.filter (fun p => !decide (p.1 = x)) ((w, v) :: rest)) z
      = ValSubstMap.lookup ((w, v) :: rest) z
    rw [List.filter_cons]
    by_cases hwx : w = x
    · have hcond : (!decide ((w, v).1 = x)) = false := by simp [hwx]
      rw [if_neg (by rw [hcond]; simp)]
      -- LHS = lookup (delete rest x) z. Want = lookup ((w, v) :: rest) z.
      -- Since w = x, the head doesn't match z (since z ≠ x), so RHS reduces to lookup rest z.
      show ValSubstMap.lookup (delete rest x) z = ValSubstMap.lookup ((w, v) :: rest) z
      rw [ih]
      show ValSubstMap.lookup rest z = ValSubstMap.lookup ((w, v) :: rest) z
      simp only [ValSubstMap.lookup]
      have hzNeW : ¬ (z = w) := by intro h; subst h; exact hxz hwx
      cases ValSubstMap.lookup rest z with
      | some _ => rfl
      | none => simp [hzNeW]
    · have hcond : (!decide ((w, v).1 = x)) = true := by simp [hwx]
      rw [if_pos hcond]
      show (match ValSubstMap.lookup (delete rest x) z with
            | some q => some q
            | none => if z = w then some v else none)
        = (match ValSubstMap.lookup rest z with
            | some q => some q
            | none => if z = w then some v else none)
      rw [ih]

/-- Membership in `vs.delete x` excludes any pair with key `x`. -/
theorem mem_delete (vs : ValSubstMap) (x : Var) (p : Var × (Val × Val)) :
    p ∈ vs.delete x ↔ p ∈ vs ∧ p.1 ≠ x := by
  unfold delete
  rw [List.mem_filter]
  simp

/-- The fst-projection of `vs.delete x` filters x out of vs.fst. -/
theorem fst_delete (vs : ValSubstMap) (x : Var) :
    (vs.delete x).fst = vs.fst.filter (fun p => !decide (p.1 = x)) := by
  unfold delete fst
  induction vs with
  | nil => rfl
  | cons p rest ih =>
    obtain ⟨z, v1, v2⟩ := p
    simp only [List.filter_cons, List.map_cons]
    by_cases hzx : z = x
    · simp [hzx]; exact ih
    · have h1 : (!decide ((z, v1, v2).1 = x)) = true := by simp [hzx]
      have h2 : (!decide ((z, v1.1).1 = x)) = true := by simp [hzx]
      rw [if_pos h1]
      simp only [List.map_cons]
      rw [if_pos h2]
      simp only [List.cons.injEq, true_and]
      exact ih

/-- Snd analog. -/
theorem snd_delete (vs : ValSubstMap) (x : Var) :
    (vs.delete x).snd = vs.snd.filter (fun p => !decide (p.1 = x)) := by
  unfold delete snd
  induction vs with
  | nil => rfl
  | cons p rest ih =>
    obtain ⟨z, v1, v2⟩ := p
    simp only [List.filter_cons, List.map_cons]
    by_cases hzx : z = x
    · simp [hzx]; exact ih
    · have h1 : (!decide ((z, v1, v2).1 = x)) = true := by simp [hzx]
      have h2 : (!decide ((z, v2.1).1 = x)) = true := by simp [hzx]
      rw [if_pos h1]
      simp only [List.map_cons]
      rw [if_pos h2]
      simp only [List.cons.injEq, true_and]
      exact ih

/-- Domain of `vs.delete x` excludes x. -/
theorem map_fst_delete_notMem (vs : ValSubstMap) (x : Var) :
    x ∉ ((vs.delete x).map (·.1)).toFinset := by
  intro h
  simp only [List.mem_toFinset, List.mem_map] at h
  obtain ⟨p, hpmem, hpeq⟩ := h
  rw [mem_delete] at hpmem
  exact hpmem.2 hpeq

/-- Domain of `vs.delete x` is contained in domain of vs. -/
theorem map_fst_delete_subset (vs : ValSubstMap) (x : Var) :
    ((vs.delete x).map (·.1)).toFinset ⊆ (vs.map (·.1)).toFinset := by
  intro z hz
  simp only [List.mem_toFinset, List.mem_map] at hz ⊢
  obtain ⟨p, hpmem, hpeq⟩ := hz
  rw [mem_delete] at hpmem
  exact ⟨p, hpmem.1, hpeq⟩

/-- The pair returned by `lookup` is the rightmost matching member. -/
theorem mem_of_lookup_eq_some {vs : ValSubstMap} {y : Var} {w1 w2 : Val}
    (h : vs.lookup y = some (w1, w2)) : (y, (w1, w2)) ∈ vs := by
  induction vs with
  | nil => simp [ValSubstMap.lookup] at h
  | cons p rest ih =>
    obtain ⟨z, ⟨v1, v2⟩⟩ := p
    simp only [ValSubstMap.lookup] at h
    cases hr : ValSubstMap.lookup rest y with
    | some q =>
      rw [hr] at h
      -- h : some q = some (w1, w2)
      have hqe : q = (w1, w2) := by injection h
      have ihp := ih (by rw [hr, hqe])
      exact List.mem_cons.mpr (.inr ihp)
    | none =>
      rw [hr] at h
      split_ifs at h with hyz
      · subst hyz
        simp at h
        obtain ⟨h1, h2⟩ := h
        subst h1; subst h2
        exact List.mem_cons.mpr (.inl rfl)

/-- After delete + cons of new x-binding, fst-projection equals
substituting via subst _ x w in front of the deleted vs.fst. Used in `bin_log_related_rename`. -/
theorem fst_cons_delete (vs : ValSubstMap) (x : Var) (w1 w2 : Val) :
    ValSubstMap.fst ((x, (w1, w2)) :: vs.delete x)
      = (x, w1.1) :: (vs.delete x).fst := rfl

theorem snd_cons_delete (vs : ValSubstMap) (x : Var) (w1 w2 : Val) :
    ValSubstMap.snd ((x, (w1, w2)) :: vs.delete x)
      = (x, w2.1) :: (vs.delete x).snd := rfl

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
      simp only at hvs'
      injection hvs' with heq
      obtain ⟨rfl, rfl⟩ := heq
      iexact HA

/-- Helper: a `RelCtx.lookup` that returns `some` implies the key appears in the list. -/
theorem RelCtx.mem_of_lookup_isSome {Γ : RelCtx GF} {y : Var}
    (h : (Γ.lookup y).isSome) : y ∈ (Γ.map (·.1)).toFinset := by
  induction Γ with
  | nil => simp [RelCtx.lookup] at h
  | cons q rest ih =>
    obtain ⟨k, B⟩ := q
    simp only [RelCtx.lookup] at h
    cases hr : RelCtx.lookup rest y with
    | some _ =>
      rw [hr] at h
      have hsome : (RelCtx.lookup rest y).isSome := by rw [hr]; rfl
      have ihm := ih hsome
      simp at ihm ⊢
      exact Or.inr ihm
    | none =>
      rw [hr] at h
      split_ifs at h with hyk
      · simp [hyk]
      · simp at h

/-- Drop a head binding for a fresh atom: if `y ∉ Γ.dom`, then
`env_ltyped2 ((y, A) :: Γ) vs ⊢ env_ltyped2 Γ (vs.delete y)`. -/
theorem env_ltyped2_drop_head (Γ : RelCtx GF) (vs : ValSubstMap)
    (y : Var) (A : lrel GF)
    (hyNotDom : y ∉ (Γ.map (·.1)).toFinset) :
    env_ltyped2 ((y, A) :: Γ) vs ⊢@{IProp GF} env_ltyped2 Γ (vs.delete y) := by
  unfold env_ltyped2
  iintro ⟨%Hdom, %Hclosed, #Hall⟩
  have hΓy : Γ.lookup y = none := by
    cases hΓ : Γ.lookup y with
    | none => rfl
    | some _ =>
      exfalso
      have hsome : (Γ.lookup y).isSome := by rw [hΓ]; rfl
      exact hyNotDom (RelCtx.mem_of_lookup_isSome hsome)
  isplitr
  · ipure_intro
    intro z
    by_cases hzy : z = y
    · subst hzy
      rw [hΓy, ValSubstMap.lookup_delete_self]
      simp
    · rw [ValSubstMap.lookup_delete_other vs y z hzy]
      have hcons : RelCtx.lookup ((y, A) :: Γ) z =
          match Γ.lookup z with
          | some B => some B
          | none => if z = y then some A else none := rfl
      have heq := Hdom z
      rw [hcons] at heq
      cases hΓz : Γ.lookup z with
      | some B =>
        rw [hΓz] at heq
        simp at heq ⊢
        exact heq
      | none =>
        rw [hΓz] at heq
        simp [hzy] at heq ⊢
        exact heq
  isplitr
  · ipure_intro
    intro p hp
    rw [ValSubstMap.mem_delete] at hp
    exact Hclosed p hp.1
  iintro %z %B %v1 %v2 %hΓz %hvsz
  -- z ≠ y because (vs.delete y).lookup y = none, so z lookup landing is at z ≠ y.
  have hzy : z ≠ y := by
    intro heq; subst heq
    rw [ValSubstMap.lookup_delete_self] at hvsz
    cases hvsz
  rw [ValSubstMap.lookup_delete_other vs y z hzy] at hvsz
  -- ((y, A) :: Γ).lookup z = some B since Γ.lookup z = some B and z ≠ y → head doesn't fire.
  have hΓhead : RelCtx.lookup ((y, A) :: Γ) z = some B := by
    show (match Γ.lookup z with
          | some B' => some B'
          | none => if z = y then some A else none) = some B
    rw [hΓz]
  iapply Hall $$ %z %B %v1 %v2
  · ipure_intro; exact hΓhead
  · ipure_intro; exact hvsz

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

/-- **α-renaming for `bin_log_related`.** From related-at-`x` infer related-at-`y`
for the appropriately-renamed expressions, when both atoms are outside `Γ.dom`,
distinct, and `y` doesn't already appear in the bodies. -/
theorem bin_log_related_rename {E : CoPset} {Γ : RelCtx GF}
    {x y : Var} {A : lrel GF} {τE τE' : Exp} {B : lrel GF}
    (hxy : x ≠ y)
    (hxNotDom : x ∉ (Γ.map (·.1)).toFinset)
    (hyNotDom : y ∉ (Γ.map (·.1)).toFinset)
    (hyFvE : y ∉ τE.fv) (hyFvE' : y ∉ τE'.fv) :
    bin_log_related E ((x, A) :: Γ) τE τE' B ⊢@{IProp GF}
      bin_log_related E ((y, A) :: Γ) (τE.subst x (.fvar y)) (τE'.subst x (.fvar y)) B := by
  unfold bin_log_related
  iintro Hold %vs #Hvs
  -- Extract (w1, w2) at y from Hvs.
  have hΓy_lookup : Γ.lookup y = none := by
    cases hΓ : Γ.lookup y with
    | none => rfl
    | some _ =>
      exfalso
      have : (Γ.lookup y).isSome := by rw [hΓ]; rfl
      exact hyNotDom (RelCtx.mem_of_lookup_isSome this)
  have hyHeadLookup : RelCtx.lookup ((y, A) :: Γ) y = some A := by
    show (match Γ.lookup y with
          | some B => some B
          | none => if y = y then some A else none) = some A
    rw [hΓy_lookup]; simp
  ihave HvsAtY := env_ltyped2_lookup ((y, A) :: Γ) vs y A hyHeadLookup $$ Hvs
  icases HvsAtY with ⟨%w1, %w2, %hvsLookupY, HA_w⟩
  -- Closedness of (w1, w2) extracted from env_ltyped2.
  ihave %Hvs_clos := env_ltyped2_allClosed _ vs $$ Hvs
  -- Build vs' := (x, (w1, w2)) :: vs.delete y. Need env_ltyped2 ((x, A) :: Γ) vs'.
  -- Step 1: env_ltyped2 Γ (vs.delete y) via env_ltyped2_drop_head.
  ihave HvsDrop := env_ltyped2_drop_head Γ vs y A hyNotDom $$ Hvs
  -- Step 2: env_ltyped2 ((x, A) :: Γ) vs' via env_ltyped2_insert.
  -- Need closedness of w1, w2.
  have hw_closed : w1.1.isClosed .empty ∧ w2.1.isClosed .empty :=
    Hvs_clos (y, (w1, w2)) (ValSubstMap.mem_of_lookup_eq_some hvsLookupY)
  obtain ⟨hw1c, hw2c⟩ := hw_closed
  ihave Hvs' : iprop(env_ltyped2 ((x, A) :: Γ) ((x, (w1, w2)) :: vs.delete y))
      $$ [HA_w HvsDrop]
  · iapply (env_ltyped2_insert Γ (vs.delete y) x A w1 w2 hw1c hw2c)
    isplitr [HA_w]
    · iexact HA_w
    iexact HvsDrop
  -- Apply Hold at vs' := (x, (w1, w2)) :: vs.delete y.
  set vs' : ValSubstMap := (x, (w1, w2)) :: vs.delete y with hvs'_def
  ihave Hrefines := Hold $$ %vs' Hvs'
  -- Domain agreement: x ∉ vs.dom (since x ≠ y and x ∉ Γ.dom).
  ihave %Hvs_dom := env_ltyped2_domEq _ vs $$ Hvs
  have hvsLookupX : vs.lookup x = none := by
    have hΓx : Γ.lookup x = none := by
      cases hΓ : Γ.lookup x with
      | none => rfl
      | some _ =>
        exfalso
        have : (Γ.lookup x).isSome := by rw [hΓ]; rfl
        exact hxNotDom (RelCtx.mem_of_lookup_isSome this)
    have hΓheadX : RelCtx.lookup ((y, A) :: Γ) x = none := by
      show (match Γ.lookup x with
            | some B => some B
            | none => if x = y then some A else none) = none
      rw [hΓx]; simp [hxy]
    cases hvs : vs.lookup x with
    | none => rfl
    | some _ =>
      exfalso
      have : (vs.lookup x).isSome := by rw [hvs]; rfl
      have hΓsome : (RelCtx.lookup ((y, A) :: Γ) x).isSome := (Hvs_dom x).mpr this
      rw [hΓheadX] at hΓsome
      cases hΓsome
  -- vs.fst is AllClosed (from Hvs_clos).
  have hvs_fst_closed : SubstMap.AllClosed vs.fst := by
    intro p hp
    obtain ⟨⟨z, ⟨v1, v2⟩⟩, hmem, hpeq⟩ := List.mem_map.mp hp
    rw [← hpeq]
    exact (Hvs_clos (z, v1, v2) hmem).1
  have hvs_snd_closed : SubstMap.AllClosed vs.snd := by
    intro p hp
    obtain ⟨⟨z, ⟨v1, v2⟩⟩, hmem, hpeq⟩ := List.mem_map.mp hp
    rw [← hpeq]
    exact (Hvs_clos (z, v1, v2) hmem).2
  -- x ∉ vs.fst.dom (and vs.snd.dom): same set as vs.dom.
  have hvsFst_dom : (vs.fst.map (·.1)).toFinset = (vs.map (·.1)).toFinset := by
    show ((vs.map fun p => (p.1, p.2.1.1)).map (·.1)).toFinset = _
    simp only [List.map_map]; rfl
  have hvsSnd_dom : (vs.snd.map (·.1)).toFinset = (vs.map (·.1)).toFinset := by
    show ((vs.map fun p => (p.1, p.2.2.1)).map (·.1)).toFinset = _
    simp only [List.map_map]; rfl
  have hxNotVsDom : x ∉ (vs.map (·.1)).toFinset := by
    intro h
    simp only [List.mem_toFinset, List.mem_map] at h
    obtain ⟨p, hpmem, hpeq⟩ := h
    have hsome : (vs.lookup x).isSome := by
      apply ValSubstMap.lookup_isSome_of_mem
      refine ⟨p.2, ?_⟩
      rw [← hpeq]
      exact hpmem
    rw [hvsLookupX] at hsome
    cases hsome
  -- Use fst_lookup to get vs.fst.lookup y = some w1.1.
  have hvsFstLookupY : vs.fst.lookup y = some w1.1 := by
    rw [ValSubstMap.fst_lookup, hvsLookupY]; rfl
  have hvsSndLookupY : vs.snd.lookup y = some w2.1 := by
    rw [ValSubstMap.snd_lookup, hvsLookupY]; rfl
  -- Apply the swap lemma.
  have hxNotVsFst : x ∉ (vs.fst.map (·.1)).toFinset := by rw [hvsFst_dom]; exact hxNotVsDom
  have hxNotVsSnd : x ∉ (vs.snd.map (·.1)).toFinset := by rw [hvsSnd_dom]; exact hxNotVsDom
  have hswapFst :=
    Exp.substMap_subst_fvar_lookup vs.fst τE x y w1.1 hxy hxNotVsFst hvs_fst_closed
      hvsFstLookupY hyFvE
  have hswapSnd :=
    Exp.substMap_subst_fvar_lookup vs.snd τE' x y w2.1 hxy hxNotVsSnd hvs_snd_closed
      hvsSndLookupY hyFvE'
  -- Bridge: vs.fst.filter (·≠y) = (vs.delete y).fst.
  have hfilter1 : vs.fst.filter (fun p => !decide (p.1 = y)) = (vs.delete y).fst := by
    rw [ValSubstMap.fst_delete]
  have hfilter2 : vs.snd.filter (fun p => !decide (p.1 = y)) = (vs.delete y).snd := by
    rw [ValSubstMap.snd_delete]
  rw [hfilter1] at hswapFst
  rw [hfilter2] at hswapSnd
  -- Now hswapFst : substMap vs.fst (subst τE x (.fvar y)) = subst (substMap (vs.delete y).fst τE) x w1.1.
  -- And substMap vs'.fst τE = subst (substMap (vs.delete y).fst τE) x w1.1 (definitionally for cons).
  -- So substMap vs.fst (subst τE x (.fvar y)) = substMap vs'.fst τE.
  have heqFst : Exp.substMap vs.fst (Exp.subst τE x (.fvar y)) = Exp.substMap vs'.fst τE := by
    rw [hswapFst]
    show _ = Exp.subst (Exp.substMap (vs.delete y).fst τE) x w1.1
    rfl
  have heqSnd : Exp.substMap vs.snd (Exp.subst τE' x (.fvar y)) = Exp.substMap vs'.snd τE' := by
    rw [hswapSnd]
    show _ = Exp.subst (Exp.substMap (vs.delete y).snd τE') x w2.1
    rfl
  -- Now rewrite the goal to match Hrefines.
  rw [heqFst, heqSnd]
  iexact Hrefines

/-- α-renaming for `bin_log_related_ty` (interp-typed wrapper). -/
theorem bin_log_related_ty_rename {E : CoPset} {Δ : TyEnv GF} {Γ : RelCtx GF}
    {x y : Var} {A : lrel GF} {τE τE' : Exp} {τ : Ty}
    (hxy : x ≠ y)
    (hxNotDom : x ∉ (Γ.map (·.1)).toFinset)
    (hyNotDom : y ∉ (Γ.map (·.1)).toFinset)
    (hyFvE : y ∉ τE.fv) (hyFvE' : y ∉ τE'.fv) :
    bin_log_related_ty E Δ ((x, A) :: Γ) τE τE' τ ⊢@{IProp GF}
      bin_log_related_ty E Δ ((y, A) :: Γ) (τE.subst x (.fvar y)) (τE'.subst x (.fvar y)) τ :=
  bin_log_related_rename hxy hxNotDom hyNotDom hyFvE hyFvE'

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
