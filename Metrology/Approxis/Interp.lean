module

public import Metrology.Approxis.PrimitiveLaws
public import Metrology.Approxis.Model
public import Metrology.ProbLang.Metatheory
public import Metrology.ProbLang.Syntax.Types

@[expose] public section


/-!
# Type Interpretation

Nonexpansive map `interp : Ty → TyEnv rT GF → lrel rT GF` sending each syntactic
type to its logical relation under a type-variable environment.
-/

open Std Iris Iris.Std Iris.BI Iris.ProofMode OFE COFE ProbLang ProbLang.ApproxisWpGS

namespace ProbLang


variable {rT : Type _} [ProbLangℝ rT]

section TyEnvSetup
variable {GF : BundledGFunctors}

abbrev TyEnv (rT : Type _) (GF : BundledGFunctors) := Nat → lrel rT GF

def TyEnv.cons (X : lrel rT GF) (Δ : TyEnv rT GF) : TyEnv rT GF
  | 0 => X
  | n + 1 => Δ n

omit [ProbLangℝ rT] in
theorem TyEnv.cons_ne_head {n : Nat} {X Y : lrel rT GF} {Δ : TyEnv rT GF}
    (h : X ≡{n}≡ Y) : (TyEnv.cons X Δ) ≡{n}≡ (TyEnv.cons Y Δ)
  | 0 => h
  | _ + 1 => Dist.rfl

omit [ProbLangℝ rT] in
theorem TyEnv.cons_ne_tail {n : Nat} {X : lrel rT GF} {Δ Δ' : TyEnv rT GF}
    (h : Δ ≡{n}≡ Δ') : (TyEnv.cons X Δ) ≡{n}≡ (TyEnv.cons X Δ')
  | 0 => Dist.rfl
  | m + 1 => h m

@[reducible] def ctxLookup (x : Nat) (Δ : TyEnv rT GF) : lrel rT GF := Δ x

end TyEnvSetup

section interp
variable {hlc : HasLC} {GF : BundledGFunctors} [ApproxisRGS rT hlc GF]

/-- A function `TyEnv rT GF → lrel rT GF` paired with its pointwise
nonexpansiveness witness. -/
structure NEFun (rT : Type _) [ProbLangℝ rT] [MeasurableSingletonClass rT]
    (GF : BundledGFunctors) where
  fn  : TyEnv rT GF → lrel rT GF
  ne  : ∀ {n : Nat} {Δ Δ' : TyEnv rT GF}, Δ ≡{n}≡ Δ' → fn Δ ≡{n}≡ fn Δ'

namespace NEFun
variable {GF : BundledGFunctors} [ApproxisRGS rT hlc GF]

@[reducible] noncomputable def const (L : lrel rT GF) : NEFun rT GF :=
  { fn := fun _ => L, ne := fun _ => Dist.rfl }

@[reducible] def ofCtx (x : Nat) : NEFun rT GF :=
  { fn := fun Δ => ctxLookup x Δ, ne := fun h => h x }

@[reducible] noncomputable def map2 (F : lrel rT GF → lrel rT GF → lrel rT GF)
    [OFE.NonExpansive₂ F] (A B : NEFun rT GF) : NEFun rT GF :=
  { fn := fun Δ => F (A.fn Δ) (B.fn Δ)
    ne := fun h => OFE.NonExpansive₂.ne (A.ne h) (B.ne h) }

@[reducible] noncomputable def map1 (F : lrel rT GF → lrel rT GF)
    [OFE.NonExpansive F] (A : NEFun rT GF) : NEFun rT GF :=
  { fn := fun Δ => F (A.fn Δ)
    ne := fun h => OFE.NonExpansive.ne (A.ne h) }

@[reducible] noncomputable def rec' (A : NEFun rT GF) : NEFun rT GF :=
  { fn := fun Δ => lrel_rec
      { f := fun X => A.fn (TyEnv.cons X Δ)
        ne := ⟨fun {_ _ _} hXY => A.ne (TyEnv.cons_ne_head hXY)⟩ }
    ne := fun h => lrel_rec_ne (fun _ => A.ne (TyEnv.cons_ne_tail h)) }

@[reducible] noncomputable def forall' (A : NEFun rT GF) : NEFun rT GF :=
  { fn := fun Δ => lrel_forall (fun X => A.fn (TyEnv.cons X Δ))
    ne := fun h => lrel_forall_ne (fun _ => A.ne (TyEnv.cons_ne_tail h)) }

@[reducible] noncomputable def exists' (A : NEFun rT GF) : NEFun rT GF :=
  { fn := fun Δ => lrel_exists (fun X => A.fn (TyEnv.cons X Δ))
    ne := fun h => lrel_exists_ne (fun _ => A.ne (TyEnv.cons_ne_tail h)) }

end NEFun

/-- Bundled interpretation paired with a pointwise ne-witness. -/
noncomputable def interpNE : Ty → NEFun rT GF
  | .unit         => NEFun.const lrel_unit
  | .int          => NEFun.const lrel_int
  | .bool         => NEFun.const lrel_bool
  | .real         => NEFun.const lrel_real
  | .tape         => NEFun.const lrel_tape
  | .var x        => NEFun.ofCtx x
  | .prod τ1 τ2   => NEFun.map2 lrel_prod (interpNE τ1) (interpNE τ2)
  | .sum  τ1 τ2   => NEFun.map2 lrel_sum  (interpNE τ1) (interpNE τ2)
  | .arrow τ1 τ2  => NEFun.map2 lrel_arr  (interpNE τ1) (interpNE τ2)
  | .ref τ        => NEFun.map1 lrel_ref (interpNE τ)
  | .rec' τ'      => NEFun.rec'    (interpNE τ')
  | .forall' τ'   => NEFun.forall' (interpNE τ')
  | .exists' τ'   => NEFun.exists' (interpNE τ')

noncomputable def interp (τ : Ty) (Δ : TyEnv rT GF) : lrel rT GF :=
  (interpNE τ).fn Δ

theorem interp_ne_env (τ : Ty) {n : Nat} {Δ Δ' : TyEnv rT GF}
    (h : Δ ≡{n}≡ Δ') : interp τ Δ ≡{n}≡ interp τ Δ' :=
  (interpNE τ).ne h

/-! ### `interp` head-shape equations

These centralize the defeq bridges between `interp` at a constructor type and
the corresponding `lrel_*` builder. Rewriting through these is preferable to
inline `have h : interp ... = lrel_... := rfl; rw [h]` patterns: if the shape
of `interp` ever changes (e.g. an extra wrapper), only these lemmas need
updating. -/

@[simp] theorem interp_unit (Δ : TyEnv rT GF) : interp Ty.unit Δ = lrel_unit := rfl
@[simp] theorem interp_int  (Δ : TyEnv rT GF) : interp Ty.int  Δ = lrel_int  := rfl
@[simp] theorem interp_bool (Δ : TyEnv rT GF) : interp Ty.bool Δ = lrel_bool := rfl
@[simp] theorem interp_real (Δ : TyEnv rT GF) : interp Ty.real Δ = lrel_real := rfl
@[simp] theorem interp_tape (Δ : TyEnv rT GF) : interp Ty.tape Δ = lrel_tape := rfl

theorem interp_prod (Δ : TyEnv rT GF) (τ1 τ2 : Ty) :
    interp (Ty.prod τ1 τ2) Δ = lrel_prod (interp τ1 Δ) (interp τ2 Δ) := rfl

theorem interp_sum (Δ : TyEnv rT GF) (τ1 τ2 : Ty) :
    interp (Ty.sum τ1 τ2) Δ = lrel_sum (interp τ1 Δ) (interp τ2 Δ) := rfl

theorem interp_arrow (Δ : TyEnv rT GF) (τ1 τ2 : Ty) :
    interp (Ty.arrow τ1 τ2) Δ = lrel_arr (interp τ1 Δ) (interp τ2 Δ) := rfl

theorem interp_ref (Δ : TyEnv rT GF) (τ : Ty) :
    interp (Ty.ref τ) Δ = lrel_ref (interp τ Δ) := rfl

end interp

/-! ## Closedness of related values -/

section interp_closed
variable {hlc : HasLC} {GF : BundledGFunctors} [ApproxisRGS rT hlc GF]

/-- Every `interp τ Δ` value-relation only relates closed values. -/
theorem interp_closed {Δ : TyEnv rT GF} (τ : Ty) (v v' : Val rT) :
    (interp τ Δ).car v v' ⊢@{IProp GF}
      ⌜v.1.isClosedEmpty ∧ v'.1.isClosedEmpty⌝ :=
  (interp τ Δ).closed v v'

end interp_closed

/-! ## Unboxed-value predicate -/

@[simp] def Exp.isUnboxedV : Exp rT → Prop
  | .lit _ => True
  | .inl (.lit _) => True
  | .inr (.lit _) => True
  | _ => False

@[reducible] def Val.isUnboxed (v : Val rT) : Prop := v.1.isUnboxedV

/-! ## Soundness of the semantic type interpretation -/

section interp_sound
variable {hlc : HasLC} {GF : BundledGFunctors} [ApproxisRGS rT hlc GF]

/-- At an unboxed type, both related values are bare literals. Stronger than
`unboxed_type_sound`: `UnboxedType` doesn't include sums. -/
theorem unboxed_type_lit_shape {τ : Ty} {Δ : TyEnv rT GF} {v v' : Val rT}
    (H : UnboxedType τ) :
    (interp τ Δ).car v v' ⊢@{IProp GF}
      ⌜∃ l l' : BaseLit rT, v.1 = .lit l ∧ v'.1 = .lit l'⌝ := by
  cases H
  · show iprop(⌜ _ ⌝) ⊢ _
    iintro ⟨%h1, %h2⟩ !%
    exact ⟨_, _, Val.ext_iff.mp h1, Val.ext_iff.mp h2⟩
  · show iprop(∃ _, _) ⊢ _
    iintro ⟨%n, %h1, %h2⟩ !%
    exact ⟨_, _, Val.ext_iff.mp h1, Val.ext_iff.mp h2⟩
  · show iprop(∃ _, _) ⊢ _
    iintro ⟨%b, %h1, %h2⟩ !%
    exact ⟨_, _, Val.ext_iff.mp h1, Val.ext_iff.mp h2⟩
  · show iprop(∃ _ _, _) ⊢ _
    iintro ⟨%l1, %l2, %h1, %h2, _⟩ !%
    exact ⟨_, _, Val.ext_iff.mp h1, Val.ext_iff.mp h2⟩

/-- Unboxed-type values are unboxed. -/
theorem unboxed_type_sound {τ : Ty} {Δ : TyEnv rT GF} {v v' : Val rT}
    (H : UnboxedType τ) :
    (interp τ Δ).car v v' ⊢@{IProp GF} ⌜ Val.isUnboxed v ∧ Val.isUnboxed v' ⌝ := by
  refine (unboxed_type_lit_shape H).trans ?_
  iintro %h !%
  obtain ⟨l, l', h1, h2⟩ := h
  exact ⟨by simp [Val.isUnboxed, h1], by simp [Val.isUnboxed, h2]⟩

/-- At equality-types, both related values are pointwise equal. -/
theorem eq_type_sound {τ : Ty} {Δ : TyEnv rT GF} {v v' : Val rT} (H : EqType τ) :
    (interp τ Δ).car v v' ⊢@{IProp GF} ⌜ v = v' ⌝ := by
  induction H generalizing v v'
  · show iprop(⌜ _ ⌝) ⊢ _
    iintro ⟨%h1, %h2⟩ !%
    rw [h1, h2]
  · show iprop(∃ _, _) ⊢ _
    iintro ⟨%n, %h1, %h2⟩ !%
    rw [h1, h2]
  · show iprop(∃ _, _) ⊢ _
    iintro ⟨%b, %h1, %h2⟩ !%
    rw [h1, h2]
  · rename_i τ1 τ2 Hτ1 Hτ2 ih1 ih2
    unfold interp at ih1 ih2
    show iprop(∃ _ _ _ _, _) ⊢ _
    iintro ⟨%a1, %a2, %b1, %b2, %h1, %h2, HA, HB⟩
    ihave %heq1 := ih1 $$ HA
    ihave %heq2 := ih2 $$ HB
    ipureintro
    apply Val.ext
    rw [h1, h2, heq1, heq2]
  · rename_i τ1 τ2 Hτ1 Hτ2 ih1 ih2
    unfold interp at ih1 ih2
    show iprop(∃ _ _, _) ⊢ _
    iintro ⟨%w1, %w2, Hd⟩
    icases Hd with (⟨%h1, %h2, HA⟩ | ⟨%h1, %h2, HB⟩)
    · ihave %heq := ih1 $$ HA
      ipureintro
      apply Val.ext
      rw [h1, h2, heq]
    · ihave %heq := ih2 $$ HB
      ipureintro
      apply Val.ext
      rw [h1, h2, heq]

/-- Equality-type values are equal on both sides at once. -/
theorem eq_type_eq_iff {τ : Ty} {Δ : TyEnv rT GF} {v1 v2 w1 w2 : Val rT} (H : EqType τ) :
    (interp τ Δ).car v1 v2 ⊢@{IProp GF}
      (interp τ Δ).car w1 w2 -∗ |={⊤}=> ⌜ v1 = w1 ↔ v2 = w2 ⌝ := by
  iintro H1 H2
  ihave %heq1 := eq_type_sound H $$ H1
  ihave %heq2 := eq_type_sound H $$ H2
  imodintro
  ipureintro
  subst heq1 heq2
  exact .rfl

/-- The value shape forced by `lrel_ref`. -/
private theorem lrel_ref_shape (A : lrel rT GF) (v1 v2 : Val rT) :
    (lrel_ref A).car v1 v2 ⊢@{IProp GF} ⌜∃ l1 l2 : Loc, v1 = .loc l1 ∧ v2 = .loc l2⌝ := by
  unfold lrel_ref
  iintro ⟨%l1, %l2, %h1, %h2, -⟩ !%
  exact ⟨l1, l2, h1, h2⟩

/-- Decidable equality at unboxed types. -/
theorem unboxed_type_eq {τ : Ty} {Δ : TyEnv rT GF} {v1 v2 w1 w2 : Val rT}
    (H : UnboxedType τ) :
    (interp τ Δ).car v1 v2 ⊢@{IProp GF}
      (interp τ Δ).car w1 w2 -∗ |={⊤}=> ⌜ v1 = w1 ↔ v2 = w2 ⌝ := by
  cases H
  · exact eq_type_eq_iff .unit
  · exact eq_type_eq_iff .int
  · exact eq_type_eq_iff .bool
  · rename_i τ'
    rw [interp_ref]
    iintro H1 H2
    ihave %hs1 := lrel_ref_shape _ v1 v2 $$ H1
    ihave %hs2 := lrel_ref_shape _ w1 w2 $$ H2
    obtain ⟨l1, l2, rfl, rfl⟩ := hs1
    obtain ⟨r1, r2, rfl, rfl⟩ := hs2
    have hloc : ∀ a b : Loc, ((.loc a : Val rT) = .loc b) ↔ a = b := fun a b =>
      ⟨fun h => by injection Val.ext_iff.mp h with h; injection h, (· ▸ rfl)⟩
    simp only [hloc]
    by_cases hl : l1 = r1
    · subst hl
      imod interp_ref_funct (E := ⊤) (interp τ' Δ) l1 l2 r2 CoPset.subseteq_top $$ H1 H2 with %h
      imodintro
      ipureintro
      simp [h]
    · by_cases hr : l2 = r2
      · -- `l2 = r2` would force `l1 = r1` by injectivity on the spec side.
        subst hr
        imod interp_ref_inj (E := ⊤) (interp τ' Δ) l2 l1 r1 CoPset.subseteq_top $$ H1 H2 with %h
        exact (hl h).elim
      · imodintro
        ipureintro
        exact iff_of_false hl hr

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
abbrev RelCtx (rT : Type _) (GF : BundledGFunctors) := List (Var × lrel rT GF)

/-- Value substitution: atoms → pairs of values. -/
abbrev ValSubstMap (rT : Type _) := List (Var × (Val rT × Val rT))

namespace RelCtx
variable {rT : Type _} [ProbLangℝ rT]
variable {GF : BundledGFunctors}

/-- Lookup in a relational context. **Rightmost** binding wins (matching
`Exp.substMap`'s foldr semantics: rightmost is applied first / wins). -/
def lookup : RelCtx rT GF → Var → Option (lrel rT GF)
  | [], _ => none
  | (y, A) :: rest, x =>
    match lookup rest x with
    | some B => some B
    | none => if x = y then some A else none

omit [ProbLangℝ rT] in
/-- An entry's existence in `Γ` implies the lookup at its key is some. -/
theorem lookup_isSome_of_mem {Γ : RelCtx rT GF} {p : Var × lrel rT GF}
    (h : p ∈ Γ) : (Γ.lookup p.1).isSome := by
  induction Γ with
  | nil => cases h
  | cons q rest ih =>
    simp only [RelCtx.lookup]
    rcases List.mem_cons.mp h with rfl | hRest
    · cases RelCtx.lookup rest p.1 <;> simp
    · have := ih hRest
      cases hr : RelCtx.lookup rest p.1 <;> simp_all

end RelCtx

namespace ValSubstMap
variable {rT : Type _} [ProbLangℝ rT]

/-- Lookup in a value substitution. **Rightmost** binding wins. -/
def lookup : ValSubstMap rT → Var → Option (Val rT × Val rT)
  | [], _ => none
  | (y, p) :: rest, x =>
    match lookup rest x with
    | some q => some q
    | none => if x = y then some p else none

/-- Left projection as a `SubstMap`. -/
def fst (vs : ValSubstMap rT) : SubstMap rT := vs.map (fun p => (p.1, p.2.1.1))

/-- Right projection as a `SubstMap`. -/
def snd (vs : ValSubstMap rT) : SubstMap rT := vs.map (fun p => (p.1, p.2.2.1))

/-! The `.fst`/`.snd` projections are both instances of projecting each bound pair
through a component selector `f`, so their theory is proved once, generically,
and specialised by `exact`-defeq. -/
section proj
variable (f : Val rT × Val rT → Val rT)

/-- Lookup commutes with a pointwise projection. -/
theorem proj_lookup : ∀ (vs : ValSubstMap rT) (x : Var),
    SubstMap.lookup (vs.map fun p => (p.1, (f p.2).1)) x = (vs.lookup x).map (fun q => (f q).1)
  | [], _ => rfl
  | (y, w) :: rest, x => by
    simp only [List.map_cons, SubstMap.lookup, ValSubstMap.lookup, proj_lookup rest x]
    cases ValSubstMap.lookup rest x <;> simp

omit [ProbLangℝ rT] in
/-- A pointwise projection leaves the domain unchanged. -/
theorem proj_dom (vs : ValSubstMap rT) :
    (((vs.map fun p => (p.1, (f p.2).1))).map (·.1)).toFinset = (vs.map (·.1)).toFinset := by
  simp only [List.map_map]; rfl

/-- Closedness transfers to a pointwise projection. -/
theorem proj_allClosed {vs : ValSubstMap rT} (h : ∀ p ∈ vs, (f p.2).1.isClosed .empty) :
    SubstMap.AllClosed (vs.map fun p => (p.1, (f p.2).1)) := by
  intro p hp
  obtain ⟨q, hmem, rfl⟩ := List.mem_map.mp hp
  exact h q hmem

end proj

/-- Lookup commutes with `.fst` projection. -/
theorem fst_lookup (vs : ValSubstMap rT) (x : Var) :
    SubstMap.lookup vs.fst x = (vs.lookup x).map (fun p => p.1.1) :=
  proj_lookup Prod.fst vs x

omit [ProbLangℝ rT] in
/-- A variable outside the domain is unbound. Feeds the `hdom` premise of
`Exp.lam_substMap_isLocallyClosed`. -/
theorem lookup_eq_none_of_not_mem {y : Var} : ∀ (vs : ValSubstMap rT),
    y ∉ (vs.map (·.1)).toFinset → ValSubstMap.lookup vs y = none
  | [], _ => rfl
  | p :: rest, hyNot => by
    obtain ⟨z, _⟩ := p
    simp only [List.map_cons, List.toFinset_cons, Finset.mem_insert, not_or] at hyNot
    simp only [ValSubstMap.lookup, lookup_eq_none_of_not_mem rest hyNot.2]
    simp [hyNot.1]

/-- `.fst` specialisation of `lookup_eq_none_of_not_mem`. -/
theorem fst_lookup_eq_none_of_not_mem {vs : ValSubstMap rT} {y : Var}
    (hy : y ∉ (vs.map (·.1)).toFinset) : SubstMap.lookup vs.fst y = none := by
  rw [fst_lookup, lookup_eq_none_of_not_mem vs hy]; rfl

/-- Lookup commutes with `.snd` projection. -/
theorem snd_lookup (vs : ValSubstMap rT) (x : Var) :
    SubstMap.lookup vs.snd x = (vs.lookup x).map (fun p => p.2.1) :=
  proj_lookup Prod.snd vs x

/-- `.snd` specialisation of `lookup_eq_none_of_not_mem`. -/
theorem snd_lookup_eq_none_of_not_mem {vs : ValSubstMap rT} {y : Var}
    (hy : y ∉ (vs.map (·.1)).toFinset) : SubstMap.lookup vs.snd y = none := by
  rw [snd_lookup, lookup_eq_none_of_not_mem vs hy]; rfl

/-- Projecting to the left component leaves the domain unchanged. -/
theorem fst_dom (vs : ValSubstMap rT) :
    (vs.fst.map (·.1)).toFinset = (vs.map (·.1)).toFinset :=
  proj_dom Prod.fst vs

/-- Projecting to the right component leaves the domain unchanged. -/
theorem snd_dom (vs : ValSubstMap rT) :
    (vs.snd.map (·.1)).toFinset = (vs.map (·.1)).toFinset :=
  proj_dom Prod.snd vs

omit [ProbLangℝ rT] in
/-- The pair returned by `lookup` is the rightmost matching member. -/
theorem mem_of_lookup_eq_some {vs : ValSubstMap rT} {y : Var} {w1 w2 : Val rT}
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
      exact List.mem_cons.mpr (.inr (ih (by rw [hr, hqe])))
    | none =>
      rw [hr] at h
      split_ifs at h with hyz
      · subst hyz
        simp at h
        obtain ⟨h1, h2⟩ := h
        subst h1; subst h2
        exact List.mem_cons.mpr (.inl rfl)

omit [ProbLangℝ rT] in
/-- A lookup that returns `some` implies the key appears in the list. -/
theorem mem_of_lookup_isSome {vs : ValSubstMap rT} {x : Var}
    (h : (vs.lookup x).isSome) : ∃ p ∈ vs, p.1 = x := by
  obtain ⟨⟨w1, w2⟩, hw⟩ := Option.isSome_iff_exists.mp h
  exact ⟨(x, (w1, w2)), mem_of_lookup_eq_some hw, rfl⟩

omit [ProbLangℝ rT] in
/-- If a key appears in vs, lookup is some. -/
theorem lookup_isSome_of_mem {vs : ValSubstMap rT} {x : Var}
    (hmem : ∃ w, (x, w) ∈ vs) : (vs.lookup x).isSome := by
  obtain ⟨w, hmem⟩ := hmem
  induction vs with
  | nil => simp at hmem
  | cons q rest ih =>
    obtain ⟨k, v⟩ := q
    simp only [ValSubstMap.lookup]
    cases hr : ValSubstMap.lookup rest x with
    | some _ => rfl
    | none =>
      rcases List.mem_cons.mp hmem with hq | hm
      · injection hq with hkx _
        simp [hkx]
      · rw [hr] at ih
        exact absurd (ih hm) (by simp)

/-- Delete all entries with key `x` from a value substitution map. -/
def delete (vs : ValSubstMap rT) (x : Var) : ValSubstMap rT :=
  vs.filter (fun p => !decide (p.1 = x))

omit [ProbLangℝ rT] in
/-- `delete` in cons form: drop the head when its key matches, else recurse. -/
theorem delete_cons (z : Var) (w : Val rT × Val rT) (rest : ValSubstMap rT) (x : Var) :
    ValSubstMap.delete ((z, w) :: rest) x
      = if z = x then rest.delete x else (z, w) :: rest.delete x := by
  by_cases hzx : z = x <;> simp [ValSubstMap.delete, hzx]

omit [ProbLangℝ rT] in
/-- After deleting `x`, lookup at `x` returns `none`. -/
theorem lookup_delete_self (vs : ValSubstMap rT) (x : Var) :
    (vs.delete x).lookup x = none := by
  induction vs with
  | nil => rfl
  | cons p rest ih =>
    obtain ⟨z, w⟩ := p
    rw [delete_cons]
    split
    · exact ih
    · rename_i hzx
      simp [ValSubstMap.lookup, ih, Ne.symm hzx]

omit [ProbLangℝ rT] in
/-- After deleting `x`, lookup at any other key is unchanged. -/
theorem lookup_delete_other (vs : ValSubstMap rT) (x z : Var) (hxz : z ≠ x) :
    (vs.delete x).lookup z = vs.lookup z := by
  induction vs with
  | nil => rfl
  | cons p rest ih =>
    obtain ⟨w, v⟩ := p
    rw [delete_cons]
    split
    · -- the head binds `x`, which `z` is not, so the head never fires on either side
      rename_i hwx
      subst hwx
      simp only [ValSubstMap.lookup, ih]
      cases ValSubstMap.lookup rest z <;> simp [hxz]
    · simp [ValSubstMap.lookup, ih]

omit [ProbLangℝ rT] in
/-- Membership in `vs.delete x` excludes any pair with key `x`. -/
theorem mem_delete (vs : ValSubstMap rT) (x : Var) (p : Var × (Val rT × Val rT)) :
    p ∈ vs.delete x ↔ p ∈ vs ∧ p.1 ≠ x := by
  unfold delete
  rw [List.mem_filter]
  simp

omit [ProbLangℝ rT] in
/-- A pointwise projection commutes with `delete`. -/
theorem proj_delete (f : Val rT × Val rT → Val rT) (vs : ValSubstMap rT) (x : Var) :
    (vs.delete x).map (fun p => (p.1, (f p.2).1))
      = (vs.map fun p => (p.1, (f p.2).1)).filter (fun p => !decide (p.1 = x)) := by
  induction vs with
  | nil => rfl
  | cons p rest ih =>
    obtain ⟨z, w⟩ := p
    rw [delete_cons, List.map_cons, List.filter_cons]
    by_cases hzx : z = x <;> simp [hzx, ih]

/-- The fst-projection of `vs.delete x` filters x out of vs.fst. -/
theorem fst_delete (vs : ValSubstMap rT) (x : Var) :
    (vs.delete x).fst = vs.fst.filter (fun p => !decide (p.1 = x)) :=
  proj_delete Prod.fst vs x

/-- Snd analog. -/
theorem snd_delete (vs : ValSubstMap rT) (x : Var) :
    (vs.delete x).snd = vs.snd.filter (fun p => !decide (p.1 = x)) :=
  proj_delete Prod.snd vs x

end ValSubstMap

section env_typed
variable {hlc : HasLC} {GF : BundledGFunctors} [ApproxisRGS rT hlc GF]

/-- The relational typing assertion on value substitutions.

Pointwise property: for every variable `x`, either both `Γ` and `vs` are
undefined at `x`, or both are defined and the pair in `vs x` lies in the
relation assigned by `Γ x`. Matches the unfolded semantics of Rocq's
`big_sepM2`. -/
noncomputable def env_ltyped2 (Γ : RelCtx rT GF) (vs : ValSubstMap rT) : IProp GF :=
  iprop(⌜∀ x, (Γ.lookup x).isSome ↔ (vs.lookup x).isSome⌝ ∗
    ⌜∀ p ∈ vs, p.2.1.1.isClosed .empty ∧ p.2.2.1.isClosed .empty⌝ ∗
    (∀ (x : Var) (A : lrel rT GF) (v1 v2 : Val rT),
      ⌜Γ.lookup x = some A⌝ -∗ ⌜vs.lookup x = some (v1, v2)⌝ -∗ A v1 v2))

/-- `env_ltyped2` is persistent: both conjuncts are persistent (pure
propositions and a forall of persistent lrels). -/
instance env_ltyped2_persistent (Γ : RelCtx rT GF) (vs : ValSubstMap rT) :
    Persistent (env_ltyped2 Γ vs) := by
  unfold env_ltyped2
  infer_instance

omit [ProbLangℝ rT] in
/-- Domain agreement: `Γ.lookup x = some _ ↔ vs.lookup x = some _`. -/
theorem env_ltyped2_domEq (Γ : RelCtx rT GF) (vs : ValSubstMap rT) :
    env_ltyped2 Γ vs ⊢@{IProp GF}
      ⌜∀ x, (Γ.lookup x).isSome ↔ (vs.lookup x).isSome⌝ := by
  unfold env_ltyped2
  iintro ⟨%H, _, _⟩
  ipureintro; exact H

omit [ProbLangℝ rT] in
/-- Closedness: every binding in `vs` is closed. -/
theorem env_ltyped2_allClosed (Γ : RelCtx rT GF) (vs : ValSubstMap rT) :
    env_ltyped2 Γ vs ⊢@{IProp GF}
      ⌜∀ p ∈ vs, p.2.1.1.isClosed .empty ∧ p.2.2.1.isClosed .empty⌝ := by
  unfold env_ltyped2
  iintro ⟨_, %Hc, _⟩
  ipureintro; exact Hc

/-- `.fst` corollary of `env_ltyped2_allClosed`, in the form `Exp.substMap` lemmas want. -/
theorem env_ltyped2_fst_allClosed (Γ : RelCtx rT GF) (vs : ValSubstMap rT) :
    env_ltyped2 Γ vs ⊢@{IProp GF} ⌜SubstMap.AllClosed vs.fst⌝ := by
  iintro Hvs
  ihave %Hc := env_ltyped2_allClosed Γ vs $$ Hvs
  ipureintro
  exact ValSubstMap.proj_allClosed Prod.fst fun p hp => (Hc p hp).1

/-- `.snd` corollary of `env_ltyped2_allClosed`, in the form `Exp.substMap` lemmas want. -/
theorem env_ltyped2_snd_allClosed (Γ : RelCtx rT GF) (vs : ValSubstMap rT) :
    env_ltyped2 Γ vs ⊢@{IProp GF} ⌜SubstMap.AllClosed vs.snd⌝ := by
  iintro Hvs
  ihave %Hc := env_ltyped2_allClosed Γ vs $$ Hvs
  ipureintro
  exact ValSubstMap.proj_allClosed Prod.snd fun p hp => (Hc p hp).2

omit [ProbLangℝ rT] in
/-- The domain of `Γ` is covered by the domain of any related substitution. -/
theorem env_ltyped2_domSubset (Γ : RelCtx rT GF) (vs : ValSubstMap rT) :
    env_ltyped2 Γ vs ⊢@{IProp GF}
      ⌜(Γ.map (·.1)).toFinset ⊆ (vs.map (·.1)).toFinset⌝ := by
  iintro Hvs
  ihave %hDom := env_ltyped2_domEq Γ vs $$ Hvs
  ipureintro
  intro y hy
  simp only [List.mem_toFinset, List.mem_map] at hy
  obtain ⟨p, hpmem, rfl⟩ := hy
  obtain ⟨q, hqmem, hqeq⟩ :=
    ValSubstMap.mem_of_lookup_isSome ((hDom p.1).mp (RelCtx.lookup_isSome_of_mem hpmem))
  simp only [List.mem_toFinset, List.mem_map]
  exact ⟨q, hqmem, hqeq⟩

omit [ProbLangℝ rT] in
/-- Lookup-by-Γ: if `Γ x = some A`, the substitution has a matching pair
and the pair is in `A`. -/
theorem env_ltyped2_lookup (Γ : RelCtx rT GF) (vs : ValSubstMap rT) (x : Var) (A : lrel rT GF)
    (hΓ : Γ.lookup x = some A) :
    env_ltyped2 Γ vs ⊢@{IProp GF}
      ∃ (v1 v2 : Val rT), ⌜vs.lookup x = some (v1, v2)⌝ ∗ A v1 v2 := by
  unfold env_ltyped2
  iintro ⟨%Hdom, %Hclosed, Hall⟩
  have hvs : (vs.lookup x).isSome := (Hdom x).mp (by rw [hΓ]; rfl)
  obtain ⟨⟨v1, v2⟩, hvs_eq⟩ := Option.isSome_iff_exists.mp hvs
  iexists v1, v2
  iframe %hvs_eq
  iapply Hall $$ %x %A %v1 %v2 %(hΓ)
  · ipureintro; exact hvs_eq

omit [ProbLangℝ rT] in
/-- Empty-Γ empty-vs. -/
theorem env_ltyped2_empty : ⊢@{IProp GF} env_ltyped2 ([] : RelCtx rT GF) [] := by
  unfold env_ltyped2
  isplitr
  · ipureintro; intro x; simp [RelCtx.lookup, ValSubstMap.lookup]
  isplitr
  · ipureintro; intro p hp; cases hp
  iintro %x %A %v1 %v2 %hΓ %hvs
  simp [RelCtx.lookup] at hΓ

omit [ProbLangℝ rT] in
/-- Empty-Γ forces vs empty. -/
theorem env_ltyped2_empty_inv (vs : ValSubstMap rT) :
    env_ltyped2 ([] : RelCtx rT GF) vs ⊢@{IProp GF} ⌜vs = []⌝ := by
  unfold env_ltyped2
  iintro ⟨%Hdom, _, _⟩ !%
  cases vs with
  | nil => rfl
  | cons p rest =>
    exfalso
    have hsome : (ValSubstMap.lookup (p :: rest) p.1).isSome := by
      simp only [ValSubstMap.lookup]
      cases ValSubstMap.lookup rest p.1 <;> simp
    have := (Hdom p.1).mpr hsome
    simp [RelCtx.lookup] at this

omit [ProbLangℝ rT] in
/-- Extending both contexts preserves `env_ltyped2`. Requires the new values
to be closed (since `env_ltyped2` records closedness of all bindings). -/
theorem env_ltyped2_insert (Γ : RelCtx rT GF) (vs : ValSubstMap rT)
    (x : Var) (A : lrel rT GF) (v1 v2 : Val rT)
    (hv1c : v1.1.isClosed .empty) (hv2c : v2.1.isClosed .empty) :
    iprop(A v1 v2 ∗ env_ltyped2 Γ vs) ⊢@{IProp GF}
      env_ltyped2 ((x, A) :: Γ) ((x, (v1, v2)) :: vs) := by
  iintro ⟨HA, HΓ⟩
  unfold env_ltyped2
  icases HΓ with ⟨%Hdom, %Hclosed, #Hall⟩
  isplitr
  · ipureintro
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
  · ipureintro
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
    iapply Hall $$ %y %Bold %w1 %w2 %(hΓy)
    · ipureintro; exact hvy
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

omit [ProbLangℝ rT] in
/-- Helper: a `RelCtx.lookup` that returns `some` implies the key appears in the list. -/
theorem RelCtx.mem_of_lookup_isSome {Γ : RelCtx rT GF} {y : Var}
    (h : (Γ.lookup y).isSome) : y ∈ (Γ.map (·.1)).toFinset := by
  induction Γ with
  | nil => simp [RelCtx.lookup] at h
  | cons q rest ih =>
    obtain ⟨k, B⟩ := q
    simp only [RelCtx.lookup] at h
    cases hr : RelCtx.lookup rest y with
    | some _ => simp [ih (by rw [hr]; rfl)]
    | none => rw [hr] at h; split_ifs at h with hyk <;> simp_all

omit [ProbLangℝ rT] in
/-- Cons equation for `RelCtx.lookup`: the tail wins, the head is the fallback. -/
theorem RelCtx.lookup_cons (y : Var) (A : lrel rT GF) (Γ : RelCtx rT GF) (z : Var) :
    RelCtx.lookup ((y, A) :: Γ) z
      = match Γ.lookup z with
        | some B => some B
        | none => if z = y then some A else none := rfl

omit [ProbLangℝ rT] in
/-- Contrapositive of `RelCtx.mem_of_lookup_isSome`. -/
theorem RelCtx.lookup_eq_none_of_not_mem {Γ : RelCtx rT GF} {y : Var}
    (hyNotDom : y ∉ (Γ.map (·.1)).toFinset) : Γ.lookup y = none := by
  cases hΓ : Γ.lookup y with
  | none => rfl
  | some _ => exact absurd (RelCtx.mem_of_lookup_isSome (by rw [hΓ]; rfl)) hyNotDom

omit [ProbLangℝ rT] in
/-- Drop a head binding for a fresh atom: if `y ∉ Γ.dom`, then
`env_ltyped2 ((y, A) :: Γ) vs ⊢ env_ltyped2 Γ (vs.delete y)`. -/
theorem env_ltyped2_drop_head (Γ : RelCtx rT GF) (vs : ValSubstMap rT)
    (y : Var) (A : lrel rT GF)
    (hyNotDom : y ∉ (Γ.map (·.1)).toFinset) :
    env_ltyped2 ((y, A) :: Γ) vs ⊢@{IProp GF} env_ltyped2 Γ (vs.delete y) := by
  unfold env_ltyped2
  iintro ⟨%Hdom, %Hclosed, #Hall⟩
  have hΓy : Γ.lookup y = none := RelCtx.lookup_eq_none_of_not_mem hyNotDom
  isplitr
  · ipureintro
    intro z
    by_cases hzy : z = y
    · subst hzy
      rw [hΓy, ValSubstMap.lookup_delete_self]
      simp
    · rw [ValSubstMap.lookup_delete_other vs y z hzy]
      have heq := Hdom z
      rw [RelCtx.lookup_cons] at heq
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
  · ipureintro
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
    rw [RelCtx.lookup_cons, hΓz]
  iapply Hall $$ %z %B %v1 %v2 %(hΓhead)
  · ipureintro; exact hvsz

end env_typed

/-! ## The semantic typing judgement

Mirrors `bin_log_related` (interp.v:274–279). Takes an already-lifted
relational context `Γ : RelCtx rT GF` (clients holding a syntactic `Tctx`
can lift via `fun x => (Γ.lookupTy x).map (fun τ => interp τ Δ)` or a
list analogue). -/

section bin_log_related
variable {hlc : HasLC} {GF : BundledGFunctors} [ApproxisRGS rT hlc GF]

noncomputable def bin_log_related (E : CoPset) (Γ : RelCtx rT GF)
    (e e' : Exp rT) (A : lrel rT GF) : IProp GF :=
  iprop(∀ (vs : ValSubstMap rT),
    env_ltyped2 Γ vs -∗
    refines E (Exp.substMap vs.fst e) (Exp.substMap vs.snd e') A)

/-- Convenience wrapper: take a syntactic type `τ` and a type-env `Δ`,
and use `interp τ Δ` as the relation. -/
noncomputable abbrev bin_log_related_ty (E : CoPset) (Δ : TyEnv rT GF)
    (Γ : RelCtx rT GF) (e e' : Exp rT) (τ : Ty) : IProp GF :=
  bin_log_related E Γ e e' (interp τ Δ)

/-- **α-renaming for `bin_log_related`.** From related-at-`x` infer related-at-`y`
for the appropriately-renamed expressions, when both atoms are outside `Γ.dom`,
distinct, and `y` doesn't already appear in the bodies. -/
theorem bin_log_related_rename {E : CoPset} {Γ : RelCtx rT GF}
    {x y : Var} {A : lrel rT GF} {τE τE' : Exp rT} {B : lrel rT GF}
    (hxy : x ≠ y)
    (hxNotDom : x ∉ (Γ.map (·.1)).toFinset)
    (hyNotDom : y ∉ (Γ.map (·.1)).toFinset)
    (hyFvE : y ∉ τE.fv) (hyFvE' : y ∉ τE'.fv) :
    bin_log_related E ((x, A) :: Γ) τE τE' B ⊢@{IProp GF}
      bin_log_related E ((y, A) :: Γ) (τE.subst x (.fvar y)) (τE'.subst x (.fvar y)) B := by
  unfold bin_log_related
  iintro Hold %vs #Hvs
  -- Extract (w1, w2) at y from Hvs.
  have hyHeadLookup : RelCtx.lookup ((y, A) :: Γ) y = some A := by
    rw [RelCtx.lookup_cons, RelCtx.lookup_eq_none_of_not_mem hyNotDom]; simp
  icases env_ltyped2_lookup ((y, A) :: Γ) vs y A hyHeadLookup $$ Hvs with ⟨%w1, %w2, %hvsLookupY,
    HA_w⟩
  -- Closedness of (w1, w2) extracted from env_ltyped2.
  ihave %Hvs_clos := env_ltyped2_allClosed _ vs $$ Hvs
  obtain ⟨hw1c, hw2c⟩ :=
    Hvs_clos (y, (w1, w2)) (ValSubstMap.mem_of_lookup_eq_some hvsLookupY)
  -- Build vs' := (x, (w1, w2)) :: vs.delete y, related to `(x, A) :: Γ`.
  ihave HvsDrop := env_ltyped2_drop_head Γ vs y A hyNotDom $$ Hvs
  ihave Hvs' : iprop% env_ltyped2 ((x, A) :: Γ) ((x, (w1, w2)) :: vs.delete y)
      $$ [HA_w HvsDrop]
  · iapply (env_ltyped2_insert Γ (vs.delete y) x A w1 w2 hw1c hw2c)
    iframe HA_w
    iexact HvsDrop
  -- Apply Hold at vs' := (x, (w1, w2)) :: vs.delete y.
  set vs' : ValSubstMap rT := (x, (w1, w2)) :: vs.delete y with hvs'_def
  ihave Hrefines := Hold $$ %vs' Hvs'
  -- Domain agreement: x ∉ vs.dom (since x ≠ y and x ∉ Γ.dom).
  ihave %Hvs_dom := env_ltyped2_domEq _ vs $$ Hvs
  have hvsLookupX : vs.lookup x = none := by
    have hΓheadX : RelCtx.lookup ((y, A) :: Γ) x = none := by
      rw [RelCtx.lookup_cons, RelCtx.lookup_eq_none_of_not_mem hxNotDom]; simp [hxy]
    cases hvs : vs.lookup x with
    | none => rfl
    | some _ =>
      have hΓsome : (RelCtx.lookup ((y, A) :: Γ) x).isSome := (Hvs_dom x).mpr (by rw [hvs]; rfl)
      rw [hΓheadX] at hΓsome
      cases hΓsome
  have hxNotVsDom : x ∉ (vs.map (·.1)).toFinset := by
    intro h
    simp only [List.mem_toFinset, List.mem_map] at h
    obtain ⟨p, hpmem, hpeq⟩ := h
    have hsome : (vs.lookup x).isSome := by
      refine ValSubstMap.lookup_isSome_of_mem ⟨p.2, ?_⟩
      rw [← hpeq]; exact hpmem
    rw [hvsLookupX] at hsome
    cases hsome
  -- Apply the swap lemma on each projection, then fold the filter back into `delete`.
  have hswapFst :=
    Exp.substMap_subst_fvar_lookup vs.fst τE x y w1.1 hxy
      (by rw [ValSubstMap.fst_dom]; exact hxNotVsDom)
      (ValSubstMap.proj_allClosed Prod.fst fun p hp => (Hvs_clos p hp).1)
      (by rw [ValSubstMap.fst_lookup, hvsLookupY]; rfl) hyFvE
  have hswapSnd :=
    Exp.substMap_subst_fvar_lookup vs.snd τE' x y w2.1 hxy
      (by rw [ValSubstMap.snd_dom]; exact hxNotVsDom)
      (ValSubstMap.proj_allClosed Prod.snd fun p hp => (Hvs_clos p hp).2)
      (by rw [ValSubstMap.snd_lookup, hvsLookupY]; rfl) hyFvE'
  rw [← ValSubstMap.fst_delete] at hswapFst
  rw [← ValSubstMap.snd_delete] at hswapSnd
  -- `substMap vs'.fst τE` is, for the cons `vs'`, definitionally
  -- `subst (substMap (vs.delete y).fst τE) x w1.1` — which is what the swap lemma produced.
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
theorem bin_log_related_ty_rename {E : CoPset} {Δ : TyEnv rT GF} {Γ : RelCtx rT GF}
    {x y : Var} {A : lrel rT GF} {τE τE' : Exp rT} {τ : Ty}
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
variable {hlc : HasLC} {GF : BundledGFunctors} [ApproxisRGS rT hlc GF]

/-- Composing a `TyEnv` with a renaming. -/
@[reducible] def TyEnv.comp (Δ : TyEnv rT GF) (ξ : Nat → Nat) : TyEnv rT GF :=
  fun n => Δ (ξ n)

omit [ProbLangℝ rT] in
/-- `cons X (Δ ∘ ξ) = cons X Δ ∘ upren ξ`. -/
theorem TyEnv.comp_upren (X : lrel rT GF) (Δ : TyEnv rT GF) (ξ : Nat → Nat) :
    TyEnv.cons X (TyEnv.comp Δ ξ) = TyEnv.comp (TyEnv.cons X Δ) (Renaming.under ξ) := by
  funext n; cases n <;> rfl

/-- The binder step shared by the `rec'`/`forall'`/`exists'` cases of
`interp_rename`: the induction hypothesis, transported across `TyEnv.comp_upren`. -/
private theorem interp_rename_under {τ' : Ty} {ξ : Nat → Nat} {Δ : TyEnv rT GF}
    (ih : ∀ (ξ : Nat → Nat) (Δ : TyEnv rT GF),
      interp (τ'.rename ξ) Δ = interp τ' (TyEnv.comp Δ ξ))
    (X : lrel rT GF) :
    interp (τ'.rename (Renaming.under ξ)) (TyEnv.cons X Δ)
      = interp τ' (TyEnv.cons X (TyEnv.comp Δ ξ)) :=
  (ih _ _).trans (congrArg (interp τ') (TyEnv.comp_upren X Δ ξ).symm)

/-- **Renaming equivariance.** Renaming `τ` by `ξ` syntactically is
equivalent to composing the environment with `ξ` semantically. -/
theorem interp_rename (τ : Ty) (ξ : Nat → Nat) (Δ : TyEnv rT GF) :
    interp (τ.rename ξ) Δ = interp τ (TyEnv.comp Δ ξ) := by
  induction τ generalizing ξ Δ with
  | prod τ1 τ2 ih1 ih2 => exact congrArg₂ lrel_prod (ih1 ξ Δ) (ih2 ξ Δ)
  | sum τ1 τ2 ih1 ih2 => exact congrArg₂ lrel_sum (ih1 ξ Δ) (ih2 ξ Δ)
  | arrow τ1 τ2 ih1 ih2 => exact congrArg₂ lrel_arr (ih1 ξ Δ) (ih2 ξ Δ)
  | ref τ ih => exact congrArg lrel_ref (ih ξ Δ)
  | rec' τ' ih =>
    exact OFE.eq_dist.mpr fun _ => lrel_rec_ne fun X => (interp_rename_under ih X).dist
  | forall' τ' ih =>
    exact OFE.eq_dist.mpr fun _ => lrel_forall_ne fun X => (interp_rename_under ih X).dist
  | exists' τ' ih =>
    exact OFE.eq_dist.mpr fun _ => lrel_exists_ne fun X => (interp_rename_under ih X).dist
  -- int, bool, unit, real, tape, var
  | _ => rfl

/-- **`interp_ren`**: shifting `τ` and consing the env preserves
interpretation. -/
theorem interp_ren (τ : Ty) (X : lrel rT GF) (Δ : TyEnv rT GF) :
    interp (Ty.shift τ) (TyEnv.cons X Δ) = interp τ Δ :=
  -- `TyEnv.comp (cons X Δ) (· + 1)` is definitionally `Δ`.
  interp_rename τ (· + 1) (TyEnv.cons X Δ)

/-- Lift a syntactic substitution to a semantic env by interpreting each
image type under `Δ`. -/
@[reducible] noncomputable def semSubst (σ : Nat → Ty) (Δ : TyEnv rT GF) : TyEnv rT GF :=
  fun n => interp (σ n) Δ

/-- Commutation of `up σ` with `cons X`: `semSubst (up σ) (cons X Δ) = cons X (semSubst σ Δ)`,
up to pointwise equivalence. (Equality would require extensionality on `lrel`.) -/
theorem semSubst_up (σ : Nat → Ty) (X : lrel rT GF) (Δ : TyEnv rT GF) :
    ∀ n, semSubst (up σ) (TyEnv.cons X Δ) n = TyEnv.cons X (semSubst σ Δ) n
  | 0 => rfl
  -- ((σ k).rename (· + 1)).interp (cons X Δ) = (σ k).interp Δ
  | k + 1 => interp_ren (σ k) X Δ

/-- The binder step shared by the `rec'`/`forall'`/`exists'` cases of
`interp_substG`: the induction hypothesis, transported across `semSubst_up`. -/
private theorem interp_substG_under {τ' : Ty} {σ : Nat → Ty} {Δ : TyEnv rT GF}
    (ih : ∀ (σ : Nat → Ty) (Δ : TyEnv rT GF),
      interp (τ'.subst σ) Δ = interp τ' (semSubst σ Δ))
    (X : lrel rT GF) :
    interp (τ'.subst (up σ)) (TyEnv.cons X Δ)
      = interp τ' (TyEnv.cons X (semSubst σ Δ)) :=
  (ih _ _).trans <|
    OFE.eq_dist.mpr fun _ => interp_ne_env τ' fun k => (semSubst_up σ X Δ k).dist

/-- **Substitution equivariance.** Substituting in `τ` syntactically is
equivalent to evaluating under the semantic environment obtained by
interpreting each substitution image. -/
theorem interp_substG (τ : Ty) (σ : Nat → Ty) (Δ : TyEnv rT GF) :
    interp (τ.subst σ) Δ = interp τ (semSubst σ Δ) := by
  induction τ generalizing σ Δ with
  | prod τ1 τ2 ih1 ih2 => exact congrArg₂ lrel_prod (ih1 σ Δ) (ih2 σ Δ)
  | sum τ1 τ2 ih1 ih2 => exact congrArg₂ lrel_sum (ih1 σ Δ) (ih2 σ Δ)
  | arrow τ1 τ2 ih1 ih2 => exact congrArg₂ lrel_arr (ih1 σ Δ) (ih2 σ Δ)
  | ref τ ih => exact congrArg lrel_ref (ih σ Δ)
  | rec' τ' ih =>
    exact OFE.eq_dist.mpr fun _ => lrel_rec_ne fun X => (interp_substG_under ih X).dist
  | forall' τ' ih =>
    exact OFE.eq_dist.mpr fun _ => lrel_forall_ne fun X => (interp_substG_under ih X).dist
  | exists' τ' ih =>
    exact OFE.eq_dist.mpr fun _ => lrel_exists_ne fun X => (interp_substG_under ih X).dist
  -- int, bool, unit, real, tape, var
  | _ => rfl

/-- **`interp_subst`**: single substitution at the head. Mirrors
`interp.v:210–212`. With `Ty.single τ τ' = τ[τ'/0]`, this reads:
interpreting `τ[τ'/0]` is the same as interpreting `τ` under an
environment extended with the interpretation of `τ'`. -/
theorem interp_subst (τ' τ : Ty) (Δ : TyEnv rT GF) :
    interp (Ty.single τ τ') Δ = interp τ (TyEnv.cons (interp τ' Δ) Δ) := by
  unfold Ty.single
  -- The `semSubst` of that substitution is pointwise `cons (interp τ' Δ) Δ`.
  refine (interp_substG τ _ Δ).trans (congrArg (interp τ) ?_)
  funext n; cases n <;> rfl

end interp_subst

end ProbLang
