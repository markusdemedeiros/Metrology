module

public import Metrology.TotalEris

@[expose] public section

/-!
# Geometric distribution (total correctness)

Port of `clutch/theories/eris/tutorial/geometric_total.v`. The target
spec — termination-with-probability-one of the geometric sampler — is
proved here using Eris's *error induction*: a recursive program
`geometric ()` that returns `0` with probability `1/3` and otherwise
recurses with `+1` terminates almost surely returning a non-negative
integer.

Status: all four top-level theorems (`geo_nonneg`, `geo_nonneg_pos_err`,
`geo_tgl`, `geo_mass_one`) are **fully proved with no `sorry` along any
dependency chain**, including through `twp_rand_exp` /
`twp_rand_exp_nat` and the total-adequacy chain (`twp_tgl`,
`twp_mass_lim_exec`, etc.). `geo_tgl` and `geo_mass_one` require
`[AppPreGS rT GF] [ECPreGS GF] [InvGpreS GF]` (passed through from
`twp_tgl`). -/

open Std Iris Iris.Std Iris.BI Iris.ProofMode OFE COFE ProbLang ProbLang.TotalEris
  ProbLang.TotalEris.ErisWpGS
open scoped AppGS ENNReal

namespace ProbLang
namespace TotalEris
namespace Examples


variable {rT : Type _} [ProbLangℝ rT] [Countable rT] [MeasurableSingletonClass rT]
variable {hlc : Bool} {GF : BundledGFunctors.{0,0,0}} [ErisGS rT hlc GF]

/-! ## The geometric sampler

  ```
  geometric := rec "geo" "n" => if rand 2 = 0 then 0 else geo n + 1
  ```

  Encoded under locally-nameless: `bvar 0` is the bound recursor argument
  (we don't actually use it), and the body samples uniformly from
  `[0, 3) = {0, 1, 2}` (Eris's `rand #2`). -/

/-- The geometric sampler. Rocq:
```
Definition geometric : val :=
  rec: "geo" "n" :=
    if: rand #2 = #0 then #0 else "geo" "n" + #1.
``` -/
def geometric : Exp rT :=
  pl(rec geo n :=
      if rand(#2, #.unit) = #0
        then #0
        else (geo n) + #1)

/-- The result-postcondition shared by all geometric specs: the sampler
returns a non-negative integer. -/
abbrev geoPost : Val rT → IProp GF :=
  fun w => iprop(∃ m : Int, ⌜w = ⟨.lit (.int m), IsVal.lit⟩ ∧ 0 ≤ m⌝)

/-! ## Spec: `geo_nonneg_pos_err`

  Assuming `↯ε` for some `ε > 0`, the geometric sampler applied to any
  unit-typed argument terminates returning a non-negative integer.
  Mirrors `geometric_total.v:147`. -/
theorem geo_nonneg_pos_err (E : CoPset) (ε : ENNReal) (hε : 0 < ε) :
    iprop(↯ε) ⊢@{IProp GF}
      tglWp E (Exp.app (geometric (rT := rT)) (Exp.lit .unit))
        (geoPost (rT := rT) (GF := GF)) := by
  -- Error induction via `ec_ind_simpl_external` with multiplier `k = 3/2`.
  -- Gives us an IH `↯((3/2) * ε) -∗ WP geometric()` together with `↯ε`.
  refine ec_ind_simpl_external (k := (3/2 : NNReal)) hε (by norm_num) ?_
  iintro ⟨IH, Herr⟩
  -- β-reduce `geometric ()` via two pure steps (`app_fix`, `app_lam`).
  -- Unfold `geometric` and reduce the `Exp.close` from `pl(...)` into the
  -- raw `bvar` form so `twp_pure_step_fupd`'s explicit `e₁`/`e₂` match.
  -- The `pl(rec geo n := …)` body wraps each binder in `Exp.close` over a
  -- fresh atom; reduce all of these so the body becomes the explicit bvar
  -- form that `twp_pure_step_fupd`'s `e₁`/`e₂` arguments expect.
  simp only [geometric, Exp.close, Exp.closeRec, Nat.zero_add,
    Var.internal.injEq, ↓reduceIte, reduceCtorEq]
  set innerBody : Exp rT :=
    Exp.cond
      (Exp.binop .eq (Exp.rand (Exp.lit (.int 2)) (Exp.lit .unit)) (Exp.lit (.int 0)))
      (Exp.lit (.int 0))
      (Exp.binop .plus (Exp.app (Exp.bvar 1) (Exp.bvar 0)) (Exp.lit (.int 1)))
    with hInner
  -- Step 1: `app_fix`.
  iapply (ErisWpGS.twp_pure_step_fupd (n := 1)
    (e₁ := Exp.app (Exp.fix (Exp.lam innerBody)) (Exp.lit .unit))
    (e₂ := Exp.app (Exp.open' (Exp.lam innerBody) (Exp.fix (Exp.lam innerBody)))
      (Exp.lit .unit))
    (Exp.lit .unit : Exp rT).isValue ⟨IsVal.lit⟩)
  -- Reduce the substitution `bvar 1 := geometric` (leaves the inner `lam`).
  simp only [hInner, Exp.open', Exp.openRec, ↓reduceIte, Nat.reduceAdd,
    Nat.reduceEqDiff]
  -- Step 2: `app_lam` with argument `()`.
  set reducedBody : Exp rT :=
    Exp.cond
      (Exp.binop .eq (Exp.rand (Exp.lit (.int 2)) (Exp.lit .unit)) (Exp.lit (.int 0)))
      (Exp.lit (.int 0))
      (Exp.binop .plus (Exp.app (Exp.fix (Exp.lam innerBody)) (Exp.bvar 0))
        (Exp.lit (.int 1)))
    with hReduced
  iapply (ErisWpGS.twp_pure_step_fupd (n := 1)
    (e₁ := Exp.app (Exp.lam reducedBody) (Exp.lit .unit))
    (e₂ := Exp.open' reducedBody (Exp.lit .unit))
    (Exp.lit .unit : Exp rT).isValue ⟨IsVal.lit⟩)
  simp only [hReduced, Exp.open', Exp.openRec, ↓reduceIte]
  -- Collapse `openRec 2 () innerBody = innerBody` (innerBody has only
  -- bvar 0/1, so a level-2 open is a no-op).
  simp only [hInner, Exp.openRec, ↓reduceIte, Nat.reduceAdd, Nat.reduceEqDiff]
  -- Focus on `rand 2 ()` via `twp_bind`. Trick: a direct `iapply (tglWp_bind …)`
  -- fails because `iapply`'s unifier won't reduce `K.fill` to the `cond …`
  -- syntactic form. Instead, build the bind entailment as a typed `have`
  -- (Lean's elaborator checks the type ascription via defeq on `K.fill`),
  -- then `iapply` that pre-shaped entailment.
  have hBind : iprop(tglWp E (Exp.rand (Exp.lit (.int 2)) (Exp.lit .unit))
      (fun v => tglWp E
        (Exp.cond
          (Exp.binop .eq (Exp.ofVal v) (Exp.ofVal ⟨.lit (.int 0), IsVal.lit⟩))
          (.lit (.int 0))
          (.binop .plus (.app (Exp.fix (Exp.lam innerBody)) (.lit .unit))
            (.lit (.int 1))))
        geoPost))
    ⊢@{IProp GF}
      iprop(tglWp E
        (Exp.cond
          (Exp.binop .eq (Exp.rand (Exp.lit (.int 2)) (Exp.lit .unit))
            (Exp.lit (.int 0)))
          (.lit (.int 0))
          (.binop .plus (.app (Exp.fix (Exp.lam innerBody)) (.lit .unit))
            (.lit (.int 1))))
        geoPost) :=
    ErisWpGS.tglWp_bind (K :=
      [EctxItem.binopL .eq ⟨.lit (.int 0), IsVal.lit⟩,
       EctxItem.condC (.lit (.int 0))
         (.binop .plus (.app (Exp.fix (Exp.lam innerBody)) (.lit .unit))
           (.lit (.int 1)))])
  iapply hBind
  -- Goal: `tglWp E (rand 2 ()) (fun v => tglWp E (cond (v = 0) 0 (geo()+1)) _)`.
  -- Apply `twp_rand_exp` with `F(n) = if n=0 then 0 else (3/2)*ε`. The
  -- `$$ [Herr]` clause threads the iris hypothesis `Herr : ↯ε` into the
  -- lemma's `↯ε₁` precondition.
  let F : ℕ → ENNReal := fun n => if n = 0 then 0 else (3/2 : NNReal) * ε
  iapply (twp_rand_exp (z := 2) (ε₁ := ε) (ε₂ := F) (Hz := by decide)
    (HSum := by
      -- `∑ n ∈ range 2, F n = F 0 + F 1 = 0 + (3/2)*ε = (3/2)*ε ≤ 2 * ε`.
      simp only [F, show (2 : Int).toNat = 2 from rfl, Finset.sum_range_succ,
        Finset.sum_range_zero, zero_add, Nat.reduceEqDiff, ↓reduceIte]
      rw [show ((2 : ℕ) : ENNReal) = 2 from by norm_num]
      -- Goal reduces to `(3/2)*ε ≤ 2 * ε`. Multiplying by 2: `3*ε ≤ 4*ε`. ✓
      rw [show (2 : ENNReal) = (3/2 : NNReal) + (1/2 : NNReal) from by
            rw [← ENNReal.coe_add]; norm_num, add_mul]
      exact le_add_right le_rfl)) $$ Herr
  iintro %n ⟨%Hn, Hcr⟩
  -- With `0 ≤ n < 2`, the sampled `n : ℤ` is either 0 or 1. Case-split.
  obtain ⟨Hn₁, Hn₂⟩ := Hn
  interval_cases n
  · -- n = 0 branch. Reduce `cond (binop eq 0 0) 0 (…) → … → lit 0`.
    -- Step A: `twp_bind` on the cond context to focus the discriminant.
    have hBindCond0 : iprop(tglWp E
        (Exp.binop .eq (Exp.ofVal ⟨.lit (.int 0), IsVal.lit⟩)
          (Exp.ofVal ⟨.lit (.int 0), IsVal.lit⟩))
        (fun v => tglWp E
          (Exp.cond (Exp.ofVal v) (.lit (.int 0))
            (.binop .plus (.app (Exp.fix (Exp.lam innerBody)) (.lit .unit))
              (.lit (.int 1))))
          geoPost))
      ⊢@{IProp GF}
      iprop(tglWp E
        (Exp.cond
          (Exp.binop .eq (Exp.ofVal ⟨.lit (.int 0), IsVal.lit⟩)
            (Exp.ofVal ⟨.lit (.int 0), IsVal.lit⟩))
          (.lit (.int 0))
          (.binop .plus (.app (Exp.fix (Exp.lam innerBody)) (.lit .unit))
            (.lit (.int 1))))
        geoPost) :=
      ErisWpGS.tglWp_bind (K :=
        [EctxItem.condC (.lit (.int 0))
          (.binop .plus (.app (Exp.fix (Exp.lam innerBody)) (.lit .unit))
            (.lit (.int 1)))])
    iapply hBindCond0
    -- Step B: reduce `binop eq 0 0 → lit true` (pure step). `ofVal` is reducible;
    -- normalise so the goal exposes the literal form before invoking `PureExec_discrete`.
    simp only [Exp.ofVal]
    iapply (ErisWpGS.twp_pure_step_fupd (n := 1)
      (e₁ := (Exp.binop .eq (Exp.lit (.int 0)) (Exp.lit (.int 0)) : Exp rT))
      (e₂ := (Exp.lit (.bool true) : Exp rT))
      _
      (show (Exp.lit (.int 0) : Exp rT).isValue ∧
            (Exp.lit (.int 0) : Exp rT).isValue ∧
            BinOp.eval .eq (.lit (.int 0) : Exp rT) (.lit (.int 0))
              = some (Exp.lit (.bool true) : Exp rT)
        from ⟨⟨IsVal.lit⟩, ⟨IsVal.lit⟩, rfl⟩))
    -- Step C: value collapse — `tglWp E (lit true) (fun v => P v) ⊢ P (lit true)`.
    iapply (ErisWpGS.tglWp_value_of_toVal
      (v := ⟨.lit (.bool true), IsVal.lit⟩) rfl)
    -- Step D: `cond (lit true) et ef → et` via `pureExec_cond_true_discrete`.
    -- After C, the goal still has `cond (ofVal ⟨lit true, lit⟩) …`. The
    -- `PureExec_discrete`/`iapply` unifier won't reduce `ofVal` even though defeq —
    -- so `simp only [Exp.ofVal]` makes the literal form syntactic.
    simp only
    -- Step D: `cond (lit true) et ef → et` via `pureExec_cond_true_discrete`.
    twp_pure_at
      (Exp.cond (.lit (.bool true)) (.lit (.int 0))
        (.binop .plus (.app (Exp.fix (Exp.lam innerBody)) (.lit .unit))
          (.lit (.int 1))))
      ↦ (.lit (.int 0))
    -- Step E: conclude `tglWp E (lit 0) geoPost` via the value rule.
    iapply (ErisWpGS.tglWp_value_of_toVal (v := ⟨.lit (.int 0), IsVal.lit⟩) rfl)
    iexists 0
    ipure_intro
    exact ⟨rfl, _root_.le_refl _⟩
  · -- n = 1 branch: symmetric to n=0 up to step D, then recurses via `IH`.
    -- Step A: bind on the cond context.
    have hBindCond1 : iprop(tglWp E
        (Exp.binop .eq (Exp.ofVal ⟨.lit (.int 1), IsVal.lit⟩)
          (Exp.ofVal ⟨.lit (.int 0), IsVal.lit⟩))
        (fun v => tglWp E
          (Exp.cond (Exp.ofVal v) (.lit (.int 0))
            (.binop .plus (.app (Exp.fix (Exp.lam innerBody)) (.lit .unit))
              (.lit (.int 1))))
          geoPost))
      ⊢@{IProp GF}
      iprop(tglWp E
        (Exp.cond
          (Exp.binop .eq (Exp.ofVal ⟨.lit (.int 1), IsVal.lit⟩)
            (Exp.ofVal ⟨.lit (.int 0), IsVal.lit⟩))
          (.lit (.int 0))
          (.binop .plus (.app (Exp.fix (Exp.lam innerBody)) (.lit .unit))
            (.lit (.int 1))))
        geoPost) :=
      ErisWpGS.tglWp_bind (K :=
        [EctxItem.condC (.lit (.int 0))
          (.binop .plus (.app (Exp.fix (Exp.lam innerBody)) (.lit .unit))
            (.lit (.int 1)))])
    iapply hBindCond1
    -- Step B: reduce `binop eq 1 0 → lit false`.
    simp only [Exp.ofVal]
    iapply (ErisWpGS.twp_pure_step_fupd (n := 1)
      (e₁ := (Exp.binop .eq (Exp.lit (.int 1)) (Exp.lit (.int 0)) : Exp rT))
      (e₂ := (Exp.lit (.bool false) : Exp rT))
      _
      (show (Exp.lit (.int 1) : Exp rT).isValue ∧
            (Exp.lit (.int 0) : Exp rT).isValue ∧
            BinOp.eval .eq (.lit (.int 1) : Exp rT) (.lit (.int 0))
              = some (Exp.lit (.bool false) : Exp rT)
        from ⟨⟨IsVal.lit⟩, ⟨IsVal.lit⟩, rfl⟩))
    -- Step C: value collapse.
    iapply (ErisWpGS.tglWp_value_of_toVal
      (v := ⟨.lit (.bool false), IsVal.lit⟩) rfl)
    simp only
    -- Step D: `cond (lit false) et ef → ef` via `pureExec_cond_false_discrete`.
    twp_pure_at
      (Exp.cond (.lit (.bool false)) (.lit (.int 0))
        (.binop .plus (.app (Exp.fix (Exp.lam innerBody)) (.lit .unit))
          (.lit (.int 1))))
      ↦ (.binop .plus (.app (Exp.fix (Exp.lam innerBody)) (.lit .unit))
          (.lit (.int 1)))
    -- Step E: bind on `[binopL .plus ⟨lit 1, lit⟩]` to focus the recursive call.
    have hBindPlus : iprop(tglWp E
        (Exp.app (Exp.fix (Exp.lam innerBody)) (.lit .unit))
        (fun v => tglWp E
          (.binop .plus (Exp.ofVal v) (.lit (.int 1)))
          geoPost))
      ⊢@{IProp GF}
      iprop(tglWp E
        (.binop .plus (.app (Exp.fix (Exp.lam innerBody)) (.lit .unit))
          (.lit (.int 1)))
        geoPost) :=
      ErisWpGS.tglWp_bind (K := [EctxItem.binopL .plus ⟨.lit (.int 1), IsVal.lit⟩])
    iapply hBindPlus
    -- Step F: invoke IH via `tglWp_wand` — IH's post is `geoPost`, but our
    -- bound continuation expects `fun v => tglWp E (plus v 1) geoPost`. Use
    -- `tglWp_wand` to weaken.
    iapply (ErisWpGS.tglWp_wand (Φ := geoPost))
    isplitl [Hcr IH]
    · iapply IH
      -- Bridge `↯ F (Int.toNat 1)` to `↯ ↑(3/2)*ε` (defeq) via `ec_eq`.
      iapply (ec_eq (show F (Int.toNat 1) = ((3/2 : NNReal) : ENNReal) * ε from rfl))
      iexact Hcr
    -- Step G: pointwise continuation — given `geoPost w`, produce
    -- `tglWp E (binop plus (ofVal w) 1) geoPost`.
    iintro %w Hgeo
    -- Step H: destructure `Hgeo : ∃ m, ⌜w = ⟨lit m, lit⟩ ∧ 0 ≤ m⌝`.
    ihave ⟨%m, %Hmp⟩ := Hgeo
    obtain ⟨Hweq, Hmnn⟩ := Hmp
    subst Hweq
    simp only [Exp.ofVal]
    -- Step I: reduce `binop plus (lit m) (lit 1) → lit (m + 1)`.
    iapply (ErisWpGS.twp_pure_step_fupd (n := 1)
      (e₁ := (Exp.binop .plus (Exp.lit (.int m)) (Exp.lit (.int 1)) : Exp rT))
      (e₂ := (Exp.lit (.int (m + 1)) : Exp rT))
      _
      (show (Exp.lit (.int m) : Exp rT).isValue ∧
            (Exp.lit (.int 1) : Exp rT).isValue ∧
            BinOp.eval .plus (.lit (.int m) : Exp rT) (.lit (.int 1))
              = some (Exp.lit (.int (m+1)) : Exp rT)
        from ⟨⟨IsVal.lit⟩, ⟨IsVal.lit⟩, rfl⟩))
    -- Step J: value-collapse + close `geoPost` with `m + 1 ≥ 0`.
    iapply (ErisWpGS.tglWp_value_of_toVal
      (v := ⟨.lit (.int (m + 1)), IsVal.lit⟩) rfl)
    iexists (m + 1)
    ipure_intro
    exact ⟨rfl, by omega⟩

/-! ## Spec: `geo_nonneg`

  Unconditional: the geometric sampler terminates returning a non-negative
  integer with probability 1. Mirrors `geometric_total.v:220`. Obtained
  from `geo_nonneg_pos_err` by `twp_err_pos`. -/
theorem geo_nonneg (E : CoPset) :
    ⊢@{IProp GF} tglWp E (Exp.app (geometric (rT := rT)) (Exp.lit .unit))
      (geoPost (rT := rT) (GF := GF)) := by
  have Hnv : (Exp.app (geometric (rT := rT)) (Exp.lit .unit)).toVal? = none :=
    Exp.toVal?_eq_none.mpr fun ⟨w⟩ => nomatch w
  iapply (twp_err_pos Hnv)
  iintro %ε %Hε Herr
  iapply (geo_nonneg_pos_err E ε Hε)
  iexact Herr

/-! ## Probabilistic statement via `twp_tgl`

  Pure-Prop version of `geoPost`, suitable for feeding into `twp_tgl`. -/

/-- Pure predicate version of `geoPost`. -/
def geoPredicate (v : Val rT) : Prop :=
  ∃ m : Int, v = ⟨.lit (.int m), IsVal.lit⟩ ∧ 0 ≤ m

/-- The geometric sampler almost-surely terminates at a non-negative
integer (Tgl-form). -/
theorem geo_tgl [AppPreGS rT GF] [ECPreGS GF] [InvGpreS GF] (σ : State rT) :
    Tgl (limExec ⟨Exp.app geometric (Exp.lit .unit), σ⟩) geoPredicate 0 := by
  refine twp_tgl (GF := GF) (e := Exp.app geometric (Exp.lit .unit)) (σ := σ)
    (φ := geoPredicate) ?_
  intro _
  have hwp : ⊢@{IProp GF} tglWp ⊤ (Exp.app (geometric (rT := rT)) (Exp.lit .unit))
      (fun v : Val rT => iprop(⌜geoPredicate v⌝)) := by
    have := geo_nonneg (rT := rT) (GF := GF) ⊤
    refine this.trans (ErisWpGS.tglWp_mono (Φ := geoPost (rT := rT) (GF := GF)) ?_)
    intro v
    iintro ⟨%m, %Hm⟩
    ipure_intro
    exact ⟨m, Hm.1, Hm.2⟩
  iintro _
  iapply hwp

/-- The geometric sampler almost-surely terminates. -/
theorem geo_mass_one [AppPreGS rT GF] [ECPreGS GF] [InvGpreS GF] (σ : State rT) :
    1 ≤ (limExec ⟨Exp.app geometric (Exp.lit .unit), σ⟩) Set.univ := by
  have h := Tgl.termination_ineq (geo_tgl (GF := GF) σ)
  rwa [tsub_zero] at h

end Examples
end TotalEris
end ProbLang
