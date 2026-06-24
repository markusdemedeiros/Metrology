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


variable {rT : Type _} [ProbLangℝ rT]
variable {hlc : HasLC} {GF : BundledGFunctors.{0,0,0}} [ErisGS rT hlc GF]

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
@[pl_names]
def geometric : Exp rT :=
  pl% rec geo n :=
        if rand(#2, #.unit) = #0
          then #0
          else (geo n) + #1

/-- The result-postcondition shared by all geometric specs: the sampler
returns a non-negative integer. -/
abbrev geoPost : Val rT → IProp GF :=
  fun w => iprop(∃ m : Int, ⌜w = .int m ∧ 0 ≤ m⌝)

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
  refine ErrorCredit.Induction.external_simple (k := (3/2 : NNReal)) hε (by norm_num) ?_
  iintro ⟨IH, Herr⟩
  -- β/fix-reduce `geometric ()` to its body. `twp_pures` discovers each redex and
  -- its surrounding evaluation context, and the shared `is_value` discharger closes
  -- the `app_fix`/`app_lam` value side conditions automatically — no hand-written
  -- `IsVal` witnesses, no explicit `Exp.close`/`open'` bookkeeping.
  twp_pures
  -- Focus on `rand 2 ()` via `twp_bind`, which discovers the evaluation context
  -- `K = [binopL .eq 0, condC …]` automatically (replacing the explicit `tglWp_bind`).
  twp_bind (Exp.rand (Exp.lit (.int 2)) (Exp.lit .unit))
  -- Goal: `tglWp E (rand 2 ()) (fun v => tglWp E (cond (v = 0) 0 (geo()+1)) _)`.
  -- Apply `twp_rand_exp` with `F(n) = if n=0 then 0 else (3/2)*ε`. The
  -- `$$ [Herr]` clause threads the iris hypothesis `Herr : ↯ε` into the
  -- lemma's `↯ε₁` precondition.
  let F : ℕ → ENNReal := fun n => if n = 0 then 0 else (3/2 : NNReal) * ε
  iapply (twp_rand_exp (z := 2) (ε₁ := ε) (ε₂ := F) (Hz := by decide)
    (HSum := by
      -- New signature: `(∑ n ∈ range 2, F n) / 2 ≤ ε`. Convert to the multiplicative
      -- form `∑ ≤ 2 * ε` via `div_le_iff'`, then the original bound applies.
      rw [ENNReal.div_le_iff' (by simp) (by simp)]
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
  · -- n = 0 branch. `twp_pures` takes the `binop eq 0 0 → true` and `cond true → 0`
    -- steps — their value/evaluator side conditions discharged by `is_value` — and
    -- `twp_value` closes the resulting value WP `tglWp E 0 geoPost`.
    twp_pures
    twp_value
    iexists 0
    ipureintro
    exact ⟨rfl, _root_.le_refl _⟩
  · -- n = 1 branch: `binop eq 1 0 → false` then `cond false → geo () + 1`. Step
    -- exactly those two (NOT the recursive call, which `twp_pures` would unfold),
    -- then bind the recursive call and recurse via `IH`.
    twp_pure
    twp_pure
    -- Focus the recursive call (context `[binopL .plus 1]` discovered automatically).
    twp_bind (Exp.app geometric (.lit .unit))
    -- Invoke IH via `tglWp_wand` — IH's post is `geoPost`, but our bound continuation
    -- expects `fun v => tglWp E (plus v 1) geoPost`. Use `tglWp_wand` to weaken.
    iapply (ErisWpGS.tglWp_wand (Φ := geoPost))
    isplitl [Hcr IH]
    · iapply IH
      -- Bridge `↯ F (Int.toNat 1)` to `↯ ↑(3/2)*ε` (defeq) via `ec_eq`.
      iapply (ErrorCredit.ext (show F (Int.toNat 1) = ((3/2 : NNReal) : ENNReal) * ε from rfl))
      iexact Hcr
    -- Pointwise continuation — given `geoPost w`, produce `tglWp E (plus w 1) geoPost`.
    iintro %w Hgeo
    ihave ⟨%m, %Hmp⟩ := Hgeo
    obtain ⟨Hweq, Hmnn⟩ := Hmp
    subst Hweq
    -- `binop plus (lit m) (lit 1) → lit (m + 1)`, then conclude with `m + 1 ≥ 0`.
    twp_pures
    twp_value
    iexists (m + 1)
    ipureintro
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
  ∃ m : Int, v = .int m ∧ 0 ≤ m

/-- `{v | geoPredicate v}` is measurable: it is the countable set of integer
literals `⟨.lit (.int m), _⟩` over `m : ℤ`. -/
theorem geoPredicate_measurableSet :
    MeasurableSet {v : Val rT | geoPredicate v} := by
  have hc : {v : Val rT | geoPredicate v}.Countable := by
    apply Set.Countable.mono
      (s₂ := (fun m : Int => (.int m : Val rT)) '' Set.univ)
    · rintro v ⟨m, rfl, _⟩; exact ⟨m, trivial, rfl⟩
    · exact (Set.countable_univ).image _
  exact hc.measurableSet

/-- The geometric sampler almost-surely terminates at a non-negative
integer (Tgl-form). -/
theorem geo_tgl [AppPreGS rT GF] [ECPreGS GF] [InvGpreS GF] (σ : State rT) :
    Tgl (limExec ⟨Exp.app geometric (Exp.lit .unit), σ⟩) geoPredicate 0 := by
  refine twp_tgl (GF := GF) (e := Exp.app geometric (Exp.lit .unit)) (σ := σ)
    (φ := geoPredicate) geoPredicate_measurableSet ?_
  intro _
  have hwp : ⊢@{IProp GF} tglWp ⊤ (Exp.app (geometric (rT := rT)) (Exp.lit .unit))
      (fun v : Val rT => iprop(⌜geoPredicate v⌝)) := by
    have := geo_nonneg (rT := rT) (GF := GF) ⊤
    refine this.trans (ErisWpGS.tglWp_mono (Φ := geoPost (rT := rT) (GF := GF)) ?_)
    intro v
    iintro ⟨%m, %Hm⟩
    ipureintro
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
