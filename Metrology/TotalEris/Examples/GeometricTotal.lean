module

public import Metrology.TotalEris

@[expose] public section

/-!
# Geometric distribution (total correctness)

Termination-with-probability-one of the geometric sampler, proved using
Eris's *error induction*: a recursive program `geometric ()` that returns
`0` with probability `1/3` and otherwise recurses with `+1` terminates
almost surely returning a non-negative integer. -/

open Iris Iris.BI Iris.ProofMode ProbLang ProbLang.TotalEris ProbLang.TotalEris.ErisWpGS
open scoped ENNReal

namespace ProbLang
namespace TotalEris
namespace Examples

variable {rT : Type _} [ProbLangℝ rT]
variable {hlc : HasLC} {GF : BundledGFunctors.{0,0,0}} [ErisGS rT hlc GF]

/-! ## The geometric sampler

  Encoded under locally-nameless: `bvar 0` is the bound recursor argument
  (we don't actually use it), and the body samples uniformly from
  `[0, 3) = {0, 1, 2}`. -/

/-- The geometric sampler. -/
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
  unit-typed argument terminates returning a non-negative integer. -/
theorem geo_nonneg_pos_err (E : CoPset) (ε : ENNReal) (hε : 0 < ε) :
    iprop(↯ε) ⊢@{IProp GF}
      tglWp E (Exp.app (geometric (rT := rT)) (Exp.lit .unit))
        (geoPost (rT := rT) (GF := GF)) := by
  refine ErrorCredit.Induction.external_simple (k := (3/2 : NNReal)) hε (by norm_num) ?_
  iintro ⟨IH, Herr⟩
  twp_pures
  twp_bind (Exp.rand (Exp.lit (.int 2)) (Exp.lit .unit))
  let F : ℕ → ENNReal := fun n => if n = 0 then 0 else (3/2 : NNReal) * ε
  have htoNat : (2 : Int).toNat = 2 := rfl
  have hF : ∑ n ∈ Finset.range 2, F n = (3/2 : NNReal) * ε := by
    simp [F, Finset.sum_range_succ]
  have hsplit : ((2 : ℕ) : ENNReal) = (3/2 : NNReal) + (1/2 : NNReal) := by
    rw [← ENNReal.coe_add]
    norm_num
  have HSum : (∑ n ∈ Finset.range (2 : Int).toNat, F n) / ((2 : Int).toNat : ENNReal) ≤ ε := by
    rw [ENNReal.div_le_iff' (by simp) (by simp), htoNat, hF, hsplit, add_mul]
    exact le_add_right le_rfl
  iapply (twp_rand_exp' (z := 2) (ε₁ := ε) (ε₂ := F) (Hz := by decide) (HSum := HSum)) $$ Herr
  iintro %n ⟨%⟨Hn₁, Hn₂⟩, Hcr⟩
  simp only [Exp.ofVal]
  interval_cases n
  · twp_pures
    twp_value
    iexists 0
    itrivial
  · twp_pure
    twp_pure
    twp_bind (Exp.app geometric (.lit .unit))
    iapply (ErisWpGS.tglWp_wand (Φ := geoPost))
    isplitl [Hcr IH]
    · iapply IH
      iapply (ErrorCredit.ext (show F (Int.toNat 1) = ((3/2 : NNReal) : ENNReal) * ε from rfl))
      iexact Hcr
    iintro %w ⟨%m, %⟨rfl, Hmnn⟩⟩
    twp_pures
    twp_value
    iexists (m + 1)
    ipureintro
    exact ⟨rfl, by omega⟩

/-! ## Spec: `geo_nonneg`

  Unconditional: the geometric sampler terminates returning a non-negative
  integer with probability 1. Obtained from `geo_nonneg_pos_err` by
  `twp_err_pos`. -/
theorem geo_nonneg (E : CoPset) :
    ⊢@{IProp GF} tglWp E (Exp.app (geometric (rT := rT)) (Exp.lit .unit))
      (geoPost (rT := rT) (GF := GF)) := by
  iapply twp_err_pos solve_not_value
  iintro %ε %Hε Herr
  iapply (geo_nonneg_pos_err E ε Hε) $$ Herr

/-! ## Probabilistic statement via `twp_tgl`

  Pure-Prop version of `geoPost`, suitable for feeding into `twp_tgl`. -/

/-- Pure predicate version of `geoPost`. -/
def geoPredicate (v : Val rT) : Prop :=
  ∃ m : Int, v = .int m ∧ 0 ≤ m

/-- `{v | geoPredicate v}` is measurable: it is the countable set of integer
literals `⟨.lit (.int m), _⟩` over `m : ℤ`. -/
theorem measurableSet_geoPredicate :
    MeasurableSet {v : Val rT | geoPredicate v} := by
  refine Set.Countable.measurableSet
    (Set.Countable.mono ?_ (Set.countable_range fun m : Int => (.int m : Val rT)))
  rintro v ⟨m, rfl, _⟩
  exact ⟨m, rfl⟩

/-- The geometric sampler almost-surely terminates at a non-negative
integer (Tgl-form). -/
theorem geo_tgl [AppPreGS rT GF] [ECPreGS GF] [InvGpreS GF] (σ : State rT) :
    Tgl (limExec ⟨Exp.app geometric (Exp.lit .unit), σ⟩) geoPredicate 0 := by
  refine twp_tgl (GF := GF) (e := Exp.app geometric (Exp.lit .unit)) (σ := σ)
    (φ := geoPredicate) measurableSet_geoPredicate ?_
  intro _
  have hwp : ⊢@{IProp GF} tglWp ⊤ (Exp.app (geometric (rT := rT)) (Exp.lit .unit))
      (fun v : Val rT => iprop(⌜geoPredicate v⌝)) :=
    (geo_nonneg ⊤).trans
      (ErisWpGS.tglWp_mono fun v => by iintro ⟨%m, %Hm⟩; ipureintro; exact ⟨m, Hm⟩)
  iintro _
  iapply hwp

/-- The geometric sampler almost-surely terminates. -/
theorem geo_mass_one [AppPreGS rT GF] [ECPreGS GF] [InvGpreS GF] (σ : State rT) :
    1 ≤ (limExec ⟨Exp.app geometric (Exp.lit .unit), σ⟩) Set.univ := by
  simpa using Tgl.termination_ineq (geo_tgl (GF := GF) σ)

end Examples
end TotalEris
end ProbLang
