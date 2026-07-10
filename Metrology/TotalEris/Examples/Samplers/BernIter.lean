-- Bounded Bernoulli iteration
module

public import Metrology.ProbLang.Reals
public import Metrology.TotalEris

@[expose] public section

open Std Iris Iris.Std Iris.BI Iris.ProofMode OFE COFE ProbLang ProbLang.TotalEris
  ProbLang.TotalEris.ErisWpGS
open scoped AppGS ENNReal NNReal

namespace ProbLang
namespace TotalEris
namespace Examples

noncomputable section

variable {hlc : HasLC} {GF : BundledGFunctors.{0,0,0}} [ErisGS ℝ hlc GF]

section program

structure AbstractBernoulliI (v : Val ℝ) (γ : ↑unitInterval) (I : IProp GF) where
  spec {E} : iprop%
    ⊢@{IProp GF} ∀ (F : Bool → ℝ≥0∞),
      ↯ (.ofReal γ * F true + (1 - .ofReal γ) * F false) ∗ I -∗
      tglWp E pl(&v.1 #.unit)
        (fun w : Val ℝ => iprop% ∃ b : Bool, ⌜w.1 = .lit (.bool b)⌝ ∗ ↯ (F b) ∗ I)

@[pl_fold]
def IterTrial : Exp ℝ := pl%
  rec iter b k :=
    if k = #0 then #true
    else if b #.unit then iter b (k - #1) else #false

end program

section distribution

def IterPMF (γ : ↑unitInterval) (N : ℕ) : Bool → ℝ≥0∞
  | true => .ofReal ((γ : ℝ) ^ N)
  | false => 1 - .ofReal ((γ : ℝ) ^ N)

end distribution

section creditExpectation

def IterCreditV (F : Bool → ℝ≥0∞) (γ : ↑unitInterval) (N : ℕ) : ℝ≥0∞ :=
  .ofReal ((γ : ℝ) ^ N) * F true + (1 - .ofReal ((γ : ℝ) ^ N)) * F false

end creditExpectation

section creditKernel

def IterCont (F : Bool → ℝ≥0∞) (γ : ↑unitInterval) (N : ℕ) : Bool → ℝ≥0∞
  | true => IterCreditV F γ N
  | false => F false

end creditKernel

section measurability

lemma one_sub_ofReal {x : ℝ} (hx : 0 ≤ x) :
    (1 : ℝ≥0∞) - ENNReal.ofReal x = ENNReal.ofReal (1 - x) := by
  rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_sub _ hx]

end measurability

section creditExpectation

theorem IterCreditV_succ (F : Bool → ℝ≥0∞) (γ : ↑unitInterval) (N : ℕ) :
    IterCreditV F γ (N + 1) =
      .ofReal γ * IterCont F γ N true + (1 - .ofReal γ) * IterCont F γ N false := by
  have hγ0 : (0:ℝ) ≤ (γ:ℝ) := γ.2.1
  have hγ1 : (γ:ℝ) ≤ 1 := γ.2.2
  have hγN1 : (γ:ℝ) ^ N ≤ 1 := pow_le_one₀ hγ0 hγ1

  have hT : ENNReal.ofReal ((γ:ℝ) ^ (N + 1)) =
      ENNReal.ofReal (γ:ℝ) * ENNReal.ofReal ((γ:ℝ) ^ N) := by
    rw [ENNReal.ofReal_pow hγ0, ENNReal.ofReal_pow hγ0, pow_succ]; ring

  have hF : ENNReal.ofReal (γ:ℝ) * ENNReal.ofReal (1 - (γ:ℝ) ^ N) + ENNReal.ofReal (1 - (γ:ℝ))
      = ENNReal.ofReal (1 - (γ:ℝ) ^ (N + 1)) := by
    rw [← ENNReal.ofReal_mul hγ0,
        ← ENNReal.ofReal_add (mul_nonneg hγ0 (by linarith)) (by linarith)]
    congr 1; ring

  simp only [IterCreditV, IterCont]
  rw [one_sub_ofReal (x := (γ:ℝ) ^ (N + 1)) (by positivity)]
  rw [one_sub_ofReal (x := (γ:ℝ) ^ N) (by positivity)]
  rw [one_sub_ofReal (x := (γ:ℝ)) hγ0]
  rw [hT, ← hF]
  ring

end creditExpectation

section specification

theorem twp_IterTrial (E : CoPset) (v : Val ℝ) (γ : ↑unitInterval) (I : IProp GF)
    (Hspec : AbstractBernoulliI (hlc := hlc) (GF := GF) v γ I)
    (F : Bool → ℝ≥0∞) (N : ℕ) :
    ⊢@{IProp GF} ↯ (IterCreditV F γ N) ∗ I -∗
      tglWp E pl(&IterTrial &v.1 #(.int (N : ℤ)))
        (fun w : Val ℝ => iprop(∃ b : Bool, ⌜w.1 = .lit (.bool b)⌝ ∗ ↯ (F b) ∗ I)) := by
  induction N generalizing F with
  | zero =>
    iintro ⟨Hcr, HI⟩

    twp_pures
    twp_value
    imodintro
    iexists true
    have h0 : IterCreditV F γ 0 = F true := by
      simp only [IterCreditV, pow_zero, ENNReal.ofReal_one, one_mul, tsub_self, zero_mul, add_zero]
    rw [← h0]
    iframe Hcr HI
    itrivial
  | succ N IH =>
    iintro ⟨Hcr, HI⟩

    twp_pures

    twp_bind pl({v.fst} #.unit)
    iapply (tglWp_wand (Φ := fun w : Val ℝ => iprop(∃ b : Bool,
      ⌜w.1 = .lit (.bool b)⌝ ∗ ↯ (IterCont F γ N b) ∗ I)))
    isplitl [Hcr HI]
    · iapply (Hspec.spec (E := E)) $$ %(IterCont F γ N)
      isplitl [Hcr]
      · rw [← IterCreditV_succ]; iexact Hcr
      · iexact HI
    iintro %w' ⟨%b, %hret, Hcrb, HIb⟩
    obtain ⟨w', hwlc'⟩ := w'
    simp only at hret
    subst hret
    cases b
    ·
      twp_pures
      twp_value
      imodintro
      iexists false
      rw [IterCont]
      iframe Hcrb HIb
      itrivial
    ·
      twp_pure
      twp_pure
      have hk : ((N + 1 : ℕ) : ℤ) - 1 = (N : ℤ) := by omega
      rw [hk]
      twp_bind pl(&IterTrial {v.fst} #(.int (N : ℤ)))
      iapply (tglWp_wand (Φ := fun w : Val ℝ => iprop(∃ b : Bool,
        ⌜w.1 = .lit (.bool b)⌝ ∗ ↯ (F b) ∗ I)))
      isplitl [Hcrb HIb]
      · iapply IH
        isplitl [Hcrb]
        · rw [IterCont]
          iexact Hcrb
        · iexact HIb
      iintro %w Hpost
      iapply tglWp_value
      iexact Hpost

end specification

end
end Examples
end TotalEris
end ProbLang
