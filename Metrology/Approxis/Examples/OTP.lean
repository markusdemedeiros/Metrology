module

public import Metrology.Approxis.Compatibility
import Metrology.ProbLang.Syntax.Notation
public import Metrology.Approxis.AppRelRules
public import Metrology.Approxis.AdequacyRel

@[expose] public section


/-! # One-Time Pad refinement example, using modular addition as the combiner. -/

namespace ProbLang
open Iris Iris.BI Iris.ProofMode OFE COFE ProbLang ProbLang.ApproxisWpGS

namespace OTP

variable {rT : Type} [ProbLangℝ rT] [MeasurableSingletonClass rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [IR : ApproxisRGS rT hlc GF]

/-! ### The bijection -/

/-- Modular addition: `(n + m) mod N`. -/
def addMod (m N : Int) (n : Int) : Int := (n + m) % N

/-- Euclidean remainder lands in `[0, N)`. -/
private theorem emod_bounds (a : Int) {N : Int} (HN : 0 < N) : 0 ≤ a % N ∧ a % N < N :=
  ⟨Int.emod_nonneg _ (Int.ne_of_gt HN), Int.emod_lt_of_pos _ HN⟩

theorem addMod_dom (m N : Int) (HN : 0 < N) :
    ∀ n : Int, 0 ≤ n → n < N → 0 ≤ addMod m N n ∧ addMod m N n < N :=
  fun _ _ _ => emod_bounds _ HN

/-- Bijection witness: for every `m' ∈ [0, N)`, there's a unique `n ∈ [0, N)`
with `(n + m) mod N = m'`. The unique `n` is `(m' - m) mod N`. -/
theorem addMod_bij (m N : Int) (HN : 0 < N) :
    ∀ m' : Int, 0 ≤ m' → m' < N →
      ∃! n : Int, (0 ≤ n ∧ n < N) ∧ addMod m N n = m' := by
  intro m' hm'0 hm'N
  refine ⟨(m' - m) % N, ⟨emod_bounds _ HN, ?_⟩, ?_⟩
  · unfold addMod
    rw [Int.emod_add_emod, Int.sub_add_cancel, Int.emod_eq_of_lt hm'0 hm'N]
  · rintro n ⟨⟨hn0, hnN⟩, hadd⟩
    unfold addMod at hadd
    -- `(m' - m) % N = ((n+m)%N - m) % N = (n+m-m) % N = n % N = n`.
    rw [← hadd, Int.emod_sub_emod, Int.add_sub_cancel, Int.emod_eq_of_lt hn0 hnN]

/-! ### The OTP refinement -/

/-- The LHS program: sample a key, then output `(m + k) mod N`. -/
def otp_enc (m N : Int) : Exp rT :=
  pl% let k := rand(#(.int N), #(.unit)); (#(.int m) + k) % #(.int N)

/-- The RHS program: just sample uniformly. -/
def otp_ideal (N : Int) : Exp rT :=
  pl% rand(#(.int N), #(.unit))

/-- The β-redex body of `otp_enc m N`: `(m + bvar 0) % N`. Open at `bvar 0`,
which gets bound by `otp_enc`'s outer `let k := …; …` (a `lam`-encoded let). -/
abbrev otpLam (m N : Int) : Exp rT := pl% fun k, (#(.int m) + k) % #(.int N)

/-- The evaluation context that `otp_enc m N` reduces to after the `let` is
β-encoded as `(λ k. body) (rand …)`: applying `(λ. otpBody)` to its argument. -/
def otpKLam (m N : Int) : Ectx rT := [EctxItem.appR (otpLam m N)]

/-- Every integer literal refines itself at `lrel_int`. -/
private theorem refines_lit_int (n : Int) :
    ⊢@{IProp GF} refines (⊤ : CoPset) (pl(#(.int n)) : Exp rT) pl(#(.int n)) lrel_int := by
  iapply refines_ret (v1 := .int n) (v2 := .int n) (hv1 := rfl) (hv2 := rfl)
  iintro !>
  iapply lrel_int_lit

/-- **OTP refinement**: for any fixed `m ∈ [0, N)`, encrypting `m` with a fresh
random key is observationally equivalent to a fresh random sample. -/
theorem otp_refines (m N : Int) (HN : 0 < N) :
  ⊢@{IProp GF} refines (⊤ : CoPset) (otp_enc (rT := rT) m N) (otp_ideal N) lrel_int := by
  simp only [otp_enc, otp_ideal, Exp.close, Exp.closeRec, ↓reduceIte]
  show ⊢@{IProp GF} refines ⊤
    ((otpKLam m N).fill pl(rand(#(.int N), #(.unit))))
    (Ectx.fill ([] : Ectx rT) pl(rand(#(.int N), #(.unit)))) lrel_int
  iapply refines_couple_rands_lr (f := addMod m N)
    (hdom := addMod_dom m N HN) (hbij := addMod_bij m N HN) (Hz := HN)
  iintro %n ⟨%_, %_⟩
  -- Three pure steps on the left: β-reduce the `let`, add, then take the remainder.
  show ⊢@{IProp GF} refines ⊤ (Ectx.fill ([] : Ectx rT) pl({otpLam m N} #(.int n))) _ lrel_int
  iapply refines_pure_l (Hex := pureExec_app_lam) ⟨IsVal.lit.toIsValue, by is_lc⟩
  inext
  let Kmod : Ectx rT := [EctxItem.binopL .mod (.int N)]
  show ⊢@{IProp GF} refines ⊤ (Kmod.fill pl(#(.int m) + #(.int n))) _ lrel_int
  iapply refines_pure_l ⟨IsVal.lit.toIsValue, IsVal.lit.toIsValue, rfl⟩
  inext
  show ⊢@{IProp GF} refines ⊤
    (Ectx.fill ([] : Ectx rT) pl(#(.int (m + n)) % #(.int N))) _ lrel_int
  iapply refines_pure_l ⟨IsVal.lit.toIsValue, IsVal.lit.toIsValue, rfl⟩
  inext
  rw [show (m + n) % N = addMod m N n by unfold addMod; ring_nf]
  exact refines_lit_int _

/-! ### Reverse direction -/

/-- For `0 ≤ n < N`: `(m + (n - m) mod N) mod N = n`. -/
theorem addMod_neg_inv (m N : Int) :
    ∀ n : Int, 0 ≤ n → n < N → (m + (n + (-m)) % N) % N = n := by
  intro n hn0 hnN
  rw [Int.add_emod_emod, show m + (n + -m) = n by ring, Int.emod_eq_of_lt hn0 hnN]

/-- **Reverse OTP refinement**: a fresh random sample refines encrypting `m`
with a fresh random key. -/
theorem otp_refines_rev (m N : Int) (HN : 0 < N) :
    ⊢@{IProp GF} refines (⊤ : CoPset) (otp_ideal (rT := rT) N) (otp_enc m N) lrel_int := by
  simp only [otp_enc, otp_ideal, Exp.close, Exp.closeRec, ↓reduceIte]
  show ⊢@{IProp GF} refines ⊤
    (Ectx.fill ([] : Ectx rT) pl(rand(#(.int N), #(.unit))))
    ((otpKLam m N).fill pl(rand(#(.int N), #(.unit)))) lrel_int
  iapply refines_couple_rands_lr (f := addMod (-m) N)
    (hdom := addMod_dom (-m) N HN) (hbij := addMod_bij (-m) N HN) (Hz := HN)
  iintro %n ⟨%Hn0, %HnN⟩
  -- The same three pure steps, now on the right.
  show ⊢@{IProp GF} refines ⊤ _
    (Ectx.fill ([] : Ectx rT) pl({otpLam m N} #(.int (addMod (-m) N n)))) lrel_int
  iapply refines_pure_r (Hex := pureExec_app_lam) ⟨IsVal.lit.toIsValue, by is_lc⟩
  let Kmod : Ectx rT := [EctxItem.binopL .mod (.int N)]
  show ⊢@{IProp GF} refines ⊤ _ (Kmod.fill pl(#(.int m) + #(.int (addMod (-m) N n)))) lrel_int
  iapply refines_pure_r ⟨IsVal.lit.toIsValue, IsVal.lit.toIsValue, rfl⟩
  show ⊢@{IProp GF} refines ⊤ _
    (Ectx.fill ([] : Ectx rT) pl(#(.int (m + addMod (-m) N n)) % #(.int N))) lrel_int
  iapply refines_pure_r ⟨IsVal.lit.toIsValue, IsVal.lit.toIsValue, rfl⟩
  -- The RHS-reduced value is `(m + (n + (-m)) % N) % N = n` by `addMod_neg_inv`.
  rw [show (m + addMod (-m) N n) % N = n from addMod_neg_inv m N n Hn0 HnN]
  exact refines_lit_int n

/-! ## Adequacy: exit the logic

Apply `refines_coupling` to obtain a semantic property of OTP outside the
Iris logic: the limit-step distributions of `otp_enc m N` and `otp_ideal N`
are coupled by integer equality, with zero error. -/

/-- The φ-relation we extract from `lrel_int`: the two values are the same
integer literal. -/
def otpφ (v v' : Val rT) : Prop :=
  ∃ n : Int, v = .int n ∧ v' = .int n

theorem lrel_int_to_otpφ {GF : BundledGFunctors} [ApproxisRGS rT hlc GF] (v v' : Val rT) :
    ⊢@{IProp GF} (lrel_int (GF := GF)).car v v' -∗ ⌜otpφ v v'⌝ := by
  iintro Hint
  icases lrel_int_unfold v v' $$ Hint with ⟨%n, %hv, %hv'⟩
  ipureintro; exact ⟨n, hv, hv'⟩

/-- **Semantic OTP guarantee (forward)**: the encrypted-message distribution
and the uniform-sample distribution are coupled by value-equality with zero
error. This is `otp_refines` exited from the Iris logic via `refines_coupling`. -/
theorem otp_adequate
    (GF : BundledGFunctors.{0, 0, 0})
    [RefinesPreGS rT GF]
    (m N : Int) (HN : 0 < N)
    (σ σ' : State rT) :
    AddCoupl 0 (adequacyRel otpφ)
      (limExecV ⟨otp_enc m N, σ⟩) (limExecV ⟨otp_ideal N, σ'⟩) :=
  ProbLang.refines_coupling (A := fun _ => lrel_int) (φ := otpφ)
    (otp_enc m N) (otp_ideal N) σ σ'
    (fun _ v v' => lrel_int_to_otpφ v v')
    (fun IR => otp_refines (hlc := .hasNoLC) (GF := GF) (IR := IR) m N HN)

/-- **Semantic OTP guarantee (reverse)**: the uniform-sample distribution and
the encrypted-message distribution are coupled by value-equality with zero
error. This is `otp_refines_rev` exited from the Iris logic. -/
theorem otp_adequate_rev
    (GF : BundledGFunctors.{0, 0, 0})
    [RefinesPreGS rT GF]
    (m N : Int) (HN : 0 < N)
    (σ σ' : State rT) :
    AddCoupl 0 (adequacyRel otpφ)
      (limExecV ⟨otp_ideal N, σ⟩) (limExecV ⟨otp_enc m N, σ'⟩) :=
  ProbLang.refines_coupling (A := fun _ => lrel_int) (φ := otpφ)
    (otp_ideal N) (otp_enc m N) σ σ'
    (fun _ v v' => lrel_int_to_otpφ v v')
    (fun IR => otp_refines_rev (hlc := .hasNoLC) (GF := GF) (IR := IR) m N HN)

/-! ## Final closed statement: instantiated at the concrete model

`(ApproxisFunctor rT) : BundledGFunctors` from `AdequacyRel.lean` provides all the
required PreGS instances, so we can close off `otp_adequate{,_rev}` with no
remaining type-class hypotheses or `GF` parameter. -/

/-- **Final OTP guarantee (closed)**: at the concrete model `(ApproxisFunctor rT)`,
the encrypted-message and uniform distributions are coupled with zero error. -/
theorem otp_adequate_closed
    (m N : Int) (HN : 0 < N)
    (σ σ' : State rT) :
    AddCoupl 0 (adequacyRel otpφ)
      (limExecV ⟨otp_enc m N, σ⟩) (limExecV ⟨otp_ideal N, σ'⟩) :=
  otp_adequate (ApproxisFunctor rT) m N HN σ σ'

theorem otp_adequate_rev_closed
    (m N : Int) (HN : 0 < N)
    (σ σ' : State rT) :
    AddCoupl 0 (adequacyRel otpφ)
      (limExecV ⟨otp_ideal N, σ⟩) (limExecV ⟨otp_enc m N, σ'⟩) :=
  otp_adequate_rev (ApproxisFunctor rT) m N HN σ σ'

end OTP

end ProbLang
