module

public import Metrology.Approxis.Compatibility
public import Metrology.Approxis.AppRelRules
public import Metrology.Approxis.AdequacyRel

@[expose] public section

/-! # One-Time Pad refinement example, using modular addition as the combiner. -/

namespace ProbLang
open Iris Iris.BI Iris.ProofMode OFE COFE ProbLang ProbLang.ApproxisWpGS

namespace OTP

variable {hlc : Bool} {GF : BundledGFunctors} [IR : ApproxisRGS hlc GF]

/-! ### The bijection -/

/-- Modular addition: `(n + m) mod N`. -/
def addMod (m N : Int) (n : Int) : Int := (n + m) % N

theorem addMod_dom (m N : Int) (HN : 0 < N) :
    ∀ n : Int, 0 ≤ n → n < N → 0 ≤ addMod m N n ∧ addMod m N n < N :=
  fun _ _ _ => ⟨Int.emod_nonneg _ (Int.ne_of_gt HN), Int.emod_lt_of_pos _ HN⟩

/-- Bijection witness: for every `m' ∈ [0, N)`, there's a unique `n ∈ [0, N)`
with `(n + m) mod N = m'`. The unique `n` is `(m' - m) mod N`. -/
theorem addMod_bij (m N : Int) (HN : 0 < N) :
    ∀ m' : Int, 0 ≤ m' → m' < N →
      ∃! n : Int, (0 ≤ n ∧ n < N) ∧ addMod m N n = m' := by
  intro m' hm'0 hm'N
  refine ⟨(m' - m) % N, ?_, ?_⟩
  · refine ⟨⟨Int.emod_nonneg _ (Int.ne_of_gt HN),
            Int.emod_lt_of_pos _ HN⟩, ?_⟩
    unfold addMod
    rw [Int.add_emod, Int.emod_emod_of_dvd _ (dvd_refl N), ← Int.add_emod,
        Int.sub_add_cancel, Int.emod_eq_of_lt hm'0 hm'N]
  · rintro n ⟨⟨hn0, hnN⟩, hadd⟩
    unfold addMod at hadd
    -- Goal: n = (m' - m) % N. From `(n+m)%N = m'`, derive `(m' - m) % N = n` by:
    -- `(m'-m) % N = ((n+m)%N - m) % N = (n+m-m) % N = n % N = n`.
    rw [← hadd, Int.sub_emod, Int.emod_emod_of_dvd _ (dvd_refl N), ← Int.sub_emod,
        Int.add_sub_cancel, Int.emod_eq_of_lt hn0 hnN]

/-! ### The OTP refinement -/

/-- The LHS program: sample a key, then output `(m + k) mod N`. -/
def otp_enc (m N : Int) : Exp :=
  pl(let k := rand(#(.int N), #(.unit)); (#(.int m) + k) % #(.int N))

/-- The RHS program: just sample uniformly. -/
def otp_ideal (N : Int) : Exp :=
  pl(rand(#(.int N), #(.unit)))

/-- The β-redex body of `otp_enc m N`: `(m + bvar 0) % N`. Open at `bvar 0`,
which gets bound by `otp_enc`'s outer `let k := …; …` (a `lam`-encoded let). -/
def otpBody (m N : Int) : Exp :=
  Exp.binop .mod (Exp.binop .plus (Exp.lit (.int m)) (Exp.bvar 0)) (Exp.lit (.int N))

/-- The evaluation context that `otp_enc m N` reduces to after the `let` is
β-encoded as `(λ k. body) (rand …)`: applying `(λ. otpBody)` to its argument. -/
def otpKLam (m N : Int) : Ectx := [EctxItem.appR (Exp.lam (otpBody m N))]

/-- **OTP refinement**: for any fixed `m ∈ [0, N)`, encrypting `m` with a fresh
random key is observationally equivalent to a fresh random sample. -/
theorem otp_refines (m N : Int) (HN : 0 < N) :
  ⊢@{IProp GF} refines (⊤ : CoPset) (otp_enc m N) (otp_ideal N) lrel_int := by
  simp only [otp_enc, otp_ideal, Exp.close, Exp.closeRec, ↓reduceIte]
  let Kmod : Ectx := [EctxItem.binopL .mod ⟨.lit (.int N), IsVal.lit⟩]
  show ⊢@{IProp GF} iprop(refines ⊤
    ((otpKLam m N).fill pl(rand(#(.int N), #(.unit))))
    (Ectx.fill ([] : Ectx) pl(rand(#(.int N), #(.unit)))) lrel_int)
  iapply (refines_couple_rands_lr (E := ⊤) (K := otpKLam m N) (K' := ([] : Ectx))
    (A := lrel_int) (z := N) (f := addMod m N)
    (hdom := addMod_dom m N HN)
    (hbij := addMod_bij m N HN)
    (Hz := HN))
  iintro %n ⟨%_, %_⟩
  show ⊢@{IProp GF} iprop(refines ⊤
    (Ectx.fill ([] : Ectx) pl({Exp.lam (otpBody m N)} #(.int n)))
    pl(#(.int (addMod m N n))) lrel_int)
  iapply (refines_pure_l (K := []) (Hex := pureExec_app_lam) IsVal.lit.toIsValue)
  simp only [Nat.repeat]
  iintro !>
  show ⊢@{IProp GF} iprop(refines ⊤
    (Kmod.fill pl(#(.int m) + #(.int n)))
    pl(#(.int (addMod m N n))) lrel_int)
  iapply (refines_pure_l (K := Kmod) (Hex := pureExec_binop)
    ⟨IsVal.lit.toIsValue, IsVal.lit.toIsValue, rfl⟩)
  simp only [Nat.repeat]
  iintro !>
  show ⊢@{IProp GF} iprop(refines ⊤
    (Ectx.fill ([] : Ectx) pl(#(.int (m + n)) % #(.int N)))
    pl(#(.int (addMod m N n))) lrel_int)
  iapply (refines_pure_l (K := [])
    (Hex := pureExec_binop)
    ⟨IsVal.lit.toIsValue, IsVal.lit.toIsValue, rfl⟩)
  simp only [Nat.repeat]
  iintro !>
  rw [show (m + n) % N = addMod m N n by unfold addMod; ring_nf]
  show ⊢@{IProp GF}
    iprop(refines ⊤ pl(#(.int (addMod m N n))) pl(#(.int (addMod m N n))) lrel_int)
  iapply (refines_ret (v1 := ⟨.lit (.int (addMod m N n)), IsVal.lit⟩)
    (v2 := ⟨.lit (.int (addMod m N n)), IsVal.lit⟩)
    (hv1 := rfl) (hv2 := rfl))
  imodintro
  unfold lrel_int
  iexists (addMod m N n)
  ipure_intro
  exact ⟨rfl, rfl⟩

/-! ### Reverse direction -/

/-- For `0 ≤ n < N`: `(m + (n - m) mod N) mod N = n`. -/
theorem addMod_neg_inv (m N : Int) :
    ∀ n : Int, 0 ≤ n → n < N → (m + (n + (-m)) % N) % N = n := by
  intro n hn0 hnN
  rw [Int.add_emod m ((n + -m) % N) N, Int.emod_emod_of_dvd _ (dvd_refl N),
      ← Int.add_emod, show m + (n + -m) = n by ring, Int.emod_eq_of_lt hn0 hnN]

/-- **Reverse OTP refinement**: a fresh random sample refines encrypting `m`
with a fresh random key. -/
theorem otp_refines_rev (m N : Int) (HN : 0 < N) :
    ⊢@{IProp GF} refines (⊤ : CoPset) (otp_ideal N) (otp_enc m N) lrel_int := by
  simp only [otp_enc, otp_ideal, Exp.close, Exp.closeRec, ↓reduceIte]
  let Kmod : Ectx := [EctxItem.binopL .mod ⟨.lit (.int N), IsVal.lit⟩]
  show ⊢@{IProp GF} iprop(refines ⊤
    (Ectx.fill ([] : Ectx) pl(rand(#(.int N), #(.unit))))
    ((otpKLam m N).fill pl(rand(#(.int N), #(.unit)))) lrel_int)
  iapply (refines_couple_rands_lr (E := ⊤) (K := ([] : Ectx)) (K' := otpKLam m N)
    (A := lrel_int) (z := N) (f := addMod (-m) N)
    (hdom := addMod_dom (-m) N HN)
    (hbij := addMod_bij (-m) N HN)
    (Hz := HN))
  iintro %n ⟨%Hn0, %HnN⟩
  -- β-reduce LHS literal-fill, then expose β-redex on RHS.
  show ⊢@{IProp GF} iprop(refines ⊤
    pl(#(.int n))
    (Ectx.fill ([] : Ectx) pl({Exp.lam (otpBody m N)} #(.int (addMod (-m) N n))))
    lrel_int)
  iapply (refines_pure_r (K := ([] : Ectx)) (Hex := pureExec_app_lam) IsVal.lit.toIsValue)
  -- Step 2 (inner plus).
  show ⊢@{IProp GF} iprop(refines ⊤
    pl(#(.int n))
    (Kmod.fill pl(#(.int m) + #(.int (addMod (-m) N n))))
    lrel_int)
  iapply (refines_pure_r (K := Kmod) (Hex := pureExec_binop)
    ⟨IsVal.lit.toIsValue, IsVal.lit.toIsValue, rfl⟩)
  -- Step 3 (outer mod).
  show ⊢@{IProp GF} iprop(refines ⊤
    pl(#(.int n))
    (Ectx.fill ([] : Ectx) pl(#(.int (m + addMod (-m) N n)) % #(.int N)))
    lrel_int)
  iapply (refines_pure_r (K := ([] : Ectx))
    (Hex := pureExec_binop)
    ⟨IsVal.lit.toIsValue, IsVal.lit.toIsValue, rfl⟩)
  -- The RHS-reduced value is `(m + (n + (-m)) % N) % N = n` by addMod_neg_inv.
  rw [show (m + addMod (-m) N n) % N = n from addMod_neg_inv m N n Hn0 HnN]
  show ⊢@{IProp GF} iprop(refines ⊤ pl(#(.int n)) pl(#(.int n)) lrel_int)
  iapply (refines_ret (v1 := ⟨.lit (.int n), IsVal.lit⟩)
    (v2 := ⟨.lit (.int n), IsVal.lit⟩)
    (hv1 := rfl) (hv2 := rfl))
  imodintro
  unfold lrel_int
  iexists n
  ipure_intro
  exact ⟨rfl, rfl⟩

/-! ## Adequacy: exit the logic

Apply `refines_coupling` to obtain a semantic property of OTP outside the
Iris logic: the limit-step distributions of `otp_enc m N` and `otp_ideal N`
are coupled by integer equality, with zero error. -/

/-- The φ-relation we extract from `lrel_int`: the two values are the same
integer literal. -/
def otpφ (v v' : Val) : Prop :=
  ∃ n : Int, v.1 = .lit (.int n) ∧ v'.1 = .lit (.int n)

theorem lrel_int_to_otpφ {GF : BundledGFunctors} (v v' : Val) :
    ⊢@{IProp GF} iprop((lrel_int (GF := GF)).car v v' -∗ ⌜otpφ v v'⌝) := by
  iintro Hint
  ihave ⟨%n, %hv, %hv'⟩ := lrel_int_unfold v v' $$ Hint
  ipure_intro
  exact ⟨n, hv, hv'⟩

/-- **Semantic OTP guarantee (forward)**: the encrypted-message distribution
and the uniform-sample distribution are coupled by value-equality with zero
error. This is `otp_refines` exited from the Iris logic via `refines_coupling`. -/
theorem otp_adequate
    (GF : BundledGFunctors.{0, 0, 0})
    [RefinesPreGS GF]
    (m N : Int) (HN : 0 < N)
    (σ σ' : State) :
    AddCoupl 0 (adequacyRel otpφ) (limExecV ⟨otp_enc m N, σ⟩) (limExecV ⟨otp_ideal N, σ'⟩) :=
  ProbLang.refines_coupling (A := fun _ => lrel_int) (φ := otpφ)
    (otp_enc m N) (otp_ideal N) σ σ'
    (fun _ v v' => lrel_int_to_otpφ v v')
    (fun IR => otp_refines (hlc := false) (GF := GF) (IR := IR) m N HN)

/-- **Semantic OTP guarantee (reverse)**: the uniform-sample distribution and
the encrypted-message distribution are coupled by value-equality with zero
error. This is `otp_refines_rev` exited from the Iris logic. -/
theorem otp_adequate_rev
    (GF : BundledGFunctors.{0, 0, 0})
    [RefinesPreGS GF]
    (m N : Int) (HN : 0 < N)
    (σ σ' : State) :
    AddCoupl 0 (adequacyRel otpφ) (limExecV ⟨otp_ideal N, σ⟩) (limExecV ⟨otp_enc m N, σ'⟩) :=
  ProbLang.refines_coupling (A := fun _ => lrel_int) (φ := otpφ)
    (otp_ideal N) (otp_enc m N) σ σ'
    (fun _ v v' => lrel_int_to_otpφ v v')
    (fun IR => otp_refines_rev (hlc := false) (GF := GF) (IR := IR) m N HN)

/-! ## Final closed statement: instantiated at the concrete model

`ApproxisFunctor : BundledGFunctors` from `AdequacyRel.lean` provides all the
required PreGS instances, so we can close off `otp_adequate{,_rev}` with no
remaining type-class hypotheses or `GF` parameter. -/

/-- **Final OTP guarantee (closed)**: at the concrete model `ApproxisFunctor`,
the encrypted-message and uniform distributions are coupled with zero error. -/
theorem otp_adequate_closed
    (m N : Int) (HN : 0 < N)
    (σ σ' : State) :
    AddCoupl 0 (adequacyRel otpφ) (limExecV ⟨otp_enc m N, σ⟩) (limExecV ⟨otp_ideal N, σ'⟩) :=
  otp_adequate ApproxisFunctor m N HN σ σ'

theorem otp_adequate_rev_closed
    (m N : Int) (HN : 0 < N)
    (σ σ' : State) :
    AddCoupl 0 (adequacyRel otpφ) (limExecV ⟨otp_ideal N, σ⟩) (limExecV ⟨otp_enc m N, σ'⟩) :=
  otp_adequate_rev ApproxisFunctor m N HN σ σ'

end OTP

end ProbLang
