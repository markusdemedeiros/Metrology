module

public import Metrology.Approxis.Compatibility
public import Metrology.Approxis.AppRelRules
public import Metrology.Approxis.RelTactics
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
    ∀ n : Int, 0 ≤ n → n < N → 0 ≤ addMod m N n ∧ addMod m N n < N := by
  intro n _ _
  unfold addMod
  refine ⟨Int.emod_nonneg _ (Int.ne_of_gt HN), Int.emod_lt_of_pos _ HN⟩

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
    have h1 : ((m' - m) % N + m) % N = (m' - m + m) % N := by
      rw [Int.add_emod, Int.emod_emod_of_dvd _ (dvd_refl N), ← Int.add_emod]
    rw [h1, show m' - m + m = m' from by ring, Int.emod_eq_of_lt hm'0 hm'N]
  · rintro n ⟨⟨hn0, hnN⟩, hadd⟩
    unfold addMod at hadd
    have hn_eq : n = n % N := (Int.emod_eq_of_lt hn0 hnN).symm
    have h1 : (n - (m' - m)) % N = 0 := by
      have h2 : (n + m - m') % N = 0 := by
        have hsub : ((n + m) - m') % N = ((n + m) % N - m' % N) % N := Int.sub_emod _ _ _
        have hm'eq : m' % N = m' := Int.emod_eq_of_lt hm'0 hm'N
        rw [hsub, hadd, hm'eq, Int.sub_self, Int.zero_emod]
      have heq : n + m - m' = n - (m' - m) := by ring
      rw [heq] at h2; exact h2
    rw [hn_eq]
    have hsub2 := Int.sub_emod n (m' - m) N
    rw [h1] at hsub2
    have hr1 : 0 ≤ (m' - m) % N := Int.emod_nonneg _ (Int.ne_of_gt HN)
    have hr2 : (m' - m) % N < N := Int.emod_lt_of_pos _ HN
    have hl1 : 0 ≤ n % N := Int.emod_nonneg _ (Int.ne_of_gt HN)
    have hl2 : n % N < N := Int.emod_lt_of_pos _ HN
    have h_diff_zero : (n % N) - ((m' - m) % N) = 0 := by
      have hmod_eq : ((n % N) - ((m' - m) % N)) % N = 0 := hsub2.symm
      have hdvd : (N : Int) ∣ ((n % N) - ((m' - m) % N)) :=
        Int.dvd_of_emod_eq_zero hmod_eq
      rcases hdvd with ⟨q, hq⟩
      have hbound : N * q < N ∧ -N < N * q := by rw [← hq]; omega
      have : q = 0 := by nlinarith
      rw [this, mul_zero] at hq
      linarith
    omega

/-! ### The OTP refinement -/

/-- The LHS program: sample a key, then output `(m + k) mod N`. -/
def otp_enc (m N : Int) : Exp :=
  pl(let k := rand(#(.int N), #(.unit)); (#(.int m) + k) % #(.int N))

/-- The RHS program: just sample uniformly. -/
def otp_ideal (N : Int) : Exp :=
  pl(rand(#(.int N), #(.unit)))

/-- **OTP refinement**: for any fixed `m ∈ [0, N)`, encrypting `m` with a fresh
random key is observationally equivalent to a fresh random sample. -/
theorem otp_refines (m N : Int) (HN : 0 < N) (Hm0 : 0 ≤ m) (HmN : m < N) :
    ⊢@{IProp GF} refines (⊤ : CoPset) (otp_enc m N) (otp_ideal N) lrel_int := by
  unfold otp_enc otp_ideal
  simp only [Exp.close, Exp.closeRec, ite_true, ↓reduceIte]
  set body : Exp := Exp.binop .mod
      (Exp.binop .plus (Exp.lit (.int m)) (Exp.bvar 0))
      (Exp.lit (.int N)) with hbody
  set K_lam : Ectx := [EctxItem.appR (Exp.lam body)] with hKlam
  have hReshape :
      (iprop(refines ⊤ (Exp.app (Exp.lam body) (Exp.rand (.lit (.int N)) (.lit .unit)))
                     (Exp.rand (.lit (.int N)) (.lit .unit)) lrel_int) : IProp GF) =
      iprop(refines ⊤ (K_lam.fill (Exp.rand (.lit (.int N)) (.lit .unit)))
                     (Ectx.fill ([] : Ectx) (Exp.rand (.lit (.int N)) (.lit .unit))) lrel_int) := rfl
  rw [hReshape]
  iapply (refines_couple_rands_lr (E := ⊤) (K := K_lam) (K' := ([] : Ectx)) (A := lrel_int)
    (z := N) (f := addMod m N)
    (hdom := addMod_dom m N HN)
    (hbij := addMod_bij m N HN)
    (Hz := HN))
  iintro %n ⟨%Hn0, %HnN⟩
  rw [show K_lam.fill (Exp.lit (.int n)) =
      Exp.app (Exp.lam body) (Exp.lit (.int n)) from rfl]
  rw [show Ectx.fill ([] : Ectx) (Exp.lit (.int (addMod m N n))) =
      Exp.lit (.int (addMod m N n)) from rfl]
  rw [show Exp.app (Exp.lam body) (Exp.lit (.int n)) =
      Ectx.fill ([] : Ectx) (Exp.app (Exp.lam body) (Exp.lit (.int n))) from rfl]
  iapply (refines_pure_l (K := []) (e := Exp.app (Exp.lam body) (Exp.lit (.int n)))
    (e' := Exp.open' body (Exp.lit (.int n)))
    (Hex := pureExec_app_lam) IsVal.lit.toIsValue)
  simp only [Nat.repeat]
  iintro !>
  rw [show Ectx.fill ([] : Ectx) (Exp.open' body (Exp.lit (.int n))) =
      Exp.open' body (Exp.lit (.int n)) from rfl]
  rw [show Exp.open' body (Exp.lit (.int n)) =
      Exp.binop .mod
        (Exp.binop .plus (Exp.lit (.int m)) (Exp.lit (.int n)))
        (Exp.lit (.int N)) from rfl]
  rw [show Exp.binop .mod
        (Exp.binop .plus (Exp.lit (.int m)) (Exp.lit (.int n)))
        (Exp.lit (.int N)) =
      Ectx.fill [EctxItem.binopL .mod ⟨.lit (.int N), IsVal.lit⟩]
        (Exp.binop .plus (Exp.lit (.int m)) (Exp.lit (.int n))) from rfl]
  iapply (refines_pure_l (K := [EctxItem.binopL .mod ⟨.lit (.int N), IsVal.lit⟩])
    (e := Exp.binop .plus (Exp.lit (.int m)) (Exp.lit (.int n)))
    (e' := Exp.lit (.int (m + n)))
    (Hex := pureExec_binop)
    ⟨IsVal.lit.toIsValue, IsVal.lit.toIsValue, rfl⟩)
  simp only [Nat.repeat]
  iintro !>
  rw [show Ectx.fill [EctxItem.binopL .mod ⟨.lit (.int N), IsVal.lit⟩]
        (Exp.lit (.int (m + n))) =
      Exp.binop .mod (Exp.lit (.int (m + n))) (Exp.lit (.int N)) from rfl]
  rw [show Exp.binop .mod (Exp.lit (.int (m + n))) (Exp.lit (.int N)) =
      Ectx.fill ([] : Ectx) (Exp.binop .mod (Exp.lit (.int (m + n))) (Exp.lit (.int N))) from rfl]
  have hmod_eval : BinOp.eval .mod (Exp.lit (.int (m + n))) (Exp.lit (.int N)) =
      some (Exp.lit (.int ((m + n) % N))) := by
    have hN_ne : N ≠ 0 := Int.ne_of_gt HN
    unfold BinOp.eval
    split <;> simp_all
  iapply (refines_pure_l (K := [])
    (e := Exp.binop .mod (Exp.lit (.int (m + n))) (Exp.lit (.int N)))
    (e' := Exp.lit (.int ((m + n) % N)))
    (Hex := pureExec_binop)
    ⟨IsVal.lit.toIsValue, IsVal.lit.toIsValue, hmod_eval⟩)
  simp only [Nat.repeat]
  iintro !>
  rw [show Ectx.fill ([] : Ectx) (Exp.lit (.int ((m + n) % N))) =
      Exp.lit (.int ((m + n) % N)) from rfl]
  have heq : (m + n) % N = addMod m N n := by
    unfold addMod; rw [show n + m = m + n from by ring]
  rw [heq]
  iapply (refines_ret (e1 := Exp.lit (.int (addMod m N n)))
    (e2 := Exp.lit (.int (addMod m N n)))
    (v1 := ⟨.lit (.int (addMod m N n)), IsVal.lit⟩)
    (v2 := ⟨.lit (.int (addMod m N n)), IsVal.lit⟩)
    (hv1 := rfl) (hv2 := rfl))
  imodintro
  unfold lrel_int
  iexists (addMod m N n)
  ipure_intro
  exact ⟨rfl, rfl⟩

/-! ### Reverse direction -/

/-- For `0 ≤ n < N`: `(m + (n - m) mod N) mod N = n`. -/
theorem addMod_neg_inv (m N : Int) (HN : 0 < N) :
    ∀ n : Int, 0 ≤ n → n < N → (m + (n + (-m)) % N) % N = n := by
  intro n hn0 hnN
  have h1 : (m + (n + (-m)) % N) % N = (m + (n + (-m))) % N := by
    rw [Int.add_emod m ((n + -m) % N) N, Int.emod_emod_of_dvd _ (dvd_refl N),
        ← Int.add_emod]
  rw [h1, show m + (n + -m) = n from by ring, Int.emod_eq_of_lt hn0 hnN]

/-- **Reverse OTP refinement**: a fresh random sample refines encrypting `m`
with a fresh random key. -/
theorem otp_refines_rev (m N : Int) (HN : 0 < N) (Hm0 : 0 ≤ m) (HmN : m < N) :
    ⊢@{IProp GF} refines (⊤ : CoPset) (otp_ideal N) (otp_enc m N) lrel_int := by
  unfold otp_enc otp_ideal
  simp only [Exp.close, Exp.closeRec, ite_true, ↓reduceIte]
  set body : Exp := Exp.binop .mod
      (Exp.binop .plus (Exp.lit (.int m)) (Exp.bvar 0))
      (Exp.lit (.int N)) with hbody
  set K_lam : Ectx := [EctxItem.appR (Exp.lam body)] with hKlam
  have hReshape :
      (iprop(refines ⊤ (Exp.rand (.lit (.int N)) (.lit .unit))
                     (Exp.app (Exp.lam body) (Exp.rand (.lit (.int N)) (.lit .unit)))
                     lrel_int) : IProp GF) =
      iprop(refines ⊤ (Ectx.fill ([] : Ectx) (Exp.rand (.lit (.int N)) (.lit .unit)))
                     (K_lam.fill (Exp.rand (.lit (.int N)) (.lit .unit))) lrel_int) := rfl
  rw [hReshape]
  iapply (refines_couple_rands_lr (E := ⊤) (K := ([] : Ectx)) (K' := K_lam) (A := lrel_int)
    (z := N) (f := addMod (-m) N)
    (hdom := addMod_dom (-m) N HN)
    (hbij := addMod_bij (-m) N HN)
    (Hz := HN))
  iintro %n ⟨%Hn0, %HnN⟩
  rw [show Ectx.fill ([] : Ectx) (Exp.lit (.int n)) = Exp.lit (.int n) from rfl]
  rw [show K_lam.fill (Exp.lit (.int (addMod (-m) N n))) =
      Exp.app (Exp.lam body) (Exp.lit (.int (addMod (-m) N n))) from rfl]
  rw [show Exp.app (Exp.lam body) (Exp.lit (.int (addMod (-m) N n))) =
      Ectx.fill ([] : Ectx) (Exp.app (Exp.lam body) (Exp.lit (.int (addMod (-m) N n)))) from rfl]
  iapply (refines_pure_r (K := ([] : Ectx))
    (e := Exp.app (Exp.lam body) (Exp.lit (.int (addMod (-m) N n))))
    (e' := Exp.open' body (Exp.lit (.int (addMod (-m) N n))))
    (Hex := pureExec_app_lam) IsVal.lit.toIsValue)
  rw [show Ectx.fill ([] : Ectx) (Exp.open' body (Exp.lit (.int (addMod (-m) N n)))) =
      Exp.binop .mod
        (Exp.binop .plus (Exp.lit (.int m)) (Exp.lit (.int (addMod (-m) N n))))
        (Exp.lit (.int N)) from rfl]
  -- Step 2 (inner plus).
  rw [show Exp.binop .mod
        (Exp.binop .plus (Exp.lit (.int m)) (Exp.lit (.int (addMod (-m) N n))))
        (Exp.lit (.int N)) =
      Ectx.fill [EctxItem.binopL .mod ⟨.lit (.int N), IsVal.lit⟩]
        (Exp.binop .plus (Exp.lit (.int m)) (Exp.lit (.int (addMod (-m) N n)))) from rfl]
  iapply (refines_pure_r (K := [EctxItem.binopL .mod ⟨.lit (.int N), IsVal.lit⟩])
    (e := Exp.binop .plus (Exp.lit (.int m)) (Exp.lit (.int (addMod (-m) N n))))
    (e' := Exp.lit (.int (m + addMod (-m) N n)))
    (Hex := pureExec_binop)
    ⟨IsVal.lit.toIsValue, IsVal.lit.toIsValue, rfl⟩)
  rw [show Ectx.fill [EctxItem.binopL .mod ⟨.lit (.int N), IsVal.lit⟩]
        (Exp.lit (.int (m + addMod (-m) N n))) =
      Exp.binop .mod (Exp.lit (.int (m + addMod (-m) N n))) (Exp.lit (.int N)) from rfl]
  -- Step 3 (outer mod).
  rw [show Exp.binop .mod (Exp.lit (.int (m + addMod (-m) N n))) (Exp.lit (.int N)) =
      Ectx.fill ([] : Ectx)
        (Exp.binop .mod (Exp.lit (.int (m + addMod (-m) N n))) (Exp.lit (.int N))) from rfl]
  have hmod_eval : BinOp.eval .mod (Exp.lit (.int (m + addMod (-m) N n)))
        (Exp.lit (.int N)) = some (Exp.lit (.int ((m + addMod (-m) N n) % N))) := by
    have hN_ne : N ≠ 0 := Int.ne_of_gt HN
    unfold BinOp.eval
    split <;> simp_all
  iapply (refines_pure_r (K := ([] : Ectx))
    (e := Exp.binop .mod (Exp.lit (.int (m + addMod (-m) N n))) (Exp.lit (.int N)))
    (e' := Exp.lit (.int ((m + addMod (-m) N n) % N)))
    (Hex := pureExec_binop)
    ⟨IsVal.lit.toIsValue, IsVal.lit.toIsValue, hmod_eval⟩)
  rw [show Ectx.fill ([] : Ectx) (Exp.lit (.int ((m + addMod (-m) N n) % N))) =
      Exp.lit (.int ((m + addMod (-m) N n) % N)) from rfl]
  -- The RHS-reduced value is `(m + (n + (-m)) % N) % N = n` by addMod_neg_inv.
  have heq : (m + addMod (-m) N n) % N = n := by
    unfold addMod; exact addMod_neg_inv m N HN n Hn0 HnN
  rw [heq]
  iapply (refines_ret (e1 := Exp.lit (.int n)) (e2 := Exp.lit (.int n))
    (v1 := ⟨.lit (.int n), IsVal.lit⟩) (v2 := ⟨.lit (.int n), IsVal.lit⟩)
    (hv1 := rfl) (hv2 := rfl))
  imodintro
  unfold lrel_int
  iexists n
  ipure_intro
  exact ⟨rfl, rfl⟩

/-
  -- Earlier draft with manual reshape; left as reference.
  unfold otp_enc otp_ideal
  let K_lam : Ectx := [EctxItem.appR (Exp.lam (Exp.binop .mod
      (Exp.binop .plus (Exp.lit (.int m)) (Exp.bvar 0))
      (Exp.lit (.int N))))]
  iintro %n %Hbnds
  obtain ⟨Hn0, HnN⟩ := Hbnds
  -- Reshape: LHS pure-steps to (m + n) mod N via beta + binop reduction.
  -- The lam body opened with #n is `(m + n) mod N` (substituting bvar 0 = #n).
  -- Hbeta : Ectx.fill [appR ...] #n = .app (.lam body) #n.
  -- We'll pure-step beta, then pure-step the inner binop, then the outer binop.
  rw [show Ectx.fill [EctxItem.appR (Exp.lam _)] (Exp.lit (.int n)) =
      Exp.app (Exp.lam (Exp.binop .mod
        (Exp.binop .plus (Exp.lit (.int m)) (Exp.bvar 0))
        (Exp.lit (.int N)))) (Exp.lit (.int n)) from rfl]
  -- Step 1: beta. (λ k. (m + k) mod N) #n → (m + #n) mod N.
  have hβ : Exp.app (Exp.lam (Exp.binop .mod
        (Exp.binop .plus (Exp.lit (.int m)) (Exp.bvar 0))
        (Exp.lit (.int N)))) (Exp.lit (.int n)) =
      Ectx.fill [] (Exp.app (Exp.lam _) (Exp.lit (.int n))) := rfl
  rw [hβ]
  iapply (refines_pure_l (K := []) (Hex := pureExec_app_lam) IsVal.lit.toIsValue)
  simp only [Nat.repeat]
  iintro !>
  -- After β: Ectx.fill [] (Exp.open' body #n) = (m + #n) mod N.
  rw [show Exp.open' (Exp.binop .mod
        (Exp.binop .plus (Exp.lit (.int m)) (Exp.bvar 0))
        (Exp.lit (.int N))) (Exp.lit (.int n)) =
      Exp.binop .mod
        (Exp.binop .plus (Exp.lit (.int m)) (Exp.lit (.int n)))
        (Exp.lit (.int N)) from rfl]
  rw [show Ectx.fill ([] : Ectx) (Exp.binop .mod
        (Exp.binop .plus (Exp.lit (.int m)) (Exp.lit (.int n)))
        (Exp.lit (.int N))) =
      Exp.binop .mod
        (Exp.binop .plus (Exp.lit (.int m)) (Exp.lit (.int n)))
        (Exp.lit (.int N)) from rfl]
  -- Step 2: inner plus. (m + n) → #(m + n). Need pureExec_binop.
  have hinner : Exp.binop .mod
        (Exp.binop .plus (Exp.lit (.int m)) (Exp.lit (.int n)))
        (Exp.lit (.int N)) =
      Ectx.fill [EctxItem.binopR .mod (Exp.lit (.int N))]
        (Exp.binop .plus (Exp.lit (.int m)) (Exp.lit (.int n))) := rfl
  -- Wait, that's wrong order. binopR is for the RIGHT operand, so the inner
  -- plus is the LEFT. Use binopL with (lit N) as v2.
  -- Actually the OUTER binop is `mod (plus _ _) (lit N)`. We want to step the
  -- LEFT operand (the plus), so context is `binopL .mod ⟨#N, IsVal.lit⟩`.
  rw [show Exp.binop .mod
        (Exp.binop .plus (Exp.lit (.int m)) (Exp.lit (.int n)))
        (Exp.lit (.int N)) =
      Ectx.fill [EctxItem.binopL .mod ⟨.lit (.int N), IsVal.lit⟩]
        (Exp.binop .plus (Exp.lit (.int m)) (Exp.lit (.int n))) from rfl]
  have hφ_plus : (Exp.lit (.int m)).isValue ∧ (Exp.lit (.int n)).isValue ∧
      BinOp.eval .plus (Exp.lit (.int m)) (Exp.lit (.int n)) = some _ :=
    ⟨IsVal.lit.toIsValue, IsVal.lit.toIsValue, rfl⟩
  iapply (refines_pure_l (K := [EctxItem.binopL .mod ⟨.lit (.int N), IsVal.lit⟩])
    (Hex := pureExec_binop) hφ_plus)
  simp only [Nat.repeat]
  iintro !>
  -- Now LHS = mod (#(m+n)) #N. Step the outer mod.
  rw [show Ectx.fill [EctxItem.binopL .mod ⟨.lit (.int N), IsVal.lit⟩]
        (Exp.lit (.int (m + n))) =
      Exp.binop .mod (Exp.lit (.int (m + n))) (Exp.lit (.int N)) from rfl]
  have hφ_mod : (Exp.lit (.int (m + n))).isValue ∧ (Exp.lit (.int N)).isValue ∧
      BinOp.eval .mod (Exp.lit (.int (m + n))) (Exp.lit (.int N)) =
        some (Exp.lit (.int ((m + n) % N))) := by
    refine ⟨IsVal.lit.toIsValue, IsVal.lit.toIsValue, ?_⟩
    -- BinOp.eval mod (#(m+n)) (#N): need N ≠ 0.
    have hN_ne : N ≠ 0 := Int.ne_of_gt HN
    show (match BinOp.mod, Exp.lit (.int (m + n)), Exp.lit (.int N) with | _, _, _ => _) = _
    unfold BinOp.eval
    rw [if_neg hN_ne]
  rw [show Exp.binop .mod (Exp.lit (.int (m + n))) (Exp.lit (.int N)) =
      Ectx.fill [] (Exp.binop .mod (Exp.lit (.int (m + n))) (Exp.lit (.int N))) from rfl]
  iapply (refines_pure_l (K := []) (Hex := pureExec_binop) hφ_mod)
  simp only [Nat.repeat]
  iintro !>
  rw [show Ectx.fill ([] : Ectx) (Exp.lit (.int ((m + n) % N))) =
      Exp.lit (.int ((m + n) % N)) from rfl]
  -- LHS is now `#((m + n) % N)`. RHS is `#(addMod m N n) = #((n + m) % N)`.
  -- These are equal via commutativity of +.
  rw [show Ectx.fill ([] : Ectx) (Exp.lit (.int (addMod m N n))) =
      Exp.lit (.int (addMod m N n)) from rfl]
  unfold addMod
  rw [show m + n = n + m from by ring]
  -- Now LHS = #((n + m) % N), RHS = #((n + m) % N).
  iapply refines_ret (e1 := Exp.lit (.int ((n + m) % N))) (e2 := Exp.lit (.int ((n + m) % N)))
    (v1 := ⟨.lit (.int ((n + m) % N)), IsVal.lit⟩)
    (v2 := ⟨.lit (.int ((n + m) % N)), IsVal.lit⟩)
    (hv1 := rfl) (hv2 := rfl)
  imodintro
  unfold lrel_int
  iexists ((n + m) % N)
  ipure_intro
  exact ⟨rfl, rfl⟩
-/

/-! ## Adequacy: exit the logic

Apply `refines_coupling` to obtain a semantic property of OTP outside the
Iris logic: the limit-step distributions of `otp_enc m N` and `otp_ideal N`
are coupled by integer equality, with zero error. -/

/-- The φ-relation we extract from `lrel_int`: the two values are the same
integer literal. -/
def otpφ : Val → Val → Prop := fun v v' =>
  ∃ n : Int, v.1 = .lit (.int n) ∧ v'.1 = .lit (.int n)

theorem lrel_int_to_otpφ {GF : BundledGFunctors} (v v' : Val) :
    ⊢@{IProp GF} iprop((lrel_int (GF := GF)).car v v' -∗ ⌜otpφ v v'⌝) := by
  iintro Hint
  ihave HEx := lrel_int_unfold v v' $$ Hint
  icases HEx with ⟨%n, %hv, %hv'⟩
  ipure_intro
  exact ⟨n, hv, hv'⟩

theorem lrel_int_to_otpφ_rev {GF : BundledGFunctors} (v v' : Val) :
    ⊢@{IProp GF} iprop((lrel_int (GF := GF)).car v v' -∗ ⌜otpφ v' v⌝) := by
  iintro Hint
  ihave HEx := lrel_int_unfold v v' $$ Hint
  icases HEx with ⟨%n, %hv, %hv'⟩
  ipure_intro
  exact ⟨n, hv', hv⟩

/-- **Semantic OTP guarantee (forward)**: the encrypted-message distribution
and the uniform-sample distribution are coupled by value-equality with zero
error. This is `otp_refines` exited from the Iris logic via `refines_coupling`. -/
theorem otp_adequate
    (GF : BundledGFunctors.{0, 0, 0})
    [AppPreGS GF] [SpecPreGS GF] [ECPreGS GF] [InvGpreS GF] [NaInvG GF]
    (m N : Int) (HN : 0 < N) (Hm0 : 0 ≤ m) (HmN : m < N)
    (σ σ' : State) :
    AddCoupl 0 (adequacyRel otpφ)
      ((limExec ⟨otp_enc m N, σ⟩).map (·.expr))
      ((limExec ⟨otp_ideal N, σ'⟩).map (·.expr)) := by
  apply ProbLang.refines_coupling (GF := GF)
    (A := fun _ => lrel_int) (φ := otpφ)
  · intro IR v v'
    exact lrel_int_to_otpφ v v'
  · intro IR
    exact otp_refines (hlc := false) (GF := GF) (IR := IR) m N HN Hm0 HmN

/-- **Semantic OTP guarantee (reverse)**: the uniform-sample distribution and
the encrypted-message distribution are coupled by value-equality with zero
error. This is `otp_refines_rev` exited from the Iris logic. -/
theorem otp_adequate_rev
    (GF : BundledGFunctors.{0, 0, 0})
    [AppPreGS GF] [SpecPreGS GF] [ECPreGS GF] [InvGpreS GF] [NaInvG GF]
    (m N : Int) (HN : 0 < N) (Hm0 : 0 ≤ m) (HmN : m < N)
    (σ σ' : State) :
    AddCoupl 0 (adequacyRel otpφ)
      ((limExec ⟨otp_ideal N, σ⟩).map (·.expr))
      ((limExec ⟨otp_enc m N, σ'⟩).map (·.expr)) := by
  apply ProbLang.refines_coupling (GF := GF)
    (A := fun _ => lrel_int) (φ := otpφ)
  · intro IR v v'
    exact lrel_int_to_otpφ v v'
  · intro IR
    exact otp_refines_rev (hlc := false) (GF := GF) (IR := IR) m N HN Hm0 HmN

/-! ## Final closed statement: instantiated at the concrete model

`otpSigma : BundledGFunctors` from `AdequacyRel.lean` provides all the required
PreGS instances, so we can close off `otp_adequate{,_rev}` with no remaining
type-class hypotheses or `GF` parameter. -/

/-- **Final OTP guarantee (closed)**: at the concrete model `otpSigma`, the
encrypted-message and uniform distributions are coupled with zero error. -/
theorem otp_adequate_closed
    (m N : Int) (HN : 0 < N) (Hm0 : 0 ≤ m) (HmN : m < N)
    (σ σ' : State) :
    AddCoupl 0 (adequacyRel otpφ)
      ((limExec ⟨otp_enc m N, σ⟩).map (·.expr))
      ((limExec ⟨otp_ideal N, σ'⟩).map (·.expr)) :=
  otp_adequate ProbLang.otpSigma m N HN Hm0 HmN σ σ'

theorem otp_adequate_rev_closed
    (m N : Int) (HN : 0 < N) (Hm0 : 0 ≤ m) (HmN : m < N)
    (σ σ' : State) :
    AddCoupl 0 (adequacyRel otpφ)
      ((limExec ⟨otp_ideal N, σ⟩).map (·.expr))
      ((limExec ⟨otp_enc m N, σ'⟩).map (·.expr)) :=
  otp_adequate_rev ProbLang.otpSigma m N HN Hm0 HmN σ σ'

end OTP

end ProbLang
