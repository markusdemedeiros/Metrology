module

public import Metrology.Approxis.ContinuousSampler
public import Metrology.Approxis.Soundness
public import Metrology.ProbLang.Advantage
import Metrology.ProbLang.Syntax.Notation
public import Metrology.ProbLang.Reals
public import Metrology.Approxis.AdequacyRel

@[expose] public section

/-! # A continuous one-time pad

The continuous analogue of `Examples/OTP.lean`. There the key is uniform on
`{0, …, N-1}` and the combiner is `+ mod N`; here the key is uniform on the unit
interval and the combiner is `frac (m + ·)`, rotation of the circle by `m`.

The whole point is that **`rT` is not countable here**. The refinement rests on
`refines_couple_urands_lr`, whose only hypothesis is that the combiner preserves
`unifUnit` — which for `ℝ` is `measurePreserving_fracAdd`. -/

namespace ProbLang
open Iris Iris.BI Iris.ProofMode OFE COFE ProbLang ProbLang.ApproxisWpGS

namespace ContinuousOTP

variable {rT : Type} [ProbLangℝ rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [IR : ApproxisRGS rT hlc GF]

/-- The LHS program: sample a uniform key `k`, output `frac (m + k)`. -/
def otp_enc (m : rT) : Exp rT :=
  pl% let k := urand; frac(#(.real m) + k)

/-- The RHS program: just sample uniformly. -/
def otp_ideal : Exp rT := pl% urand

/-- The `lam` that `otp_enc m` exposes once its `let` is read as an application. -/
abbrev otpLam (m : rT) : Exp rT := pl% fun k, frac(#(.real m) + k)

/-- The evaluation context `otp_enc m` exposes once its `let` is read as a
`lam`-application. -/
def otpKLam (m : rT) : Ectx rT := [EctxItem.appR (otpLam m)]

/-- **Continuous OTP refinement**: encrypting `m` with a fresh uniform key on the
unit interval is observationally equivalent to a fresh uniform sample, provided
the combiner `frac (m + ·)` preserves `unifUnit`. -/
theorem otp_refines (m : rT)
    (hmp : MeasureTheory.MeasurePreserving
      (fun r : rT => ProbLangℝ.realFrac (ProbLangℝ.realAdd m r))
      (ProbLangℝ.unifUnit (T := rT)) (ProbLangℝ.unifUnit (T := rT))) :
    ⊢@{IProp GF} refines (⊤ : CoPset)
      (otp_enc (rT := rT) m) (otp_ideal (rT := rT)) lrel_real := by
  simp only [otp_enc, otp_ideal, Exp.close, Exp.closeRec, ↓reduceIte]
  show ⊢@{IProp GF} iprop(refines ⊤
    ((otpKLam (rT := rT) m).fill pl(urand))
    (Ectx.fill ([] : Ectx rT) pl(urand)) lrel_real)
  iapply (refines_couple_urands_lr (E := ⊤) (K := otpKLam (rT := rT) m)
    (K' := ([] : Ectx rT)) (A := lrel_real)
    (f := fun r : rT => ProbLangℝ.realFrac (ProbLangℝ.realAdd m r)) hmp)
  iintro %r %_hr
  let Kfrac : Ectx rT := [EctxItem.unop .frac]
  show ⊢@{IProp GF} iprop(refines ⊤
    (Ectx.fill ([] : Ectx rT) pl({otpLam (rT := rT) m} #(.real r)))
    pl(#(.real (ProbLangℝ.realFrac (ProbLangℝ.realAdd m r)))) lrel_real)
  -- β-reduce the `let`.
  iapply (refines_pure_l (K := ([] : Ectx rT))
    (Hex := pureExec_app_lam) ⟨IsVal.lit.toIsValue, by is_lc⟩)
  simp only [Nat.repeat]
  iintro !>
  show ⊢@{IProp GF} iprop(refines ⊤
    (Kfrac.fill pl(#(.real m) + #(.real r)))
    pl(#(.real (ProbLangℝ.realFrac (ProbLangℝ.realAdd m r)))) lrel_real)
  -- Evaluate the addition.
  iapply (refines_pure_l (K := Kfrac) (Hex := pureExec_binop)
    ⟨IsVal.lit.toIsValue, IsVal.lit.toIsValue, rfl⟩)
  simp only [Nat.repeat]
  iintro !>
  show ⊢@{IProp GF} iprop(refines ⊤
    (Ectx.fill ([] : Ectx rT) pl(frac(#(.real (ProbLangℝ.realAdd m r)))))
    pl(#(.real (ProbLangℝ.realFrac (ProbLangℝ.realAdd m r)))) lrel_real)
  -- Evaluate `frac`.
  iapply (refines_pure_l (K := ([] : Ectx rT)) (Hex := pureExec_unop)
    ⟨IsVal.lit.toIsValue, rfl⟩)
  simp only [Nat.repeat]
  iintro !>
  show ⊢@{IProp GF} iprop(refines ⊤
    pl(#(.real (ProbLangℝ.realFrac (ProbLangℝ.realAdd m r))))
    pl(#(.real (ProbLangℝ.realFrac (ProbLangℝ.realAdd m r)))) lrel_real)
  iapply (refines_ret
    (v1 := (.real (ProbLangℝ.realFrac (ProbLangℝ.realAdd m r)) : Val rT))
    (v2 := (.real (ProbLangℝ.realFrac (ProbLangℝ.realAdd m r)) : Val rT))
    (hv1 := rfl) (hv2 := rfl))
  imodintro
  unfold lrel_real
  iexists (ProbLangℝ.realFrac (ProbLangℝ.realAdd m r))
  ipureintro
  exact ⟨rfl, rfl⟩

/-! ### The reverse direction

Couple the ideal sample against the encryption's key using the *inverse* rotation
`g`, so that the encryption's combiner sends `g r` back to `r`. -/

/-- **Reverse refinement**: a fresh uniform sample refines encrypting `m` with a
fresh uniform key, given an inverse `g` for the combiner on the support. -/
theorem otp_refines_rev (m : rT) (g : rT → rT)
    (hmp : MeasureTheory.MeasurePreserving g
      (ProbLangℝ.unifUnit (T := rT)) (ProbLangℝ.unifUnit (T := rT)))
    (hinv : ∀ r ∈ ProbLangℝ.unifUnitSupport,
      ProbLangℝ.realFrac (ProbLangℝ.realAdd m (g r)) = r) :
    ⊢@{IProp GF} refines (⊤ : CoPset)
      (otp_ideal (rT := rT)) (otp_enc (rT := rT) m) lrel_real := by
  simp only [otp_enc, otp_ideal, Exp.close, Exp.closeRec, ↓reduceIte]
  show ⊢@{IProp GF} iprop(refines ⊤
    (Ectx.fill ([] : Ectx rT) pl(urand))
    ((otpKLam (rT := rT) m).fill pl(urand)) lrel_real)
  iapply (refines_couple_urands_lr (E := ⊤) (K := ([] : Ectx rT))
    (K' := otpKLam (rT := rT) m) (A := lrel_real) (f := g) hmp)
  iintro %r %hr
  let Kfrac : Ectx rT := [EctxItem.unop .frac]
  show ⊢@{IProp GF} iprop(refines ⊤
    pl(#(.real r))
    (Ectx.fill ([] : Ectx rT) pl({otpLam (rT := rT) m} #(.real (g r))))
    lrel_real)
  -- β-reduce the RHS `let`.
  iapply (refines_pure_r (K := ([] : Ectx rT))
    (Hex := pureExec_app_lam) ⟨IsVal.lit.toIsValue, by is_lc⟩)
  show ⊢@{IProp GF} iprop(refines ⊤
    pl(#(.real r))
    (Kfrac.fill pl(#(.real m) + #(.real (g r)))) lrel_real)
  -- Evaluate the addition.
  iapply (refines_pure_r (K := Kfrac) (Hex := pureExec_binop)
    ⟨IsVal.lit.toIsValue, IsVal.lit.toIsValue, rfl⟩)
  show ⊢@{IProp GF} iprop(refines ⊤
    pl(#(.real r))
    (Ectx.fill ([] : Ectx rT) pl(frac(#(.real (ProbLangℝ.realAdd m (g r))))))
    lrel_real)
  -- Evaluate `frac`; the inverse law collapses the result to `r`.
  iapply (refines_pure_r (K := ([] : Ectx rT)) (Hex := pureExec_unop)
    ⟨IsVal.lit.toIsValue, rfl⟩)
  rw [hinv r hr]
  show ⊢@{IProp GF} iprop(refines ⊤ pl(#(.real r)) pl(#(.real r)) lrel_real)
  iapply (refines_ret (v1 := (.real r : Val rT)) (v2 := (.real r : Val rT))
    (hv1 := rfl) (hv2 := rfl))
  imodintro
  unfold lrel_real
  iexists r
  ipureintro
  exact ⟨rfl, rfl⟩

/-! ### At `rT = ℝ`

The abstract hypothesis is discharged by rotation invariance of `Uniform[0,1]`,
so the refinement holds outright for the genuinely continuous instance. -/

/-- **Continuous OTP over `ℝ`.** For a message `m ∈ [0,1)`, `let k := urand;
frac (m + k)` refines `urand`. No countability anywhere. -/
theorem otp_refines_real (m : ℝ)
    {hlc : HasLC} {GF : BundledGFunctors} [ApproxisRGS ℝ hlc GF] :
    ⊢@{IProp GF} refines (⊤ : CoPset)
      (otp_enc (rT := ℝ) m) (otp_ideal (rT := ℝ)) lrel_real :=
  otp_refines m (measurePreserving_fracAdd m)

/-- The `ℝ` inverse rotation: `g r = frac (-m + r)`. -/
noncomputable def invRot (m : ℝ) : ℝ → ℝ := fun r => Int.fract (-m + r)

/-- **Continuous OTP over `ℝ`, reverse direction.** -/
theorem otp_refines_rev_real (m : ℝ)
    {hlc : HasLC} {GF : BundledGFunctors} [ApproxisRGS ℝ hlc GF] :
    ⊢@{IProp GF} refines (⊤ : CoPset)
      (otp_ideal (rT := ℝ)) (otp_enc (rT := ℝ) m) lrel_real :=
  otp_refines_rev m (invRot m) (measurePreserving_fracAdd (-m))
    (fun r hr => by
      have hr' : r ∈ Set.Ioo (0:ℝ) 1 := hr
      show Int.fract (m + Int.fract (-m + r)) = r
      rw [fract_add_fract_right, show m + (-m + r) = r by ring]
      exact Int.fract_eq_self.mpr ⟨le_of_lt hr'.1, hr'.2⟩)

/-! ## Adequacy: exiting the logic

`refines_coupling` turns each refinement into a statement about the limiting
execution distributions, with no Iris in sight. -/

/-- The relation extracted from `lrel_real`: both sides are the same real. -/
def otpφ (v v' : Val rT) : Prop :=
  ∃ r : rT, v.1 = pl(#(.real r)) ∧ v'.1 = pl(#(.real r))

theorem lrel_real_to_otpφ {GF : BundledGFunctors} [ApproxisRGS rT hlc GF] (v v' : Val rT) :
    ⊢@{IProp GF} iprop((lrel_real (GF := GF)).car v v' -∗ ⌜otpφ v v'⌝) := by
  iintro Hr
  ihave HrEx := lrel_real_unfold v v' $$ Hr
  icases HrEx with ⟨%r, %hv, %hv'⟩
  ipureintro
  exact ⟨r, hv, hv'⟩

section Adequacy
variable {GF : BundledGFunctors.{0, 0, 0}}

/-- **Semantic guarantee (forward)**: the encrypted-message distribution and the
uniform distribution are coupled by value-equality at zero error. -/
theorem otp_adequate_real [RefinesPreGS ℝ GF] (m : ℝ) (σ σ' : State ℝ) :
    AddCoupl 0 (adequacyRel (otpφ (rT := ℝ)))
      (limExecV ⟨otp_enc (rT := ℝ) m, σ⟩) (limExecV ⟨otp_ideal (rT := ℝ), σ'⟩) :=
  ProbLang.refines_coupling (A := fun _ => lrel_real) (φ := otpφ)
    (otp_enc (rT := ℝ) m) (otp_ideal (rT := ℝ)) σ σ'
    (fun _ v v' => lrel_real_to_otpφ v v')
    (fun _ => otp_refines_real (hlc := .hasNoLC) (GF := GF) m)

/-- **Semantic guarantee (reverse)**. -/
theorem otp_adequate_rev_real [RefinesPreGS ℝ GF] (m : ℝ) (σ σ' : State ℝ) :
    AddCoupl 0 (adequacyRel (otpφ (rT := ℝ)))
      (limExecV ⟨otp_ideal (rT := ℝ), σ⟩) (limExecV ⟨otp_enc (rT := ℝ) m, σ'⟩) :=
  ProbLang.refines_coupling (A := fun _ => lrel_real) (φ := otpφ)
    (otp_ideal (rT := ℝ)) (otp_enc (rT := ℝ) m) σ σ'
    (fun _ v v' => lrel_real_to_otpφ v v')
    (fun _ => otp_refines_rev_real (hlc := .hasNoLC) (GF := GF) m)

end Adequacy

/-! ## Closed statement

At the concrete model `ApproxisFunctor ℝ` every ghost-state hypothesis is
discharged, leaving a self-contained theorem about `ℝ`-valued programs. -/

omit [ProbLangℝ rT] in
/-- On value configurations, `adequacyRel otpφ` *is* equality: both sides are the
same real literal. This is what lets the two couplings be eliminated. -/
theorem adequacyRel_otpφ_subset_eq :
    adequacyRel (otpφ (rT := rT)) ⊆ {p : Exp rT × Exp rT | p.1 = p.2} := by
  rintro ⟨e₁, e₂⟩ ⟨v, v', hv, hv', r, hr, hr'⟩
  have h1 : e₁ = v.1 := (Exp.ofVal_of_toVal_some hv).symm
  have h2 : e₂ = v'.1 := (Exp.ofVal_of_toVal_some hv').symm
  show e₁ = e₂
  rw [h1, h2, hr, hr']

/-- **The continuous one-time pad is an observational equivalence.**

Mutual refinement at error `0` and at a relation that is equality on values
eliminates (`AddCoupl.eq_elim`, the Rocq `ARcoupl_eq_elim`) to give what one
actually wants: `let k := urand; frac (m + k)` and `urand` induce *literally the
same* output distribution, from any pair of starting states. -/
theorem otp_distribution_eq (m : ℝ) (σ σ' : State ℝ) :
    limExecV (⟨otp_enc (rT := ℝ) m, σ⟩ : Cfg ℝ)
      = limExecV (⟨otp_ideal (rT := ℝ), σ'⟩ : Cfg ℝ) :=
  AddCoupl.eq_of_eq_zero
    (AddCoupl.mono_rel adequacyRel_otpφ_subset_eq
      (otp_adequate_real (GF := ApproxisFunctor ℝ) m σ σ'))
    (AddCoupl.mono_rel adequacyRel_otpφ_subset_eq
      (otp_adequate_rev_real (GF := ApproxisFunctor ℝ) m σ' σ))

/-! ### Non-vacuity

An equality of measures says nothing if both sides are the zero measure, so we
pin down the mass. `urand` reaches a value in one step, hence `execN 2` already
carries the whole mass; the a.e. step "every successor is a value" is exactly
`Atomic.urand'`. -/

/-- The ideal sampler's output distribution is a probability measure. -/
theorem otp_ideal_mass (σ : State ℝ) :
    (limExecV (⟨otp_ideal (rT := ℝ), σ⟩ : Cfg ℝ)) Set.univ = 1 := by
  have hnv : ¬ (pl(urand) : Exp ℝ).isValue := fun ⟨w⟩ => nomatch w
  -- One step of `urand` lands on a value, so `execN 2` already has full mass.
  have hstep : execN 2 (⟨otp_ideal (rT := ℝ), σ⟩ : Cfg ℝ) Set.univ = 1 := by
    show execN 2 (⟨pl(urand), σ⟩ : Cfg ℝ) Set.univ = 1
    rw [execN_succ_not_isValue hnv,
        MeasureTheory.Measure.bind_apply MeasurableSet.univ (execN_measurable 1).aemeasurable]
    have hae : ∀ᵐ ρ' ∂(primStep (⟨pl(urand), σ⟩ : Cfg ℝ)),
        execN 1 ρ' Set.univ = 1 := by
      rw [MeasureTheory.ae_iff]
      refine MeasureTheory.measure_mono_null ?_ (Atomic.urand' (rT := ℝ) σ)
      intro ρ' hρ'
      simp only [Set.mem_compl_iff, Set.mem_setOf_eq]
      intro hv
      exact hρ' (by rw [execN_succ_isValue hv]; simp)
    rw [MeasureTheory.lintegral_congr_ae hae]
    simp only [MeasureTheory.lintegral_const, one_mul]
    have : primStep (⟨pl(urand), σ⟩ : Cfg ℝ) = Cfg.uniformReal σ :=
      primStep_eq_headStep
        (Exp.decompItem_none_of_lc_headReducible (by is_lc)
          (show Cfg.uniformReal σ ≠ 0 from MeasureTheory.IsProbabilityMeasure.ne_zero _))
    rw [this]
    exact Cfg.uniformReal_isProbabilityMeasure.measure_univ
  have hle : (limExec (⟨otp_ideal (rT := ℝ), σ⟩ : Cfg ℝ)) Set.univ ≤ 1 :=
    limExec_leq_mass (fun n => execN_univ_le_one n _)
  have hge : (1 : ENNReal) ≤ (limExec (⟨otp_ideal (rT := ℝ), σ⟩ : Cfg ℝ)) Set.univ := by
    rw [limExec_univ', ← hstep]
    exact le_iSup (fun n => (execN n (⟨otp_ideal (rT := ℝ), σ⟩ : Cfg ℝ)) Set.univ) 2
  have hlim : (limExec (⟨otp_ideal (rT := ℝ), σ⟩ : Cfg ℝ)) Set.univ = 1 :=
    le_antisymm hle hge
  show (asExpr (limExec _)) Set.univ = 1
  rw [asExpr, MeasureTheory.Measure.map_apply Cfg.measurable_expr MeasurableSet.univ]
  simpa using hlim

/-- Hence so is the encryption's — by `otp_distribution_eq`. The equivalence is
therefore between two genuine probability distributions, not a vacuous identity
of null measures. -/
theorem otp_enc_mass (m : ℝ) (σ : State ℝ) :
    (limExecV (⟨otp_enc (rT := ℝ) m, σ⟩ : Cfg ℝ)) Set.univ = 1 := by
  rw [otp_distribution_eq m σ σ]
  exact otp_ideal_mass σ

/-! ## Contextual equivalence

With `Ty.real` in the type system the one-time pad finally lands where Clutch's
discrete examples land: contextual refinement in both directions, via
`refines_sound_fresh`. `GF` is a parameter in the Rocq sense (`refines_sound Σ`)
— the statement holds for any ghost-state bundle able to host the Approxis
resources. -/

section Typing

omit [ProbLangℝ rT] in
theorem otp_ideal_typed : Typed (rT := rT) Tctx.empty otp_ideal .real := .urand

omit [ProbLangℝ rT] in
theorem otpLam_typed (m : rT) :
    Typed (rT := rT) Tctx.empty (otpLam m) (.arrow .real .real) := by
  refine Typed.lam ∅ (fun x _ => ?_)
  exact .unop_real (.binop_real .lit_real (.fvar (by simp [Tctx.insert])) rfl) rfl

omit [ProbLangℝ rT] in
/-- `otp_enc m` reads as `(fun k, frac (m + k)) urand`. -/
theorem otp_enc_typed (m : rT) :
    Typed (rT := rT) Tctx.empty (otp_enc m) .real :=
  .app (otpLam_typed m) .urand

end Typing

/-- **Contextual refinement.** Every Bool-typed closing context observes
`otp_enc m` no more often than `otp_ideal`. -/
theorem otp_ctx_refines_real (GF : BundledGFunctors.{0, 0, 0}) [RefinesPreGS ℝ GF] (m : ℝ) :
    ∀ (K : Ctx ℝ) (σ₀ : State ℝ) (b : Bool),
      TypedCtx K Tctx.empty .real Tctx.empty .bool →
      Ctx.BindersFresh K ∅ →
      (∀ x ∈ Ctx.binderAtoms K, x ∉ (otp_enc (rT := ℝ) m).fv ∧
        x ∉ (otp_ideal (rT := ℝ)).fv ∧ x ∉ Ctx.payloadFv K) →
      limExec ⟨K.fill (otp_enc (rT := ℝ) m), σ₀⟩ (finalBool b) ≤
      limExec ⟨K.fill (otp_ideal (rT := ℝ)), σ₀⟩ (finalBool b) :=
  refines_sound_fresh (GF := GF) _ _ .real (otp_enc_typed m) otp_ideal_typed
    (fun IR _ => @otp_refines_real m HasLC.hasNoLC GF IR)

/-- **Contextual refinement, reverse direction.** Together with
`otp_ctx_refines_real` this is contextual *equivalence*. -/
theorem otp_ctx_refines_rev_real (GF : BundledGFunctors.{0, 0, 0}) [RefinesPreGS ℝ GF] (m : ℝ) :
    ∀ (K : Ctx ℝ) (σ₀ : State ℝ) (b : Bool),
      TypedCtx K Tctx.empty .real Tctx.empty .bool →
      Ctx.BindersFresh K ∅ →
      (∀ x ∈ Ctx.binderAtoms K, x ∉ (otp_ideal (rT := ℝ)).fv ∧
        x ∉ (otp_enc (rT := ℝ) m).fv ∧ x ∉ Ctx.payloadFv K) →
      limExec ⟨K.fill (otp_ideal (rT := ℝ)), σ₀⟩ (finalBool b) ≤
      limExec ⟨K.fill (otp_enc (rT := ℝ) m), σ₀⟩ (finalBool b) :=
  refines_sound_fresh (GF := GF) _ _ .real otp_ideal_typed (otp_enc_typed m)
    (fun IR _ => @otp_refines_rev_real m HasLC.hasNoLC GF IR)

/-- **Contextual equivalence of the continuous one-time pad.** No context can
distinguish the encryption from a fresh uniform sample — at any Bool
observation, in any state. -/
theorem otp_ctx_equiv_real (GF : BundledGFunctors.{0, 0, 0}) [RefinesPreGS ℝ GF] (m : ℝ)
    (K : Ctx ℝ) (σ₀ : State ℝ) (b : Bool)
    (hK : TypedCtx K Tctx.empty .real Tctx.empty .bool)
    (hbf : Ctx.BindersFresh K ∅)
    (hfresh : ∀ x ∈ Ctx.binderAtoms K, x ∉ (otp_enc (rT := ℝ) m).fv ∧
      x ∉ (otp_ideal (rT := ℝ)).fv ∧ x ∉ Ctx.payloadFv K) :
    limExec ⟨K.fill (otp_enc (rT := ℝ) m), σ₀⟩ (finalBool b) =
    limExec ⟨K.fill (otp_ideal (rT := ℝ)), σ₀⟩ (finalBool b) :=
  le_antisymm
    (otp_ctx_refines_real GF m K σ₀ b hK hbf hfresh)
    (otp_ctx_refines_rev_real GF m K σ₀ b hK hbf
      (fun x hx => ⟨(hfresh x hx).2.1, (hfresh x hx).1, (hfresh x hx).2.2⟩))

/-- **Zero advantage.** No measurable test on the result, at any initial state,
distinguishes the encryption from a fresh uniform sample. This is the
security statement in its usual cryptographic form; `advantage` is total
variation distance, which is the only reading that says anything about a diffuse
result. -/
theorem otp_advantage_zero (m : ℝ) :
    advantage (otp_enc (rT := ℝ) m) (otp_ideal (rT := ℝ)) = 0 :=
  advantage_eq_zero_of_limExecV_eq (fun σ => otp_distribution_eq m σ σ)

end ContinuousOTP
end ProbLang
