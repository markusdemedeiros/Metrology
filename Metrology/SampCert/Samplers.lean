import Metrology.SampCert.SLang

/-! # Dynamic embeddings of SampCert samplers

  Each sampler is embedded as a closed ProbLang lambda with all its `ℕ`/`ℕ⁺`
  parameters bound. The embedding hypotheses are of the form:
    `∀ args, IsEmbedding (slangFn args) (.app^k samplerE (as_expr arg₁) ... (as_expr argₖ))`
  and proofs proceed by `probLangApp_isEmbedding` (one β-reduction per λ) followed
  by composition of the inner embedding lemmas.
-/

namespace EmbedSLang
open SLang ProbLang Classical MeasureTheory ProbabilityTheory Measure PMF Measurable
noncomputable section

/-! ## probUniformByteUpperBits — `λ i. (rand 256 ()).toNat >>> (8 - i)` -/

/-- Closed ProbLang expression for `probUniformByteUpperBits`. Takes one runtime Nat
    argument `i` (the number of upper bits to extract). -/
def plProbUniformByteUpperBits (iV bV : Var) : Exp :=
  -- λ i. let b := rand 256 (); b >> (8 - i)
  .lam (Exp.close
    (probLangBind bV probLangUniformByte
      (.binop .shr (.fvar bV)
        (.binop .minus (.lit (.int 8)) (.fvar iV))))
    iV)

theorem plProbUniformByteUpperBits_isEmbedding
    {iV bV : Var} (hiV_bV : iV ≠ bV) (i : Nat) :
    IsEmbedding (SLang.probUniformByteUpperBits i)
                (.app (plProbUniformByteUpperBits iV bV) (as_expr i)) := by
  show IsEmbedding (SLang.probBind SLang.probUniformByte (fun w : UInt8 =>
                       SLang.probPure (w.toNat.shiftRight (8 - i)))) _
  unfold plProbUniformByteUpperBits
  refine probLangApp_isEmbedding (a := i) ?_ ?_
  · -- LC of probLangBind bV byte (binop shr (fvar bV) (binop minus (lit 8) (fvar iV))).
    have hinner_lc : Exp.IsLocallyClosed
        (.binop .shr (.fvar bV) (.binop .minus (.lit (.int 8)) (.fvar iV)) : Exp) :=
      .binop _ (.fvar _) (.binop _ (.lit _) (.fvar _))
    exact .app (Exp.IsLocallyClosed.lam ∅ _ (fun y _ => by
        rw [Exp.open_close_subst_lc bV y _ hinner_lc]
        exact Exp.subst_lc hinner_lc (.fvar _))) (.rand (.lit _) (.lit _))
  -- Push subst through probLangBind. iV ≠ bV (avoids close-binder capture).
  have hsubst : Exp.subst
      (probLangBind bV probLangUniformByte
        (.binop .shr (.fvar bV) (.binop .minus (.lit (.int 8)) (.fvar iV))))
      iV (as_expr i)
      = probLangBind bV probLangUniformByte
          (.binop .shr (.fvar bV) (.binop .minus (.lit (.int 8)) (.lit (.int i)))) := by
    unfold probLangBind probLangUniformByte
    show Exp.app (Exp.lam _) _ = Exp.app (Exp.lam _) _
    rw [show (as_expr i : Exp) = .lit (.int i) from rfl]
    simp only [Exp.subst]
    rw [Exp.subst_close iV bV (.lit (.int i)) _ hiV_bV (by simp [Exp.fv])]
    simp [Exp.subst, hiV_bV, Ne.symm hiV_bV]
  rw [hsubst]
  refine probLangBind_isEmbedding (x := bV) ?_ probLangUniformByte_isEmbedding ?_
  · exact .binop _ (.fvar _) (.binop _ (.lit _) (.lit _))
  intro b
  show IsEmbedding (SLang.probPure (b.toNat.shiftRight (8 - i))) _
  -- subst at bV: `fvar bV` becomes `as_expr b = lit (int b.toNat)`.
  have hsubst2 : Exp.subst
      (.binop .shr (.fvar bV) (.binop .minus (.lit (.int 8)) (.lit (.int i))))
      bV (as_expr b)
      = .binop .shr (.lit (.int b.toNat)) (.binop .minus (.lit (.int 8)) (.lit (.int i))) := by
    show Exp.binop _ _ _ = Exp.binop _ _ _
    simp [Exp.subst]; rfl
  rw [hsubst2]
  refine IsEmbedding.of_limExec_eq (fun σ => ?_) probLangPure_isEmbedding
  -- Two det reductions: minus → lit (8 - i) under [binopR shr], then shr → lit ((b/2^(8-i)).
  have hMinus : DetStep_discrete
      ⟨.binop .minus (.lit (.int 8)) (.lit (.int i)), σ⟩
      ⟨.lit (.int ((8 : Int) - i)), σ⟩ :=
    (DetHeadStep_discrete.binop .lit .lit (op := .minus) rfl σ).toDetStep
  rw [limExec_binopR_step (e1 := .lit (.int b.toNat)) hMinus, limExec_shr_lit_lit]
  -- Numeric equality: (b.toNat : Int) / 2^(8-i).toNat = b.toNat.shiftRight (8-i).
  show limExec ⟨.lit _, σ⟩ = limExec ⟨.lit _, σ⟩
  congr 4
  rw [show b.toNat.shiftRight (8 - i) = b.toNat / 2^(8 - i) from
      Nat.shiftRight_eq_div_pow b.toNat (8 - i)]
  have htoNat : ((8 : Int) - (i : Int)).toNat = 8 - i := by
    by_cases hi : i ≤ 8 <;> omega
  rw [htoNat]; push_cast; rfl

/-! ## probUniformP2 — bridging to `probNatRec`

  SampCert's `probUniformP2 i` is genuinely meta-recursive (decreases by 8 per step).
  We bridge to `probNatRec` form by separating the residue `r := i % 8` (read in
  the OUTER bind, then a `probNatRec` over `i / 8` byte-folds).

  Order matters: SampCert reads the byte BEFORE recursing, while `probNatRec` reads
  the residue first (in the outer bind) then folds bytes. These produce equal SLang
  distributions because the samples are independent (probBind commutes for
  independent distributions). -/

/-- The reformulated `probUniformP2`: read residue `r` first, then `n` bytes, combining
    each via 256 * acc + byte. -/
def probUniformP2_alt (r n : ℕ) : SLang ℕ :=
  SLang.probBind (SLang.probUniformByteUpperBits r) (fun base : ℕ =>
    probNatRec base
      (fun _ acc => SLang.probBind SLang.probUniformByte
          (fun v : UInt8 => SLang.probPure (UInt8.size * acc + v.toNat)))
      n)

/-- Independence-based commutation: for independent SLang distributions, the
    order of `probBind` doesn't matter. We use this to swap the byte-first order
    of SampCert's `probUniformP2` into the residue-first order of `probUniformP2_alt`. -/
theorem probBind_comm {T1 T2 U : Type _} [SLangType T1] [SLangType T2] [SLangType U]
    (s1 : SLang T1) (s2 : SLang T2) (f : T1 → T2 → SLang U) :
    SLang.probBind s1 (fun a => SLang.probBind s2 (fun b => f a b))
    = SLang.probBind s2 (fun b => SLang.probBind s1 (fun a => f a b)) := by
  funext x
  show ∑' a, s1 a * (∑' b, s2 b * f a b x) = ∑' b, s2 b * (∑' a, s1 a * f a b x)
  -- Both sides expand to ∑' a b, s1 a * s2 b * f a b x.
  rw [show (∑' a, s1 a * (∑' b, s2 b * f a b x)) = ∑' a, ∑' b, s1 a * s2 b * f a b x from by
        congr 1; funext a; rw [← ENNReal.tsum_mul_left]; congr 1; funext b; ring]
  rw [show (∑' b, s2 b * (∑' a, s1 a * f a b x)) = ∑' b, ∑' a, s1 a * s2 b * f a b x from by
        congr 1; funext b; rw [← ENNReal.tsum_mul_left]; congr 1; funext a; ring]
  exact ENNReal.tsum_comm

/-- The bridge lemma: `probUniformP2 i = probUniformP2_alt (i % 8) (i / 8)`. -/
theorem probUniformP2_eq_alt (i : ℕ) :
    SLang.probUniformP2 i = probUniformP2_alt (i % 8) (i / 8) := by
  -- Strong induction, decreasing by 8.
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    unfold SLang.probUniformP2
    by_cases hi : i < 8
    · -- i < 8: SampCert's if-branch is upperBits i.
      simp only [hi, ↓reduceIte]
      have hmod : i % 8 = i := Nat.mod_eq_of_lt hi
      have hdiv : i / 8 = 0 := Nat.div_eq_of_lt hi
      rw [hmod, hdiv]
      -- probUniformP2_alt i 0 = bind (upperBits i) (fun base => probNatRec base step 0)
      --                      = bind (upperBits i) (fun base => probPure base)
      --                      = upperBits i.
      unfold probUniformP2_alt
      show _ = SLang.probBind _ _
      have h_inner : (fun base : ℕ => probNatRec base
              (fun (_ : ℕ) (acc : ℕ) => SLang.probBind SLang.probUniformByte fun (v : UInt8) =>
                SLang.probPure (UInt8.size * acc + v.toNat)) 0)
          = SLang.probPure := by funext base; rfl
      rw [h_inner, SLang.bind_pure]
    · -- i ≥ 8: SampCert's else branch: bind byte (fun v => bind (probUniformP2 (i-8)) ...).
      simp only [hi, ↓reduceIte]
      push_neg at hi
      -- IH on i - 8.
      have hlt : i - 8 < i := by omega
      have hih := ih (i - 8) hlt
      -- i / 8 = (i-8)/8 + 1, i % 8 = (i-8) % 8.
      have hdiv : i / 8 = (i - 8) / 8 + 1 := by omega
      have hmod : i % 8 = (i - 8) % 8 := by omega
      rw [hdiv, hmod]
      -- Show: (do let v ← byte; let w ← probUniformP2 (i-8); return 256*w + v.toNat)
      --     = probUniformP2_alt ((i-8)%8) ((i-8)/8 + 1).
      -- Unfold probUniformP2_alt (n+1).
      unfold probUniformP2_alt
      show SLang.probBind _ _ = SLang.probBind _ _
      -- probNatRec base step (n+1) = bind (probNatRec base step n) (step n).
      have hrec : ∀ base : ℕ, probNatRec base
            (fun (_ : ℕ) (acc : ℕ) => SLang.probBind SLang.probUniformByte fun (v : UInt8) =>
              SLang.probPure (UInt8.size * acc + v.toNat)) ((i - 8) / 8 + 1)
          = SLang.probBind (probNatRec base
              (fun (_ : ℕ) (acc : ℕ) => SLang.probBind SLang.probUniformByte fun (v : UInt8) =>
                SLang.probPure (UInt8.size * acc + v.toNat)) ((i - 8) / 8))
            (fun acc => SLang.probBind SLang.probUniformByte fun (v : UInt8) =>
              SLang.probPure (UInt8.size * acc + v.toNat)) := by
        intro base; rfl
      have hrhs : (fun base : ℕ => probNatRec base
              (fun (_ : ℕ) (acc : ℕ) => SLang.probBind SLang.probUniformByte fun (v : UInt8) =>
                SLang.probPure (UInt8.size * acc + v.toNat)) ((i - 8) / 8 + 1))
          = (fun base : ℕ => SLang.probBind (probNatRec base
              (fun (_ : ℕ) (acc : ℕ) => SLang.probBind SLang.probUniformByte fun (v : UInt8) =>
                SLang.probPure (UInt8.size * acc + v.toNat)) ((i - 8) / 8))
            (fun acc => SLang.probBind SLang.probUniformByte fun (v : UInt8) =>
              SLang.probPure (UInt8.size * acc + v.toNat))) := by
        funext base; exact hrec base
      rw [hrhs]
      -- Now RHS: bind (upperBits ((i-8)%8)) (fun base => bind (probNatRec_n) (fun acc => bind byte (fun v => pure ...)))
      -- Refold the inner double-bind via bind_bind:
      -- bind X (fun base => bind (g base) h) = bind (bind X g) h
      rw [← SLang.bind_bind]
      -- Now RHS: bind (bind (upperBits ((i-8)%8)) (fun base => probNatRec_n)) (fun acc => bind byte (fun v => ...))
      -- The inner is exactly probUniformP2_alt ((i-8)%8) ((i-8)/8) = probUniformP2 (i-8) by IH.
      have hbind_eq : SLang.probBind (SLang.probUniformByteUpperBits ((i - 8) % 8))
            (fun base : ℕ => probNatRec base
              (fun (_ : ℕ) (acc : ℕ) => SLang.probBind SLang.probUniformByte fun (v : UInt8) =>
                SLang.probPure (UInt8.size * acc + v.toNat)) ((i - 8) / 8))
          = SLang.probUniformP2 (i - 8) := by
        rw [hih]; rfl
      rw [hbind_eq]
      -- Goal: bind byte (fun v => bind (probUniformP2 (i-8)) (fun w => pure (256*w + v.toNat)))
      --     = bind (probUniformP2 (i-8)) (fun acc => bind byte (fun v => pure (256*acc + v.toNat)))
      show SLang.probBind SLang.probUniformByte (fun v => SLang.probBind (SLang.probUniformP2 (i - 8))
              (fun w => SLang.probPure (UInt8.size * w + v.toNat)))
          = SLang.probBind (SLang.probUniformP2 (i - 8))
            (fun acc => SLang.probBind SLang.probUniformByte
              (fun v => SLang.probPure (UInt8.size * acc + v.toNat)))
      exact probBind_comm SLang.probUniformByte (SLang.probUniformP2 (i - 8))
        (fun v w => SLang.probPure (UInt8.size * w + v.toNat))

/-! ### Closed ProbLang expression for probUniformP2

  `probUniformP2_alt r n` = `bind (upperBits r) (fun base => probNatRec base step n)`
  where `step _ acc = bind byte (fun v => pure (256 * acc + v.toNat))`.

  The dynamic embedding takes `i` runtime, computes `r := i % 8` and `n := i / 8`
  inline, and uses `plProbNatRec_loopE` with `.fvar nV` and `.fvar baseV` for the
  runtime n and base values. -/

/-- ProbLang expression for the byte-fold step: `λ k. λ acc. let v := rand 256 (); 256 * acc + v.toNat`.
    The outer `k` is unused (since the step is index-independent). -/
def plProbUniformP2_step (kV accV vV : Var) : Exp :=
  .lam (Exp.close
    (.lam (Exp.close
      (probLangBind vV probLangUniformByte
        (probLangAdd
          (probLangMul (probLangInt UInt8.size) (.fvar accV))
          (.fvar vV)))
      accV))
    kV)

/-- Closed dynamic ProbLang expression for `probUniformP2`. Takes runtime arg `i`.

    The body, after β-reducing `iV ↦ .lit (.int i)`:
      bind baseV ← upperBits (i % 8); loop (i / 8) baseV step
    where `i % 8` and `i / 8` are computed inline via `binop mod`/`div`.
-/
def plProbUniformP2 (iV baseV f x v xs ws w kV accV vV bV upperBitsIV upperBitsBV : Var) : Exp :=
  .lam (Exp.close
    (probLangBind baseV
      (.app (plProbUniformByteUpperBits upperBitsIV upperBitsBV)
            (.binop .mod (.fvar iV) (.lit (.int 8))))
      (EmbedSLang.plProbNatRec_loopE f x v xs ws w
        (.binop .div (.fvar iV) (.lit (.int 8)))
        (.fvar baseV)
        (plProbUniformP2_step kV accV vV)))
    iV)

/-! ### Reusable LC and freshness facts for the closed ProbLang expressions -/

theorem plProbUniformByteUpperBits_lc (iV bV : Var) :
    Exp.IsLocallyClosed (plProbUniformByteUpperBits iV bV) := by
  unfold plProbUniformByteUpperBits
  apply Exp.IsLocallyClosed.lamClose
  unfold probLangBind probLangUniformByte
  refine .app (Exp.IsLocallyClosed.lam ∅ _ (fun y _ => ?_)) (.rand (.lit _) (.lit _))
  have h : Exp.IsLocallyClosed
      (.binop .shr (.fvar bV) (.binop .minus (.lit (.int 8)) (.fvar iV)) : Exp) :=
    .binop _ (.fvar _) (.binop _ (.lit _) (.fvar _))
  rw [Exp.open_close_subst_lc bV y _ h]
  exact Exp.subst_lc h (.fvar _)

theorem plProbUniformByteUpperBits_fresh {a iV bV : Var}
    (ha_iV : a ≠ iV) (ha_bV : a ≠ bV) :
    a ∉ (plProbUniformByteUpperBits iV bV).fv := by
  unfold plProbUniformByteUpperBits
  apply Exp.close_preserve_not_fvar
  refine probLangBind_fresh ?_ ?_
  · simp [probLangUniformByte, Exp.fv]
  · simp only [Exp.fv, Finset.notMem_union, Finset.notMem_singleton,
               Finset.notMem_empty, not_false_iff]
    exact ⟨ha_bV, by trivial, ha_iV⟩

theorem plProbUniformP2_step_lc' (kV accV vV : Var) :
    Exp.IsLocallyClosed (plProbUniformP2_step kV accV vV) := by
  unfold plProbUniformP2_step
  refine Exp.IsLocallyClosed.lamClose _ (Exp.IsLocallyClosed.lamClose _ ?_)
  unfold probLangBind probLangUniformByte probLangAdd probLangMul probLangInt
  refine .app (Exp.IsLocallyClosed.lam ∅ _ (fun y _ => ?_)) (.rand (.lit _) (.lit _))
  have h : Exp.IsLocallyClosed
      (Exp.binop .plus (.binop .mult (.lit (.int UInt8.size)) (.fvar accV)) (.fvar vV)) :=
    .binop _ (.binop _ (.lit _) (.fvar _)) (.fvar _)
  rw [Exp.open_close_subst_lc vV y _ h]
  exact Exp.subst_lc h (.fvar _)

theorem plProbUniformP2_step_fresh {a kV accV vV : Var}
    (ha_kV : a ≠ kV) (ha_accV : a ≠ accV) (ha_vV : a ≠ vV) :
    a ∉ (plProbUniformP2_step kV accV vV).fv := by
  unfold plProbUniformP2_step
  apply Exp.close_preserve_not_fvar
  apply Exp.close_preserve_not_fvar
  refine probLangBind_fresh ?_ ?_
  · simp [probLangUniformByte, Exp.fv]
  · simp only [probLangAdd, probLangMul, probLangInt, Exp.fv,
               Finset.notMem_union, Finset.notMem_singleton, Finset.notMem_empty, not_false_iff]
    exact ⟨⟨by trivial, ha_accV⟩, ha_vV⟩

/-! ### Embedding theorem -/

/-- The byte-fold step embeds: `(.app (.app stepE (as_expr k)) (as_expr acc))`
    embeds `bind byte (fun v => pure (256 * acc + v.toNat))` (the SLang step). -/
theorem plProbUniformP2_step_isEmbedding {kV accV vV : Var}
    (hkV_accV : kV ≠ accV) (haccV_vV : accV ≠ vV) (hkV_vV : kV ≠ vV)
    (k acc : Nat) :
    IsEmbedding
      (SLang.probBind SLang.probUniformByte (fun v : UInt8 =>
        SLang.probPure (UInt8.size * acc + v.toNat)))
      (.app (.app (plProbUniformP2_step kV accV vV) (as_expr k)) (as_expr acc)) := by
  unfold plProbUniformP2_step
  refine probLangApp2_isEmbedding (b := acc) (a := k) hkV_accV ?_
    (fun a => as_expr_not_fv kV a) (fun a => as_expr_not_fv accV a) ?_
  · -- LC of inner body.
    unfold probLangBind probLangUniformByte probLangAdd probLangMul probLangInt
    refine .app (Exp.IsLocallyClosed.lam ∅ _ (fun y _ => ?_)) (.rand (.lit _) (.lit _))
    have hinner_lc : Exp.IsLocallyClosed
        (Exp.binop .plus (.binop .mult (.lit (.int UInt8.size)) (.fvar accV)) (.fvar vV)) :=
      .binop _ (.binop _ (.lit _) (.fvar _)) (.fvar _)
    rw [Exp.open_close_subst_lc vV y _ hinner_lc]
    exact Exp.subst_lc hinner_lc (.fvar _)
  -- Push subst at accV (preserved by close-binder vV) and at kV (vacuous: kV not free).
  have hsubst1 : Exp.subst (probLangBind vV probLangUniformByte
        (probLangAdd (probLangMul (probLangInt UInt8.size) (.fvar accV)) (.fvar vV)))
      accV (as_expr acc)
      = probLangBind vV probLangUniformByte
          (probLangAdd (probLangMul (probLangInt UInt8.size) (as_expr acc)) (.fvar vV)) := by
    unfold probLangBind probLangUniformByte probLangAdd probLangMul probLangInt
    show Exp.app _ _ = Exp.app _ _
    rw [show (as_expr acc : Exp) = .lit (.int acc) from rfl]
    simp only [Exp.subst]
    rw [Exp.subst_close accV vV (.lit (.int acc)) _ haccV_vV (by simp [Exp.fv])]
    simp [Exp.subst, haccV_vV]
  have hsubst2 : Exp.subst
        (probLangBind vV probLangUniformByte
          (probLangAdd (probLangMul (probLangInt UInt8.size) (as_expr acc)) (.fvar vV)))
        kV (as_expr k)
      = probLangBind vV probLangUniformByte
          (probLangAdd (probLangMul (probLangInt UInt8.size) (as_expr acc)) (.fvar vV)) := by
    apply Exp.subst_fresh
    unfold probLangBind probLangUniformByte probLangAdd probLangMul probLangInt
    simp [Exp.fv, as_expr_fv, hkV_vV]
  rw [hsubst1, hsubst2]
  refine probLangBind_isEmbedding (x := vV)
    (.binop _ (.binop _ (.lit _) (.lit _)) (.fvar _))
    probLangUniformByte_isEmbedding ?_
  intro b
  -- subst at vV: `fvar vV` becomes `lit (int b.toNat)`.
  have hsubst3 : Exp.subst
      (probLangAdd (probLangMul (probLangInt UInt8.size) (as_expr acc)) (.fvar vV))
      vV (as_expr b)
      = .binop .plus (.binop .mult (.lit (.int UInt8.size)) (.lit (.int acc))) (.lit (.int b.toNat)) := by
    unfold probLangAdd probLangMul probLangInt
    show Exp.binop _ _ _ = Exp.binop _ _ _
    simp [Exp.subst]; rfl
  rw [hsubst3]
  refine IsEmbedding.of_limExec_eq (fun σ => ?_) probLangPure_isEmbedding
  -- Two det reductions: mult → lit (256*acc) under [binopL plus (lit b.toNat, val)], then plus → lit (256*acc+b.toNat).
  have hMult : DetStep_discrete
      ⟨.binop .mult (.lit (.int UInt8.size)) (.lit (.int acc)), σ⟩
      ⟨.lit (.int (UInt8.size * acc)), σ⟩ :=
    (DetHeadStep_discrete.binop .lit .lit (op := .mult) (by simp [BinOp.eval]) σ).toDetStep
  rw [limExec_binopL_step .lit hMult, limExec_plus_lit_lit]
  rfl

/-! ### Main embedding theorem for probUniformP2

  Strategy: bridge to `probUniformP2_alt` via `probUniformP2_eq_alt`, then β-reduce
  the outer λ over `i` via `probLangApp_isEmbedding`, then compose
  `probLangBind_isEmbedding` (for upperBits sample) with `plProbNatRec_loop_isEmbedding`. -/
theorem plProbUniformP2_isEmbedding
    {iV baseV f x v xs ws w kV accV vV bV upperBitsIV upperBitsBV : Var}
    (hfx : f ≠ x) (hfv : f ≠ v) (hxv : x ≠ v)
    (hxs_ws : xs ≠ ws) (hxs_w : xs ≠ w) (hws_w : ws ≠ w)
    (hxsf : xs ≠ f) (hxsx : xs ≠ x) (hxsv : xs ≠ v)
    (hwsf : ws ≠ f) (hwsx : ws ≠ x) (hwsv : ws ≠ v)
    (hwf : w ≠ f) (hwx : w ≠ x) (hwv : w ≠ v)
    (hkV_accV : kV ≠ accV) (hkV_vV : kV ≠ vV) (haccV_vV : accV ≠ vV)
    (hiV_baseV : iV ≠ baseV) (hiV_w : iV ≠ w)
    (hupperBitsIV_BV : upperBitsIV ≠ upperBitsBV)
    -- iV must be fresh wrt all other Vars to handle subst correctly.
    (hiV_f : iV ≠ f) (hiV_x : iV ≠ x) (hiV_v : iV ≠ v)
    (hiV_xs : iV ≠ xs) (hiV_ws : iV ≠ ws)
    (hiV_kV : iV ≠ kV) (hiV_accV : iV ≠ accV) (hiV_vV : iV ≠ vV)
    (hiV_upperBitsIV : iV ≠ upperBitsIV) (hiV_upperBitsBV : iV ≠ upperBitsBV)
    (hbaseV_f : baseV ≠ f) (hbaseV_x : baseV ≠ x) (hbaseV_v : baseV ≠ v)
    (hbaseV_xs : baseV ≠ xs) (hbaseV_ws : baseV ≠ ws) (hbaseV_w : baseV ≠ w)
    (hbaseV_kV : baseV ≠ kV) (hbaseV_accV : baseV ≠ accV) (hbaseV_vV : baseV ≠ vV)
    (hbaseV_upperBitsIV : baseV ≠ upperBitsIV) (hbaseV_upperBitsBV : baseV ≠ upperBitsBV)
    (i : Nat) :
    IsEmbedding (SLang.probUniformP2 i)
                (.app (plProbUniformP2 iV baseV f x v xs ws w kV accV vV bV
                                        upperBitsIV upperBitsBV) (as_expr i)) := by
  rw [probUniformP2_eq_alt]
  -- After β: body of plProbUniformP2 with iV substituted by lit (.int i).
  unfold plProbUniformP2
  refine probLangApp_isEmbedding (a := i) ?_ ?_
  · -- LC of body before β.
    -- Body = probLangBind baseV (.app upperBits (binop mod (fvar iV) 8))
    --                             (loopE (binop div (fvar iV) 8) (fvar baseV) step)
    -- = .app (.lam (close LoopBody baseV)) (.app upperBits (...))
    have hupperBits_lc : Exp.IsLocallyClosed
        (plProbUniformByteUpperBits upperBitsIV upperBitsBV) := by
      unfold plProbUniformByteUpperBits
      have hbody_lc : Exp.IsLocallyClosed
          (probLangBind upperBitsBV probLangUniformByte
            (.binop .shr (.fvar upperBitsBV)
              (.binop .minus (.lit (.int 8)) (.fvar upperBitsIV)))) := by
        unfold probLangBind probLangUniformByte
        refine .app ?_ (.rand (.lit _) (.lit _))
        refine .lam ∅ _ (fun y _ => ?_)
        have hi_lc : Exp.IsLocallyClosed
            (.binop .shr (.fvar upperBitsBV)
              (.binop .minus (.lit (.int 8)) (.fvar upperBitsIV)) : Exp) :=
          .binop _ (.fvar _) (.binop _ (.lit _) (.fvar _))
        rw [Exp.open_close_subst_lc upperBitsBV y _ hi_lc]
        exact Exp.subst_lc hi_lc (.fvar _)
      exact Exp.IsLocallyClosed.lamClose _ hbody_lc
    have hupperBitsCall_lc : Exp.IsLocallyClosed
        (.app (plProbUniformByteUpperBits upperBitsIV upperBitsBV)
              (.binop .mod (.fvar iV) (.lit (.int 8)))) :=
      .app hupperBits_lc (.binop _ (.fvar _) (.lit _))
    have hstep_lc : Exp.IsLocallyClosed (plProbUniformP2_step kV accV vV) := by
      unfold plProbUniformP2_step
      have hinner_lc : Exp.IsLocallyClosed
          (probLangBind vV probLangUniformByte
            (probLangAdd (probLangMul (probLangInt UInt8.size) (.fvar accV)) (.fvar vV))) := by
        unfold probLangBind probLangUniformByte probLangAdd probLangMul probLangInt
        refine .app ?_ (.rand (.lit _) (.lit _))
        refine .lam ∅ _ (fun y _ => ?_)
        have hh : Exp.IsLocallyClosed
            (Exp.binop .plus (.binop .mult (.lit (.int UInt8.size)) (.fvar accV)) (.fvar vV)) :=
          .binop _ (.binop _ (.lit _) (.fvar _)) (.fvar _)
        rw [Exp.open_close_subst_lc vV y _ hh]
        exact Exp.subst_lc hh (.fvar _)
      exact Exp.IsLocallyClosed.lamClose _ (Exp.IsLocallyClosed.lamClose _ hinner_lc)
    have hloopE_lc : Exp.IsLocallyClosed
        (EmbedSLang.plProbNatRec_loopE f x v xs ws w
          (.binop .div (.fvar iV) (.lit (.int 8)))
          (.fvar baseV)
          (plProbUniformP2_step kV accV vV)) := by
      unfold plProbNatRec_loopE probLangBind probLangWhile plProbNatRec_condE plProbNatRec_bodyE
      -- This is .app (.lam (close (.snd (.fvar w)) w)) (probLangWhile ... (.pair ... ))
      refine .app ?_ ?_
      · -- LC of .lam (close (.snd (.fvar w)) w)
        exact Exp.IsLocallyClosed.lamClose _ (.snd (.fvar _))
      · -- LC of probLangWhile ... = .app (.fix (close (.lam (close body f)) f)) initE
        refine .app ?_ ?_
        · -- LC of .fix (close (.lam (close body f)) f).
          have hcondE_lc : Exp.IsLocallyClosed
              (Exp.lam (Exp.close
                (.binop .lt (.fst (.fvar xs)) (.binop .div (.fvar iV) (.lit (.int 8)))) xs)) := by
            apply Exp.IsLocallyClosed.lamClose
            exact .binop _ (.fst (.fvar _)) (.binop _ (.fvar _) (.lit _))
          have hbodyE_lc : Exp.IsLocallyClosed
              (Exp.lam (Exp.close
                (probLangBind ws
                  (.app (.app (plProbUniformP2_step kV accV vV) (.fst (.fvar xs))) (.snd (.fvar xs)))
                  (.pair (.binop .plus (.fst (.fvar xs)) (.lit (.int 1))) (.fvar ws))) xs)) := by
            apply Exp.IsLocallyClosed.lamClose
            unfold probLangBind
            refine .app ?_ (.app (.app hstep_lc (.fst (.fvar _))) (.snd (.fvar _)))
            apply Exp.IsLocallyClosed.lamClose
            exact .pair (.binop _ (.fst (.fvar _)) (.lit _)) (.fvar _)
          -- inner body of fix = .cond (.app condE (fvar x)) (probLangBind v (...) (.app (fvar f) (fvar v))) (fvar x)
          have hinner_lc : Exp.IsLocallyClosed
              (Exp.cond (.app
                (Exp.lam (Exp.close (.binop .lt (.fst (.fvar xs)) (.binop .div (.fvar iV) (.lit (.int 8)))) xs))
                (.fvar x))
                (probLangBind v
                  (.app (Exp.lam (Exp.close (probLangBind ws
                    (.app (.app (plProbUniformP2_step kV accV vV) (.fst (.fvar xs))) (.snd (.fvar xs)))
                    (.pair (.binop .plus (.fst (.fvar xs)) (.lit (.int 1))) (.fvar ws))) xs))
                  (.fvar x))
                  (.app (.fvar f) (.fvar v)))
                (.fvar x)) := by
            refine .cond (.app hcondE_lc (.fvar _)) ?_ (.fvar _)
            unfold probLangBind
            refine .app ?_ (.app hbodyE_lc (.fvar _))
            apply Exp.IsLocallyClosed.lamClose
            exact .app (.fvar _) (.fvar _)
          have houter_lc : Exp.IsLocallyClosed
              (Exp.lam (Exp.close (.cond (.app
                (Exp.lam (Exp.close (.binop .lt (.fst (.fvar xs)) (.binop .div (.fvar iV) (.lit (.int 8)))) xs))
                (.fvar x))
                (probLangBind v
                  (.app (Exp.lam (Exp.close (probLangBind ws
                    (.app (.app (plProbUniformP2_step kV accV vV) (.fst (.fvar xs))) (.snd (.fvar xs)))
                    (.pair (.binop .plus (.fst (.fvar xs)) (.lit (.int 1))) (.fvar ws))) xs))
                  (.fvar x))
                  (.app (.fvar f) (.fvar v)))
                (.fvar x)) x)) :=
            Exp.IsLocallyClosed.lamClose _ hinner_lc
          refine Exp.IsLocallyClosed.fix ∅ _ (fun y _ => ?_)
          rw [Exp.open_close_subst_lc f y _ houter_lc]
          exact Exp.subst_lc houter_lc (.fvar _)
        · -- LC of init = .pair (.lit 0) (.fvar baseV)
          exact .pair (.lit _) (.fvar _)
    -- Now we have LCs for upperBitsCall and loopE. The full body LC:
    -- .app (.lam (close loopE baseV)) upperBitsCall
    refine .app ?_ hupperBitsCall_lc
    apply Exp.IsLocallyClosed.lamClose
    exact hloopE_lc
  · -- IsEmbedding (probUniformP2_alt (i % 8) (i / 8)) (subst body iV (.lit (.int i)))
    -- We need to compute the subst explicitly, then apply probLangBind_isEmbedding.
    -- Hypothesis we need: iV doesn't appear in upperBits, step, f/x/v/xs/ws/w/baseV (outer).
    -- We have hiV_* hypotheses establishing these.
    -- Decision: rather than chase freshness manually, parameterize the theorem to
    -- TAKE these as hypotheses. The user supplies them when invoking.
    -- Since we already pass hiV_* freshness against individual Vars, and the Vars
    -- are the only fv contributors to the closed lambdas, iV ∉ ... follows.
    -- For now, sorry (with TODO):
    -- iV ∉ (plProbUniformByteUpperBits ...).fv: iV differs from both upperBitsIV and upperBitsBV,
    -- and these are the only fvar names in the closed expression.
    have hiV_upperBits : iV ∉ (plProbUniformByteUpperBits upperBitsIV upperBitsBV).fv := by
      unfold plProbUniformByteUpperBits probLangBind probLangUniformByte
      -- Show that iV doesn't appear in the innermost expression (.binop shr (fvar bV) (binop minus (lit 8) (fvar iV))).
      have h_inner_no_iV : iV ∉ (Exp.binop .shr (.fvar upperBitsBV)
                            (Exp.binop .minus (.lit (.int 8)) (.fvar upperBitsIV)) : Exp).fv := by
        show iV ∉ (_ ∪ _ : Finset Var)
        rw [Finset.mem_union, not_or]
        refine ⟨?_, ?_⟩
        · show iV ∉ ({upperBitsBV} : Finset Var)
          rw [Finset.mem_singleton]; exact hiV_upperBitsBV
        · show iV ∉ (_ ∪ _ : Finset Var)
          rw [Finset.mem_union, not_or]
          refine ⟨by simp [Exp.fv], ?_⟩
          show iV ∉ ({upperBitsIV} : Finset Var)
          rw [Finset.mem_singleton]; exact hiV_upperBitsIV
      change iV ∉ (Exp.lam _).fv
      simp only [Exp.fv]
      apply Exp.close_preserve_not_fvar
      change iV ∉ (Exp.app _ _).fv
      simp only [Exp.fv, Finset.mem_union, not_or]
      refine ⟨?_, ?_⟩
      · apply Exp.close_preserve_not_fvar
        exact h_inner_no_iV
      · simp [Exp.fv]
    have hiV_step : iV ∉ (plProbUniformP2_step kV accV vV).fv := by
      unfold plProbUniformP2_step probLangBind probLangUniformByte probLangAdd probLangMul probLangInt
      have h_inner_no_iV : iV ∉ (Exp.binop .plus
                            (Exp.binop .mult (.lit (.int UInt8.size)) (.fvar accV)) (.fvar vV) : Exp).fv := by
        show iV ∉ (_ ∪ _ : Finset Var)
        rw [Finset.mem_union, not_or]
        refine ⟨?_, ?_⟩
        · show iV ∉ (_ ∪ _ : Finset Var)
          rw [Finset.mem_union, not_or]
          refine ⟨by simp [Exp.fv], ?_⟩
          show iV ∉ ({accV} : Finset Var)
          rw [Finset.mem_singleton]; exact hiV_accV
        · show iV ∉ ({vV} : Finset Var)
          rw [Finset.mem_singleton]; exact hiV_vV
      simp only [Exp.fv]
      apply Exp.close_preserve_not_fvar
      simp only [Exp.fv]
      apply Exp.close_preserve_not_fvar
      simp only [Exp.fv, Finset.mem_union, not_or]
      refine ⟨?_, ?_⟩
      · apply Exp.close_preserve_not_fvar
        exact h_inner_no_iV
      · simp [Exp.fv]
    -- Compute the subst.
    -- Compute subst step by step. The probLangBind is .app (.lam (close body baseV)) e1.
    -- subst pushes through: .app, .lam (subst goes inside via subst_lamClose with iV ≠ baseV), close.
    -- Inside, the binop mod has (fvar iV) which becomes (lit i).
    -- The plProbNatRec_loopE body has nE := (binop div (fvar iV) (lit 8)) which becomes (lit i / lit 8).
    -- The fvar baseV stays (since iV ≠ baseV).
    -- Other fvars (f/x/v/xs/ws/w/etc.) are unaffected (iV differs from all).
    -- Helper for the close-fresh facts (we'll need this many times below).
    have hi_emp : (as_expr i).fv = (∅ : Finset Var) := rfl
    have hwi : w ∉ (as_expr i).fv := by rw [hi_emp]; simp
    have hxi : x ∉ (as_expr i).fv := by rw [hi_emp]; simp
    have hvi : v ∉ (as_expr i).fv := by rw [hi_emp]; simp
    have hfi : f ∉ (as_expr i).fv := by rw [hi_emp]; simp
    have hxsi : xs ∉ (as_expr i).fv := by rw [hi_emp]; simp
    have hwsi : ws ∉ (as_expr i).fv := by rw [hi_emp]; simp
    have hbaseVi : baseV ∉ (as_expr i).fv := by rw [hi_emp]; simp
    have hiV_loopE_internals :
        Exp.subst (EmbedSLang.plProbNatRec_loopE f x v xs ws w
            (.binop .div (.fvar iV) (.lit (.int 8)))
            (.fvar baseV)
            (plProbUniformP2_step kV accV vV))
          iV (as_expr i)
        = EmbedSLang.plProbNatRec_loopE f x v xs ws w
            (.binop .div (.lit (.int i)) (.lit (.int 8)))
            (.fvar baseV)
            (plProbUniformP2_step kV accV vV) := by
      sorry
    have hsubst_body : Exp.subst
        (probLangBind baseV
          (.app (plProbUniformByteUpperBits upperBitsIV upperBitsBV)
                (.binop .mod (.fvar iV) (.lit (.int 8))))
          (EmbedSLang.plProbNatRec_loopE f x v xs ws w
            (.binop .div (.fvar iV) (.lit (.int 8)))
            (.fvar baseV)
            (plProbUniformP2_step kV accV vV)))
        iV (as_expr i)
        = probLangBind baseV
            (.app (plProbUniformByteUpperBits upperBitsIV upperBitsBV)
                  (.binop .mod (.lit (.int i)) (.lit (.int 8))))
            (EmbedSLang.plProbNatRec_loopE f x v xs ws w
              (.binop .div (.lit (.int i)) (.lit (.int 8)))
              (.fvar baseV)
              (plProbUniformP2_step kV accV vV)) := by
      unfold probLangBind
      show Exp.app _ _ = Exp.app _ _
      simp only [Exp.subst]
      congr 1
      · -- .lam (close loopE-body baseV) under subst iV (lit i).
        rw [Exp.subst_close iV baseV (as_expr i) _ hiV_baseV (by simp [Exp.fv]),
            hiV_loopE_internals]
      · -- .app upperBits (binop mod (fvar iV) (lit 8))
        congr 1
        exact Exp.subst_fresh iV _ _ hiV_upperBits
    rw [hsubst_body]
    sorry

-- Helper: the step lambda is LC.
theorem plProbUniformP2_step_lc (kV accV vV : Var) (hkV_accV : kV ≠ accV)
    (hkV_vV : kV ≠ vV) (haccV_vV : accV ≠ vV) :
    Exp.IsLocallyClosed (plProbUniformP2_step kV accV vV) := by
  unfold plProbUniformP2_step
  have hbody_lc : Exp.IsLocallyClosed
      (probLangBind vV probLangUniformByte
        (probLangAdd (probLangMul (probLangInt UInt8.size) (.fvar accV)) (.fvar vV))) := by
    unfold probLangBind probLangUniformByte probLangAdd probLangMul probLangInt
    refine .app ?_ (.rand (.lit _) (.lit _))
    refine .lam ∅ _ (fun y _ => ?_)
    have hinner_lc : Exp.IsLocallyClosed
        (Exp.binop .plus (.binop .mult (.lit (.int UInt8.size)) (.fvar accV)) (.fvar vV)) :=
      .binop _ (.binop _ (.lit _) (.fvar _)) (.fvar _)
    rw [Exp.open_close_subst_lc vV y _ hinner_lc]
    exact Exp.subst_lc hinner_lc (.fvar _)
  refine .lam ∅ _ (fun y _ => ?_)
  have hclose_inner_lc : Exp.IsLocallyClosed
      (Exp.lam (Exp.close
        (probLangBind vV probLangUniformByte
          (probLangAdd (probLangMul (probLangInt UInt8.size) (.fvar accV)) (.fvar vV))) accV)) := by
    refine .lam ∅ _ (fun z _ => ?_)
    rw [Exp.open_close_subst_lc accV z _ hbody_lc]
    exact Exp.subst_lc hbody_lc (.fvar _)
  rw [Exp.open_close_subst_lc kV y _ hclose_inner_lc]
  exact Exp.subst_lc hclose_inner_lc (.fvar _)

end
end EmbedSLang

/-
noncomputable section

open EmbedSLang ProbLang

/-! ## probUntil combinator -/

-- def probUntil (body : SLang T) (cond : T → Bool) : SLang T := do
--   let v ← body
--   probWhile (λ v : T => ¬ cond v) (λ _ : T => body) v
def plProbUntil (f x dummy : String) (bodyE condE : Exp) : Exp :=
  probLangBind (.named x) bodyE
    (probLangWhile f x dummy
      (probLangNot (probLangApp condE (Exp.var x)))  -- ¬ cond v
      (probLangLam dummy bodyE)                       -- fun _ => body
      (Exp.var x))                                    -- init = v

/-! ## UniformSample -/

-- def UniformSample (n : PNat) : SLang Nat := do
--   let r ← probUntil (UniformPowerOfTwoSample (2 * n)) (λ x : Nat => x < n)
--   return r
-- Uniform over {0, ..., n-1} via rejection sampling from rand (n-1).
-- rand (n-1) gives uniform over {0, ..., n-1} directly when n is a power of two.
-- For general n, we use probUntil with rand on a sufficiently large range.
def plUniformSample (n : ℕ) : Exp :=
  plProbUntil "f" "r" "r'"
    (.rand (probLangInt (n - 1)) probLangUnit)  -- rand(n-1, ()) samples {0,...,n-1}
    (probLangLam "x" (probLangLt (Exp.var "x") (probLangInt n)))

/-! ## BernoulliSample -/

-- def BernoulliSample (num : Nat) (den : PNat) (_ : num ≤ den) : SLang Bool := do
--   let d ← UniformSample den
--   return d < num
def plBernoulliSample (num den : ℕ) : Exp :=
  probLangBind (.named "d") (plUniformSample den)
    (probLangLt (Exp.var "d") (probLangInt num))

/-! ## Geometric sampler -/

-- variable (trial : SLang Bool)
-- def geoLoopCond (st : Bool × ℕ) : Bool := st.1
-- def geoLoopBody (st : Bool × ℕ) : SLang (Bool × ℕ):= do
--   let x ← trial
--   return (x,st.2 + 1)
-- def probGeometric : SLang ℕ := do
--   let st ← probWhile geoLoopCond (geoLoopBody trial) (true,0)
--   return st.2
def plGeoLoopBody (trialE : Exp) : Exp :=
  probLangLam "st"
    (probLangBind (.named "x") trialE
      (probLangPair (Exp.var "x")
        (probLangAdd (probLangSnd (Exp.var "st")) (probLangInt 1))))

def plProbGeometric (trialE : Exp) : Exp :=
  probLangBind (.named "st")
    (probLangWhile "f" "st" "x"
      (probLangFst (Exp.var "st"))
      (plGeoLoopBody trialE)
      (probLangPair (probLangBool true) (probLangInt 0)))
    (probLangSnd (Exp.var "st"))

/-! ## BernoulliExpNeg -/

-- def BernoulliExpNegSampleUnitLoop (num : Nat) (den : PNat) (wf : num ≤ den)
--     (state : (Bool × PNat)) : SLang (Bool × PNat) := do
--   let A ← BernoulliSample num (state.2 * den) (halve_wf num den state.2 wf)
--   return (A, state.2 + 1)
-- Note: BernoulliSample depends on state.2 * den as denominator.
-- Since the denominator is dynamic (depends on state), we inline the
-- uniform sampler using rand.
def plBernoulliExpNegUnitLoop (num den : ℕ) : Exp :=
  probLangLam "state"
    (let dynDen := probLangMul (probLangSnd (Exp.var "state")) (probLangInt den)
     probLangBind (.named "d")
      (.rand (probLangSub dynDen (probLangInt 1)) probLangUnit)  -- rand(dynDen-1, ())
      (probLangBind (.named "a")
        (probLangCond (probLangLt (Exp.var "d") (probLangInt num))
          (probLangBool true) (probLangBool false))
        (probLangPair (Exp.var "a")
          (probLangAdd (probLangSnd (Exp.var "state")) (probLangInt 1)))))

-- def BernoulliExpNegSampleUnitAux (num : Nat) (den : PNat) (wf : num ≤ den) : SLang Nat := do
--   let r ← probWhile (λ state : Bool × PNat => state.1)
--     (BernoulliExpNegSampleUnitLoop num den wf) (true,1)
--   return r.2
def plBernoulliExpNegUnitAux (num den : ℕ) : Exp :=
  probLangBind (.named "r")
    (probLangWhile "f" "state" "s'"
      (probLangFst (Exp.var "state"))
      (plBernoulliExpNegUnitLoop num den)
      (probLangPair (probLangBool true) (probLangInt 1)))
    (probLangSnd (Exp.var "r"))

-- def BernoulliExpNegSampleUnit (num : Nat) (den : PNat) (wf : num ≤ den) : SLang Bool := do
--   let K ← BernoulliExpNegSampleUnitAux num den wf
--   if K % 2 = 0 then return true else return false
def plBernoulliExpNegUnit (num den : ℕ) : Exp :=
  probLangBind (.named "k")
    (plBernoulliExpNegUnitAux num den)
    (probLangCond
      (probLangEq (probLangMod (Exp.var "k") (probLangInt 2)) (probLangInt 0))
      (probLangBool true)
      (probLangBool false))

-- def BernoulliExpNegSampleGenLoop (iter : Nat) : SLang Bool := do
--   if iter = 0 then return true
--   else
--     let B ← BernoulliExpNegSampleUnit 1 1 (le_refl 1)
--     if ¬ B then return B else
--       let R ← BernoulliExpNegSampleGenLoop (iter - 1)
--       return R
-- Encoding: while loop with state = (result : Bool, remaining : Int)
-- while remaining > 0 && result:  result ← unit(1,1);  remaining -= 1
def plBernoulliExpNegGenLoop (iter : ℕ) : Exp :=
  probLangBind (.named "st")
    (probLangWhile "f" "st" "st'"
      (probLangAnd
        (probLangFst (Exp.var "st"))
        (probLangNot (probLangEq (probLangSnd (Exp.var "st")) (probLangInt 0))))
      (probLangLam "st"
        (probLangBind (.named "b") (plBernoulliExpNegUnit 1 1)
          (probLangPair (Exp.var "b")
            (probLangSub (probLangSnd (Exp.var "st")) (probLangInt 1)))))
      (probLangPair (probLangBool true) (probLangInt iter)))
    (probLangFst (Exp.var "st"))

-- def BernoulliExpNegSample (num : Nat) (den : PNat) : SLang Bool := ...
-- Complex: branches on num ≤ den statically. For now, only handle the num ≤ den case.
-- def BernoulliExpNegSample (num : Nat) (den : PNat) : SLang Bool := do
--   if h : num ≤ den
--   then let X ← BernoulliExpNegSampleUnit num den h
--        return X
--   else
--     let gamf := num / den
--     let B ← BernoulliExpNegSampleGenLoop (gamf)
--     if B
--     then
--       let X ← BernoulliExpNegSampleUnit (num % den) den (rat_less_floor_le1 num den)
--       return X
--     else return false
-- Full version: uses dynamic branching on num ≤ den
def plBernoulliExpNegSample (num den : ℕ) : Exp :=
  probLangCond (probLangNot (probLangLt (probLangInt den) (probLangInt num)))  -- num ≤ den
    (plBernoulliExpNegUnit num den)
    (probLangBind (.named "b") (plBernoulliExpNegGenLoop (num / den))
      (probLangCond (Exp.var "b")
        (plBernoulliExpNegUnit (num % den) den)
        (probLangBool false)))

-- def DiscreteLaplaceGenSample (num : PNat) (den : PNat) (μ : ℤ) : SLang ℤ := do
--   let s ← DiscreteLaplaceSample num den
--   return s + μ
def plDiscreteLaplaceGenSample (laplaceSamplerE : Exp) (μ : Int) : Exp :=
  probLangBind (.named "s") laplaceSamplerE
    (probLangAdd (Exp.var "s") (probLangInt μ))

/-! ## Laplace sampler -/

-- def DiscreteLaplaceSampleLoopIn1Aux (t : PNat) : SLang (Nat × Bool) := do
--   let U ← UniformSample t
--   let D ← BernoulliExpNegSample U t
--   return (U,D)
-- Note: BernoulliExpNegSample takes dynamic (U, t). Since U is runtime,
-- we pass it via a lambda. bernExpNegE is a function: numerator → Bool sampler.
def plLaplaceSampleLoopIn1Aux (t : ℕ) (bernExpNegE : Exp) : Exp :=
  probLangBind (.named "u") (plUniformSample t)
    (probLangBind (.named "d") (probLangApp bernExpNegE (Exp.var "u"))
      (probLangPair (Exp.var "u") (Exp.var "d")))

-- def DiscreteLaplaceSampleLoopIn1 (t : PNat) : SLang Nat := do
--   let r1 ← probUntil (DiscreteLaplaceSampleLoopIn1Aux t) (λ x : Nat × Bool => x.2)
--   return r1.1
def plLaplaceSampleLoopIn1 (t : ℕ) (bernExpNegE : Exp) : Exp :=
  probLangBind (.named "r1")
    (plProbUntil "f" "x" "x'"
      (plLaplaceSampleLoopIn1Aux t bernExpNegE)
      (probLangLam "x" (probLangSnd (Exp.var "x"))))
    (probLangFst (Exp.var "r1"))

-- def DiscreteLaplaceSampleLoopIn2Aux (num : Nat) (den : PNat)
--     (K : Bool × Nat) : SLang (Bool × Nat) := do
--   let A ← BernoulliExpNegSample num den
--   return (A, K.2 + 1)
def plLaplaceSampleLoopIn2Aux (num den : ℕ) : Exp :=
  probLangLam "k"
    (probLangBind (.named "a") (plBernoulliExpNegSample num den)
      (probLangPair (Exp.var "a")
        (probLangAdd (probLangSnd (Exp.var "k")) (probLangInt 1))))

-- def DiscreteLaplaceSampleLoopIn2 (num : Nat) (den : PNat) : SLang Nat := do
--   let r2 ← probWhile (λ K : Bool × Nat => K.1)
--     (DiscreteLaplaceSampleLoopIn2Aux num den) (true,0)
--   return r2.2
def plLaplaceSampleLoopIn2 (num den : ℕ) : Exp :=
  probLangBind (.named "r2")
    (probLangWhile "f" "k" "k'"
      (probLangFst (Exp.var "k"))
      (plLaplaceSampleLoopIn2Aux num den)
      (probLangPair (probLangBool true) (probLangInt 0)))
    (probLangSnd (Exp.var "r2"))

-- def DiscreteLaplaceSampleLoop (num : PNat) (den : PNat) : SLang (Bool × Nat) := do
--   let v ← DiscreteLaplaceSampleLoopIn2 den num
--   let V := v - 1
--   let B ← BernoulliSample 1 2 (Nat.le.step Nat.le.refl)
--   return (B,V)
def plLaplaceSampleLoop (num den : ℕ) : Exp :=
  probLangBind (.named "v") (plLaplaceSampleLoopIn2 den num)
    (probLangBind (.named "b") (plBernoulliSample 1 2)
      (probLangPair (Exp.var "b")
        (probLangSub (Exp.var "v") (probLangInt 1))))

-- def DiscreteLaplaceSample (num den : PNat) : SLang ℤ := do
--   let r ← probUntil (DiscreteLaplaceSampleLoop num den)
--     (λ x : Bool × Nat => ¬ (x.1 ∧ x.2 = 0))
--   let Z : Int := if r.1 then - r.2 else r.2
--   return Z
def plDiscreteLaplaceSample (num den : ℕ) : Exp :=
  probLangBind (.named "r")
    (plProbUntil "f" "x" "x'"
      (plLaplaceSampleLoop num den)
      (probLangLam "x"
        (probLangNot
          (probLangAnd
            (probLangFst (Exp.var "x"))
            (probLangEq (probLangSnd (Exp.var "x")) (probLangInt 0))))))
    (probLangCond (probLangFst (Exp.var "r"))
      (probLangNegInt (probLangSnd (Exp.var "r")))
      (probLangSnd (Exp.var "r")))

/-! ## Gaussian sampler -/

-- def DiscreteGaussianSampleLoop (num den t : PNat) (mix : ℕ) : SLang (Int × Bool) := do
--   let Y : Int ← DiscreteLaplaceSampleMixed t 1 mix
--   let y : Nat := Int.natAbs Y
--   let n : Nat := (Int.natAbs (Int.sub (y * t * den) num))^2
--   let d : PNat := 2 * num * t^2 * den
--   let C ← BernoulliExpNegSample n d
--   return (Y,C)
-- abs(e) = if e < 0 then -e else e;  e^2 = e * e
-- BernoulliExpNegSample takes dynamic (n, d) — we use a lambda.
def plAbsInt (e : Exp) : Exp :=
  probLangCond (probLangLt e (probLangInt 0)) (probLangNegInt e) e

def plSquare (e : Exp) : Exp := probLangMul e e

def plDiscreteGaussianSampleLoop (num den t : ℕ) (laplaceMixedE bernExpNegDynE : Exp) : Exp :=
  probLangBind (.named "Y") laplaceMixedE
    (let y := plAbsInt (Exp.var "Y")
     let raw := probLangSub
       (probLangMul (probLangMul y (probLangInt t)) (probLangInt den))
       (probLangInt num)
     let n := plSquare (plAbsInt raw)
     let d := probLangMul
       (probLangMul (probLangInt 2)
         (probLangMul (probLangInt num)
           (probLangMul (plSquare (probLangInt t)) (probLangInt den))))
       (probLangInt 1)
     probLangBind (.named "C") (probLangApp (probLangApp bernExpNegDynE n) d)
       (probLangPair (Exp.var "Y") (Exp.var "C")))

-- def DiscreteGaussianSample (num : PNat) (den : PNat) (mix : ℕ) : SLang ℤ := do
--   let r ← probUntil (DiscreteGaussianSampleLoop num den t mix) (λ x : Int × Bool => x.2)
--   return r.1
def plDiscreteGaussianSample (gaussianLoopE : Exp) : Exp :=
  probLangBind (.named "r")
    (plProbUntil "f" "x" "x'"
      gaussianLoopE
      (probLangLam "x" (probLangSnd (Exp.var "x"))))
    (probLangFst (Exp.var "r"))

-- def DiscreteGaussianGenSample (num : PNat) (den : PNat) (μ : ℤ) : SLang ℤ := do
--   let s ← DiscreteGaussianSample num den 7
--   return s + μ
def plDiscreteGaussianGenSample (gaussianSamplerE : Exp) (μ : Int) : Exp :=
  probLangBind (.named "s") gaussianSamplerE
    (probLangAdd (Exp.var "s") (probLangInt μ))
-/
