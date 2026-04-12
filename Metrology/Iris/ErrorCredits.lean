import Iris
import Mathlib.Probability.Kernel.Basic
import Mathlib.Data.ENNReal.Basic
import Mathlib.MeasureTheory.Measure.Sub
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Iris.Algebra.View
import Iris.Instances.IProp.Instance
import Iris.Algebra.Auth
import Iris.Algebra.Numbers

import Metrology.Iris.Algebra

noncomputable section

open Std Iris COFE ProbabilityTheory MeasureTheory

abbrev ErrorCredit : Type _ := ENNReal

instance : COFE ErrorCredit := COFE.ofDiscrete _ Eq_Equivalence
instance : OFE.Discrete ErrorCredit := ⟨id⟩

instance : CMRA ErrorCredit where
  pcore _ := some 0
  op := (· + ·)
  ValidN _ ε := ε < 1
  Valid ε := ε < 1
  op_ne.ne _ _ _ h := by rw [h]
  pcore_ne _ := by rintro ⟨rfl⟩; exists 0
  validN_ne {_ _ _} := by rintro ⟨rfl⟩; exact id
  valid_iff_validN := .symm <| forall_const Nat
  validN_succ := (·)
  validN_op_left {n x y} H := lt_of_add_lt_of_nonneg_left H (zero_le y)
  assoc {_ _ _} := (add_assoc ..).symm
  comm {_ _} := (add_comm ..).symm
  pcore_op_left {_ _} := by rintro ⟨rfl⟩; simp [OFE.Equiv]
  pcore_idem := by simp
  pcore_op_mono {_ _} := by rintro ⟨rfl⟩ _; exists 0; simp
  extend _ h := ⟨_, _, OFE.discrete h, .rfl, .rfl⟩

instance : UCMRA ErrorCredit where
  unit := 0
  unit_valid := by simp [CMRA.Valid]
  unit_left_id := by simp [CMRA.op]
  pcore_unit := by simp [CMRA.pcore]

theorem ErrorCredit.included_iff {ε₁ ε₂ : ErrorCredit} : ε₁ ≼ ε₂ ↔ ε₁ ≤ ε₂ := by
  refine ⟨?_, (⟨ε₂ - ε₁, add_tsub_cancel_of_le · |>.symm⟩)⟩
  rintro ⟨ε₃, rfl⟩
  exact le_self_add

instance {ε : ErrorCredit} : CMRA.Cancelable ε where
  cancelableN {n ε₁ ε₂} := by
    simp [CMRA.ValidN, CMRA.op, OFE.Dist]
    intro H1 H2
    -- refine (ENNReal.toReal_eq_toReal_iff' ?_ ?_).mp ?_
    -- · rintro rfl; simp at H1
    -- · rintro rfl
    --   simp only [add_top, ENNReal.add_eq_top] at H2
    --   rcases H2 with (rfl|rfl) <;> simp at H1
    sorry


--   Lemma nonnegreal_local_update (x y x' y' : nonnegreal) :
--     y' <= y → x + y' = x' + y → (x,y) ~l~> (x',y').
--   Proof.
--     intros ??; apply (local_update_unital_discrete x y x' y') => z H1 H2.
--     compute in H2; simplify_eq; simpl.
--     destruct y, x', y', z; simplify_eq; simpl.
--     split.
--     - compute; compute in *.
--       eapply Rle_lt_trans; [| eapply H1].
--       lra.
--     - compute.
--       apply nnreal_ext; simpl in *; lra.
--   Qed.

theorem ErrorCredit.localUpdate {ε₁ ε₂ ε₁' ε₂' : ErrorCredit} (h1 : ε₂' <= ε₂)
    (h2 : ε₁ + ε₂' = ε₁' + ε₂) : (ε₁, ε₂) ~l~> (ε₁', ε₂') := by
  rintro n (_|ε) <;> simp only [OFE.Dist, CMRA.op?, CMRA.ValidN, CMRA.op]
  · rintro H rfl
    refine ⟨?_, ?_⟩
    · sorry
    · sorry
  · rintro H rfl
    refine ⟨?_, ?_⟩
    · sorry
    · sorry

instance : Iris.IsUnit (◯ 0 : Auth ℕ+ ErrorCredit) where
  unit_valid := Auth.frag_valid.mpr (by simp [CMRA.Valid])
  unit_left_id := by simp [CMRA.op]
  pcore_unit := .rfl

class ECPreGS (GF : BundledGFunctors) where
  ec : ElemG GF (constOF (Auth ℕ+ ErrorCredit))

attribute [reducible, instance] ECPreGS.ec

class ECGS (GF : BundledGFunctors) extends ECPreGS GF where
  γec : GName

section Resources

variable {GF : BundledGFunctors} [IEC : ECGS GF]

def ecAuth (ε : ENNReal) : IProp GF := iOwn (E := IEC.ec) IEC.γec (● ε)
def ec (ε : ENNReal) : IProp GF := iOwn (E := IEC.ec) IEC.γec (◯ ε)
notation "↯" r:50 => ec r
notation "●↯" r:50 => ecAuth r

end Resources

namespace ErrorCredit

variable {GF : BundledGFunctors} [IEC : ECGS GF]

theorem ext {ε₁ ε₂} (he : ε₁ = ε₂) : ↯ε₁ ⊢@{IProp GF} ↯ε₂ := by simp [he]

theorem extAuth {ε₁ ε₂} (he : ε₁ = ε₂) : ●↯ ε₁ ⊢@{IProp GF} ●↯ ε₂ := by simp [he]

theorem split {ε₁ ε₂} : ↯(ε₁ + ε₂) ⊢@{IProp GF} ↯ε₁ ∗ ↯ε₂ := by
  unfold ec
  iintro Hε
  iapply iOwn_op
  simp [CMRA.op]

theorem difference {ε₁ ε₂} (Hwf : ε₁ ≤ ε₂) : ↯ε₂ ⊢@{IProp GF} ↯ε₁ ∗ ↯(ε₂ - ε₁) := by
  iintro H
  iapply split
  iapply ext (add_tsub_cancel_of_le Hwf).symm $$ H

theorem combine {ε₁ ε₂} : ↯ε₁ ∗ ↯ε₂ ⊢@{IProp GF} ↯(ε₁ + ε₂) := by
  unfold ec
  iintro H
  ihave _ := iOwn_op (E := IEC.ec) |>.mpr $$ H
  simp [CMRA.op]

theorem zero : ⊢@{IProp GF} |==> ↯0 := iOwn_unit


-- Lemma ec_supply_bound (ε1 : R) (ε2 : nonnegreal) :
--   ec_supply ε2 -∗ ↯ ε1 -∗ ⌜ε1 <= ε2⌝.
-- Proof.
--   rewrite ec_unseal /ec_def ec_supply_unseal /ec_supply_def.
--   iIntros "H1 (%r & <- & H2)".
--   iDestruct (own_valid_2 with "H1 H2") as "%Hop".
--   by eapply auth_both_valid_discrete in Hop as [Hlt%nonnegreal_included ?].
-- Qed.

theorem supply_bound {εₛ ε} : ⊢@{IProp GF} ●↯ εₛ -∗ ↯ε -∗ ⌜ε ≤ εₛ ⌝:= by
  unfold ec ecAuth
  iintro Hs Hε
  ihave _ := iOwn_op (E := IEC.ec) |>.mpr $$ [Hs Hε]
  all_goals sorry

-- theorem supply_decrease {εₛ ε} :
--   ⊢@{IProp GF} ●↯ εₛ -∗ ↯ε -∗ |==> ∃ (εₛ' ε' : ENNReal), ⌜εₛ = εₛ' + ε'⌝ ∗

end ErrorCredit


/-


  Lemma ec_supply_ec_inv r1 x2 :
    ec_supply x2 -∗ ↯ r1 -∗ ∃ x1 x3, ⌜x2 = (x1 + x3)%NNR⌝ ∗ ⌜x1.(nonneg) = r1⌝.
  Proof.
    iIntros "Hx2 Hr1".
    iDestruct (ec_supply_bound with "Hx2 Hr1") as %Hb.
    iDestruct "Hr1" as (x1) "[<- Hx1]".
    set (x3 := nnreal_minus x2 x1 Hb).
    iExists _, x3. iSplit; [|done].
    iPureIntro. apply nnreal_ext=>/=; lra.
  Qed.

  (** The statement of this lemma is a bit convoluted, because only implicitly (by validity and
      unfolding) can we conclude that [0 <= r1 <= x2] so thus that [x2 - r1] is nonnegative *)
  Lemma ec_supply_decrease (r1 : R) (x2 : nonnegreal) :
    ec_supply x2 -∗ ↯ r1 -∗ |==> ∃ x1 x3, ⌜(x2 = x3 + x1)%NNR⌝ ∗ ⌜x1.(nonneg) = r1⌝ ∗ ec_supply x3.
  Proof.
    iIntros "Hx2 Hr1".
    iDestruct (ec_supply_ec_inv with "Hx2 Hr1") as %(x1 & x3 & -> & <-).
    iDestruct "Hr1" as (x1') "[% Hx1]".
    rewrite ec_unseal /ec_def ec_supply_unseal /ec_supply_def.
    iMod (own_update_2 with "Hx2 Hx1") as "Hown".
    { eapply (auth_update_dealloc _ _ x3), nonnegreal_local_update.
      - apply cond_nonneg.
      - apply nnreal_ext =>/=. lra. }
    iModIntro.
    iExists _, _. iFrame. iSplit; [|done].
    iPureIntro. apply nnreal_ext=>/=; lra.
  Qed.

  Lemma ec_supply_increase (ε1 ε2 : nonnegreal) :
    ε1 + ε2 < 1 →
    ec_supply ε1 -∗ |==> ec_supply (ε1 + ε2)%NNR ∗ ↯ ε2.
  Proof.
    rewrite ec_unseal /ec_def.
    rewrite ec_supply_unseal /ec_supply_def.
    iIntros (?) "H".
    iMod (own_update with "H") as "[$ $]"; [|done].
    eapply auth_update_alloc.
    apply (local_update_unital_discrete _ _ _ _) => z H1 H2.
    split; [done|].
    apply nnreal_ext. simpl.
    rewrite Rplus_comm.
    apply Rplus_eq_compat_l.
    rewrite H2 /=. lra.
  Qed.

  Lemma ec_weaken (r1 r2 : R) :
    0 <= r2 <= r1 → ↯ r1 -∗ ↯ r2.
  Proof.
    iIntros (?) "Hr1".
    assert (r1 = (r1 - r2) + r2) as -> by lra.
    iDestruct (ec_split with "Hr1") as "[? $]"; lra.
  Qed.

  Lemma ec_supply_eq x1 x2 :
    (x1.(nonneg) = x2.(nonneg)) → ec_supply x1 -∗ ec_supply x2.
  Proof.
    iIntros (?) "?".
    replace x1 with x2; [iFrame|by apply nnreal_ext].
  Qed.

  Lemma ec_contradict (ε : R) :
    1 <= ε → ↯ ε ⊢ False.
  Proof.
    iIntros (Hge1) "(% & <- & Hε)".
    rewrite ec_unseal /ec_def.
    iDestruct (own_valid with "Hε") as %?%auth_frag_valid_1.
    destruct x.
    compute in H.
    simpl in *.
    lra.
  Qed.

  Lemma ec_valid (ε : R) : ↯ ε -∗ ⌜(0<=ε<1)%R⌝.
  Proof.
    iIntros "(%&<-&H)".
    rewrite ec_unseal /ec_def.
    iDestruct (own_valid with "H") as %?%auth_frag_valid_1.
    destruct x. compute in H. simpl in *. iPureIntro. lra.
  Qed.

  #[local] Lemma err_amp_power ε k :
    0 < ε →
    1 < k →
    ∃ n, 1 <= ε * k ^ n.
  Proof.
    intros Hε Hk.
    destruct (Lim_seq.is_lim_seq_geom_p k Hk (λ r, / ε <= r)) as [n Hn] => /=.
    - exists (/ ε). real_solver.
    - exists n.
      apply (Rmult_le_reg_l (/ ε)).
      + apply Rinv_0_lt_compat, Hε.
      + rewrite -Rmult_assoc Rinv_l; [|lra].
        rewrite Rmult_1_l Rmult_1_r. by apply Hn.
  Qed.

  #[local] Lemma err_amp_mult ε ε' k :
    0 < ε →
    ε <= ε' ->
    1 < k →
    (exists n:nat, 1 <= n*(k-1)*ε + ε').
  Proof.
    intros Hε Hleq Hk.
    edestruct (Rcomplements.nfloor_ex (1/((k-1)*ε))) as [n [Hn1 Hn2]].
    - apply Rmult_le_pos; [lra|].
      left.
      apply Rinv_0_lt_compat.
      real_solver.
    - exists (S n).
      rewrite S_INR.
      transitivity ((1 / ((k - 1) * ε)) * (k - 1) * ε + ε').
      + rewrite Rmult_assoc.
        rewrite /Rdiv Rmult_1_l.
        rewrite Rinv_l; [lra |].
        assert (0<(k-1)*ε); real_solver.
      + apply Rplus_le_compat_r.
        apply Rmult_le_compat_r; [lra|].
        apply Rmult_le_compat_r; lra.
  Qed.

  Lemma ec_ind_amp_external (ε k : R) P :
    0 < ε →
    1 < k →
    (∀ (ε' : R), 0 < ε' → □ (↯ (k * ε') -∗ P) ∗ ↯ ε' ⊢ P) →
    (↯ ε ⊢ P).
  Proof.
    iIntros (Hε Hk Hamp) "Herr".
    destruct (err_amp_power ε k) as [n Hn]; [done|done|].
    iInduction n as [|m] "IH" forall (ε Hε Hn Hk) "Herr".
    - iDestruct (ec_contradict with "Herr") as %[]. lra.
    - iApply (Hamp with "[$Herr]"); [done|].
      iIntros "!> Herr".
      iApply ("IH" with "[] [] [//] Herr"); iPureIntro.
      + real_solver.
      + simpl in Hn. lra.
  Qed.


  #[local] Lemma ec_ind_simpl_external_aux (ε ε' k : R) P :
    0 < ε →
    ε <= ε' ->
    1 < k →
    ((↯ (k * ε) -∗ P) ∗ ↯ ε ⊢ P) →
    (↯ ε' ⊢ P).
  Proof.
    iIntros (Hε Hleq Hk Hamp) "Herr".
    destruct (err_amp_mult ε ε' k) as [n Hn]; auto.
    iInduction n as [|m] "IH" forall (ε ε' Hε Hleq Hn Hk Hamp) "Herr".
    - iDestruct (ec_contradict with "Herr") as %[].
      simpl in Hn.
      lra.
    - replace (ε') with (ε + (ε' - ε)) by lra.
      iDestruct (ec_split with "Herr") as "[Herr1 Herr2]"; [lra | lra |].
      iApply (Hamp with "[$Herr1 Herr2]").
      iIntros "Herr".
      assert (k * ε = (k-1)*ε + ε) as ->; [lra |].
      iDestruct (ec_split with "Herr") as "[Herr3 Herr4]"; [ real_solver | lra |].
      iDestruct (ec_combine with "[$Herr2 $Herr3]") as "Herr".
      iDestruct (ec_combine with "[$Herr $Herr4]") as "Herr".
      iApply ("IH" $! ε with "[] [] [] [] [] Herr"); auto.
      + iPureIntro.
        replace (ε' - ε + (k-1) * ε + ε) with (ε' + (k-1) * ε) by lra.
        rewrite <- (Rplus_0_r ε) at 1.
        apply Rplus_le_compat; auto.
        apply Rmult_le_pos; lra.
      + iPureIntro.
        replace (ε' - ε + (k - 1) * ε + ε) with (ε' + (k - 1) * ε) by lra.
        replace (m * (k - 1) * ε + (ε' + (k - 1) * ε)) with ((m + 1) * (k - 1) * ε + ε') by lra.
        etrans; eauto.
        rewrite S_INR //.
  Qed.


  Lemma ec_ind_simpl_external (ε k : R) P :
    0 < ε →
    1 < k →
    ((↯ (k * ε) -∗ P) ∗ ↯ ε ⊢ P) →
    (↯ ε ⊢ P).
  Proof.
    iIntros (Hε HK Hamp).
    eapply ec_ind_simpl_external_aux; eauto.
    lra.
  Qed.

  #[local] Lemma ec_ind_simpl_aux (ε ε' k : R) P :
    0 < ε →
    ε <= ε' ->
    1 < k →
    □ ((↯ (k * ε) -∗ P) ∗ ↯ ε -∗ P) ⊢
    (↯ ε' -∗ P).
  Proof.
    iIntros (Hε Hleq Hk) "#Hamp Herr".
    destruct (err_amp_mult ε ε' k) as [n Hn]; auto.
    iInduction n as [|m] "IH" forall (ε ε' Hε Hleq Hn Hk) "Hamp Herr".
    - iDestruct (ec_contradict with "Herr") as %[].
      simpl in Hn.
      lra.
    - replace (ε') with (ε + (ε' - ε)) by lra.
      iDestruct (ec_split with "Herr") as "[Herr1 Herr2]"; [lra | lra |].
      iApply ("Hamp" with "[$Herr1 Herr2]").
      iIntros "Herr".
      assert (k * ε = (k-1)*ε + ε) as ->; [lra |].
      iDestruct (ec_split with "Herr") as "[Herr3 Herr4]"; [ real_solver | lra |].
      iDestruct (ec_combine with "[$Herr2 $Herr3]") as "Herr".
      iDestruct (ec_combine with "[$Herr $Herr4]") as "Herr".
      iApply ("IH" $! ε with "[] [] [] [] [] Herr"); auto.
      + iPureIntro.
        replace (ε' - ε + (k-1) * ε + ε) with (ε' + (k-1) * ε) by lra.
        rewrite <- (Rplus_0_r ε) at 1.
        apply Rplus_le_compat; auto.
        apply Rmult_le_pos; lra.
      + iPureIntro.
        replace (ε' - ε + (k - 1) * ε + ε) with (ε' + (k - 1) * ε) by lra.
        replace (m * (k - 1) * ε + (ε' + (k - 1) * ε)) with ((m + 1) * (k - 1) * ε + ε') by lra.
        etrans; eauto.
        rewrite S_INR //.
      + replace ((k - 1) * ε + ε) with (k * ε) by lra.
        auto.
  Qed.

  Lemma ec_ind_simpl (ε k : R) P :
    0 < ε →
    1 < k →
    □((↯ (k * ε) -∗ P) ∗ ↯ ε -∗ P) ⊢
    (↯ ε -∗ P).
  Proof.
    iIntros (Hε Hk) "#Hamp Herr".
    iApply ec_ind_simpl_aux; eauto.
    lra.
  Qed.


  Lemma ec_ind_incr (ε ε': R) P :
    0 < ε →
    ε < ε' →
    □((↯ ε' -∗ P) ∗ ↯ ε -∗ P) ⊢
    (↯ ε -∗ P).
  Proof.
    iIntros (Hε Hε') "#Hamp Herr".
    iApply (ec_ind_simpl ε (ε'/ε) with "[Hamp]"); auto.
    - apply Rcomplements.Rlt_div_r; lra.
    - iModIntro.
      iIntros "(H & Herr)".
      iApply ("Hamp" with "[H $Herr]").
      iIntros "Herr".
      iApply "H".
      rewrite /Rdiv Rmult_assoc Rinv_l; [|lra].
      rewrite Rmult_1_r.
      iFrame.
  Qed.



  (* TODO: can [ec_ind_amp] be derived from [ec_ind_amp_external] ? *)
  Lemma ec_ind_amp (ε k : R) P :
    0 < ε →
    1 < k →
    □ (∀ (ε' : R), ⌜0 < ε'⌝ -∗ □ (↯ (k * ε') -∗ P) -∗ ↯ ε' -∗ P) ⊢
    (↯ ε -∗ P).
  Proof.
    iIntros (Hpos Hgt1) "#Hamp Herr".
    destruct (err_amp_power ε k) as [n Hn]; [done|done|].
    iInduction n as [|m] "IH" forall (ε Hpos Hn Hgt1) "Herr".
    - iDestruct (ec_contradict with "Herr") as %[].
      simpl in Hn. lra.
    - iApply ("Hamp" with "[//] [] Herr").
      iIntros "!# Herr".
      iApply ("IH" with "[] [] [//] Herr"); iPureIntro.
      + real_solver.
      + simpl in Hn. lra.
  Qed.

  Global Instance ec_timeless r : Timeless (↯ r).
  Proof. rewrite ec_unseal /ec_def. apply _. Qed.

End error_credit_theory.

Lemma ec_alloc `{!ecGpreS Σ} (n : nonnegreal) :
  (n < 1)%R → ⊢ |==> ∃ _ : ecGS Σ, ec_supply n ∗ ↯ n.
Proof.
  iIntros (?).
  rewrite ec_unseal /ec_def ec_supply_unseal /ec_supply_def.
  iMod (own_alloc (● n ⋅ ◯ n)) as (γEC) "[H● H◯]".
  - apply auth_both_valid_2.
    + compute. destruct n; simpl in H. lra.
    + apply nonnegreal_included; lra.
  - pose (C := EcGS _ _ γEC).
    iModIntro. iExists C. by iFrame.
Qed.

#[global] Hint Resolve cond_nonneg : core.
-/

end
