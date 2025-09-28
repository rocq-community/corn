(*
Copyright © 2009 Valentin Blot

Permission is hereby granted, free of charge, to any person obtaining a copy of
this proof and associated documentation files (the "Proof"), to deal in
the Proof without restriction, including without limitation the rights to
use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies of
the Proof, and to permit persons to whom the Proof is furnished to do so,
subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Proof.

THE PROOF IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS
FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR
COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER
IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN
CONNECTION WITH THE PROOF OR THE USE OR OTHER DEALINGS IN THE PROOF.
*)
Require Import CRing_Homomorphisms.
Require Import CPoly_NthCoeff.
Require Import MoreFunctions.
Require Import Rolle.

Require Import Zlcm Q_can RX_deg QX_ZX QX_root_loc QX_extract_roots.

Section CPoly_bounded.

Variable I : interval.
Hypothesis I_fin : finite I.

Fixpoint AbsPoly (P : cpoly_cring IR) : cpoly_cring IR :=
  match P with
    | cpoly_zero _ => cpoly_zero IR
    | cpoly_linear _ c P => cpoly_linear IR (AbsIR c) (AbsPoly P)
  end.

Lemma AbsPoly_zero : AbsPoly [0] = [0].
Proof. reflexivity. Qed.
Lemma AbsPoly_linear : forall c P, AbsPoly (c[+X*]P) = AbsIR c[+X*]AbsPoly P.
Proof. reflexivity. Qed.

Lemma Abs_poly_nth_coeff : forall P i, nth_coeff i (AbsPoly P) [=] AbsIR (nth_coeff i P).
Proof.
 intro P.
 pattern P; apply Ccpoly_induc; clear P.
  intro; rewrite -> AbsPoly_zero, nth_coeff_zero.
  symmetry; apply AbsIRz_isz.
 intros P c Hrec n.
 rewrite AbsPoly_linear.
 destruct n.
  rewrite -> coeff_O_lin; reflexivity.
 rewrite -> coeff_Sm_lin.
 rewrite -> Hrec.
 apply AbsIR_wd.
 symmetry; apply coeff_Sm_lin.
Qed.

Definition CPoly_bound (P : cpoly_cring IR)  : IR :=
            (AbsPoly P) ! (Max (AbsIR (left_end I I_fin)) (AbsIR (right_end I I_fin))).

Lemma AbsIR_leEq : forall a b, a [<=] b -> [--]a [<=] b -> AbsIR a [<=] b.
Proof.
 intros a b Hp Hm.
 unfold AbsIR, ABSIR; simpl.
 apply Max_leEq; assumption.
Qed.

Lemma abs_max : forall a b x, a [<=] x -> x [<=] b -> AbsIR x [<=] Max (AbsIR a) (AbsIR b).
Proof.
 intros a b x Ha Hb.
 apply AbsIR_leEq.
  apply (leEq_transitive _ _ (AbsIR b)); [|apply rht_leEq_Max].
  apply (leEq_transitive _ _ b); [assumption|apply leEq_AbsIR].
 apply (leEq_transitive _ _ (AbsIR a)); [|apply lft_leEq_Max].
 apply (leEq_transitive _ _ ([--]a)).
  apply inv_resp_leEq; assumption.
 rewrite -> AbsIR_inv; apply leEq_AbsIR.
Qed.

Lemma Abs_min_max : forall x, I x ->
        AbsIR x [<=] Max (AbsIR (left_end I I_fin)) (AbsIR (right_end I I_fin)).
Proof.
 intros x HI; unfold left_end, right_end.
 destruct I; try inversion I_fin; destruct HI; apply abs_max;
   (apply less_leEq; assumption)|| assumption.
Qed.

Lemma CPoly_bound_spec : forall x P, I x -> AbsIR (P ! x) [<=] CPoly_bound P.
Proof.
 intros x P HI.
 destruct (Cpoly_ex_degree _ P) as [n Hdeg].
 destruct (Cpoly_ex_degree _ (AbsPoly P)) as [m HdegA].
 unfold CPoly_bound.
 generalize (degree_le_mon _ _ _ _ (Nat.le_max_l n m) Hdeg).
 generalize (degree_le_mon _ _ _ _ (Nat.le_max_r n m) HdegA).
 revert HI.
 generalize (Nat.max n m). clear.
 intros n HI HdegP HdegA.
 rewrite -> (poly_as_sum _ _ _ HdegP).
 rewrite -> (poly_as_sum _ _ _ HdegA).
 apply (leEq_transitive _ _ (Sum 0 n (fun i => AbsIR (nth_coeff i P[*]x[^]i)))).
  apply triangle_SumIR.
  apply Nat.le_0_l.
 apply Sum_resp_leEq.
  apply Nat.le_0_l.
 intros i H1 H2.
 rewrite -> AbsIR_resp_mult.
 rewrite -> Abs_poly_nth_coeff.
 apply mult_resp_leEq_lft; [|apply AbsIR_nonneg].
 rewrite -> AbsIR_nexp_op.
 apply nexp_resp_leEq; [apply AbsIR_nonneg|].
 apply Abs_min_max; assumption.
Qed.

End CPoly_bounded.

Section poly_law_of_mean.

Variable I : interval.
Hypothesis I_fin : finite I.
Hypothesis I_proper : proper I.
Variable P : cpoly_cring IR.

Let C := CPoly_bound I I_fin (_D_ P).
Let Hderiv := Derivative_poly I I_proper P.

Lemma poly_law_of_mean : forall a b, I a -> I b ->
     AbsIR (P ! b [-] P ! a) [<=] C [*] (AbsIR (b [-] a)).
Proof.
 intros a b Ha Hb.
 set (Law_of_the_Mean_Abs_ineq I I_proper (FPoly IR P) (FPoly IR (_D_ P)) Hderiv a b Ha Hb
   (CPoly_bound I I_fin (_D_ P))).
 simpl in c.
 apply c; [|auto|auto].
 clear c; intros x Hcomp Htrue; clear Htrue.
 apply CPoly_bound_spec.
 destruct Hcomp.
 destruct I; simpl in *; try auto; try split; try (destruct Ha; destruct Hb);
   (apply (less_leEq_trans _ _ (MIN a b)); [apply less_Min|]; assumption)||
     (apply (leEq_less_trans _ _ (MAX a b)); [|apply Max_less]; assumption)||
       (apply (leEq_transitive _ _ (MIN a b)); [apply leEq_Min|]; assumption)||
         (apply (leEq_transitive _ _ (MAX a b)); [|apply Max_leEq]; assumption).
Qed.

End poly_law_of_mean.

Section liouville_lemmas.

Variable a : IR.
Definition Ia : interval := clcr (a[-]Two) (a[+]Two).
Lemma Ia_fin : finite Ia.
Proof. simpl; auto. Qed.
Lemma Ia_proper : proper Ia.
Proof.
 simpl.
 apply shift_minus_less.
 apply (less_wdl _ (a[+](([0][+][0][+][0])[+]([0][+][0][+][0])))); [|rational].
 apply (less_wdr _ _ (a[+](Two[+]Two))); [|rational].
 apply plus_resp_less_lft.
 apply plus_resp_less_both.
  apply plus_resp_less_both; [|apply pos_one].
  apply plus_resp_less_lft; apply pos_one.
 apply plus_resp_less_both; [|apply pos_one].
 apply plus_resp_less_lft; apply pos_one.
Qed.
Lemma a_in_Ia : Ia a.
Proof.
 split.
  apply less_leEq.
  apply (less_wdr _ _ (a[-]([0][+][0][+][0]))); [|rational].
  apply minus_resp_less_rht.
  apply plus_resp_less_both; [|apply pos_one].
  apply plus_resp_less_lft; apply pos_one.
 apply less_leEq.
 apply (less_wdl _ (a[+]([0][+][0][+][0]))); [|rational].
 apply plus_resp_less_lft.
 apply plus_resp_less_both; [|apply pos_one].
 apply plus_resp_less_lft; apply pos_one.
Qed.

Lemma Liouville_lemma1 : forall x : IR, AbsIR (x[-]a) [<=] Two -> Ia x.
Proof.
 intros x Hle.
 split.
  apply (leEq_wdr _ _ (x[+]Two[-]Two)); [|rational].
  apply minus_resp_leEq.
  apply (leEq_wdl _ (x[+](a[-]x))); [|rational].
  apply plus_resp_leEq_lft.
  rewrite -> AbsIR_minus in Hle.
  apply (leEq_transitive _ _ (AbsIR (a[-]x))); [|assumption].
  apply leEq_AbsIR.
 apply (leEq_wdl _ (x[-]Two[+]Two)); [|rational].
 apply plus_resp_leEq.
 apply (leEq_wdr _ _ (x[-](x[-]a))); [|rational].
 apply minus_resp_leEq_rht.
 apply (leEq_transitive _ _ (AbsIR (x[-]a))); [|assumption].
 apply leEq_AbsIR.
Qed.

Variable P : cpoly_cring IR.
Let C := CPoly_bound Ia Ia_fin (_D_ P).

Lemma Liouville_lemma2 : forall x : IR, AbsIR (x[-]a) [<=] Two ->
    AbsIR (P ! x [-] P ! a) [<=] C [*] AbsIR (x [-] a).
Proof.
 intros x Hle.
 apply (poly_law_of_mean Ia Ia_fin Ia_proper P a x a_in_Ia (Liouville_lemma1 x Hle)).
Qed.

Lemma Liouville_lemma3 : forall x : IR, [1] [<] x or x [<] Two.
Proof.
 intro x.
 apply less_cotransitive_unfolded.
 apply (less_wdl _ ([0][+][0][+][1])); [|rational].
 apply plus_resp_less_rht.
 apply plus_resp_less_lft.
 apply pos_one.
Qed.

End liouville_lemmas.

Section liouville_lemmas2.

Let ZX_deg := RX_deg Z_as_CRing Z_dec.
Variable P : cpoly_cring Z_as_CRing.

Lemma Liouville_lemma4 : forall p : Z_as_CRing,
            p [#] [0] -> [1] [<=] AbsIR (inj_Q_rh p).
Proof.
 intros p Hap.
 change ([1][<=]AbsIR(inj_Q IR p)).
 rewrite -> AbsIR_Qabs.
 unfold Qabs.Qabs.
 unfold inject_Z.
 rewrite <- inj_Q_One.
 apply inj_Q_leEq.
 unfold Z.abs.
 destruct p.
   destruct Hap; reflexivity.
  simpl; unfold Qle; simpl; intuition; auto with *.
 simpl; unfold Qle; simpl; intuition; auto with *.
Qed.

Lemma Liouville_lemma5 : forall (p : Z_as_CRing) (q : positive), (zx2qx P) ! (p#q)%Q [#] [0] ->
      [1] [<=] (inj_Q_rh q)[^](ZX_deg P) [*] AbsIR (inj_Q_rh ((zx2qx P) ! (p#q)%Q)).
Proof.
 intros p q Hap.
 set (n := ZX_deg P).
 assert (Zpos q=Z.abs q); [reflexivity|].
 rewrite H; clear H.
 rewrite <- nexp_ring_hom.
 assert (((Z.abs q):Q_as_CRing)[^]n [=] Z.abs ((q:Z_as_CRing)[^]n)).
  generalize n; clear; induction n; [reflexivity|].
  rewrite <- nexp_Sn.
  rewrite <- nexp_Sn.
  rewrite Zabs_Zmult.
  rewrite -> IHn.
  reflexivity.
 rewrite -> H; clear H.
 rewrite <- (AbsIR_Qabs ((q:Z_as_CRing)[^]n)).
 rewrite <- AbsIR_resp_mult.
 change (inj_Q IR ((q:Z_as_CRing)[^]n)) with (inj_Q_rh ((q:Z_as_CRing)[^]n)).
 rewrite <- rh_pres_mult.
 assert (inject_Z ((q:Z_as_CRing)[^]n) [=] (inject_Z (q:Z_as_CRing))[^]n).
  generalize n; clear; induction n; [reflexivity|].
  rewrite <- nexp_Sn.
  rewrite <- nexp_Sn.
  rewrite <- IHn.
  reflexivity.
 rewrite -> H; clear H.
 set (H:=Q_Z_poly_apply P p q).
 cbv zeta in H.
 fold ZX_deg in H.
 fold n in H.
 rewrite -> H.
 apply Liouville_lemma4.
 intro.
 destruct (ap_imp_neq _ _ _ Hap); clear Hap.
 assert ((inject_Z (Zpos q))[^]n [#] [0]).
  generalize n; clear; induction n; [discriminate|].
  intro; destruct IHn.
  rewrite <- nexp_Sn in H.
  destruct (Qmult_integral _ _ H); [discriminate|assumption].
 rewrite -> H0 in H.
 apply (mult_eq_zero _ _ _ X); assumption.
Qed.

End liouville_lemmas2.

Section liouville_lemmas3.

Let ZX_deg := RX_deg Z_as_CRing Z_dec.
Let QX_deg := RX_deg Q_as_CRing Q_dec.
Variable P : cpoly_cring Q_as_CRing.

Lemma Liouville_lemma6 : forall (p : Z_as_CRing) (q : positive), P ! (p#q)%Q [#] [0] ->
      [1] [<=] (inj_Q_rh q)[^](QX_deg P) [*] AbsIR (inj_Q_rh ((Zlcm_den_poly P:Q_as_CRing)[*]P ! (p#q)%Q)).
Proof.
 intros p q Hap.
 assert ((zx2qx (qx2zx P)) ! (p#q)%Q[#][0]).
  case (Q_dec ((zx2qx (qx2zx P)) ! (p#q)%Q) [0]); [|tauto].
  intro Heq; destruct (ap_imp_neq _ _ _ Hap); revert Heq.
  rewrite -> qx2zx_spec.
  rewrite -> mult_apply, c_apply.
  intro Heq.
  apply (mult_eq_zero _ (Zlcm_den_poly P:Q_as_CField)).
   replace (cm_unit Q_as_CField) with (inject_Z (cm_unit Z_as_CRing)) by reflexivity.
   intro Heq2; rewrite Q.Qeq_Zeq in Heq2.
   apply (eq_imp_not_ap _ (Zlcm_den_poly P) [0]).
    assumption.
   apply Zlcm_den_poly_nz.
  assumption.
 rewrite -> qx2zx_deg; fold ZX_deg.
 apply (leEq_wdr _ _ _ _ (Liouville_lemma5 _ _ _ X)); fold ZX_deg.
 apply mult_wdr.
 apply AbsIR_wd.
 apply csf_wd.
 rewrite -> qx2zx_spec.
 rewrite -> mult_apply, c_apply; reflexivity.
Qed.

Lemma Liouville_lemma7 : forall (p : Z_as_CRing) (q : positive), P ! (p#q)%Q [#] [0] ->
      [1] [<=] (inj_Q_rh q)[^](QX_deg P) [*] AbsIR (inj_Q_rh (Zlcm_den_poly P:Q_as_CRing)) [*] AbsIR (inj_Q_rh (P ! (p#q)%Q)).
Proof.
 intros p q Hap.
 apply (leEq_wdr _ _ _ _ (Liouville_lemma6 _ _ Hap)).
 rewrite <- CRings.mult_assoc.
 apply mult_wdr.
 rewrite -> rh_pres_mult.
 apply AbsIR_resp_mult.
Qed.

Variable a : IR.
Let C := AbsIR (inj_Q_rh (Zlcm_den_poly P:Q_as_CRing)) [*] CPoly_bound (Ia a) (Ia_fin a) (_D_ (inj_QX_rh P)).
Hypothesis Ha : (inj_QX_rh P) ! a [=] [0].

Lemma Liouville_lemma8 : forall (n : nat) (q : positive), [1] [<=] (inj_Q_rh q)[^]n.
Proof.
 intros n q; induction n.
  apply leEq_reflexive.
 rewrite <- nexp_Sn.
 apply (leEq_wdl _ ([1][*][1])); [|rational].
 apply mult_resp_leEq_both; [apply less_leEq; apply pos_one|apply less_leEq; apply pos_one| |apply IHn].
 rewrite <- (rh_pres_unit _ _ inj_Q_rh).
 apply inj_Q_leEq.
 simpl; unfold Qle; simpl; rewrite Pmult_1_r.
 unfold Z.le; simpl.
 case q; intros; discriminate.
Qed.

Lemma Liouville_lemma9 : forall (p : Z_as_CRing) (q : positive),
      P ! (p#q)%Q [#] [0] -> AbsIR ((inj_Q_rh (p#q)%Q) [-] a) [<=] Two ->
      [1] [<=] (inj_Q_rh q)[^](QX_deg P) [*] C [*] AbsIR ((inj_Q_rh (p#q)%Q) [-] a).
Proof.
 intros p q Hap Hle.
 apply (leEq_transitive _ _ _ _ (Liouville_lemma7 _ _ Hap)).
 rewrite <- CRings.mult_assoc, <- CRings.mult_assoc.
 apply mult_resp_leEq_lft.
  unfold C.
  rewrite <- CRings.mult_assoc.
  apply mult_resp_leEq_lft; [|apply AbsIR_nonneg].
  apply (leEq_wdl _ _ _ _ (Liouville_lemma2 _ _ _ Hle)).
  apply AbsIR_wd.
  rewrite -> Ha.
  rewrite -> cg_inv_zero.
  unfold inj_QX_rh.
  rewrite -> cpoly_map_apply; reflexivity.
 set (Liouville_lemma8 (QX_deg P) q).
 apply (leEq_transitive _ _ [1]); [apply less_leEq; apply pos_one|].
 apply Liouville_lemma8.
Qed.

Let C' := Max [1] C.

Lemma Liouville_lemma10 : forall (p : Z_as_CRing) (q : positive),
      P ! (p#q)%Q [#] [0] ->
      [1] [<=] (inj_Q_rh q)[^](QX_deg P) [*] C' [*] AbsIR ((inj_Q_rh (p#q)%Q) [-] a).
Proof.
 intros p q Hap.
 destruct (Liouville_lemma3 (AbsIR (inj_Q_rh (p # q)%Q[-]a))).
  apply (leEq_transitive _ _ _ _ (less_leEq _ _ _ c)).
  apply (leEq_wdl _ ([1] [*] AbsIR (inj_Q_rh (p#q)%Q [-] a))); [|rational].
  apply mult_resp_leEq_rht; [|apply AbsIR_nonneg].
  apply (leEq_wdl _ ([1] [*] [1])); [|rational].
  apply mult_resp_leEq_both; [apply less_leEq; apply pos_one|apply less_leEq; apply pos_one| |apply lft_leEq_Max].
  apply Liouville_lemma8.
 apply (leEq_transitive _ _ _ _ (Liouville_lemma9 _ _ Hap (less_leEq _ _ _ c))).
 apply mult_resp_leEq_rht; [|apply AbsIR_nonneg].
 apply mult_resp_leEq_lft; [|].
  unfold C'; apply rht_leEq_Max.
 apply (leEq_transitive _ _ [1]); [apply less_leEq; apply pos_one|].
 apply Liouville_lemma8.
Qed.

End liouville_lemmas3.

Section liouville_theorem.

Variable a : IR.
Hypothesis a_irrat : forall x : Q, a [~=] inj_Q _ x.
Variable P : cpoly_cring Q_as_CRing.
Hypothesis P_nz : P [#] [0].
Hypothesis a_alg : (inj_QX_rh P) ! a [=] [0].

Let C : IR := Max [1] (AbsIR (inj_Q_rh (Zlcm_den_poly (QX_extract_roots P):Q_as_CRing)) [*] CPoly_bound (Ia a) (Ia_fin a) (_D_ (inj_QX_rh (QX_extract_roots P)))).
Lemma constant_pos : [0] [<] C.
Proof.
 unfold C.
 apply (less_leEq_trans _ _ [1]).
  apply pos_one.
 apply lft_leEq_Max.
Qed.

Lemma constant_nz : C [#] [0].
Proof. apply pos_ap_zero; apply constant_pos. Qed.

Definition Liouville_constant : IR := [1] [/] C [//] constant_nz.

Definition Liouville_degree := RX_deg _ Q_dec (QX_extract_roots P).

Theorem Liouville_theorem : forall (x : Q),
       (Liouville_constant[*]inj_Q IR (1#Qden x)%Q[^]Liouville_degree)
                             [<=] AbsIR (inj_Q _ x [-] a).
Proof.
 intro x.
 destruct x as [p q]; unfold Qden.
 apply (mult_cancel_leEq _ _ _ (inj_Q_rh q[^]Liouville_degree)).
  apply (less_leEq_trans _ _ [1]); [apply pos_one|].
  apply Liouville_lemma8.
 assert (H : inj_Q IR (1#q)%Q = inj_Q_rh (1#q)%Q).
  reflexivity.
 rewrite H; clear H.
 rewrite <- nexp_ring_hom.
 rewrite <- CRings.mult_assoc.
 rewrite <- nexp_ring_hom.
 rewrite <- rh_pres_mult.
 assert (H : (1 # q)%Q[^]Liouville_degree[*](inject_Z q)[^]Liouville_degree [=] [1]).
  rewrite <- mult_nexp.
  rewrite <- (one_nexp _ Liouville_degree).
  apply nexp_wd; reflexivity.
 rewrite -> H; clear H.
 rewrite -> rh_pres_unit.
 rewrite -> mult_one.
 unfold Liouville_constant.
 apply shift_div_leEq'.
  apply constant_pos.
 assert (H : (inj_QX_rh (QX_extract_roots P)) ! a[=][0]).
  apply QX_extract_roots_spec_nrat; assumption.
 assert (H1 : (QX_extract_roots P) ! ((p # q)%Q)[#][0]).
  apply QX_extract_roots_spec_rat; assumption.
 apply (leEq_wdr _ _ _ _ (Liouville_lemma10 _ _ H _ _ H1)).
 fold C.
 rewrite -> (mult_commutes _ _ C).
 rewrite <- CRings.mult_assoc.
 apply mult_wdr.
 rewrite -> mult_commutes.
 apply mult_wdr.
 unfold Liouville_degree.
 symmetry; apply nexp_ring_hom.
Qed.

Theorem Liouville_theorem2 :
    {n : nat | {C : IR | [0] [<] C | forall (x : Q),
         (C[*]inj_Q IR (1#Qden x)%Q[^]n) [<=] AbsIR (inj_Q _ x [-] a)}}.
Proof.
 exists Liouville_degree.
 exists Liouville_constant.
  unfold Liouville_constant.
  apply recip_resp_pos.
  apply constant_pos.
 intro x.
 apply Liouville_theorem.
Qed.

End liouville_theorem.
