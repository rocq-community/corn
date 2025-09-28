(* Copyright © 1998-2006
 * Henk Barendregt
 * Luís Cruz-Filipe
 * Herman Geuvers
 * Mariusz Giero
 * Rik van Ginneken
 * Dimitri Hendriks
 * Sébastien Hinderer
 * Bart Kirkels
 * Pierre Letouzey
 * Iris Loeb
 * Lionel Mamane
 * Milad Niqui
 * Russell O’Connor
 * Randy Pollack
 * Nickolay V. Shmyrev
 * Bas Spitters
 * Dan Synek
 * Freek Wiedijk
 * Jan Zwanenburg
 *
 * This work is free software; you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation; either version 2 of the License, or
 * (at your option) any later version.
 *
 * This work is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License along
 * with this work; if not, write to the Free Software Foundation, Inc.,
 * 51 Franklin Street, Fifth Floor, Boston, MA 02110-1301 USA.
 *)

Require Export CoRN.metrics.Prod_Sub.
Require Export CoRN.metrics.Equiv.

Section Definition_MS.
(**
** Definition of Metric Space
*)


Record CMetricSpace : Type :=
  {scms_crr :> CPsMetricSpace;
   ax_d_apdiag_imp_grzero : apdiag_imp_grzero scms_crr (cms_d (c:=scms_crr))}.


End Definition_MS.


Section MS_basics.
(**
** Metric Space basics
*)

Lemma d_CMetricSpace_apdiag_imp_grzero :
 forall X : CMetricSpace, apdiag_imp_grzero (cms_crr X) (cms_d (c:=X)).
Proof.
 intro X.
 apply ax_d_apdiag_imp_grzero.
Qed.

Lemma d_zero_imp_eq :
 forall (X : CMetricSpace) (a b : X), a[-d]b[=][0] -> a[=]b.
Proof.
 intros X a b.
 intro H.
 apply not_ap_imp_eq.
 red in |- *.
 intro H1.
 generalize H.
 apply ap_imp_neq.
 apply Greater_imp_ap.
 apply ax_d_apdiag_imp_grzero.
 exact H1.
Qed.

Lemma is_CMetricSpace_diag_zero :
 forall (X : CSetoid) (d : CSetoid_bin_fun X X IR)
   (H : com d) (H1 : tri_ineq d) (H2 : nneg d) (H3 : diag_zero X d)
   (H4 : apdiag_imp_grzero X d), CMetricSpace.
Proof.
 intros X d H H1 H2 H3 H4.
 set (H5 := Build_is_CPsMetricSpace X d H H2 (diag_zero_imp_pos_imp_ap X d H3) H1) in *.
 set (H6 := Build_CPsMetricSpace X d H5) in *.
 set (H7 := Build_CMetricSpace H6 H4) in *.
 exact H7.
Qed.

End MS_basics.
Section prodandsub.
(**
** Product-Metric-Spaces and Sub-Metric-Spaces
*)
(**
The product of two metric spaces is again a metric space.
*)

Lemma Prod0CMetricSpaces_apdiag_grzero :
 forall X Y : CMetricSpace,
 apdiag_imp_grzero (Prod0CPsMetricSpace X Y)
   (cms_d (c:=Prod0CPsMetricSpace X Y)).
Proof.
 intros X Y.
 unfold apdiag_imp_grzero in |- *.
 intros x y.
 case x.
 case y.
 intros c c0 c1 c2.
 simpl in |- *.
 intro H.
 elim H.
  intro H1.
  apply plus_resp_pos_nonneg.
   apply ax_d_apdiag_imp_grzero.
   exact H1.
  apply ax_d_nneg.
  apply CPsMetricSpace_is_CPsMetricSpace.
 intro H1.
 astepr ((c2[-d]c0)[+](c1[-d]c)).
 apply plus_resp_pos_nonneg.
  apply ax_d_apdiag_imp_grzero.
  exact H1.
 apply ax_d_nneg.
 apply CPsMetricSpace_is_CPsMetricSpace.
Qed.

Definition Prod0CMetricSpace (X Y : CMetricSpace) :=
  Build_CMetricSpace (Prod0CPsMetricSpace X Y)
    (Prod0CMetricSpaces_apdiag_grzero X Y).

(**
A subspace of a metric space is again a metric space.
*)
Arguments SubPsMetricSpace [X].

Lemma SubMetricSpace_apdiag_grzero :
 forall (X : CMetricSpace) (P : X -> CProp),
 apdiag_imp_grzero (SubPsMetricSpace P) (cms_d (c:=SubPsMetricSpace P)).
Proof.
 intros X P.
 unfold apdiag_imp_grzero in |- *.
 intros x y.
 simpl in |- *.
 case x.
 case y.
 simpl in |- *.
 intros.
 apply ax_d_apdiag_imp_grzero.
 auto.
Qed.

Definition SubMetricSpace (X : CMetricSpace) (P : X -> CProp) :=
  Build_CMetricSpace (SubPsMetricSpace P) (SubMetricSpace_apdiag_grzero X P).

Arguments SubMetricSpace [X].

End prodandsub.
Section Zeroff.
(**
** Pseudo Metric Spaces vs Metric Spaces
*)
(**
Not all pseudo metric spaces are a metric space:
*)

Lemma zf_nis_CMetricSpace :
 forall X : CSetoid,
 {x : X | {y : X | x[#]y}} ->
 Not
   (apdiag_imp_grzero (zf_as_CPsMetricSpace X)
      (cms_d (c:=zf_as_CPsMetricSpace X))).
Proof.
 intros X Z.
 red in |- *.
 intro H.
 set (H1 := Build_CMetricSpace (zf_as_CPsMetricSpace X) H) in *.
 set (H2 := d_CMetricSpace_apdiag_imp_grzero H1) in *.
 generalize H2.
 unfold H1 in |- *.
 simpl in |- *.
 unfold apdiag_imp_grzero in |- *.
 unfold Zero_fun in |- *.
 simpl in |- *.
 unfold zero_fun in |- *.
 elim Z.
 intros x Z1.
 elim Z1.
 intros y Z2.
 intros H3.
 set (H4 := H3 x y Z2) in *.
 set (H5 := less_irreflexive_unfolded IR [0] H4) in *.
 exact H5.
Qed.

(**
But a pseudo metric space induces a metric space:
*)

Definition metric_ap (X : CPsMetricSpace) (x y : X) : CProp := [0][<]x[-d]y.

Definition metric_eq (X : CPsMetricSpace) (x y : X) : Prop := x[-d]y[=][0].

Lemma metric_ap_irreflexive :
 forall X : CPsMetricSpace, irreflexive (metric_ap X).
Proof.
 intro X.
 unfold irreflexive in |- *.
 intro x.
 red in |- *.
 unfold metric_ap in |- *.
 set (H0 := pos_imp_ap_imp_diag_zero X (cms_d (c:=X))
   (ax_d_pos_imp_ap X (cms_d (c:=X)) (CPsMetricSpace_is_CPsMetricSpace X))
     (ax_d_nneg X (cms_d (c:=X)) (CPsMetricSpace_is_CPsMetricSpace X))) in *.
 generalize H0.
 unfold diag_zero in |- *.
 intros H1 H2.
 set (H3 := less_wdr IR [0] (x[-d]x) [0] H2 (H1 x)) in *.
 set (H4 := less_irreflexive_unfolded IR [0] H3) in *.
 exact H4.
Qed.

Lemma metric_ap_symmetric :
 forall X : CPsMetricSpace, Csymmetric (metric_ap X).
Proof.
 intro X.
 unfold Csymmetric in |- *.
 intros x y.
 unfold metric_ap in |- *.
 intro H.
 astepr (x[-d]y).
  exact H.
 apply ax_d_com.
 apply CPsMetricSpace_is_CPsMetricSpace.
Qed.

Lemma metric_ap_cotransitive :
 forall X : CPsMetricSpace, cotransitive (metric_ap X).
Proof.
 intro X.
 unfold cotransitive in |- *.
 unfold metric_ap in |- *.
 intros x y H z.
 cut (ZeroR[<](x[-d]z)[+](z[-d]y)).
  intro H0.
  apply positive_Sum_two.
  exact H0.
 apply less_leEq_trans with (x[-d]y).
  exact H.
 apply ax_d_tri_ineq.
 apply CPsMetricSpace_is_CPsMetricSpace.
Qed.

Lemma metric_ap_tight :
 forall X : CPsMetricSpace, tight_apart (metric_eq X) (metric_ap X).
Proof.
 intro X.
 unfold tight_apart in |- *.
 unfold metric_ap in |- *.
 unfold metric_eq in |- *.
 intros x y.
 split.
  intro H.
  cut (ZeroR[<=]x[-d]y).
   rewrite -> leEq_def in |- *.
   intro H1.
   cut (Not (x[-d]y[#][0])).
    intro H2.
    apply not_ap_imp_eq.
    exact H2.
   red in |- *.
   intro H2.
   set (H3 := less_conf_ap IR (x[-d]y) [0]) in *.
   elim H3.
   intros H4 H5.
   set (H6 := H4 H2) in *.
   elim H6.
    intuition.
   intuition.
  apply ax_d_nneg.
  apply CPsMetricSpace_is_CPsMetricSpace.
 intro H.
 red in |- *.
 intro H0.
 set (H1 := less_wdr IR [0] (x[-d]y) [0] H0 H) in *.
 set (H2 := less_irreflexive_unfolded IR [0] H1) in *.
 exact H2.
Qed.

Definition Metric_CSet_is_CSetoid (X : CPsMetricSpace) :=
  Build_is_CSetoid X (metric_eq X) (metric_ap X) (metric_ap_irreflexive X)
    (metric_ap_symmetric X) (metric_ap_cotransitive X) (
    metric_ap_tight X).

Definition Metric_CSetoid (X : CPsMetricSpace) :=
  Build_CSetoid X (metric_eq X) (metric_ap X) (Metric_CSet_is_CSetoid X).

Definition metric_d (X : CPsMetricSpace) (x y : Metric_CSetoid X) := x[-d]y.

Lemma metric_d_strext :
 forall X : CPsMetricSpace,
 bin_fun_strext (Metric_CSetoid X) (Metric_CSetoid X) IR (metric_d X).
Proof.
 intro X.
 unfold bin_fun_strext in |- *.
 intros x1 x2 y1 y2.
 simpl in |- *.
 unfold metric_d in |- *.
 unfold metric_ap in |- *.
 intro H.
 apply positive_Sum_two.
 set (H0 := less_conf_ap IR (x1[-d]y1) (x2[-d]y2)) in *.
 elim H0.
 intros H1 H2.
 set (H4 := H1 H) in *.
 elim H4.
  intro H5.
  astepr ((x1[-d]x2)[+](y1[-d]y2)[+][0]).
  astepr ((x1[-d]x2)[+](y1[-d]y2)[+]((x1[-d]y1)[-](x1[-d]y1))).
  astepr ((x1[-d]x2)[+](y1[-d]y2)[+](x1[-d]y1)[-](x1[-d]y1)).
  apply shift_less_minus.
  astepl (x1[-d]y1).
  apply less_leEq_trans with (x2[-d]y2).
   exact H5.
  apply leEq_transitive with ((x2[-d]x1)[+](x1[-d]y2)).
   apply ax_d_tri_ineq.
   apply CPsMetricSpace_is_CPsMetricSpace.
  astepr ((x2[-d]x1)[+](y1[-d]y2)[+](x1[-d]y1)).
   astepr ((x2[-d]x1)[+]((y1[-d]y2)[+](x1[-d]y1))).
   apply plus_resp_leEq_lft.
   astepr ((x1[-d]y1)[+](y1[-d]y2)).
   apply ax_d_tri_ineq.
   apply CPsMetricSpace_is_CPsMetricSpace.
  astepl ((y1[-d]y2)[+](x2[-d]x1)[+](x1[-d]y1)).
  astepr ((y1[-d]y2)[+](x1[-d]x2)[+](x1[-d]y1)).
  astepl ((y1[-d]y2)[+]((x2[-d]x1)[+](x1[-d]y1))).
  astepr ((y1[-d]y2)[+]((x1[-d]x2)[+](x1[-d]y1))).
  astepl ((y1[-d]y2)[+]((x1[-d]y1)[+](x2[-d]x1))).
  astepr ((y1[-d]y2)[+]((x1[-d]y1)[+](x1[-d]x2))).
  astepl ((y1[-d]y2)[+](x1[-d]y1)[+](x2[-d]x1)).
  astepr ((y1[-d]y2)[+](x1[-d]y1)[+](x1[-d]x2)).
  apply plus_resp_eq.
  apply ax_d_com.
  apply CPsMetricSpace_is_CPsMetricSpace.
 intro H5.
 astepr ((x1[-d]x2)[+](y1[-d]y2)[+][0]).
 astepr ((x1[-d]x2)[+](y1[-d]y2)[+]((x2[-d]y2)[-](x2[-d]y2))).
 astepr ((x1[-d]x2)[+](y1[-d]y2)[+](x2[-d]y2)[-](x2[-d]y2)).
 apply shift_less_minus.
 astepl (x2[-d]y2).
 apply less_leEq_trans with (x1[-d]y1).
  exact H5.
 apply leEq_transitive with ((x1[-d]x2)[+](x2[-d]y1)).
  apply ax_d_tri_ineq.
  apply CPsMetricSpace_is_CPsMetricSpace.
 astepr ((x1[-d]x2)[+](y1[-d]y2)[+](x2[-d]y2)).
 astepr ((x1[-d]x2)[+]((y1[-d]y2)[+](x2[-d]y2))).
 apply plus_resp_leEq_lft.
 astepr ((x2[-d]y2)[+](y1[-d]y2)).
 astepr ((x2[-d]y2)[+](y2[-d]y1)).
  apply ax_d_tri_ineq.
  apply CPsMetricSpace_is_CPsMetricSpace.
 apply plus_resp_eq.
 apply ax_d_com.
 apply CPsMetricSpace_is_CPsMetricSpace.
Qed.


Definition Metric_d (X : CPsMetricSpace) :=
  Build_CSetoid_bin_fun (Metric_CSetoid X) (Metric_CSetoid X) IR (
    metric_d X) (metric_d_strext X).

Lemma Metric_d_com : forall X : CPsMetricSpace, com (Metric_d X).
Proof.
 intro X.
 unfold com in |- *.
 intros x y.
 unfold Metric_d in |- *.
 simpl in |- *.
 unfold metric_d in |- *.
 apply ax_d_com.
 apply CPsMetricSpace_is_CPsMetricSpace.
Qed.

Lemma Metric_d_nneg : forall X : CPsMetricSpace, nneg (Metric_d X).
Proof.
 intro X.
 unfold nneg in |- *.
 intros x y.
 unfold Metric_d in |- *.
 simpl in |- *.
 unfold metric_d in |- *.
 apply ax_d_nneg.
 apply CPsMetricSpace_is_CPsMetricSpace.
Qed.

Lemma Metric_d_pos_imp_ap :
 forall X : CPsMetricSpace, pos_imp_ap (Metric_d X).
Proof.
 intro X.
 unfold pos_imp_ap in |- *.
 intros x y.
 unfold Metric_d in |- *.
 simpl in |- *.
 unfold metric_d in |- *.
 unfold metric_ap in |- *.
 intuition.
Qed.

Lemma Metric_d_tri_ineq : forall X : CPsMetricSpace, tri_ineq (Metric_d X).
Proof.
 intro X.
 unfold tri_ineq in |- *.
 intros x y z.
 unfold Metric_d in |- *.
 simpl in |- *.
 unfold metric_d in |- *.
 apply ax_d_tri_ineq.
 apply CPsMetricSpace_is_CPsMetricSpace.
Qed.

Definition QuotientCSetoid_is_CPsMetricSpace (X : CPsMetricSpace) :=
  Build_is_CPsMetricSpace (Metric_CSetoid X) (Metric_d X) (
    Metric_d_com X) (Metric_d_nneg X) (Metric_d_pos_imp_ap X)
    (Metric_d_tri_ineq X).

Definition QuotientCPsMetricSpace (X : CPsMetricSpace) :=
  Build_CPsMetricSpace (Metric_CSetoid X) (Metric_d X)
    (QuotientCSetoid_is_CPsMetricSpace X).

Lemma Metric_d_apdiag_grzero :
 forall X : CPsMetricSpace,
 apdiag_imp_grzero (QuotientCPsMetricSpace X)
   (cms_d (c:=QuotientCPsMetricSpace X)).
Proof.
 intro X.
 unfold apdiag_imp_grzero in |- *.
 intros x y.
 simpl in |- *.
 unfold metric_ap in |- *.
 unfold metric_d in |- *.
 intuition.
Qed.

Definition QuotientCMetricSpace (X : CPsMetricSpace) :=
  Build_CMetricSpace (QuotientCPsMetricSpace X) (Metric_d_apdiag_grzero X).

(**
Some pseudo metric spaces already are a metric space:
*)

Lemma dIR_apdiag_grzero :
 apdiag_imp_grzero IR_as_CPsMetricSpace (cms_d (c:=IR_as_CPsMetricSpace)).
Proof.
 unfold apdiag_imp_grzero in |- *.
 intros x y.
 simpl in |- *.
 unfold dIR in |- *.
 intro H.
 set (H0 := AbsIR_pos) in *.
 generalize H0.
 simpl in |- *.
 intro H1.
 apply H1.
 apply minus_ap_zero.
 exact H.
Qed.

Definition IR_as_CMetricSpace :=
  Build_CMetricSpace IR_as_CPsMetricSpace dIR_apdiag_grzero.

(**
In that case the induced metric space is equivalent to the original one:
*)

Definition emb (X : CPsMetricSpace) : X -> QuotientCMetricSpace X.
Proof.
 intros x.
 unfold QuotientCMetricSpace in |- *.
 simpl in |- *.
 exact x.
Defined.

Lemma emb_strext : forall X : CPsMetricSpace, fun_strext (emb X).
Proof.
 intro X.
 unfold fun_strext in |- *.
 unfold emb in |- *.
 simpl in |- *.
 unfold metric_ap in |- *.
 apply ax_d_pos_imp_ap.
 apply CPsMetricSpace_is_CPsMetricSpace.
Qed.

Definition Emb (X : CPsMetricSpace) :=
  Build_CSetoid_fun X (QuotientCMetricSpace X) (emb X) (emb_strext X).

Lemma Quotient_pres_CMetricSpace :
 forall X : CMetricSpace, isopsmetry X (QuotientCPsMetricSpace X) (Emb X).
Proof.
 intro X.
 unfold isopsmetry in |- *.
 unfold Emb in |- *.
 simpl in |- *.
 unfold emb in |- *.
 split.
  unfold bijective in |- *.
  split.
   unfold injective in |- *.
   simpl in |- *.
   intros a0 a1.
   unfold metric_ap in |- *.
   apply ax_d_apdiag_imp_grzero.
  unfold surjective in |- *.
  intro b.
  simpl in |- *.
  exists b.
  unfold metric_eq in |- *.
  apply pos_imp_ap_imp_diag_zero.
   apply d_pos_imp_ap.
  apply d_nneg.
 unfold equivalent_psmetric in |- *.
 simpl in |- *.
 split.
  split.
   apply CPsMetricSpace_is_CPsMetricSpace.
  apply Build_is_CPsMetricSpace.
     unfold com in |- *.
     simpl in |- *.
     unfold metric_d in |- *.
     apply ax_d_com.
     apply CPsMetricSpace_is_CPsMetricSpace.
    unfold nneg in |- *.
    simpl in |- *.
    unfold metric_d in |- *.
    apply ax_d_nneg.
    apply CPsMetricSpace_is_CPsMetricSpace.
   unfold pos_imp_ap in |- *.
   simpl in |- *.
   unfold metric_d in |- *.
   apply ax_d_pos_imp_ap.
   apply CPsMetricSpace_is_CPsMetricSpace.
  unfold tri_ineq in |- *.
  simpl in |- *.
  unfold metric_d in |- *.
  apply ax_d_tri_ineq.
  apply CPsMetricSpace_is_CPsMetricSpace.
 split.
  exists 0.
  unfold metric_d in |- *.
  intros x y.
  apply eq_imp_leEq.
  rational.
 exists 0.
 unfold metric_d in |- *.
 intros x y.
 apply eq_imp_leEq.
 rational.
Qed.


End Zeroff.

Section Limitt.
(**
** Limit
*)
(**
A sequence in a metric space has at most one limit.
*)
Arguments MSseqLimit [X].

(* begin hide *)
Lemma nz : forall n m : nat, n <= Nat.max n m.
Proof.
 intro n.
 intro m.
 intuition; auto with *.
Qed.
(* end hide *)

(* begin hide *)
Lemma d_wd :
 forall (X : CPsMetricSpace) (a b c : X), a[=]b -> a[-d]c[=]b[-d]c.
Proof.
 intros X a b c.
 intros H.
 apply not_ap_imp_eq.
 red in |- *.
 intro H1.
 cut (a[#]b or c[#]c).
  intro H2.
  elim H2.
   apply eq_imp_not_ap.
   exact H.
  apply ap_irreflexive_unfolded.
 cut (a[-d]c[#]b[-d]c -> a[#]b or c[#]c).
  intro H2.
  apply H2.
  exact H1.
 apply csbf_strext.
Qed.
(* end hide *)

Lemma unique_MSseqLim :
 forall (X : CMetricSpace) (seq : nat -> X) (a b : X),
 MSseqLimit seq a and MSseqLimit seq b -> a[=]b.
Proof.
 intros X seq a b.
 unfold MSseqLimit in |- *.
 simpl in |- *.
 intros H.
 apply d_zero_imp_eq.
 apply not_ap_imp_eq.
 red in |- *.
 intro H1.
 set (H2 := recip_ap_zero IR (a[-d]b) H1) in *.
 set (H3 := Archimedes' (OneR[/] a[-d]b[//]H1)) in *.
 elim H3.
 intros n H4.
 set (H6 := less_transitive_unfolded IR ([1][/] a[-d]b[//]H1) (
   nring n) (nring n[+][1]) H4 (nring_less_succ IR n)) in *.
 elim H.
 intros H5 H7.
 elim (H5 (S (S n)) (ap_symmetric_unfolded IR [0] ([0][+][1][+][1])
   (less_imp_ap IR [0] ([0][+][1][+][1]) (less_transitive_unfolded IR [0] ([0][+][1]) (
     [0][+][1][+][1]) (less_plusOne IR [0]) (less_plusOne IR (ZeroR[+][1])))))).
 intros x H8.
 elim (H7 (S (S n)) (ap_symmetric_unfolded IR [0] ([0][+][1][+][1])
   (less_imp_ap IR [0] ([0][+][1][+][1]) (less_transitive_unfolded IR [0] ([0][+][1]) (
     [0][+][1][+][1]) (less_plusOne IR [0]) (less_plusOne IR ([0][+][1]:IR)))))).
 intros y H9.
 set (H10 := H9 (Nat.max y x)) in *.
 set (H11 := H8 (Nat.max x y)) in *.
 simpl in |- *.
 set (H12 := H11 (nz x y)) in *.
 set (H13 := H10 (nz y x)) in *.
 set (H14 := ap_symmetric_unfolded IR [0] ([0][+][1][+][1]) (less_imp_ap IR [0] ([0][+][1][+][1])
   (less_transitive_unfolded IR [0] ([0][+][1]) ( [0][+][1][+][1]) (less_plusOne IR [0])
     (less_plusOne IR ([0][+][1]))))) in *.
 cut ((seq (Nat.max x y)[-d]a)[+](seq (Nat.max y x)[-d]b)[<]
   nexp IR (S (S n)) ([1][/] [0][+][1][+][1][//]H14)[+]
     nexp IR (S (S n)) ([1][/] [0][+][1][+][1][//]H14)).
  intro H15.
  cut (nexp IR (S (S n)) ([1][/] [0][+][1][+][1][//]H14)[+]
    nexp IR (S (S n)) ([1][/] [0][+][1][+][1][//]H14)[<=]
      (seq (Nat.max x y)[-d]a)[+](seq (Nat.max y x)[-d]b)).
   rewrite -> leEq_def in |- *.
   intro H16.
   auto.
  cut (nexp IR (S (S n)) ([1][/] [0][+][1][+][1][//]H14)[+]
    nexp IR (S (S n)) ([1][/] [0][+][1][+][1][//]H14)[<=] a[-d]b).
   intro H16.
   apply leEq_transitive with (a[-d]b).
    exact H16.
   astepr ((seq (Nat.max x y)[-d]a)[+](seq (Nat.max x y)[-d]b)).
    astepr ((a[-d]seq (Nat.max x y))[+](seq (Nat.max x y)[-d]b)).
     apply ax_d_tri_ineq.
     apply CPsMetricSpace_is_CPsMetricSpace.
    astepl ((seq (Nat.max x y)[-d]b)[+](a[-d]seq (Nat.max x y))).
    astepr ((seq (Nat.max x y)[-d]b)[+](seq (Nat.max x y)[-d]a)).
    apply plus_resp_eq.
    simpl in |- *.
    apply d_com.
   apply plus_resp_eq.
   apply d_wd.
   cut (Nat.max x y = Nat.max y x -> seq (Nat.max x y)[=]seq (Nat.max y x)).
    intro H17.
    apply H17.
    apply Nat.max_comm.
   intro H17.
   rewrite H17.
   apply eq_reflexive.
  astepl ((Two:IR)[*]nexp IR (S (S n)) ([1][/] [0][+][1][+][1][//]H14)).
  astepl (nexp IR (S n) ([1][/] [0][+][1][+][1][//]H14)).
   astepl (([1][/] [0][+][1][+][1][//]H14)[^]S n).
   astepl ([1][/] ([0][+][1][+][1])[^]S n[//]nexp_resp_ap_zero (S n) H14).
   apply leEq_transitive with ([1][/] nring (S n)[//] ap_symmetric_unfolded IR [0] (nring (S n))
     (less_imp_ap IR [0] (nring (S n)) (pos_Snring IR n))).
    apply leEq_transitive with ([1][/] ([0][+][1][+][1])[^]S n[//]nexp_resp_ap_zero (S n) H14).
     2: apply less_leEq.
     2: set (Hn := bin_less_un) in *.
     2: generalize Hn.
     2: simpl in |- *.
     2: intro Hn'.
     2: apply Hn'.
    apply recip_resp_leEq.
     apply nexp_resp_pos.
     astepr (Two:IR).
     apply pos_two.
    apply eq_imp_leEq.
    apply eq_reflexive_unfolded.
   apply shift_div_leEq.
    apply (pos_Snring IR n).
   apply shift_leEq_mult' with H1.
    2: apply less_leEq.
    2: apply H6.
   cut ([0][<]a[-d]b or a[-d]b[<][0]).
    intro H16.
    elim H16.
     intro H17.
     exact H17.
    intro H17.
    set (H18 := ax_d_nneg X (cms_d (c:=X))) in *.
    generalize H18.
    unfold nneg in |- *.
    intro H19.
    set (H20 := H19 (CPsMetricSpace_is_CPsMetricSpace X) a b) in *.
    rewrite -> leEq_def in H20.
    set (H21 := H20 H17) in *.
    intuition.
   apply ap_imp_less.
   apply ap_symmetric_unfolded.
   exact H1.
  astepl ((OneR[/] [0][+][1][+][1][//]H14)[^]S n).
  astepl (OneR[^]S n[/] ([0][+][1][+][1])[^]S n[//]nexp_resp_ap_zero (S n) H14).
  astepl (OneR[/] ([0][+][1][+][1])[^]S n[//]nexp_resp_ap_zero (S n) H14).
  astepl ((OneR[+][1])[*] ([1][/] ([0][+][1][+][1])[^]S (S n)[//]nexp_resp_ap_zero (S (S n)) H14)).
   apply mult_cancel_lft with (OneR[/] [0][+][1][+][1][//]H14).
    apply div_resp_ap_zero_rev.
    apply ap_symmetric_unfolded.
    apply less_imp_ap.
    apply pos_one.
   astepr (([1][/] [0][+][1][+][1][//]H14)[*]([0][+][1][+][1])[*]
     ([1][/] ([0][+][1][+][1])[^]S (S n)[//]nexp_resp_ap_zero (S (S n)) H14)).
    astepr (OneR[*] ([1][/] ([0][+][1][+][1])[^]S (S n)[//]nexp_resp_ap_zero (S (S n)) H14)).
    astepr (OneR[/] ([0][+][1][+][1])[^]S (S n)[//]nexp_resp_ap_zero (S (S n)) H14).
    astepr (OneR[*][1][/] ([0][+][1][+][1])[*]([0][+][1][+][1])[^]S n[//]
      mult_resp_ap_zero IR ([0][+][1][+][1]) (([0][+][1][+][1])[^]S n) H14
        (nexp_resp_ap_zero (S n) H14)).
    astepr ([1][*][1][/] ([0][+][1][+][1])[^]S (S n)[//] nexp_resp_ap_zero (S (S n)) H14).
    rational.
   astepr (([1][/] [0][+][1][+][1][//]H14)[*]Two[*]
     nexp IR (S (S n)) ([1][/] [0][+][1][+][1][//]H14)).
   astepr (([1][/] [0][+][1][+][1][//]H14)[*]([0][+][1][+][1])[*]
     nexp IR (S (S n)) ([1][/] [0][+][1][+][1][//]H14)).
   apply mult_wdr.
   3: apply plus_resp_less_both.
    3: exact H12.
   3: exact H13.
  astepr (([1][/] [0][+][1][+][1][//]H14)[^]S (S n)).
  apply eq_symmetric_unfolded.
  apply nexp_distr_recip.
 astepl ([1][+][1][/] ([0][+][1][+][1])[^]S (S n)[//] nexp_resp_ap_zero (S (S n)) H14).
  2: rational.
 astepl ([0][+][1][+][1][/] ([0][+][1][+][1])[^]S (S n)[//] nexp_resp_ap_zero (S (S n)) H14).
 rstepr ([0][+][1][+][1][/] ([0][+][1][+][1])[*]([0][+][1][+][1])[^]S n[//]
   mult_resp_ap_zero IR ([0][+][1][+][1]) (([0][+][1][+][1])[^]S n) H14
     (nexp_resp_ap_zero (S n) H14)).
 astepl ([0][+][1][+][1][/] ([0][+][1][+][1])[*]([0][+][1][+][1])[^]S n[//]
   mult_resp_ap_zero IR ([0][+][1][+][1]) (([0][+][1][+][1])[^]S n) H14
     (nexp_resp_ap_zero (S n) H14)).
 apply eq_reflexive_unfolded.
Qed.

End Limitt.
