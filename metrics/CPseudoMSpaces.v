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

Require Export CoRN.reals.Intervals.

(**
* Metric Spaces (traditional)
*)

Section Relations.
(**
** Relations necessary for Pseudo Metric Spaces and Metric Spaces
%\begin{convention}%
Let [A : CSetoid], [d : (CSetoid_bin_fun A A IR)].
%\end{convention}%
*)
Variable A : CSetoid.

Variable d : CSetoid_bin_fun A A IR.

Set Implicit Arguments.
Unset Strict Implicit.

Definition com : Prop := forall x y : A, d x y[=]d y x.

Definition nneg : Prop := forall x y : A, [0][<=]d x y.

Definition pos_imp_ap : CProp := forall x y : A, [0][<]d x y -> x[#]y.

Definition tri_ineq : Prop := forall x y z : A, d x z[<=]d x y[+]d y z.

Set Strict Implicit.
Unset Implicit Arguments.

Definition diag_zero (X : CSetoid) (d : CSetoid_bin_fun X X IR) : Prop :=
  forall x : X, d x x[=][0].

Definition apdiag_imp_grzero (X : CSetoid) (d : CSetoid_bin_fun X X IR) :
  CProp := forall x y : X, x[#]y -> [0][<]d x y.

End Relations.

Section Definition_PsMS0.
(**
** Definition of Pseudo Metric Space
*)
(**
A pseudo metric space consists of a setoid and a %''pseudo metric''% #"pseudo metric"#, also called
%''distance''% #"distance"#, a binairy function that fulfils certain properties.
*)

Record is_CPsMetricSpace (A : CSetoid) (d : CSetoid_bin_fun A A IR) :
  Type :=
  {ax_d_com : com d;
   ax_d_nneg : nneg d;
   ax_d_pos_imp_ap : pos_imp_ap d;
   ax_d_tri_ineq : tri_ineq d}.

Record CPsMetricSpace : Type :=
  {cms_crr :> CSetoid;
   cms_d : CSetoid_bin_fun cms_crr cms_crr IR;
   cms_proof : is_CPsMetricSpace cms_crr cms_d}.

End Definition_PsMS0.

Arguments cms_d {c}.
Infix "[-d]" := cms_d (at level 68, left associativity).


Section PsMS_axioms.
(**
** Pseudo Metric Space axioms
%\begin{convention}%
Let [A] be a pseudo metric space.
%\end{convention}%
*)
Variable A : CPsMetricSpace.

Lemma CPsMetricSpace_is_CPsMetricSpace : is_CPsMetricSpace A cms_d.
Proof cms_proof A.

Lemma d_com : com (cms_d (c:=A)).
Proof.
 elim CPsMetricSpace_is_CPsMetricSpace.
 auto.
Qed.

Lemma d_nneg : nneg (cms_d (c:=A)).
Proof.
 elim CPsMetricSpace_is_CPsMetricSpace.
 auto.
Qed.

Lemma d_pos_imp_ap : pos_imp_ap (cms_d (c:=A)).
Proof.
 elim CPsMetricSpace_is_CPsMetricSpace.
 auto.
Qed.

Lemma d_tri_ineq : tri_ineq (cms_d (c:=A)).
Proof.
 elim CPsMetricSpace_is_CPsMetricSpace.
 auto.
Qed.

End PsMS_axioms.

Section PsMS_basics.
(**
** Pseudo Metric Space basics
%\begin{convention}%
Let [Y] be a pseudo metric space.
%\end{convention}%
*)

Variable Y : CPsMetricSpace.

Lemma rev_tri_ineq :
 forall a b c : cms_crr Y, AbsSmall (b[-d]c) ((a[-d]b)[-](a[-d]c)).
Proof.
 intros.
 unfold AbsSmall in |- *.
 split.
  apply shift_leEq_minus.
  apply shift_plus_leEq'.
  unfold cg_minus in |- *.
  cut ([--][--](b[-d]c)[=]b[-d]c).
   intros.
   apply leEq_wdr with ((a[-d]b)[+](b[-d]c)).
    apply ax_d_tri_ineq.
    apply CPsMetricSpace_is_CPsMetricSpace.
   apply eq_symmetric_unfolded.
   apply bin_op_wd_unfolded.
    apply eq_reflexive_unfolded.
   exact H.
  apply cg_inv_inv.
 astepr (c[-d]b).
  apply shift_minus_leEq.
  apply shift_leEq_plus'.
  apply shift_minus_leEq.
  apply ax_d_tri_ineq.
  apply CPsMetricSpace_is_CPsMetricSpace.
 apply ax_d_com.
 apply CPsMetricSpace_is_CPsMetricSpace.
Qed.

(**
Instead of taking [pos_imp_ap] as axiom,
we could as well have taken [diag_zero].
*)

Lemma diag_zero_imp_pos_imp_ap :
 forall (X : CSetoid) (d : CSetoid_bin_fun X X IR),
 diag_zero X d -> pos_imp_ap d.
Proof.
 intros X d.
 unfold diag_zero in |- *.
 unfold pos_imp_ap in |- *.
 intros H.
 intros x y H0.
 cut (x[#]x or x[#]y).
  intro H1.
  elim H1.
   cut (Not (x[#]x)).
    intros H3 H4.
    set (H5 := H3 H4) in *.
    intuition.
   apply ap_irreflexive_unfolded.
  intro H2.
  exact H2.
 apply (csbf_strext X X IR d).
 astepl ZeroR.
 apply less_imp_ap.
 exact H0.
Qed.

Lemma pos_imp_ap_imp_diag_zero :
 forall (X : CSetoid) (d : CSetoid_bin_fun X X IR),
 pos_imp_ap d -> nneg d -> diag_zero X d.
Proof.
 intros X d.
 unfold pos_imp_ap in |- *.
 unfold nneg in |- *.
 intros H H6.
 unfold diag_zero in |- *.
 intro x.
 apply not_ap_imp_eq.
 red in |- *.
 intro H0.
 set (H1 := less_conf_ap IR (d x x) [0]) in *.
 generalize H1.
 unfold Iff in |- *.
 intro H2.
 elim H2.
 intros H3 H4.
 set (H5 := H3 H0) in *.
 elim H5.
  generalize H6.
  intros H7 H8.
  set (H9 := H7 x x) in *.
  rewrite -> leEq_def in H9.
  set (H10 := H9 H8) in *.
  exact H10.
 intro H7.
 set (H8 := H x x) in *.
 set (H9 := H8 H7) in *.
 set (H10 := ap_irreflexive_unfolded X x H9) in *.
 exact H10.
Qed.

Lemma is_CPsMetricSpace_diag_zero :
 forall (X : CSetoid) (d : CSetoid_bin_fun X X IR),
 com d /\ tri_ineq d /\ nneg d /\ diag_zero X d -> is_CPsMetricSpace X d.
Proof.
 intros X d H.
 elim H.
 intros H1 H2.
 elim H2.
 intros H3 H4.
 elim H4.
 intros H5 H6.
 apply (Build_is_CPsMetricSpace X d H1 H5 (diag_zero_imp_pos_imp_ap X d H6) H3).
Qed.

End PsMS_basics.

Section Zerof.
(**
** Zero function
*)
(**
Every setoid forms with the binary function that always returns zero,
a pseudo metric space.
*)

Definition zero_fun (X : CSetoid) (x y : X) : IR := ZeroR.

Lemma zero_fun_strext :
 forall X : CSetoid, bin_fun_strext X X IR (zero_fun X).
Proof.
 intro X.
 unfold bin_fun_strext in |- *.
 unfold zero_fun in |- *.
 intros x1 x2 y1 y2 Z.
 set (H := ap_irreflexive_unfolded IR [0] Z) in *.
 intuition.
Qed.

Definition Zero_fun (X : CSetoid) :=
  Build_CSetoid_bin_fun X X IR (zero_fun X) (zero_fun_strext X).

Lemma zero_fun_com : forall X : CSetoid, com (Zero_fun X).
Proof.
 intro X.
 unfold com in |- *.
 intros x y.
 unfold Zero_fun in |- *.
 simpl in |- *.
 unfold zero_fun in |- *.
 intuition; auto with *.
Qed.

Lemma zero_fun_nneg : forall X : CSetoid, nneg (Zero_fun X).
Proof.
 intro X.
 unfold nneg in |- *.
 intros x y.
 unfold Zero_fun in |- *.
 simpl in |- *.
 unfold zero_fun in |- *.
 apply eq_imp_leEq.
 intuition; auto with *.
Qed.

Lemma zero_fun_pos_imp_ap : forall X : CSetoid, pos_imp_ap (Zero_fun X).
Proof.
 intro X.
 unfold pos_imp_ap in |- *.
 intros x y.
 unfold Zero_fun in |- *.
 simpl in |- *.
 unfold zero_fun in |- *.
 intro Z.
 set (H := less_irreflexive IR [0] Z) in *.
 intuition.
Qed.

Lemma zero_fun_tri_ineq : forall X : CSetoid, tri_ineq (Zero_fun X).
Proof.
 intro X.
 unfold tri_ineq in |- *.
 intros x y z.
 unfold Zero_fun in |- *.
 simpl in |- *.
 unfold zero_fun in |- *.
 apply eq_imp_leEq.
 rational.
Qed.

Definition zf_is_CPsMetricSpace (X : CSetoid) :=
  Build_is_CPsMetricSpace X (Zero_fun X) (zero_fun_com X) (
    zero_fun_nneg X) (zero_fun_pos_imp_ap X) (zero_fun_tri_ineq X).

Definition zf_as_CPsMetricSpace (X : CSetoid) :=
  Build_CPsMetricSpace X (Zero_fun X) (zf_is_CPsMetricSpace X).

End Zerof.
