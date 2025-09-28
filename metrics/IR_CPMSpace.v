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

Require Export CoRN.metrics.ContFunctions.

Section Reals.
(**
** Real numbers
*)
(**
%\begin{convention}%
Let [X] be a  pseudo metric space.
%\end{convention}%
*)
(**
The real numbers with the usual distance form a pseudo metric space.
*)

Definition dIR (x y : IR) : IR := ABSIR (x[-]y).

Lemma bin_fun_strext_dIR : bin_fun_strext IR IR IR dIR.
Proof.
 unfold bin_fun_strext in |- *.
 unfold dIR in |- *.
 intros.
 apply cg_minus_strext.
 apply un_op_strext_unfolded with AbsIR.
 auto.
Qed.

Definition dIR_as_CSetoid_fun :=
  Build_CSetoid_bin_fun IR IR IR dIR bin_fun_strext_dIR.

Lemma dIR_nneg : forall x y : IR, [0][<=]dIR_as_CSetoid_fun x y.
Proof.
 unfold dIR_as_CSetoid_fun in |- *.
 unfold dIR in |- *.
 simpl in |- *.
 intros.
 apply AbsIR_nonneg.
Qed.

Lemma dIR_com :
 forall x y : IR, dIR_as_CSetoid_fun x y[=]dIR_as_CSetoid_fun y x.
Proof.
 unfold dIR_as_CSetoid_fun in |- *.
 unfold dIR in |- *.
 simpl in |- *.
 exact AbsIR_minus.
Qed.

Lemma dIR_pos_imp_ap :
 forall x y : IR, [0][<]dIR_as_CSetoid_fun x y -> x[#]y.
Proof.
 unfold dIR_as_CSetoid_fun in |- *.
 simpl in |- *.
 intros x y H.
 cut (x[#]x or y[#]x).
  intro H0.
  apply ap_symmetric_unfolded.
  elim H0.
   intro H1.
   cut False.
    intuition.
   cut (Not (x[#]x)).
    intro H2.
    exact (H2 H1).
   apply ap_irreflexive_unfolded.
  intro H1.
  exact H1.
 apply bin_fun_strext_dIR.
 astepr ZeroR.
  apply ap_symmetric_unfolded.
  apply less_imp_ap.
  exact H.
 unfold dIR in |- *.
 astepr (ABSIR ZeroR).
  apply eq_symmetric_unfolded.
  apply AbsIRz_isz.
 apply AbsIR_wd.
 apply eq_symmetric_unfolded.
 apply cg_minus_correct.
Qed.

(* begin hide *)
Lemma IR_tri_ineq : forall a b : IR, AbsIR (a[+]b)[<=]AbsIR a[+]AbsIR b.
Proof.
 intros a b.
 astepr (AbsIR (AbsIR a[+]AbsIR b)).
  apply AbsSmall_imp_AbsIR.
  unfold AbsSmall in |- *.
  split.
   apply inv_cancel_leEq.
   astepr (AbsIR (AbsIR a[+]AbsIR b)).
   astepl ([--]a[+][--]b).
   astepr (AbsIR a[+]AbsIR b).
    apply plus_resp_leEq_both.
     apply inv_leEq_AbsIR.
    apply inv_leEq_AbsIR.
   apply eq_symmetric_unfolded.
   apply AbsIR_eq_x.
   astepl (ZeroR[+]ZeroR).
   apply plus_resp_leEq_both.
    apply AbsIR_nonneg.
   apply AbsIR_nonneg.
  astepr (AbsIR a[+]AbsIR b).
   apply plus_resp_leEq_both.
    apply leEq_AbsIR.
   apply leEq_AbsIR.
  apply eq_symmetric_unfolded.
  apply AbsIR_eq_x.
  astepl (ZeroR[+]ZeroR).
  apply plus_resp_leEq_both.
   apply AbsIR_nonneg.
  apply AbsIR_nonneg.
 apply AbsIR_eq_x.
 astepl (ZeroR[+]ZeroR).
 apply plus_resp_leEq_both.
  apply AbsIR_nonneg.
 apply AbsIR_nonneg.
Qed.
(* end hide *)

Lemma dIR_tri_ineq : tri_ineq dIR_as_CSetoid_fun.
Proof.
 unfold tri_ineq in |- *.
 intros x y z.
 unfold dIR_as_CSetoid_fun in |- *.
 unfold dIR in |- *.
 simpl in |- *.
 astepl (ABSIR (x[+]([--]y[+]y)[-]z)).
  astepl (ABSIR (x[+][--]y[+](y[-]z))).
   astepl (ABSIR (x[-]y[+](y[-]z))).
   apply IR_tri_ineq.
  apply AbsIR_wd.
  rational.
 apply AbsIR_wd.
 rational.
Qed.

Definition IR_dIR_is_CPsMetricSpace :=
  Build_is_CPsMetricSpace IR dIR_as_CSetoid_fun dIR_com dIR_nneg
    dIR_pos_imp_ap dIR_tri_ineq.


Definition IR_as_CPsMetricSpace :=
  Build_CPsMetricSpace IR dIR_as_CSetoid_fun IR_dIR_is_CPsMetricSpace.

Variable X : CPsMetricSpace.

Lemma rev_tri_ineq' :
 forall a b c : X,
 cms_d (c:=IR_as_CPsMetricSpace) (a[-d]b) (a[-d]c)[<=]b[-d]c.
Proof.
 simpl in |- *.
 unfold dIR in |- *.
 intros a b c.
 apply AbsSmall_imp_AbsIR.
 apply rev_tri_ineq.
Qed.

(**
A pseudo metric is Lipschitz. Hence it is uniformly continuous and continuous.
*)

Lemma d_is_lipschitz :
 forall a : X,
 lipschitz (projected_bin_fun X X IR_as_CPsMetricSpace (cms_d (c:=X)) a).
Proof.
 intro a.
 red in |- *.
 simpl in |- *.
 exists 0.
 intros x y.
 astepr (OneR[*](x[-d]y)).
 astepr (x[-d]y).
 apply rev_tri_ineq'.
Qed.

Lemma d_is_uni_continuous :
 forall a : X,
 uni_continuous (projected_bin_fun X X IR_as_CPsMetricSpace (cms_d (c:=X)) a).
Proof.
 intro a.
 apply lipschitz_imp_uni_continuous.
 apply d_is_lipschitz.
Qed.

Lemma d_is_continuous :
 forall a : X,
 continuous (projected_bin_fun X X IR_as_CPsMetricSpace (cms_d (c:=X)) a).
Proof.
 intro a.
 apply uni_continuous_imp_continuous.
 apply d_is_uni_continuous.
Qed.

End Reals.

Section Addition.
(**
** Addition of continuous functions
*)

(**
The sum of two Lipschitz/uniformly continous/continuous functions is again
Lipschitz/uniformly continuous/continuous.
*)

Lemma plus_resp_lipschitz :
 forall (X : CPsMetricSpace) (f g : CSetoid_fun X IR_as_CPsMetricSpace)
   (H : lipschitz f) (H1 : lipschitz g),
 lipschitz
   (compose_CSetoid_bin_fun X IR_as_CPsMetricSpace IR_as_CPsMetricSpace f g
      (csg_op (c:=IR))).
Proof.
 red in |- *.
 unfold lipschitz in |- *.
 intros X f g H H1.
 elim H.
 intros x H2.
 elim H1.
 intros x0 H3.
 exists (Nat.max x x0 + 1).
 intros x1 y.
 astepl (dIR (f x1[+]g x1) (f y[+]g y)).
 unfold dIR in |- *.
 unfold dIR in |- *.
 astepl (ABSIR (g x1[-]g y[+](f x1[-]f y))).
  apply leEq_transitive with (ABSIR (g x1[-]g y)[+]ABSIR (f x1[-]f y)).
   apply IR_tri_ineq.
  apply leEq_transitive with ((Two:IR)[^]x0[*](x1[-d]y)[+]ABSIR (f x1[-]f y)).
   apply plus_resp_leEq.
   astepl (g x1[-d]g y).
   apply H3.
  apply leEq_transitive with (Two[^]x0[*](x1[-d]y)[+]Two[^]x[*](x1[-d]y)).
   apply plus_resp_leEq_lft.
   astepl (f x1[-d]f y).
   apply H2.
  astepr ((Two:IR)[*]Two[^]Nat.max x x0[*](x1[-d]y)).
   apply leEq_transitive with (Two[^]Nat.max x x0[*](x1[-d]y)[+]Two[^]Nat.max x x0[*](x1[-d]y)).
    apply plus_resp_leEq_both.
     apply mult_resp_leEq_rht.
      apply great_nexp_resp_le.
       apply less_leEq.
       apply one_less_two.
      intuition; auto with *.
     apply ax_d_nneg.
     apply CPsMetricSpace_is_CPsMetricSpace.
    apply mult_resp_leEq_rht.
     apply great_nexp_resp_le.
      apply less_leEq.
      apply one_less_two.
     intuition; auto with *.
    apply ax_d_nneg.
    apply CPsMetricSpace_is_CPsMetricSpace.
   apply eq_imp_leEq.
   rational.
  astepl (Two[^]1[*]Two[^]Nat.max x x0[*](x1[-d]y)).
  2: apply AbsIR_wd.
  apply mult_wdl.
  astepl ((Two:IR)[^](Nat.max x x0 + 1)).
   2: astepl ((Two:IR)[^]Nat.max x x0[*]Two[^]1).
   2: apply mult_commutes.
  astepr ((Two:IR)[^](Nat.max x x0 + 1)).
  rational.
 rational.

Qed.


Lemma plus_resp_uni_continuous :
 forall (X : CPsMetricSpace) (f g : CSetoid_fun X IR_as_CPsMetricSpace)
   (H : uni_continuous f) (H1 : uni_continuous g),
 uni_continuous
   (compose_CSetoid_bin_fun X IR_as_CPsMetricSpace IR_as_CPsMetricSpace f g
      (csg_op (c:=IR))).
Proof.
 unfold uni_continuous in |- *.
 unfold IR_as_CPsMetricSpace in |- *.
 unfold dIR_as_CSetoid_fun in |- *.
 unfold dIR in |- *.
 intros X f g H H0.
 intros n H1.
 elim (H (S n) H1).
 intros x H2.
 elim (H0 (S n) H1).
 intros x0 H3.
 exists (Nat.max x x0).
 intros x1 y H6.
 astepl (ABSIR (f x1[-]f y[+](g x1[-]g y))).
  apply leEq_less_trans with (ABSIR (f x1[-]f y)[+]ABSIR (g x1[-]g y)).
   apply IR_tri_ineq.
  apply less_leEq_trans with ((OneR[/] Two:IR[//]H1)[^]S n[+]ABSIR (g x1[-]g y)).
   apply plus_resp_less_rht.
   generalize H2.
   simpl in |- *.
   intro H7.
   apply H7.
   generalize H6.
   intro H8.
   apply less_leEq_trans with (nexp IR (Nat.max x x0) ([1][/] [0][+][1][+][1][//]H1)).
    apply H8.
   3: simpl in |- *.
   astepl (nexp IR (Nat.max x x0) ([1][/] Two:IR[//]H1)).
   astepr (nexp IR x ([1][/] Two:IR[//]H1)).
   astepl ((OneR[/] Two:IR[//]H1)[^]Nat.max x x0).
   astepr ((OneR[/] Two:IR[//]H1)[^]x).
   apply small_nexp_resp_le.
     apply shift_leEq_div.
      apply pos_two.
     astepl ZeroR.
     apply less_leEq.
     apply pos_one.
    apply shift_div_leEq.
     apply pos_two.
    astepr (Two:IR).
    apply less_leEq.
    apply one_less_two.
   intuition; auto with *.
  apply leEq_transitive with ((OneR[/] Two:IR[//]H1)[^]S n[+]([1][/] Two:IR[//]H1)[^]S n).
   apply plus_resp_leEq_lft.
   apply less_leEq.
   generalize H3.
   simpl in |- *.
   intro H7.
   apply H7.
   apply less_leEq_trans with (nexp IR (Nat.max x x0) ([1][/] Two:IR[//]H1)).
    exact H6.
   astepr (nexp IR x0 ([1][/] Two:IR[//]H1)).
   astepl ((OneR[/] Two:IR[//]H1)[^]Nat.max x x0).
   astepr ((OneR[/] Two:IR[//]H1)[^]x0).
   apply small_nexp_resp_le.
     apply shift_leEq_div.
      apply pos_two.
     astepl ZeroR.
     apply less_leEq.
     apply pos_one.
    apply shift_div_leEq.
     apply pos_two.
    astepr (Two:IR).
    apply less_leEq.
    apply one_less_two.
   intuition; auto with *.
  apply eq_imp_leEq.
  astepl ((Two:IR)[*]([1][/] Two:IR[//]H1)[^]S n).
  astepl ((Two:IR)[*]([1][^]S n[/] (Two:IR)[^]S n[//]nexp_resp_ap_zero (S n) H1)).
  astepl ((Two:IR)[*]([1][/] (Two:IR)[^]S n[//]nexp_resp_ap_zero (S n) H1)).
  astepl ((Two:IR)[*] (([1][/] (Two:IR)[^]n[//]nexp_resp_ap_zero n H1)[*]([1][/] Two:IR[//]H1))).
   2: apply mult_wdr.
   2: astepl (([1][/] Two:IR[//]H1)[^]S n).
    3: astepl (([1][/] Two:IR[//]H1)[^]n[*]([1][/] Two:IR[//]H1)).
    rstepl (([1][/] (Two:IR)[^]n[//]nexp_resp_ap_zero n H1)[*]Two[*] ([1][/] Two:IR[//]H1)).
    astepl (([1][/] (Two:IR)[^]n[//]nexp_resp_ap_zero n H1)[*] (Two[*]([1][/] Two:IR[//]H1))).
    rstepl (([1][/] (Two:IR)[^]n[//]nexp_resp_ap_zero n H1)[*][1]).
    rstepl ([1][/] (Two:IR)[^]n[//]nexp_resp_ap_zero n H1).
    astepl ((OneR[/] Two:IR[//]H1)[^]n).
    apply eq_reflexive.
   3: apply AbsIR_wd.
   3: rational.
  astepr ((OneR[/] Two:IR[//]H1)[^]S n).
  apply eq_reflexive.
 astepr (([1][/] Two:IR[//]H1)[^]n[*]([1][/] Two:IR[//]H1)).
 apply eq_reflexive.

Qed.

Lemma plus_resp_continuous :
 forall (X : CPsMetricSpace) (f g : CSetoid_fun X IR_as_CPsMetricSpace)
   (H : continuous f) (H1 : continuous g),
 continuous
   (compose_CSetoid_bin_fun X IR_as_CPsMetricSpace IR_as_CPsMetricSpace f g
      (csg_op (c:=IR))).
Proof.
 unfold continuous in |- *.
 simpl in |- *.
 unfold dIR in |- *.
 intros X f g H H0.
 intros x n H1.
 simpl in |- *.
 elim (H x (S n) H1).
 intros xn H2.
 elim (H0 x (S n) H1).
 intros x0 H3.
 exists (Nat.max xn x0).
 intros y H6.
 astepl (ABSIR (f x[-]f y[+](g x[-]g y))).
  apply leEq_less_trans with (ABSIR (f x[-]f y)[+]ABSIR (g x[-]g y)).
   apply IR_tri_ineq.
  apply less_leEq_trans with ((OneR[/] [0][+][1][+][1][//]H1)[^]S n[+]ABSIR (g x[-]g y)).
   apply plus_resp_less_rht.
   apply H2.
   apply less_leEq_trans with (nexp IR (Nat.max xn x0) ([1][/] [0][+][1][+][1][//]H1)).
    exact H6.
   astepl ((OneR[/] [0][+][1][+][1][//]H1)[^]Nat.max xn x0).
   astepr ((OneR[/] [0][+][1][+][1][//]H1)[^]xn).
   apply small_nexp_resp_le.
     apply shift_leEq_div.
      astepr (Two:IR).
      apply pos_two.
     astepl ZeroR.
     apply less_leEq.
     apply pos_one.
    apply shift_div_leEq.
     astepr (Two:IR).
     apply pos_two.
    astepr (OneR[+][1]).
     astepr (Two:IR).
     apply less_leEq.
     apply one_less_two.
    rational.
   intuition; auto with *.
  apply leEq_transitive with ((OneR[/] [0][+][1][+][1][//]H1)[^]S n[+]
    ([1][/] [0][+][1][+][1][//]H1)[^]S n).
   apply plus_resp_leEq_lft.
   apply less_leEq.
   apply H3.
   apply less_leEq_trans with (nexp IR (Nat.max xn x0) ([1][/] [0][+][1][+][1][//]H1)).
    exact H6.
   astepl ((OneR[/] [0][+][1][+][1][//]H1)[^]Nat.max xn x0).
   astepr ((OneR[/] [0][+][1][+][1][//]H1)[^]x0).
   apply small_nexp_resp_le.
     apply shift_leEq_div.
      astepr (Two:IR).
      apply pos_two.
     astepl ZeroR.
     apply less_leEq.
     apply pos_one.
    apply shift_div_leEq.
     astepr (Two:IR).
     apply pos_two.
    astepr (OneR[+][1]).
     astepr (Two:IR).
     apply less_leEq.
     apply one_less_two.
    rational.
   intuition; auto with *.
  apply eq_imp_leEq.
  astepl ((Two:IR)[*]([1][/] [0][+][1][+][1][//]H1)[^]S n).
  astepr ((OneR[/] [0][+][1][+][1][//]H1)[^]n).
  astepl ((Two:IR)[*] ([1][^]S n[/] ([0][+][1][+][1])[^]S n[//]nexp_resp_ap_zero (S n) H1)).
  astepl ((Two:IR)[*]([1][/] ([0][+][1][+][1])[^]S n[//]nexp_resp_ap_zero (S n) H1)).
  astepl ((Two:IR)[*] (([1][/] ([0][+][1][+][1])[^]n[//]nexp_resp_ap_zero n H1)[*]
    ([1][/] [0][+][1][+][1][//]H1))).
   2: apply mult_wdr.
   2: astepl (([1][/] [0][+][1][+][1][//]H1)[^]S n).
    3: astepl (([1][/] [0][+][1][+][1][//]H1)[^]n[*]([1][/] [0][+][1][+][1][//]H1)).
    3: astepr (([1][/] [0][+][1][+][1][//]H1)[^]n[*]([1][/] [0][+][1][+][1][//]H1)).
    3: apply eq_reflexive.
   rstepl (([1][/] ([0][+][1][+][1])[^]n[//]nexp_resp_ap_zero n H1)[*]Two[*]
     ([1][/] [0][+][1][+][1][//]H1)).
   astepl (([1][/] ([0][+][1][+][1])[^]n[//]nexp_resp_ap_zero n H1)[*]
     (Two[*]([1][/] [0][+][1][+][1][//]H1))).
   rstepl (([1][/] ([0][+][1][+][1])[^]n[//]nexp_resp_ap_zero n H1)[*][1]).
   rstepl ([1][/] ([0][+][1][+][1])[^]n[//]nexp_resp_ap_zero n H1).
   astepl ((OneR[/] [0][+][1][+][1][//]H1)[^]n).
   apply eq_reflexive.
  astepr (([1][/] [0][+][1][+][1][//]H1)[^]S n).
  apply eq_reflexive.
 apply AbsIR_wd.
 rational.
Qed.


End Addition.
