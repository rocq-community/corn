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

Require Export CoRN.metrics.CPseudoMSpaces.

Section Continuous_functions.
(**
** Continuous functions, uniformly continuous functions and Lipschitz functions
%\begin{convention}%
Let [A] and [B] be pseudo metric spaces.
%\end{convention}%
*)

Variable A : CPsMetricSpace.
Variable B : CPsMetricSpace.

(**
We will look at some notions of continuous functions.
*)

Definition continuous (f : CSetoid_fun A B) : CProp :=
  forall (x : A) (n : nat) (H : Two[#][0]),
  {m : nat |
  forall y : A,
  x[-d]y[<]([1][/] Two[//]H)[^]m -> f x[-d]f y[<]([1][/] Two[//]H)[^]n}.

Definition continuous' (f : CSetoid_fun A B) : CProp :=
  forall (x : A) (n : nat),
  {m : nat |
  forall y : A, x[-d]y[<=]one_div_succ m -> f x[-d]f y[<=]one_div_succ n}.

Definition uni_continuous (f : CSetoid_fun A B) : CProp :=
  forall (n : nat) (H : Two[#][0]),
  {m : nat |
  forall x y : A,
  x[-d]y[<]([1][/] Two:IR[//]H)[^]m -> f x[-d]f y[<]([1][/] Two:IR[//]H)[^]n}.

Definition uni_continuous' (f : CSetoid_fun A B) : CProp :=
  forall n : nat,
  {m : nat |
  forall x y : A, x[-d]y[<=]one_div_succ m -> f x[-d]f y[<=]one_div_succ n}.

Definition uni_continuous'' (f : CSetoid_fun A B) : CProp :=
  {mds : nat -> nat |
  forall (n : nat) (x y : A),
  x[-d]y[<=]one_div_succ (mds n) -> f x[-d]f y[<=]one_div_succ n}.

Definition lipschitz (f : CSetoid_fun A B) : CProp :=
  {n : nat | forall x y : A, f x[-d]f y[<=]Two[^]n[*](x[-d]y)}.

Definition lipschitz' (f : CSetoid_fun A B) : CProp :=
  {n : nat | forall x y : A, f x[-d]f y[<=]nring n[*](x[-d]y)}.

Definition lipschitz_c (f : CSetoid_fun A B) (C : IR) : CProp :=
    forall x1 x2 : A, f x1 [-d] f x2 [<=] C [*] (x1 [-d] x2).

End Continuous_functions.
Arguments continuous [A B].
Arguments uni_continuous [A B].
Arguments lipschitz [A B].
Arguments continuous' [A B].
Arguments uni_continuous' [A B].
Arguments uni_continuous'' [A B].
Arguments lipschitz' [A B].
Arguments lipschitz_c [A B].

Section Lemmas.

(* begin hide *)
Lemma nexp_power : forall p : nat, nexp IR p Two[=]nring (power p 2).
Proof.
 simple induction p.
  simpl in |- *.
  algebra.
 intros n H.
 astepr (nring (R:=IR) (power n 2 * 2)).
 astepr (nring (R:=IR) (power n 2)[*]Two).
 astepl (nexp IR n Two[*]Two).
 apply mult_wdl.
 exact H.

Qed.
(* end hide *)

Lemma continuous_imp_continuous' :
 forall (A B : CPsMetricSpace) (f : CSetoid_fun A B),
 continuous f -> continuous' f.
Proof.
 intros A B f.
 unfold continuous in |- *.
 intro H.
 unfold continuous' in |- *.
 intros x n.
 set (H1 := two_ap_zero IR) in *.
 elim H with x (S n) H1.
 intros p H2.
 exists (power p 2).
 intro y.
 intro H3.
 apply leEq_transitive with ((OneR[/] Two:IR[//]H1)[^]S n).
  apply less_leEq.
  apply H2.
  apply leEq_less_trans with (one_div_succ (R:=IR) (power p 2)).
   exact H3.
  unfold one_div_succ in |- *.
  astepr (OneR[^]p[/] (Two:IR)[^]p[//]nexp_resp_ap_zero p H1).
  astepr (OneR[/] (Two:IR)[^]p[//]nexp_resp_ap_zero p H1).
  apply recip_resp_less.
   apply nexp_resp_pos.
   apply pos_two.
  unfold Snring in |- *.
  apply less_wdr with (nexp IR p Two[+][1]).
   apply shift_less_plus.
   apply minusOne_less.
  astepl (OneR[+]nexp IR p Two).
  stepr (OneR[+]nring (power p 2)).
   apply plus_resp_eq.
   apply nexp_power.
  simpl in |- *.
  algebra.
 apply less_leEq.
 astepl (OneR[^]S n[/] (Two:IR)[^]S n[//]nexp_resp_ap_zero (S n) H1).
 astepl (OneR[/] (Two:IR)[^]S n[//]nexp_resp_ap_zero (S n) H1).
 unfold one_div_succ in |- *.
 unfold Snring in |- *.
 apply bin_less_un.
Qed.

Lemma continuous'_imp_continuous :
 forall (A B : CPsMetricSpace) (f : CSetoid_fun A B),
 continuous' f -> continuous f.
Proof.
 intros A B f.
 unfold continuous' in |- *.
 intro H.
 unfold continuous in |- *.
 intros x n H0.
 elim H with x (power n 2).
 intros p H1.
 exists (S p).
 intros y H2.
 apply leEq_less_trans with (one_div_succ (R:=IR) (power n 2)).
  apply H1.
  apply less_leEq.
  apply less_transitive_unfolded with (([1][/] Two:IR[//]H0)[^]S p).
   exact H2.
  unfold one_div_succ in |- *.
  astepl (OneR[^]S p[/] (Two:IR)[^]S p[//]nexp_resp_ap_zero (S p) H0).
  astepl (OneR[/] (Two:IR)[^]S p[//]nexp_resp_ap_zero (S p) H0).
  apply recip_resp_less.
   unfold Snring in |- *.
   apply nring_pos.
   intuition; auto with *.
  apply nat_less_bin_nexp.
 unfold one_div_succ in |- *.
 unfold Snring in |- *.
 astepr (OneR[^]n[/] (Two:IR)[^]n[//]nexp_resp_ap_zero n H0).
 astepr (OneR[/] (Two:IR)[^]n[//]nexp_resp_ap_zero n H0).
 apply recip_resp_less.
  apply nexp_resp_pos.
  apply pos_two.
 astepr (nring (R:=IR) (power n 2)[+][1]).
 astepl (nexp IR n Two[+][0]).
 apply plus_resp_leEq_less.
  apply eq_imp_leEq.
  apply nexp_power.
 apply pos_one.
Qed.

Lemma uni_continuous_imp_uni_continuous' :
 forall (A B : CPsMetricSpace) (f : CSetoid_fun A B),
 uni_continuous f -> uni_continuous' f.
Proof.
 intros A B f.
 unfold uni_continuous in |- *.
 intro H.
 unfold uni_continuous' in |- *.
 intro n.
 set (H0 := two_ap_zero IR) in *.
 elim H with (S n) H0.
 intros p H1.
 exists (power p 2).
 intros x y H2.
 apply less_leEq.
 apply less_transitive_unfolded with ((OneR[/] Two:IR[//]H0)[^]S n).
  apply H1.
  apply leEq_less_trans with (one_div_succ (R:=IR) (power p 2)).
   exact H2.
  unfold one_div_succ in |- *.
  unfold Snring in |- *.
  astepr (OneR[^]p[/] (Two:IR)[^]p[//]nexp_resp_ap_zero p H0).
  astepr (OneR[/] (Two:IR)[^]p[//]nexp_resp_ap_zero p H0).
  apply recip_resp_less.
   apply nexp_resp_pos.
   apply pos_two.
  astepr (nring (R:=IR) (power p 2)[+][1]).
  astepl (nexp IR p Two[+][0]).
  apply plus_resp_leEq_less.
   apply eq_imp_leEq.
   apply nexp_power.
  apply pos_one.
 unfold one_div_succ in |- *.
 unfold Snring in |- *.
 astepl (OneR[^]S n[/] (Two:IR)[^]S n[//]nexp_resp_ap_zero (S n) H0).
 astepl (OneR[/] (Two:IR)[^]S n[//]nexp_resp_ap_zero (S n) H0).
 apply bin_less_un.
Qed.

Lemma uni_continuous'_imp_uni_continuous :
 forall (A B : CPsMetricSpace) (f : CSetoid_fun A B),
 uni_continuous' f -> uni_continuous f.
Proof.
 intros A B f.
 unfold uni_continuous' in |- *.
 intro H.
 unfold uni_continuous in |- *.
 intros n H0.
 elim H with (power n 2).
 intros p H1.
 exists (S p).
 intros x y H2.
 apply leEq_less_trans with (one_div_succ (R:=IR) (power n 2)).
  apply H1.
  apply less_leEq.
  apply less_transitive_unfolded with ((OneR[/] Two:IR[//]H0)[^]S p).
   exact H2.
  unfold one_div_succ in |- *.
  unfold Snring in |- *.
  astepl (OneR[^]S p[/] (Two:IR)[^]S p[//]nexp_resp_ap_zero (S p) H0).
  astepl (OneR[/] (Two:IR)[^]S p[//]nexp_resp_ap_zero (S p) H0).
  apply bin_less_un.
 unfold one_div_succ in |- *.
 astepr (OneR[^]n[/] (Two:IR)[^]n[//]nexp_resp_ap_zero n H0).
 astepr (OneR[/] (Two:IR)[^]n[//]nexp_resp_ap_zero n H0).
 apply recip_resp_less.
  apply nexp_resp_pos.
  apply pos_two.
 unfold Snring in |- *.
 astepr (nring (R:=IR) (power n 2)[+][1]).
 astepl (nexp IR n Two[+][0]).
 apply plus_resp_leEq_less.
  apply eq_imp_leEq.
  apply nexp_power.
 apply pos_one.
Qed.

Lemma uni_continuous'_imp_uni_continuous'' :
 forall (A B : CPsMetricSpace) (f : CSetoid_fun A B),
 uni_continuous' f -> uni_continuous'' f.
Proof.
 intros A B f.
 unfold uni_continuous' in |- *.
 unfold uni_continuous'' in |- *.
 apply choice with (P := fun n m : nat => forall x y : A,
   x[-d]y[<=]one_div_succ m -> f x[-d]f y[<=]one_div_succ n).
Qed.

Lemma lipschitz_imp_lipschitz' :
 forall (A B : CPsMetricSpace) (f : CSetoid_fun A B),
 lipschitz f -> lipschitz' f.
Proof.
 intros A B f.
 unfold lipschitz in |- *.
 intro H.
 unfold lipschitz' in |- *.
 elim H.
 intros n H0.
 elim Archimedes with ((Two:IR)[^]n).
 intros m H1.
 exists m.
 intros x y.
 apply leEq_transitive with ((Two:IR)[^]n[*](x[-d]y)).
  apply H0.
 apply mult_resp_leEq_rht.
  exact H1.
 apply ax_d_nneg.
 apply CPsMetricSpace_is_CPsMetricSpace.
Qed.

Lemma lipschitz'_imp_lipschitz :
 forall (A B : CPsMetricSpace) (f : CSetoid_fun A B),
 lipschitz' f -> lipschitz f.
Proof.
 intros A B f.
 unfold lipschitz' in |- *.
 intro H.
 unfold lipschitz in |- *.
 elim H.
 intros m H1.
 exists m.
 intros x y.
 apply leEq_transitive with (nring m[*](x[-d]y)).
  apply H1.
 apply mult_resp_leEq_rht.
  case m.
   simpl in |- *.
   apply less_leEq.
   apply pos_one.
  intro n.
  astepl (Snring IR n).
  apply less_leEq.
  apply nat_less_bin_nexp.
 apply ax_d_nneg.
 apply CPsMetricSpace_is_CPsMetricSpace.
Qed.

Lemma lip_c_imp_lip : forall (A B : CPsMetricSpace) (f : CSetoid_fun A B) (C : IR),
lipschitz_c f C -> lipschitz' f.
Proof.
 unfold lipschitz_c.
 unfold lipschitz'.
 intros.
 assert ({n : nat| C [<=] nring n}).
  apply Archimedes.
 destruct X as [n H1].
 exists n.
 intros.
 assert (f x[-d]f y [<=] C[*](x[-d]y)).
  apply H.
 apply leEq_transitive with (C[*](x[-d]y)); auto.
 apply mult_resp_leEq_rht; auto.
 apply ax_d_nneg.
 apply CPsMetricSpace_is_CPsMetricSpace.
Qed.

(**
Every uniformly continuous function is continuous and
every Lipschitz function is uniformly continuous.
*)

Lemma uni_continuous_imp_continuous :
 forall (C D : CPsMetricSpace) (f : CSetoid_fun C D),
 uni_continuous f -> continuous f.
Proof.
 intros C D F.
 red in |- *.
 unfold uni_continuous in |- *.
 intros H0 n u H3.
 elim H0 with u H3.
 intros.
 exists x.
 intro y.
 apply p.

Qed.

Lemma lipschitz_imp_uni_continuous :
 forall (C D : CPsMetricSpace) (f : CSetoid_fun C D),
 lipschitz f -> uni_continuous f.
Proof.
 red in |- *.
 unfold lipschitz in |- *.
 intros C D f H n H0.
 elim H.
 intros.
 exists (n + x).
 intros x0 y H1.
 apply leEq_less_trans with (Two[^]x[*](x0[-d]y)).
  apply p.
 apply mult_cancel_less with (([1][/] Two:IR[//]H0)[^]x).
  apply nexp_resp_pos.
  apply div_resp_pos.
   apply pos_two.
  apply pos_one.
 apply less_wdr with (([1][/] Two:IR[//]H0)[^](n + x)).
  apply less_wdl with (x0[-d]y).
   exact H1.
  astepr (Two[^]x[*](x0[-d]y)[*]([1][^]x[/] Two[^]x[//]nexp_resp_ap_zero x H0)).
  astepr (Two[^]x[*](x0[-d]y)[*]([1][/] Two[^]x[//]nexp_resp_ap_zero x H0)).
  rational.
 apply eq_symmetric_unfolded.
 astepr (([1][/] Two:IR[//]H0)[^](n + x)).
 apply nexp_plus.

Qed.

End Lemmas.

Section Identity.
(**
** Identity
*)
(**
The identity function is Lipschitz.
Hence it is uniformly continuous and continuous.
*)

Lemma id_is_lipschitz : forall X : CPsMetricSpace, lipschitz (id_un_op X).
Proof.
 intro X.
 red in |- *.
 simpl in |- *.
 exists 0.
 intros x y.
 astepr (OneR[*](x[-d]y)).
 astepr (x[-d]y).
 apply leEq_reflexive.
Qed.

Lemma id_is_uni_continuous :
 forall X : CPsMetricSpace, uni_continuous (id_un_op X).
Proof.
 intro X.
 apply lipschitz_imp_uni_continuous.
 apply id_is_lipschitz.
Qed.

Lemma id_is_continuous : forall X : CPsMetricSpace, continuous (id_un_op X).
Proof.
 intro X.
 apply uni_continuous_imp_continuous.
 apply id_is_uni_continuous.
Qed.

End Identity.

Section Constant.
(**
** Constant functions
%\begin{convention}%
Let [B] and [X] be pseudo metric spaces.
%\end{convention}%
*)
(**
Any constant function is Lipschitz.
Hence it is uniformly continuous and continuous.
*)
Variable B : CPsMetricSpace.
Variable X : CPsMetricSpace.

Lemma const_fun_is_lipschitz :
 forall b : B, lipschitz (Const_CSetoid_fun X B b).
Proof.
 intro b.
 red in |- *.
 exists 1.
 intros.
 astepr (Two[^]1[*](x[-d]y)).
 astepr (Two[*](x[-d]y)).
 unfold Const_CSetoid_fun in |- *.
 rewrite -> leEq_def in |- *.
 red in |- *.
 simpl in |- *.
 intros H.
 apply (ap_irreflexive_unfolded B b).
 apply (ax_d_pos_imp_ap B (cms_d (c:=B)) (CPsMetricSpace_is_CPsMetricSpace B)).
 apply leEq_less_trans with (([0][+][1][+][1])[*](x[-d]y)).
  astepr ((Two:IR)[*](x[-d]y)).
  apply shift_leEq_mult' with (two_ap_zero IR).
   apply pos_two.
  astepl ZeroR.
  apply ax_d_nneg.
  apply CPsMetricSpace_is_CPsMetricSpace.
 exact H.
Qed.

Lemma const_fun_is_uni_continuous :
 forall b : B, uni_continuous (Const_CSetoid_fun X B b).
Proof.
 intro b.
 apply lipschitz_imp_uni_continuous.
 apply const_fun_is_lipschitz.
Qed.

Lemma const_fun_is_continuous :
 forall b : B, continuous (Const_CSetoid_fun X B b).
Proof.
 intro b.
 apply uni_continuous_imp_continuous.
 apply const_fun_is_uni_continuous.
Qed.

End Constant.

Section Composition.
(**
** Composition
%\begin{convention}%
Let [B],[C] and [X] be pseudo metric spaces.
Let [f : (CSetoid_fun X B)] and
[g : (CSetoid_fun  B C)].
%\end{convention}%
*)
(**
The composition of two Lipschitz/uniformly continous/continuous functions is
again Lipschitz/uniformly continuous/continuous.
*)
Variable X : CPsMetricSpace.
Variable B : CPsMetricSpace.
Variable f : CSetoid_fun X B.
Variable C : CPsMetricSpace.
Variable g : CSetoid_fun B C.

Lemma comp_resp_lipschitz :
 lipschitz f -> lipschitz g -> lipschitz (compose_CSetoid_fun X B C f g).
Proof.
 unfold lipschitz in |- *.
 intros H H0.
 elim H.
 intros x H1.
 elim H0.
 intros x0 H2.
 exists (x + x0).
 simpl in |- *.
 intros x1 y.
 apply leEq_transitive with ((Two:IR)[^]x0[*](f x1[-d]f y)).
  apply H2.
 astepr (Two[^](x + x0)[*](x1[-d]y)).
 astepr (Two[^]x[*]Two[^]x0[*](x1[-d]y)).
 astepr (Two[^]x0[*]Two[^]x[*](x1[-d]y)).
 rstepr (Two[^]x0[*](Two[^]x[*](x1[-d]y))).
 apply mult_resp_leEq_lft.
  apply H1.
 apply nexp_resp_nonneg.
 apply less_leEq.
 apply pos_two.

Qed.


Lemma comp_resp_uni_continuous :
 uni_continuous f ->
 uni_continuous g -> uni_continuous (compose_CSetoid_fun X B C f g).
Proof.
 unfold uni_continuous in |- *.
 intros H H0.
 simpl in |- *.
 intros n H1.
 elim H0 with n H1.
 intro x.
 intro H3.
 elim H with x H1.
 intro x0.
 intro H4.
 exists x0.
 intros x1 y H5.
 apply H3.
 apply H4.
 exact H5.
Qed.

Lemma comp_resp_continuous :
 continuous f -> continuous g -> continuous (compose_CSetoid_fun X B C f g).
Proof.
 unfold continuous in |- *.
 intros H H0 x n H1.
 simpl in |- *.
 elim H0 with (f x) n H1.
 intros.
 elim H with x x0 H1.
 intros.
 exists x1.
 intros y H2.
 apply p.
 apply p0.
 exact H2.

Qed.

End Composition.

Section Limit.
(**
** Limit
*)

Definition MSseqLimit (X : CPsMetricSpace) (seq : nat -> X)
  (lim : X) : CProp :=
  forall (n : nat) (H : Two[#][0]),
  {N : nat |
  forall m : nat, N <= m -> seq m[-d]lim[<]([1][/] Two:IR[//]H)[^]n}.

Arguments MSseqLimit [X].

Definition MSseqLimit' (X : CPsMetricSpace) (seq : nat -> X)
  (lim : X) : CProp :=
  forall n : nat,
  {N : nat | forall m : nat, N <= m -> seq m[-d]lim[<=]one_div_succ n}.

Arguments MSseqLimit' [X].

Lemma MSseqLimit_imp_MSseqLimit' :
 forall (X : CPsMetricSpace) (seq : nat -> X) (lim : X),
 MSseqLimit seq lim -> MSseqLimit' seq lim.
Proof.
 intros X seq lim.
 unfold MSseqLimit in |- *.
 intro H.
 unfold MSseqLimit' in |- *.
 intro n.
 set (H2 := two_ap_zero IR) in *.
 elim H with (S n) H2.
 intros p H3.
 exists p.
 intros m H4.
 apply less_leEq.
 apply less_transitive_unfolded with ((OneR[/] Two:IR[//]H2)[^]S n).
  apply H3.
  exact H4.
 unfold one_div_succ in |- *.
 unfold Snring in |- *.
 astepl (OneR[^]S n[/] (Two:IR)[^]S n[//]nexp_resp_ap_zero (S n) H2).
 astepl (OneR[/] (Two:IR)[^]S n[//]nexp_resp_ap_zero (S n) H2).
 apply bin_less_un.
Qed.

Lemma MSseqLimit'_imp_MSseqLimit :
 forall (X : CPsMetricSpace) (seq : nat -> X) (lim : X),
 MSseqLimit' seq lim -> MSseqLimit seq lim.
Proof.
 intros X seq lim.
 unfold MSseqLimit' in |- *.
 intro H.
 unfold MSseqLimit in |- *.
 intros n H0.
 elim H with (power n 2).
 intros p H1.
 exists p.
 intros m H2.
 apply leEq_less_trans with (one_div_succ (R:=IR) (power n 2)).
  apply H1.
  exact H2.
 unfold one_div_succ in |- *.
 astepr (OneR[^]n[/] (Two:IR)[^]n[//]nexp_resp_ap_zero n H0).
 astepr (OneR[/] (Two:IR)[^]n[//]nexp_resp_ap_zero n H0).
 apply recip_resp_less.
  apply nexp_resp_pos.
  apply pos_two.
 unfold Snring in |- *.
 simpl in |- *.
 apply less_wdr with (nexp IR n Two[+][1]).
  apply shift_less_plus.
  astepl (nexp IR n Two[-][1]).
  apply minusOne_less.
 astepl (OneR[+]nexp IR n Two).
 astepr (OneR[+]nring (power n 2)).
 apply plus_resp_eq.
 apply nexp_power.
Qed.


Definition seqcontinuous' (A B : CPsMetricSpace) (f : CSetoid_fun A B) :
  CProp :=
  forall (seq : nat -> A) (lim : A),
  MSseqLimit' seq lim -> MSseqLimit' (fun m : nat => f (seq m)) (f lim).

Arguments seqcontinuous' [A B].

Lemma continuous'_imp_seqcontinuous' :
 forall (A B : CPsMetricSpace) (f : CSetoid_fun A B),
 continuous' f -> seqcontinuous' f.
Proof.
 intros A B f.
 unfold continuous' in |- *.
 intro H.
 unfold seqcontinuous' in |- *.
 intros seq lim.
 unfold MSseqLimit' in |- *.
 intro H0.
 intro n.
 elim H with lim n.
 intros p H1.
 elim H0 with p.
 intros q H2.
 exists q.
 intro m.
 intro H3.
 astepl (f lim[-d]f (seq m)).
  apply H1.
  astepl (seq m[-d]lim).
   apply H2.
   exact H3.
  apply ax_d_com.
  apply CPsMetricSpace_is_CPsMetricSpace.
 apply ax_d_com.
 apply CPsMetricSpace_is_CPsMetricSpace.
Qed.

End Limit.
