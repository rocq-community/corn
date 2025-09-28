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
Require Export CoRN.algebra.COrdFields.
From Coq Require Import Lia.

(** printing one_div_succ %\ensuremath{\frac1{\cdot+1}}% *)
(** printing Half %\ensuremath{\frac12}% #&frac12;# *)

(*---------------------------------*)
Section Properties_of_leEq.
(*---------------------------------*)

(**
** Properties of [[<=]]
%\begin{convention}% Let [R] be an ordered field.
%\end{convention}%
*)

Variable R : COrdField.

Section addition.
(**
*** Addition and subtraction%\label{section:leEq-plus-minus}%
*)

Lemma plus_resp_leEq : forall x y z : R, x [<=] y -> x[+]z [<=] y[+]z.
Proof.
 intros x y z.
 do 2 rewrite -> leEq_def.
 intros. intro.
 apply H.
 apply (plus_cancel_less _ _ _ _ X).
Qed.

Lemma plus_resp_leEq_lft : forall x y z : R, x [<=] y -> z[+]x [<=] z[+]y.
Proof.
 intros.
 astepl (x[+]z).
 astepr (y[+]z).
 apply plus_resp_leEq; auto.
Qed.

Lemma minus_resp_leEq : forall x y z : R, x [<=] y -> x[-]z [<=] y[-]z.
Proof.
 intros.
 astepl (x[+][--]z).
 astepr (y[+][--]z).
 apply plus_resp_leEq; auto.
Qed.

Lemma inv_resp_leEq : forall x y : R, x [<=] y -> [--]y [<=] [--]x.
Proof.
 intros x y.
 repeat rewrite -> leEq_def.
 do 2 intro.
 apply H.
 apply inv_cancel_less.
 assumption.
Qed.

Lemma minus_resp_leEq_rht : forall x y z : R, y [<=] x -> z[-]x [<=] z[-]y.
Proof.
 intros.
 Transparent cg_minus.
 unfold cg_minus in |- *.
 apply plus_resp_leEq_lft.
 apply inv_resp_leEq.
 assumption.
Qed.

Lemma plus_resp_leEq_both : forall x y a b : R, x [<=] y -> a [<=] b -> x[+]a [<=] y[+]b.
Proof.
 intros.
 apply leEq_transitive with (y := x[+]b).
  rstepl (a[+]x).
  rstepr (b[+]x).
  apply plus_resp_leEq.
  assumption.
 apply plus_resp_leEq.
 assumption.
Qed.

Lemma plus_resp_less_leEq : forall a b c d : R, a [<] b -> c [<=] d -> a[+]c [<] b[+]d.
Proof.
 intros.
 apply leEq_less_trans with (a[+]d).
  apply plus_resp_leEq_lft. auto.
  apply plus_resp_less_rht. auto.
Qed.

Lemma plus_resp_leEq_less : forall a b c d : R, a [<=] b -> c [<] d -> a[+]c [<] b[+]d.
Proof.
 intros.
 astepl (c[+]a).
 astepr (d[+]b).
 apply plus_resp_less_leEq; auto.
Qed.

Lemma plus_resp_nonneg : forall x y : R, [0] [<=] x -> [0] [<=] y -> [0] [<=] x[+]y.
Proof.
 intros.
 astepl ([0][+][0]:R).
 apply plus_resp_leEq_both; auto.
Qed.

Lemma minus_resp_less_leEq : forall x y x' y' : R, x [<=] y -> y' [<] x' -> x[-]x' [<] y[-]y'.
Proof.
 intros.
 astepl (x[+][--]x').
 astepr (y[+][--]y').
 apply plus_resp_leEq_less.
  auto.
 apply inv_resp_less. auto.
Qed.

Lemma minus_resp_leEq_both : forall x y x' y' : R, x [<=] y -> y' [<=] x' -> x[-]x' [<=] y[-]y'.
Proof.
 intros.
 astepl (x[+][--]x').
 astepr (y[+][--]y').
 apply plus_resp_leEq_both. auto.
  apply inv_resp_leEq. auto.
Qed.

(** Cancellation properties
*)

Lemma plus_cancel_leEq_rht : forall x y z : R, x[+]z [<=] y[+]z -> x [<=] y.
Proof.
 intros.
 rstepl (x[+]z[+][--]z).
 rstepr (y[+]z[+][--]z).
 apply plus_resp_leEq.
 assumption.
Qed.

Lemma inv_cancel_leEq : forall x y : R, [--]y [<=] [--]x -> x [<=] y.
Proof.
 intros.
 rstepl ([--][--]x).
 rstepr ([--][--]y).
 apply inv_resp_leEq.
 assumption.
Qed.

(** Laws for shifting
*)

Lemma shift_plus_leEq : forall a b c : R, a [<=] c[-]b -> a[+]b [<=] c.
Proof.
 intros.
 rstepr (c[-]b[+]b).
 apply plus_resp_leEq.
 assumption.
Qed.

Lemma shift_leEq_plus : forall a b c : R, a[-]b [<=] c -> a [<=] c[+]b.
Proof.
 intros.
 rstepl (a[-]b[+]b).
 apply plus_resp_leEq.
 assumption.
Qed.

Lemma shift_plus_leEq' : forall a b c : R, b [<=] c[-]a -> a[+]b [<=] c.
Proof.
 intros.
 rstepr (a[+] (c[-]a)).
 apply plus_resp_leEq_lft.
 assumption.
Qed.

Lemma shift_leEq_plus' : forall a b c : R, a[-]b [<=] c -> a [<=] b[+]c.
Proof.
 intros.
 rstepl (b[+] (a[-]b)).
 apply plus_resp_leEq_lft. auto.
Qed.

Lemma shift_leEq_rht : forall a b : R, [0] [<=] b[-]a -> a [<=] b.
Proof.
 intros.
 astepl ([0][+]a).
 rstepr (b[-]a[+]a).
 apply plus_resp_leEq. auto.
Qed.

Lemma shift_leEq_lft : forall a b : R, a [<=] b -> [0] [<=] b[-]a.
Proof.
 intros.
 astepl (a[-]a).
 apply minus_resp_leEq. auto.
Qed.

Lemma shift_minus_leEq : forall a b c : R, a [<=] c[+]b -> a[-]b [<=] c.
Proof.
 intros.
 rstepr (c[+]b[-]b).
 apply minus_resp_leEq.
 assumption.
Qed.

Lemma shift_leEq_minus : forall a b c : R, a[+]c [<=] b -> a [<=] b[-]c.
Proof.
 intros.
 rstepl (a[+]c[-]c).
 apply minus_resp_leEq.
 assumption.
Qed.

Lemma shift_leEq_minus' : forall a b c : R, c[+]a [<=] b -> a [<=] b[-]c.
Proof.
 intros.
 rstepl (c[+]a[-]c).
 apply minus_resp_leEq.
 assumption.
Qed.

Lemma shift_zero_leEq_minus : forall x y : R, x [<=] y -> [0] [<=] y[-]x.
Proof.
 intros.
 rstepl (x[-]x).
 apply minus_resp_leEq.
 assumption.
Qed.

Lemma shift_zero_leEq_minus' : forall x y : R, [0] [<=] y[-]x -> x [<=] y.
Proof.
 intros.
 apply plus_cancel_leEq_rht with ([--]x).
 rstepl ([0]:R).
 assumption.
Qed.

End addition.

Section multiplication.
(**
*** Multiplication and division

Multiplication and division respect [[<=]]
*)

Lemma mult_resp_leEq_rht : forall x y z : R, x [<=] y -> [0] [<=] z -> x[*]z [<=] y[*]z.
Proof.
 intros x y z .
 repeat rewrite -> leEq_def.
 intros H H0 H1.
 generalize (shift_zero_less_minus _ _ _ H1); intro H2.
 cut ([0] [<] (x[-]y) [*]z).
  intro H3.
  2: rstepr (x[*]z[-]y[*]z).
  2: assumption.
 cut (forall a b : R, [0] [<] a[*]b -> [0] [<] a and [0] [<] b or a [<] [0] and b [<] [0]).
  intro H4.
  generalize (H4 _ _ H3); intro H5.
  elim H5; intro H6.
   elim H6; intros.
   elim H.
   astepl ([0][+]y).
   apply shift_plus_less.
   assumption.
  elim H6; intros.
  elim H0.
  assumption.
 intros a b H4.
 generalize (Greater_imp_ap _ _ _ H4); intro H5.
 generalize (mult_cancel_ap_zero_lft _ _ _ H5); intro H6.
 generalize (mult_cancel_ap_zero_rht _ _ _ H5); intro H7.
 elim (ap_imp_less _ _ _ H6); intro H8.
  right.
  split.
   assumption.
  elim (ap_imp_less _ _ _ H7); intro H9.
   assumption.
  exfalso.
  elim (less_irreflexive_unfolded R [0]).
  apply less_leEq_trans with (a[*]b).
   assumption.
  apply less_leEq.
  apply inv_cancel_less.
  astepl ([0]:R).
  astepr ([--]a[*]b).
  apply mult_resp_pos.
   astepl ([--]([0]:R)).
   apply inv_resp_less.
   assumption.
  assumption.
 left.
 split.
  assumption.
 elim (ap_imp_less _ _ _ H7); intro H9.
  exfalso.
  elim (less_irreflexive_unfolded R [0]).
  apply less_leEq_trans with (a[*]b).
   assumption.
  apply less_leEq.
  apply inv_cancel_less.
  astepl ([0]:R).
  astepr (a[*][--]b).
  apply mult_resp_pos.
   assumption.
  astepl ([--]([0]:R)).
  apply inv_resp_less.
  assumption.
 assumption.
Qed.

Lemma mult_resp_leEq_lft : forall x y z : R, x [<=] y -> [0] [<=] z -> z[*]x [<=] z[*]y.
Proof.
 intros.
 astepl (x[*]z).
 astepr (y[*]z).
 apply mult_resp_leEq_rht.
  assumption.
 assumption.
Qed.

Lemma mult_resp_leEq_both : forall x x' y y' : R,
 [0] [<=] x -> [0] [<=] y -> x [<=] x' -> y [<=] y' -> x[*]y [<=] x'[*]y'.
Proof.
 intros.
 apply leEq_transitive with (x[*]y').
  apply mult_resp_leEq_lft; assumption.
 apply mult_resp_leEq_rht.
  assumption.
 apply leEq_transitive with y; assumption.
Qed.

Lemma recip_resp_leEq : forall (x y : R) x_ y_, [0] [<] y -> y [<=] x -> ([1][/] x[//]x_) [<=] ([1][/] y[//]y_).
Proof.
 intros x y x_ y_ H.
 do 2 rewrite -> leEq_def.
 intros H0 H1. apply H0.
 cut (([1][/] x[//]x_) [#] [0]). intro x'_.
  cut (([1][/] y[//]y_) [#] [0]). intro y'_.
   rstepl ([1][/] [1][/] x[//]x_[//]x'_).
   rstepr ([1][/] [1][/] y[//]y_[//]y'_).
   apply recip_resp_less.
    apply recip_resp_pos; auto.
   auto.
  apply div_resp_ap_zero_rev. apply ring_non_triv.
  apply div_resp_ap_zero_rev. apply ring_non_triv.
Qed.

Lemma div_resp_leEq : forall (x y z : R) z_, [0] [<] z -> x [<=] y -> (x[/] z[//]z_) [<=] (y[/] z[//]z_).
Proof.
 intros.
 rstepl (x[*] ([1][/] z[//]z_)).
 rstepr (y[*] ([1][/] z[//]z_)).
 apply mult_resp_leEq_rht.
  assumption.
 apply less_leEq.
 apply recip_resp_pos.
 auto.
Qed.

Hint Resolve recip_resp_leEq: algebra.

(** Cancellation properties
*)

Lemma mult_cancel_leEq : forall x y z : R, [0] [<] z -> x[*]z [<=] y[*]z -> x [<=] y.
Proof.
 intros x y z H.
 do 2 rewrite -> leEq_def.
 intros H0 H1.
 apply H0.
 apply mult_resp_less.
  assumption.
 assumption.
Qed.

(** Laws for shifting
*)

Lemma shift_mult_leEq : forall (x y z : R) z_, [0] [<] z -> x [<=] (y[/] z[//]z_) -> x[*]z [<=] y.
Proof.
 intros.
 rstepr ((y[/] z[//]z_) [*]z).
 apply mult_resp_leEq_rht; [ assumption | apply less_leEq; assumption ].
Qed.

Lemma shift_mult_leEq' : forall (x y z : R) z_, [0] [<] z -> x [<=] (y[/] z[//]z_) -> z[*]x [<=] y.
Proof.
 intros.
 rstepr (z[*] (y[/] z[//]z_)).
 apply mult_resp_leEq_lft; [ assumption | apply less_leEq; assumption ].
Qed.

Lemma shift_leEq_mult' : forall (x y z : R) y_, [0] [<] y -> (x[/] y[//]y_) [<=] z -> x [<=] y[*]z.
Proof.
 intros x y z H H0. repeat rewrite -> leEq_def. intros H1 H2. apply H1.
 apply shift_less_div. auto.
  astepl (y[*]z). auto.
Qed.

Lemma shift_div_leEq : forall x y z : R, [0] [<] z -> forall z_ : z [#] [0], x [<=] y[*]z -> (x[/] z[//]z_) [<=] y.
Proof.
 intros.
 rstepr (y[*]z[/] z[//]z_).
 apply div_resp_leEq.
  assumption.
 assumption.
Qed.

Lemma shift_div_leEq' : forall (x y z : R) z_, [0] [<] z -> x [<=] z[*]y -> (x[/] z[//]z_) [<=] y.
Proof.
 intros.
 rstepr (z[*]y[/] z[//]z_).
 apply div_resp_leEq.
  assumption.
 assumption.
Qed.

Lemma shift_leEq_div : forall (x y z : R) y_, [0] [<] y -> x[*]y [<=] z -> x [<=] (z[/] y[//]y_).
Proof.
 intros x y z H X. repeat rewrite -> leEq_def. intros H0 H1. apply H0.
 astepr (y[*]x).
 apply shift_less_mult' with H; auto.
Qed.

Hint Resolve shift_leEq_div: algebra.

Lemma eps_div_leEq_eps : forall (eps d : R) d_, [0] [<=] eps -> [1] [<=] d -> (eps[/] d[//]d_) [<=] eps.
Proof.
 intros.
 apply shift_div_leEq'.
  apply less_leEq_trans with ([1]:R).
   apply pos_one.
  assumption.
 astepl ([1][*]eps).
 apply mult_resp_leEq_rht.
  assumption.
 assumption.
Qed.

Lemma nonneg_div_two : forall eps : R, [0] [<=] eps -> [0] [<=] eps [/]TwoNZ.
Proof.
 intros.
 apply shift_leEq_div.
  apply pos_two.
 astepl ([0]:R).
 assumption.
Qed.

Lemma nonneg_div_two' : forall eps : R, [0] [<=] eps -> eps [/]TwoNZ [<=] eps.
Proof.
 intros.
 apply shift_div_leEq.
  apply pos_two.
 astepl (eps[+][0]); rstepr (eps[+]eps).
 apply plus_resp_leEq_lft; auto.
Qed.

Lemma nonneg_div_three : forall eps : R, [0] [<=] eps -> [0] [<=] eps [/]ThreeNZ.
Proof.
 intros.
 apply mult_cancel_leEq with (Three:R).
  apply pos_three.
 astepl ([0]:R); rstepr eps.
 assumption.
Qed.

Lemma nonneg_div_three' : forall eps : R, [0] [<=] eps -> eps [/]ThreeNZ [<=] eps.
Proof.
 intros.
 apply shift_div_leEq.
  apply pos_three.
 rstepl (eps[+][0][+][0]); rstepr (eps[+]eps[+]eps).
 repeat apply plus_resp_leEq_both; auto.
 apply leEq_reflexive.
Qed.

Lemma nonneg_div_four : forall eps : R, [0] [<=] eps -> [0] [<=] eps [/]FourNZ.
Proof.
 intros.
 rstepr ((eps [/]TwoNZ) [/]TwoNZ).
 apply nonneg_div_two; apply nonneg_div_two; assumption.
Qed.

Lemma nonneg_div_four' : forall eps : R, [0] [<=] eps -> eps [/]FourNZ [<=] eps.
Proof.
 intros.
 rstepl ((eps [/]TwoNZ) [/]TwoNZ).
 apply leEq_transitive with (eps [/]TwoNZ).
  2: apply nonneg_div_two'; assumption.
 apply nonneg_div_two'.
 apply nonneg_div_two.
 assumption.
Qed.

End multiplication.

Section misc.
(**
*** Miscellaneous Properties
*)

Lemma sqr_nonneg : forall x : R, [0] [<=] x[^]2.
Proof.
 intros. rewrite -> leEq_def in |- *. intro H.
 cut ([0] [<] x[^]2). intro H0.
  elim (less_antisymmetric_unfolded _ _ _ H H0).
 cut (x [<] [0] or [0] [<] x). intro H0. elim H0; clear H0; intros H0.
  rstepr ([--]x[*][--]x).
   cut ([0] [<] [--]x). intro H1.
    apply mult_resp_pos; auto.
   astepl ([--]([0]:R)). apply inv_resp_less. auto.
   rstepr (x[*]x).
  apply mult_resp_pos; auto.
 apply ap_imp_less.
 apply cring_mult_ap_zero with x.
 astepl (x[^]2).
 apply less_imp_ap. auto.
Qed.

Lemma nring_nonneg : forall n : nat, [0] [<=] nring (R:=R) n.
Proof.
 intro; induction  n as [| n Hrecn].
  apply leEq_reflexive.
 apply leEq_transitive with (nring (R:=R) n);
   [ assumption | apply less_leEq; simpl in |- *; apply less_plusOne ].
Qed.


Lemma suc_leEq_dub : forall n, nring (R:=R) (S (S n)) [<=] Two[*]nring (S n).
Proof.
 intro n.
 induction  n as [| n Hrecn].
  apply eq_imp_leEq.
  rational.
 astepl (nring (R:=R) (S (S n)) [+]nring 1).
  apply leEq_transitive with (nring (R:=R) 2[*]nring (S n) [+]nring 1).
   apply plus_resp_leEq.
   astepr ((Two:R) [*]nring (S n)).
   exact Hrecn.
  simpl in |- *.
  astepr ((([0]:R) [+][1][+][1]) [*] (nring n[+][1]) [+] (([0]:R) [+][1][+][1]) [*][1]).
  apply plus_resp_leEq_lft.
  astepr (([0]:R) [+][1][+][1]).
  astepr (([0]:R) [+] ([1][+][1])).
  apply plus_resp_leEq_lft.
  astepr (Two:R).
  apply less_leEq.
  apply one_less_two.
 simpl in |- *.
 astepl (nring (R:=R) n[+][1][+] ([1][+] ([0][+][1]))).
 astepl (nring (R:=R) n[+] ([1][+] ([1][+] ([0][+][1])))).
 astepr (nring (R:=R) n[+][1][+] ([1][+][1])).
 astepr (nring (R:=R) n[+] ([1][+] ([1][+][1]))).
 rational.
Qed.

Lemma leEq_nring : forall n m, nring (R:=R) n [<=] nring m -> n <= m.
Proof.
 intro n; induction  n as [| n Hrecn].
  intros.
  auto with arith.
 intros.
 induction  m as [| m Hrecm].
  exfalso.
  cut (nring (R:=R) n [<] [0]).
   change (Not (nring (R:=R) n[<](nring 0))).
   rewrite <- leEq_def.
   apply nring_leEq.
   auto with arith.
  change (nring n [<] nring (R:=R) 0) in |- *.
  apply nring_less.
  apply Nat.lt_le_trans with (S n).
   auto with arith.
  exfalso. revert H; rewrite -> leEq_def. intro H; destruct H.
  apply nring_less; auto with arith.
 cut (n <= m).
  auto with arith.
 apply Hrecn.
 rstepr (nring (R:=R) m[+][1][-][1]).
 apply shift_leEq_minus.
 apply H.
Qed.

Lemma cc_abs_aid : forall x y : R, [0] [<=] x[^]2[+]y[^]2.
Proof.
 intros.
 astepl ([0][+] ([0]:R)).
 apply plus_resp_leEq_both; apply sqr_nonneg.
Qed.

Load "Transparent_algebra".

Lemma nexp_resp_pos : forall (x : R) k, [0] [<] x -> [0] [<] x[^]k.
Proof.
 intros.
 elim k.
  simpl in |- *.
  apply pos_one.
 intros.
 simpl in |- *.
 apply mult_resp_pos.
  assumption.
 assumption.
Qed.

Load "Opaque_algebra".

Lemma mult_resp_nonneg : forall x y : R, [0] [<=] x -> [0] [<=] y -> [0] [<=] x[*]y.
Proof.
 intros x y. repeat rewrite -> leEq_def. intros  H H0 H1. apply H0.
 cut (x[*]y [#] [0]). intro H2.
  cut (x [#] [0]). intro H3.
   cut (y [#] [0]). intro H4.
    elim (ap_imp_less _ _ _ H4); intro H5. auto.
     elim (ap_imp_less _ _ _ H3); intro H6. elim (H H6).
     elim (less_antisymmetric_unfolded _ _ _ H1 (mult_resp_pos _ _ _ H6 H5)).
   apply cring_mult_ap_zero_op with x. auto.
   apply cring_mult_ap_zero with y. auto.
  apply less_imp_ap. auto.
Qed.

Load "Transparent_algebra".

Lemma nexp_resp_nonneg : forall (x : R) (k : nat), [0] [<=] x -> [0] [<=] x[^]k.
Proof.
 intros. induction  k as [| k Hreck]. intros.
 astepr ([1]:R). apply less_leEq. apply pos_one.
  astepr (x[^]k[*]x).
 apply mult_resp_nonneg; auto.
Qed.

Lemma power_resp_leEq : forall (x y : R) k, [0] [<=] x -> x [<=] y -> x[^]k [<=] y[^]k.
Proof.
 intros. induction  k as [| k Hreck]; intros.
 astepl ([1]:R).
  astepr ([1]:R).
  apply leEq_reflexive.
 astepl (x[^]k[*]x).
 astepr (y[^]k[*]y).
 apply leEq_transitive with (x[^]k[*]y).
  apply mult_resp_leEq_lft. auto.
   apply nexp_resp_nonneg; auto.
 apply mult_resp_leEq_rht. auto.
  apply leEq_transitive with x; auto.
Qed.

Lemma nexp_resp_less : forall (x y : R) n, 1 <= n -> [0] [<=] x -> x [<] y -> x[^]n [<] y[^]n.
Proof.
 intros.
 induction  n as [| n Hrecn].
  exfalso.
  inversion H.
 elim n.
  simpl in |- *.
  astepl x.
  astepr y.
  assumption.
 intros.
 change (x[^]S n0[*]x [<] y[^]S n0[*]y) in |- *.
 apply mult_resp_less_both.
    apply nexp_resp_nonneg.
    assumption.
   assumption.
  assumption.
 assumption.
Qed.

Lemma power_cancel_leEq : forall (x y : R) k, 0 < k -> [0] [<=] y -> x[^]k [<=] y[^]k -> x [<=] y.
Proof.
 intros x y k H. repeat rewrite -> leEq_def. intros H0 H1 H2. apply H1.
 apply nexp_resp_less; try rewrite -> leEq_def; auto.
Qed.

Lemma power_cancel_less : forall (x y : R) k, [0] [<=] y -> x[^]k [<] y[^]k -> x [<] y.
Proof.
 intros x y k H H0.
 elim (zerop k); intro y0.
  rewrite y0 in H0.
  cut ([1] [<] ([1]:R)). intro H1.
   elim (less_irreflexive_unfolded _ _ H1).
  astepl (x[^]0). astepr (y[^]0). auto.
  cut (x [<] y or y [<] x). intro H1.
  elim H1; clear H1; intros H1. auto.
   cut (x [<=] y). intro. destruct (leEq_def _ x y) as [H3 _]. elim ((H3 H2) H1).
   apply power_cancel_leEq with k; auto.
  apply less_leEq. auto.
  apply ap_imp_less. apply un_op_strext_unfolded with (nexp_op (R:=R) k).
 apply less_imp_ap. auto.
Qed.

Lemma nat_less_bin_nexp : forall p : nat, Snring R p [<] Two[^]S p.
Proof.
 intro n.
 unfold Snring in |- *.
 induction  n as [| n Hrecn].
  simpl in |- *.
  astepl ([1]:R).
  astepr (([0]:R) [+][1][+][1]).
  astepr (([1]:R) [+][1]).
  astepr (Two:R).
  apply one_less_two.
 astepl (nring (R:=R) (S n) [+][1]).
 astepr ((Two:R)[^]S n[*]Two).
 astepr ((Two:R)[^]S n[*][1][+]Two[^]S n[*][1]).
  apply plus_resp_less_both.
   astepr ((Two:R)[^]S n).
   exact Hrecn.
  astepr ((Two:R)[^]S n).
  astepl (([1]:R)[^]S n).
  apply nexp_resp_less.
    intuition; auto with *.
   apply less_leEq.
   apply pos_one.
  apply one_less_two.
 rational.
Qed.

Lemma Sum_resp_leEq : forall (f g : nat -> R) a b, a <= S b ->
 (forall i, a <= i -> i <= b -> f i [<=] g i) -> Sum a b f [<=] Sum a b g.
Proof.
 intros. induction  b as [| b Hrecb]; intros.
 unfold Sum in |- *. unfold Sum1 in |- *.
  generalize (toCle _ _ H); clear H; intro H.
  inversion H as [|m X H2].
   astepl ([0]:R).
   astepr ([0]:R).
   apply leEq_reflexive.
  inversion X.
  simpl in |- *.
  rstepl (f 0).
  rstepr (g 0).
  apply H0; auto. rewrite H1. auto.
  elim (le_lt_eq_dec _ _ H); intro H1.
  apply leEq_wdl with (Sum a b f[+]f (S b)).
   apply leEq_wdr with (Sum a b g[+]g (S b)).
    apply plus_resp_leEq_both.
     apply Hrecb. auto with arith. auto.
      apply H0. auto with arith. auto.
     apply eq_symmetric_unfolded. apply Sum_last.
   apply eq_symmetric_unfolded. apply Sum_last.
  unfold Sum in |- *. unfold Sum1 in |- *.
 rewrite H1.
 simpl in |- *.
 astepl ([0]:R).
 astepr ([0]:R).
 apply leEq_reflexive.
Qed.

Lemma Sumx_resp_leEq : forall n (f g : forall i, i < n -> R),
 (forall i H, f i H [<=] g i H) -> Sumx f [<=] Sumx g.
Proof.
 simple induction n.
  intros; simpl in |- *; apply leEq_reflexive.
 clear n; intros; simpl in |- *.
 apply plus_resp_leEq_both.
  apply H; intros; apply H0.
 apply H0.
Qed.

Lemma Sum2_resp_leEq : forall m n, m <= S n -> forall f g : forall i, m <= i -> i <= n -> R,
 (forall i Hm Hn, f i Hm Hn [<=] g i Hm Hn) -> Sum2 f [<=] Sum2 g.
Proof.
 intros.
 unfold Sum2 in |- *.
 apply Sum_resp_leEq.
  assumption.
 intros.
 elim (le_lt_dec m i); intro;
   [ simpl in |- * | exfalso; apply (Nat.le_ngt m i); auto with arith ].
 elim (le_lt_dec i n); intro;
   [ simpl in |- * | exfalso; apply (Nat.le_ngt i n); auto with arith ].
 apply H0.
Qed.

Lemma approach_zero : forall x : R, (forall e, [0] [<] e -> x [<] e) -> x [<=] [0].
Proof.
 intros.
 rewrite -> leEq_def; intro.
 cut (x [<] x [/]TwoNZ).
  change (Not (x [<] x [/]TwoNZ)) in |- *.
  apply less_antisymmetric_unfolded.
  apply plus_cancel_less with (z := [--](x [/]TwoNZ)).
  apply mult_cancel_less with (z := Two:R).
   apply pos_two.
  rstepl ([0]:R).
  rstepr x.
  assumption.
 apply X.
 apply pos_div_two.
 assumption.
Qed.

Lemma approach_zero_weak : forall x : R, (forall e, [0] [<] e -> x [<=] e) -> x [<=] [0].
Proof.
 intros.
 rewrite -> leEq_def; intro.
 cut (x [<=] x [/]TwoNZ).
  rewrite -> leEq_def.
  change (~ Not (x [/]TwoNZ [<] x)) in |- *.
  intro H1.
  apply H1.
  apply plus_cancel_less with (z := [--](x [/]TwoNZ)).
  apply mult_cancel_less with (z := Two:R).
   apply pos_two.
  rstepl ([0]:R).
  rstepr x.
  assumption.
 apply H.
 apply pos_div_two.
 assumption.
Qed.
End misc.

Lemma equal_less_leEq : forall a b x y : R,
 (a [<] b -> x [<=] y) -> (a [=] b -> x [<=] y) -> a [<=] b -> x [<=] y.
Proof.
 intros.
 rewrite -> leEq_def.
 red in |- *.
 apply CNot_Not_or with (a [<] b) (a [=] b).
   firstorder using leEq_def.
  firstorder using leEq_def.
 intro.
 cut (a [=] b); intros.
  2: apply leEq_imp_eq; auto.
  auto.
 rewrite -> leEq_def.
 intro; auto.
Qed.

Lemma power_plus_leEq : forall n (x y:R), (0 < n) -> ([0][<=]x) -> ([0][<=]y) ->
(x[^]n [+] y[^]n)[<=](x[+]y)[^]n.
Proof.
 intros [|n] x y Hn Hx Hy.
  exfalso; auto with *.
 induction n.
  simpl.
  rstepl ([1][*](x[+]y)).
  apply leEq_reflexive.
 rename n into m.
 set (n:=(S m)) in *.
 apply leEq_transitive with ((x[^]n[+]y[^]n)[*](x[+]y)).
  apply shift_zero_leEq_minus'.
  change (x[^]S n) with (x[^]n[*]x).
  change (y[^]S n) with (y[^]n[*]y).
  rstepr (y[*]x[^]n[+]x[*]y[^]n).
  apply plus_resp_nonneg; apply mult_resp_nonneg; try apply nexp_resp_nonneg; try assumption.
 change ((x[+]y)[^]S n) with ((x[+]y)[^]n[*](x[+]y)).
 apply mult_resp_leEq_rht.
  apply IHn.
  unfold n; auto with *.
 apply plus_resp_nonneg; assumption.
Qed.

End Properties_of_leEq.

#[global]
Hint Resolve shift_leEq_lft mult_resp_nonneg plus_resp_nonneg: algebra.

(*---------------------------------*)
Section PosP_properties.
(*---------------------------------*)

(**
** Properties of positive numbers
%\begin{convention}% Let [R] be an ordered field.
%\end{convention}%
*)
Variable R : COrdField.

(* begin hide *)
Notation ZeroR := ([0]:R).
Notation OneR := ([1]:R).
(* end hide *)

Lemma mult_pos_imp : forall a b : R, [0] [<] a[*]b -> [0] [<] a and [0] [<] b or a [<] [0] and b [<] [0].
Proof.
 generalize I; intro.
 generalize I; intro.
 generalize I; intro.
 generalize I; intro.
 generalize I; intro.
 intros a b H4.
 generalize (Greater_imp_ap _ _ _ H4); intro H5.
 generalize (mult_cancel_ap_zero_lft _ _ _ H5); intro H6.
 generalize (mult_cancel_ap_zero_rht _ _ _ H5); intro H7.
 elim (ap_imp_less _ _ _ H6); intro H8.
  right.
  split.
   assumption.
  elim (ap_imp_less _ _ _ H7); intro.
   assumption.
  exfalso.
  elim (less_irreflexive_unfolded R [0]).
  apply less_leEq_trans with (a[*]b).
   assumption.
  apply less_leEq.
  apply inv_cancel_less.
  astepl ZeroR.
  astepr ([--]a[*]b).
  apply mult_resp_pos.
   astepl ([--]ZeroR).
   apply inv_resp_less.
   assumption.
  assumption.
 left.
 split.
  assumption.
 elim (ap_imp_less _ _ _ H7); intro.
  exfalso.
  elim (less_irreflexive_unfolded R [0]).
  apply less_leEq_trans with (a[*]b).
   assumption.
  apply less_leEq.
  apply inv_cancel_less.
  astepl ZeroR.
  astepr (a[*][--]b).
  apply mult_resp_pos.
   assumption.
  astepl ([--]ZeroR).
  apply inv_resp_less.
  assumption.
 assumption.
Qed.

Lemma plus_resp_pos_nonneg : forall x y : R, [0] [<] x -> [0] [<=] y -> [0] [<] x[+]y.
Proof.
 intros.
 apply less_leEq_trans with x. auto.
  astepl (x[+][0]).
 apply plus_resp_leEq_lft. auto.
Qed.

Lemma plus_resp_nonneg_pos : forall x y : R, [0] [<=] x -> [0] [<] y -> [0] [<] x[+]y.
Proof.
 intros.
 astepr (y[+]x).
 apply plus_resp_pos_nonneg; auto.
Qed.

Lemma pos_square : forall x : R, x [#] [0] -> [0] [<] x[^]2.
Proof.
 intros x H.
 elim (ap_imp_less _ _ _ H); intro H1.
  rstepr ([--]x[*][--]x).
  cut ([0] [<] [--]x). intro.
   apply mult_resp_pos; auto.
  astepl ([--]ZeroR).
  apply inv_resp_less. auto.
  rstepr (x[*]x).
 apply mult_resp_pos; auto.
Qed.

Lemma mult_cancel_pos_rht : forall x y : R, [0] [<] x[*]y -> [0] [<=] x -> [0] [<] y.
Proof.
 intros x y H.
 destruct (leEq_def _ [0] x) as [H0 _].
 intro H2. pose (H3:=(H0 H2)).
 elim (mult_pos_imp _ _ H); intro H1.
  elim H1; auto.
 elim H1; intros.
 contradiction.
Qed.

Lemma mult_cancel_pos_lft : forall x y : R, [0] [<] x[*]y -> [0] [<=] y -> [0] [<] x.
Proof.
 intros.
 apply mult_cancel_pos_rht with y.
  astepr (x[*]y).
  auto. auto.
Qed.

Lemma pos_wd : forall x y : R, x [=] y -> [0] [<] y -> [0] [<] x.
Proof.
 intros.
 astepr y.
 auto.
Qed.

Lemma even_power_pos : forall n, Nat.Even n -> forall x : R, x [#] [0] -> [0] [<] x[^]n.
Proof.
 intros n Hn x Hx.
 destruct (even_or_odd_plus n) as [k [Hk | Hk]].
 - astepr ((x[^]2)[^](k)).
   apply nexp_resp_pos, pos_square; exact Hx.
   astepr ((x[^]2)[^](k)); [reflexivity |].
   now rewrite nexp_mult, Hk; replace (2 * k) with (k + k) by lia.
 - exfalso; apply (Nat.Even_Odd_False n); [exact Hn |].
   exists k; lia.
Qed.

Lemma odd_power_cancel_pos : forall n, Nat.Odd n -> forall x : R, [0] [<] x[^]n -> [0] [<] x.
Proof.
 intros n [m Hm]%to_Codd x. simpl. intros H.
 apply mult_pos_imp in H as [[H1 H2] | [H1 H2]].
 - exact H2.
 - exfalso. apply less_imp_ap in H2.
   apply (even_power_pos m) in H2; [| now apply Ceven_to].
   apply less_antisymmetric_unfolded with (1 := H1).
   exact H2.
Qed.

Lemma plus_resp_pos : forall x y : R, [0] [<] x -> [0] [<] y -> [0] [<] x[+]y.
Proof.
 intros.
 apply plus_resp_pos_nonneg.
  auto.
 apply less_leEq. auto.
Qed.

Lemma pos_nring_S : forall n, ZeroR [<] nring (S n).
Proof.
 simple induction n; simpl in |- *; intros.
  (* base *)
  astepr OneR; apply pos_one.
 (* step *)
 apply less_leEq_trans with (nring (R:=R) n0[+][1]).
  assumption.
 apply less_leEq.
 apply less_plusOne.
Qed.

Lemma square_eq_pos : forall x a : R, [0] [<] a -> [0] [<] x -> x[^]2 [=] a[^]2 -> x [=] a.
Proof.
 intros.
 elim (square_eq _ x a); intros; auto.
  exfalso.
  apply less_irreflexive_unfolded with (x := ZeroR).
  apply less_leEq_trans with x.
   auto.
  apply less_leEq.
  astepl ([--]a); apply inv_cancel_less.
  astepl ZeroR; astepr a; auto.
 apply Greater_imp_ap; auto.
Qed.

Lemma square_eq_neg : forall x a : R, [0] [<] a -> x [<] [0] -> x[^]2 [=] a[^]2 -> x [=] [--]a.
Proof.
 intros.
 elim (square_eq _ x a); intros; auto.
  exfalso.
  apply less_irreflexive_unfolded with (x := ZeroR).
  apply leEq_less_trans with x.
   astepr a; apply less_leEq; auto.
  auto.
 apply Greater_imp_ap; auto.
Qed.

End PosP_properties.

#[global]
Hint Resolve mult_resp_nonneg.

(**
** Properties of one over successor
%\begin{convention}% Let [R] be an ordered field.
%\end{convention}%
*)

Definition one_div_succ (R : COrdField) i : R := [1][/] Snring R i[//]nringS_ap_zero _ i.

Arguments one_div_succ [R].

Section One_div_succ_properties.

Variable R : COrdField.

Lemma one_div_succ_resp_leEq : forall m n, m <= n -> one_div_succ (R:=R) n [<=] one_div_succ m.
Proof.
 unfold one_div_succ in |- *. unfold Snring in |- *. intros.
 apply recip_resp_leEq.
  apply pos_nring_S.
 apply nring_leEq.
 auto with arith.
Qed.

Lemma one_div_succ_pos : forall i, ([0]:R) [<] one_div_succ i.
Proof.
 intro.
 unfold one_div_succ in |- *.
 unfold Snring in |- *.
 apply recip_resp_pos.
 apply nring_pos.
 auto with arith.
Qed.

Lemma one_div_succ_resp_less : forall i j, i < j -> one_div_succ j [<] one_div_succ (R:=R) i.
Proof.
 intros.
 unfold one_div_succ in |- *. unfold Snring in |- *. intros.
 apply recip_resp_less.
  apply pos_nring_S.
 apply nring_less.
 auto with arith.
Qed.

End One_div_succ_properties.

(**
** Properties of [Half]
*)

Definition Half (R : COrdField) := ([1]:R) [/]TwoNZ.

Arguments Half {R}.

Section Half_properties.

(**
%\begin{convention}%
Let [R] be an ordered field.
%\end{convention}%
*)

Variable R : COrdField.

Lemma half_1 : (Half:R) [*]Two [=] [1].
Proof.
 unfold Half in |- *.
 apply div_1.
Qed.
Hint Resolve half_1: algebra.

Lemma pos_half : ([0]:R) [<] Half.
Proof.
 apply mult_cancel_pos_lft with (Two:R).
  apply (pos_wd R (Half[*]Two) [1]).
   exact half_1.
  apply pos_one.
 apply less_leEq; apply pos_two.
Qed.

Lemma half_1' : forall x : R, x[*]Half[*]Two [=] x.
Proof.
 intros.
 unfold Half in |- *.
 rational.
Qed.

Lemma half_2 : (Half:R) [+]Half [=] [1].
Proof.
 unfold Half in |- *.
 rational.
Qed.

Lemma half_lt1 : (Half:R) [<] [1].
Proof.
 astepr (Half[+] (Half:R)).
  rstepl ((Half:R) [+][0]).
  apply plus_resp_less_lft.
  exact pos_half.
 exact half_2.
Qed.

Lemma half_3 : forall x : R, [0] [<] x -> Half[*]x [<] x.
Proof.
 intros.
 astepr ([1][*]x).
 apply mult_resp_less; auto.
 exact half_lt1.
Qed.

End Half_properties.
#[global]
Hint Resolve half_1 half_1' half_2: algebra.
