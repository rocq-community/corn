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

(** printing {#N} $\ensuremath{\mathrel\#_{\mathbb N}}$ *)

From Coq Require Export Peano_dec.
From Coq Require Export Relations.
Require Import CoRN.logic.CLogic.
From Coq Require Import Lia.

(**
* [nat]
** About [nat]

We prove some basic lemmas of the natural numbers.

A variant of [0_S] from the standard library
*)

Lemma S_O : forall n : nat, S n <> 0.
Proof.
 intro n.
 red in |- *.
 intro H.
 generalize O_S.
 intro H0.
 red in H0.
 apply H0 with n.
 apply sym_eq.
 exact H.
Qed.

(**
*** Apartness
*)

Definition ap_nat (x y : nat) := ~ (x = y :>nat).

Infix "{#N}" := ap_nat (no associativity, at level 90).

Lemma ap_nat_irreflexive0 : forall x : nat, Not (x{#N}x).
Proof.
 red in |- *.
 unfold ap_nat in |- *.
 intros x X.
 apply X.
 auto.
Qed.

Lemma ap_nat_symmetric0 : forall x y : nat, (x{#N}y) -> y{#N}x.
Proof.
 intros x y.
 unfold ap_nat in |- *.
 intros X.
 intro Y.
 apply X.
 auto.
Qed.

Lemma ap_nat_cotransitive0 : forall x y : nat,
 (x{#N}y) -> forall z : nat, (x{#N}z) or (z{#N}y).
Proof.
 intros x y X z.
 unfold ap_nat in |- *.
 case (eq_nat_dec x z).
  intro e.
  right.
  rewrite <- e.
  assumption.
 intro.
 left.
 intro.
 elim n.
 assumption.
Qed.

Lemma ap_nat_tight0 : forall x y : nat, Not (x{#N}y) <-> x = y.
Proof.
 intros x y.
 red in |- *.
 split.
  unfold ap_nat in |- *.
  intro H.
  case (eq_nat_dec x y).
   intro e.
   assumption.
  intro n.
  elim H.
  intro H0.
  elim n.
  assumption.
 intro H.
 unfold ap_nat in |- *.
 intro H0.
 elim H0.
 assumption.
Qed.

(**
*** Addition
*)

Lemma plus_strext0 : forall x1 x2 y1 y2 : nat,
 (x1+y1{#N}x2+y2) -> (x1{#N}x2) or (y1{#N}y2).
Proof.
 intros x1 x2 y1 y2 H.
 unfold ap_nat in |- *.
 unfold ap_nat in H.
 case (eq_nat_dec x1 x2).
  intro e.
  right.
  red in |- *.
  intro H0.
  apply H.
  auto.
 intro n.
 left.
 intro H0.
 elim n.
 assumption.
Qed.

(** There is no inverse for addition, because every candidate will fail for 2
*)

Lemma no_inverse0 : forall f : nat -> nat, ~ ((2+f 2) = 0 /\ (f 2+2) = 0).
Proof.
 intro f.
 simpl in |- *.
 red in |- *.
 intro H.
 elim H.
 intros H1 H2.
 set (H3 := O_S (S (f 2))) in *.
 generalize H3.
 unfold not in |- *.
 intro H4.
 apply H4.
 lia.
Qed.



(**
*** Multiplication
*)

Lemma mult_strext0 : forall x1 x2 y1 y2 : nat,
 (x1*y1{#N}x2*y2) -> (x1{#N}x2) or (y1{#N}y2).
Proof.
 unfold ap_nat in |- *.
 intros x1 x2 y1 y2 H.
 cut ({x1 = x2} + {x1 <> x2}).
  intro H1.
  elim H1.
   intro e.
   right.
   red in |- *.
   intro H0.
   apply H.
   exact (f_equal2 mult e H0).
  intro X.
  auto.
 apply eq_nat_dec.
Qed.

(**
*** Decidability
*)
Lemma not_or:(forall (p q:nat), (p<>q)-> p<q or q<p):CProp.
Proof.
 simpl.
 intros p q H.
 set (H0:=(lt_eq_lt_dec p q)).
 elim H0.
  clear H0.
  intros H0.
  elim H0.
   clear H0.
   intros H0.
   left.
   exact H0.
  clear H0.
  intros H0.
  intuition.
 clear H0.
 intros H0.
 right.
 exact H0.
Qed.

(* begin hide *)

Lemma k_zero:forall (k i l:nat),
Not (0<k or 0=k and i<l)-> k=0.
Proof.
 intros k i l H.
 unfold Not in H.
 set (H1:=(lt_eq_lt_dec 0 k)).
 elim H1.
  clear H1.
  intro H1.
  elim H1.
   clear H1.
   intuition.
  intuition.
 intuition; auto with *.
Qed.

Lemma lexi_dec:(forall (k i l:nat),
Cdecidable (0<k or 0=k and i<l)):CProp.
Proof.
 intros k i l.
 unfold Cdecidable.
 set (H:=(lt_eq_lt_dec 0 k)).
 elim H.
  clear H.
  intro H.
  elim H.
   clear H.
   intro H.
   left.
   left.
   exact H.
  clear H.
  intro H.
  elim (le_gt_dec l i).
   intro H1.
   right.
   unfold Not.
   intro H2.
   intuition; auto with *.
  intro H1.
  left.
  right.
  intuition.
 intuition; auto with *.
Qed.


(* end hide *)
