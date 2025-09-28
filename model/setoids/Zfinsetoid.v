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
From Coq Require Export ZArith.
Require Import CoRN.algebra.CSetoids.

(**
** Setoids of the integers between 0 and [z]
*)

Record ZF (n:Z):Set:=
{ZF_crr:> Z ;
ZF_prf0: (Z.lt  ZF_crr n);
ZF_prf1: (Z.le 0 ZF_crr)
}.

Definition ZFeq (n : Z) : ZF n -> ZF n -> Prop.
Proof.
 intros a b.
 case a.
 case b.
 intros x H H' x0 H0 H0'.
 exact (x = x0).
Defined.

Definition ZFap (n : Z) : ZF n -> ZF n -> CProp.
Proof.
 intros a b.
 case a.
 case b.
 intros x H H' x0 H0 H0'.
 exact (x <> x0).
Defined.

Lemma ZFap_irreflexive : forall n : Z, irreflexive (ZFap n).
Proof.
 unfold irreflexive in |- *.
 unfold ZFap in |- *.
 intros n x.
 case x.
 intuition.
 red in |- *.
 intuition.
Qed.

Lemma ZFap_symmetric : forall n : Z, Csymmetric (ZFap n).
Proof.
 intro n.
 unfold Csymmetric in |- *.
 unfold ZFap in |- *.
 intros x y.
 case x.
 case y.
 intuition.
Qed.

Lemma ZFap_cotransitive : forall n : Z, cotransitive (ZFap n).
Proof.
 intro n.
 unfold cotransitive in |- *.
 unfold ZFap in |- *.
 intros x y.
 case x.
 case y.
 intros x0 H0 H0' x1 H1 H1' H2 z.
 case z.
 intros x2 H H'.
 set (H5 := Z.eq_dec x2 x1) in *.
 elim H5.
  clear H5.
  intro H5.
  right.
  rewrite H5.
  exact H2.
 clear H5.
 intro H5.
 left.
 exact H5.
Qed.

Lemma ZFap_tight : forall n : Z, tight_apart (ZFeq n) (ZFap n).
Proof.
 unfold tight_apart in |- *.
 unfold ZFap in |- *.
 unfold ZFeq in |- *.
 intros n x y.
 case x.
 case y.
 intros x0 H0 H0'x1 H1 H1'.
 red in |- *.
 unfold not in |- *.
 unfold Not in |- *.
 intuition; auto with *.
Qed.

Definition Zless (n : Z) :=
  Build_is_CSetoid (ZF n) (ZFeq n) (ZFap n) (ZFap_irreflexive n)
    (ZFap_symmetric n) (ZFap_cotransitive n) (ZFap_tight n).

Definition ZCSetoid_of_less (n : Z) : CSetoid :=
  Build_CSetoid (ZF n) (ZFeq n) (ZFap n) (Zless n).
