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

(** printing Q %\ensuremath{\mathbb{Q}}% *)
(** printing QZERO %\ensuremath{0_\mathbb{Q}}% #0<sub>Q</sub># *)
(** printing QONE %\ensuremath{1_\mathbb{Q}}% #1<sub>Q</sub># *)
(** printing QTWO %\ensuremath{2_\mathbb{Q}}% #2<sub>Q</sub># *)
(** printing QFOUR %\ensuremath{4_\mathbb{Q}}% #4<sub>Q</sub># *)

Require Export CoRN.logic.CLogic.
From Coq Require Import Arith.
From Coq Require Import Peano_dec.
Require Import CoRN.model.structures.Zsec.
From Coq Require Export QArith.
Require Import CoRN.stdlib_omissions.Q.

Close Scope Q_scope.
Local Open Scope Q_scope.

(**
* [Q]
** About [Q]
We define the structure of rational numbers as follows. First of all,
it consists of the set of rational numbers, defined as the set of
pairs $\langle a,n\rangle$#&lang;a,n&rang;# with [a:Z] and
[n:positive]. Intuitively, $\langle a,n\rangle$#&lang;a,n&rang;#
represents the rational number [a[/]n]. Then there is the equality on
[Q]: $\langle a,m\rangle=\langle
b,n\rangle$#&lang;a,m&rang;=&lang;b,n&rang;# iff [an [=] bm]. We
also define apartness, order, addition, multiplication, opposite,
inverse an de constants 0 and 1.  *)

#[global]
Instance Q_default : @DefaultRelation Q Qeq | 2 := {}.

Definition Qap (x y : Q) := ~(Qeq x y).
Infix "/=" := Qap (no associativity, at level 70) : Q_scope.

Definition Qinv_dep (x : Q) (x_ : Qap x 0) := Qinv x.

(**
*** Apartness
*)

Lemma Q_non_zero : forall x : Q, (x/=0) -> Qnum x <> 0%Z.
Proof. firstorder auto with qarith zarith. Qed.

Lemma ap_Q_irreflexive0 : forall x : Q, Not (x/=x).
Proof. firstorder. Qed.

Lemma ap_Q_symmetric0 : forall x y : Q, (x/=y) -> y/=x.
Proof. firstorder auto with crelations. Qed.

Lemma ap_Q_cotransitive0 : forall x y : Q, (x/=y) ->
 forall z : Q, (x/=z) or (z/=y).
Proof. 
 intros x y X z.
 unfold Qap in |- *.
 case (Qeq_dec x z).
  intro e.
  right.
  red in |- *.
  intro H0.
  apply X.
  exact (Qeq_trans x z y e H0).
 intros n.
 left.
 intro H.
 elim n.
 auto.
Qed.

Lemma ap_Q_tight0 : forall x y : Q, Not (x/=y) <-> x==y.
Proof.
 intros x y.
 red in |- *.
 split.
  unfold Qap in |- *.
  intro.
  case (Qeq_dec x y).
   intro e.
   assumption.
  intro n.
  elim H.
  intro H0.
  elim n.
  assumption.
 intro H.
 unfold Qap in |- *.
 red in |- *.
 intro H0.
 elim H0.
 assumption.
Qed.

(**
*** Addition
*)

Lemma Qplus_strext0 : forall x1 x2 y1 y2 : Q,
 (x1+y1/=x2+y2) -> (x1/=x2) or (y1/=y2).
Proof.
 unfold Qap in |- *.
 intros x1 x2 y1 y2 X.
 case (Qeq_dec x1 x2).
  intro e.
  right.
  red in |- *.
  intro H0.
  apply X.
  apply Qplus_comp; auto. 
 tauto.
Qed.

(**
*** Multiplication
*)

Lemma Qmult_strext0 : forall x1 x2 y1 y2 : Q,
 (x1*y1/=x2*y2) -> (x1/=x2) or (y1/=y2).
Proof.
 intros x1 x2 y1 y2 X.
 case (Qeq_dec x1 x2).
  right.
  intros ?.
  apply X.
  apply Qmult_comp; auto.
 tauto.
Qed.

Lemma nonZero : forall x : Q, ~(x==0) ->
  ~(Qmake (Z.sgn (Qnum x) * Qden x)%Z (posZ (Qnum x))==0).
Proof.
 intro x.
 unfold Qeq in |- *.
 unfold Qnum at 2 6 in |- *.
 repeat rewrite Zmult_0_l.
 unfold Qden at 1 3 in |- *.
 repeat rewrite Zplus_0_l.
 repeat rewrite Zmult_1_r.
 simpl in |- *.
 intro H.
 cut (Z.sgn (Qnum x) <> 0%Z).
  intro H0.
  cut (Zpos (Qden x) <> 0%Z).
   intro H1.
   intro H2.
   elim H0.
   exact (Zmult_integral_l (Qden x) (Z.sgn (Qnum x)) H1 H2).
  apply Zgt_not_eq.
  auto with zarith.
 apply Zsgn_3.
 intro; elim H; auto.
Qed.

(**
*** Inverse
*)

Lemma Qinv_strext : forall (x y : Q) x_ y_,
 ~(Qinv_dep x x_==Qinv_dep y y_) -> ~(x==y).
Proof.
 firstorder using Qinv_comp.
Qed.

Lemma Qinv_is_inv : forall (x : Q) (Hx : x/=0),
 (x*Qinv_dep x Hx==1) /\ (Qinv_dep x Hx*x==1).
Proof.
 intros x Hx.
 split.
  now apply (Qmult_inv_r x).
 rewrite -> Qmult_comm.
 now apply (Qmult_inv_r x).
Qed.


(**
*** Less-than
*)

Program Definition Zdec_sign (z: Z): (z < Z0)%Z + (Z0 < z)%Z + (z = Z0) :=
  match z with
  | Zneg p => inl _ (inl _ _)
  | Zpos p => inl _ (inr _ _)
  | Z0 => inr  _ _
  end.

Next Obligation. reflexivity. Qed.
Next Obligation. reflexivity. Qed.

Program Definition Qdec_sign (q: Q): (q < 0) + (0 < q) + (q == 0) :=
  match Zdec_sign (Qnum q) with
  | inl (inr H) => inl _ (inr _ _)
  | inl (inl _) => inl _ (inl _ _)
  | inr _ => inr _ _
  end.

Next Obligation. unfold Qlt. simpl. rewrite Zmult_1_r. assumption. Qed.
Next Obligation. unfold Qlt. simpl. rewrite Zmult_1_r. assumption. Qed.
Next Obligation. unfold Qeq. simpl. rewrite Zmult_1_r. assumption. Qed.

Lemma Qlt_strext_unfolded : forall x1 x2 y1 y2 : Q,
 (x1<y1) -> (x2<y2) or (x1/=x2) or (y1/=y2).
Proof with auto.
 intros x1 x2 y1 y2 E.
 destruct (Q_dec x2 y2) as [[|] | ]...
  destruct (Qeq_dec x1 x2) as [G | ]...
  right. right. apply Qnot_eq_sym, Qlt_not_eq. apply Qlt_trans with x2... 
  eapply Qlt_compat. symmetry. apply G. reflexivity. assumption. (* rewrite fails *)
 right.
 destruct (Qeq_dec x1 y2) as [G|G].
  right. apply Qnot_eq_sym, Qlt_not_eq. 
  eapply Qlt_compat. symmetry. apply G. reflexivity. assumption.
 left. unfold Qap. intro F. apply G. transitivity x2...
Qed.

Lemma Qlt_is_antisymmetric_unfolded : forall x y : Q, (x<y) -> Not (y<x).
Proof.
 intros x y E1 E2.
 apply (Qlt_irrefl x).
 eapply Qlt_trans; eauto.
Qed.

Lemma Qlt_gives_apartness : forall x y : Q, Iff (x/=y) ((x<y) or (y<x)).
Proof with intuition.
 intros x y; split; intros E.
  destruct (Q_dec x y); intuition; auto with *.
 destruct E. 
  apply Qlt_not_eq...
 apply Qnot_eq_sym, Qlt_not_eq...
Qed.

(**
*** Miscellaneous
We consider the injection [inject_Z] from [Z] to [Q] as a coercion.
*)

Coercion inject_Z : Z >-> Q.

Lemma injz_plus : forall m n : Z,
 (inject_Z (m + n):Q)==(inject_Z m:Q)+inject_Z n.
Proof.
 intros m n.
 unfold inject_Z in |- *.
 simpl in |- *.
 unfold Qeq in |- *.
 unfold Qnum at 1 in |- *.
 unfold Qden at 2 in |- *.
 replace ((m + n) * 1)%Z with (m + n)%Z.
  replace (Qnum (Qmake m 1+Qmake n 1)%Q * 1)%Z with (Qnum (Qmake m 1+Qmake n 1)).
   unfold Qplus in |- *.
   simpl in |- *.
   ring.
  ring.
 ring.
Qed.

Lemma injZ_One : (inject_Z 1:Q)==1.
Proof. reflexivity. Qed.

(** We can always find a natural Qnumber that is bigger than a given rational
Qnumber.
*)

Theorem Q_is_archemaedian0 : forall x : Q,
 {n : positive | x<Qmake n 1%positive}.
Proof.
 intro x.
 case x.
 intros p q.
 exists (P_of_succ_nat (Z.abs_nat p)).
 red in |- *.
 unfold Qnum at 1 in |- *.
 unfold Qden in |- *.
 apply toCProp_Zlt.
 simpl in |- *.
 rewrite Zmult_1_r.
 apply Z.lt_le_trans with (P_of_succ_nat (Z.abs_nat p) * 1)%Z.
  rewrite Zmult_1_r.
  case p; simpl in |- *. auto with zarith.
   intros; rewrite P_of_succ_nat_o_nat_of_P_eq_succ; rewrite Pplus_one_succ_r.
   change (p0 < p0 + 1)%Z in |- *.
   auto with zarith.
  intros; unfold Z.lt in |- *; auto.
 change (P_of_succ_nat (Z.abs_nat p) * 1%positive <= P_of_succ_nat (Z.abs_nat p) * q)%Z in |- *.
 apply Zmult_le_compat_l.
  change (Z.succ 0 <= q)%Z in |- *.
  apply Zgt_le_succ.
  auto with zarith.
 auto with zarith.
Qed.

Lemma Qle_is_not_lt : forall x y : Q, x <= y <-> ~ y < x.
Proof. firstorder using Qle_not_lt, Qnot_lt_le. Qed.

Lemma Qge_is_not_gt : forall x y : Q, x >= y <-> y <= x.
Proof. firstorder. Qed.

Lemma Qgt_is_lt : forall x y : Q, x > y IFF  y < x.
Proof. firstorder. Qed.

Lemma QNoDup_CNoDup_Qap(l: list Q): QNoDup l  IFF  CNoDup Qap l.
Proof with auto.
 induction l; simpl; split; intro...
   apply NoDup_nil.
  split.
   apply IHl. inversion_clear H...
  apply (CForall_prop _).
  intros ? A.
  inversion_clear H.
  intro E.
  apply H0.
  rewrite E.
  apply in_map...
 apply NoDup_cons. 2: firstorder.
 intro.
 destruct (proj1 (in_map_iff _ _ _) H) as [x [H0 H1]].
 destruct X.
 apply (snd (@CForall_prop Q (Qap a) l) c0 x)...
 rewrite <- (Qred_correct x).
 rewrite H0.
 symmetry.
 apply Qred_correct.
Qed.
