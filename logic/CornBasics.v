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

(** printing alpha %\ensuremath{\alpha}% #&alpha;# *)
(** printing beta %\ensuremath{\beta}% #&beta;# *)
(** printing delta %\ensuremath{\delta}% #&delta;# *)
(** printing eps %\ensuremath{\varepsilon}% #&epsilon;# *)
(** printing phi %\ensuremath{\phi}% #&phi;# *)
(** printing eta %\ensuremath{\eta}% #&eta;# *)
(** printing omega %\ensuremath{\omega}% #&omega;# *)

(** printing nat %\ensuremath{\mathbb N}% #<b>N</b># *)
(** printing Z %\ensuremath{\mathbb Z}% #<b>Z</b># *)

From Coq Require Export ZArith.
From Coq Require Import Lia.
Require Export CoRN.stdlib_omissions.List.
From Coq Require Import Eqdep_dec.
From Coq Require Import Setoid.

Tactic Notation "apply" ":" constr(x) := pose proof x as HHH; first [
  refine HHH | 
  refine (HHH _) |
  refine (HHH _ _) |
  refine (HHH _ _ _) |
  refine (HHH _ _ _ _) |
  refine (HHH _ _ _ _ _) |
  refine (HHH _ _ _ _ _ _) |
  refine (HHH _ _ _ _ _ _ _) |
  refine (HHH _ _ _ _ _ _ _ _) |
  refine (HHH _ _ _ _ _ _ _ _ _) |
  refine (HHH _ _ _ _ _ _ _ _ _ _) |
  refine (HHH _ _ _ _ _ _ _ _ _ _ _) |
  refine (HHH _ _ _ _ _ _ _ _ _ _ _ _) |
  refine (HHH _ _ _ _ _ _ _ _ _ _ _ _ _) |
  refine (HHH _ _ _ _ _ _ _ _ _ _ _ _ _ _)]; clear HHH.



#[global]
Instance: @DefaultRelation nat eq | 2 := {}.

(**
* Basics
This is random stuff that should be in the Coq basic library.
*)

Lemma lt_le_dec : forall n m : nat, {n < m} + {m <= n}.
Proof.
 intros.
 case (le_lt_dec m n); auto.
Qed.

Lemma lt_z_two : 0 < 2.
Proof.
 auto.
Qed.

Lemma le_pred : forall n m : nat, n <= m -> pred n <= pred m.
Proof.
 simple induction n. simpl in |- *. auto with arith.
  intros n0 Hn0. simple induction m. simpl in |- *. intro H. inversion H.
 intros n1 H H0. simpl in |- *. auto with arith.
Qed.

Lemma lt_mult_right : forall x y z : nat, x < y -> 0 < z -> x * z < y * z.
Proof.
 intros x y z H H0.
 induction  z as [| z Hrecz].
  elim (Nat.lt_irrefl _ H0).
 rewrite Nat.mul_comm.
 replace (y * S z) with (S z * y); auto with arith.
Qed.

Lemma le_mult_right : forall x y z : nat, x <= y -> x * z <= y * z.
Proof.
 intros x y z H.
 rewrite Nat.mul_comm. rewrite (Nat.mul_comm y).
 auto with arith.
Qed.

Lemma le_irrelevent : forall n m (H1 H2:le n m), H1=H2.
Proof.
 assert (forall n (H1: le n n), H1 = le_n n).
  intros n H1.
  change H1 with (eq_rec n (fun a => a <= n) H1 _ (refl_equal n)).
  generalize (refl_equal n).
  revert H1.
  generalize n at 1 3 7.
  dependent inversion H1.
   apply K_dec_set.
    decide equality.
   reflexivity.
  intros; exfalso; lia.
 induction m.
  dependent inversion H1.
  symmetry.
  apply H.
 dependent inversion H1.
  symmetry.
  apply H.
 intros H3.
 change H3 with (eq_rec (S m) (le n) (eq_rec n (fun n => n <= S m) H3 _ (refl_equal n)) _ (refl_equal (S m))).
 generalize (refl_equal n) (refl_equal (S m)).
 revert H3.
 generalize n at 1 2 7.
 generalize (S m) at 1 2 5 6.
 dependent inversion H3.
  intros; exfalso; lia.
 intros e e0.
 assert (e':=e).
 assert (e0':=e0).
 revert e e0 l0.
 rewrite e', (eq_add_S _ _ e0').
 intros e.
 elim e using K_dec_set.
  decide equality.
 intros e0.
 elim e0 using K_dec_set.
  decide equality.
 simpl.
 intros l0.
 rewrite (IHm l l0).
 reflexivity.
Qed.

Lemma minus3:forall (a b c:nat),(c<=b<=a)-> a+(b-c)=b+(a-c).
Proof.
 intros a b d H.
 cut  ((Z_of_nat a) + ((Z_of_nat b) - (Z_of_nat d)) = (Z_of_nat b) + ((Z_of_nat a) - (Z_of_nat d)))%Z.
  2:intuition; auto with *.
 intro H1.
 elim H.
 intros H2 H3.
 set (H4:=(inj_minus1 b d H2)).
 rewrite<- H4 in H1.
 cut (d <=a).
  intro H5.
  2:intuition; auto with *.
 set (H6:=(inj_minus1 a d H5)).
 rewrite<- H6 in H1.
 intuition; auto with *.
Qed.

Lemma minus4:forall (a b c d:nat), (d<=c<=b)->
  (a+b)+(c-d)=(a+c)+(b-d).
Proof.
 intros a b c0 d H.
 cut (((Z_of_nat a)+(Z_of_nat b))+((Z_of_nat c0)-(Z_of_nat d))=
   ((Z_of_nat a)+(Z_of_nat c0))+((Z_of_nat b)-(Z_of_nat d)))%Z.
  intro H0.
  2:intuition; auto with *.
 elim H.
 intros H1 H2.
 set (H3:=(inj_minus1 c0 d H1)).
 rewrite<- H3 in H0.
 cut (d<=b).
  2:intuition; auto with *.
 intro H4.
 set (H5:=(inj_minus1 b d H4)).
 rewrite<- H5 in H0.
 intuition; auto with *.
Qed.

(** The power function does not exist in the standard library *)

Fixpoint power (m : nat) : nat -> nat :=
  match m with
  | O => fun _ : nat => 1
  | S n => fun x : nat => power n x * x
  end.

(* needed for computational behavior of "Inversion" tactic *)
Transparent sym_eq.
Transparent f_equal.

Notation Pair := (pair (B:=_)) (only parsing).
Notation Proj1 := (proj1 (B:=_)) (only parsing).
Notation Proj2 := (proj2 (B:=_)) (only parsing ).

(* Following only needed in finite, but tha's now obsolete

Lemma deMorgan_or_and: (A,B,X:Prop)((A\/B)->X)->(A->X)/\(B->X).
Tauto.
Qed.

Lemma deMorgan_and_or: (A,B,X:Prop)(A->X)/\(B->X)->(A\/B->X).
Tauto.
Qed.

Lemma deMorgan_ex_all:
  (A:Set)(P:A->Prop)(X:Prop)((Ex P)->X)->(a:A)(P a)->X.
Intros. Apply H; Exists a; Assumption.
Qed.

Lemma deMorgan_all_ex:
  (A:Set)(P:A->Prop)(X:Prop)((a:A)(P a)->X)->(Ex P)->X.
Intros. Elim H0; Assumption.
Qed.

Implicit Arguments Off.

Three lemmas for proving properties about definitions made with case
distinction to a sumbool, i.e. [{A} + {B}].

Lemma sumbool_rec_or : (A,B:Prop)(S:Set)(l,r:S)(s:{A}+{B})
                  (sumbool_rec A B [_:{A}+{B}]S [x:A]l [x:B]r s) = l \/
                  (sumbool_rec A B [_:{A}+{B}]S [x:A]l [x:B]r s) = r.
Intros. Elim s.
Intros. Left. Reflexivity.
Intros. Right. Reflexivity.
Qed.
*)

Lemma not_r_sumbool_rec : forall (A B : Prop) (S : Set) (l r : S), ~ B -> forall H : {A} + {B},
 sumbool_rec (fun _ : {A} + {B} => S) (fun x : A => l) (fun x : B => r) H = l.
Proof.
 intros. elim H0.
 intros. reflexivity.
  intro. elim H. assumption.
Qed.

Lemma not_l_sumbool_rec : forall (A B : Prop) (S : Set) (l r : S), ~ A -> forall H : {A} + {B},
 sumbool_rec (fun _ : {A} + {B} => S) (fun x : A => l) (fun x : B => r) H = r.
Proof.
 intros. elim H0.
 intro. elim H. assumption.
  intros. reflexivity.
Qed.

(* begin hide *)
Set Implicit Arguments.
Unset Strict Implicit.
(* end hide *)

(**
** Some results about [Z]

We consider the injection [inject_nat] from [nat] to [Z] as a
coercion. *)
(* begin hide *)
Coercion Zpos : positive >-> Z.
Coercion Z_of_nat : nat >-> Z.
(* end hide *)

Lemma POS_anti_convert : forall n : nat, S n = Zpos (P_of_succ_nat n) :>Z.
Proof.
 simple induction n.
  simpl in |- *.
  reflexivity.
 intros n0 H.
 simpl in |- *.
 reflexivity.
Qed.

Lemma NEG_anti_convert : forall n : nat, (- S n)%Z = Zneg (P_of_succ_nat n).
Proof.
 simple induction n.
  simpl in |- *.
  reflexivity.
 intros n0 H.
 simpl in |- *.
 reflexivity.
Qed.

Lemma lt_O_positive_to_nat : forall (p : positive) (m : nat), 0 < m -> 0 < Pmult_nat p m.
Proof.
 intro p.
 elim p.
   intros p0 H m H0.
   simpl in |- *.
   auto with arith.
  intros p0 H m H0.
  simpl in |- *.
  apply H.
  auto with arith.
 intros m H.
 simpl in |- *.
 assumption.
Qed.

Lemma anti_convert_pred_convert : forall p : positive,
 p = P_of_succ_nat (pred (nat_of_P p)).
Proof.
 intro p.
 pattern p at 1 in |- *.
 rewrite <- pred_o_P_of_succ_nat_o_nat_of_P_eq_id.
 cut (exists n : nat, nat_of_P p = S n).
  intro H.
  elim H; intros x H0.
  rewrite H0.
  elim x.
   simpl in |- *.
   reflexivity.
  intros n H1.
  simpl in |- *.
  rewrite Pos.pred_succ.
  reflexivity.
 exists (pred (nat_of_P p)).
 symmetry; apply Nat.lt_succ_pred with 0.
 unfold nat_of_P in |- *.
 apply lt_O_positive_to_nat.
 auto with arith.
Qed.

Lemma p_is_some_anti_convert : forall p : positive, exists n : nat, p = P_of_succ_nat n.
Proof.
 intro p.
 exists (pred (nat_of_P p)).
 apply anti_convert_pred_convert.
Qed.

Lemma convert_is_POS : forall p : positive, nat_of_P p = Zpos p :>Z.
Proof.
 intro p.
 elim (p_is_some_anti_convert p).
 intros x H.
 rewrite H.
 rewrite nat_of_P_o_P_of_succ_nat_eq_succ.
 apply POS_anti_convert.
Qed.

Lemma min_convert_is_NEG : forall p : positive, (- nat_of_P p)%Z = Zneg p.
Proof.
 intro p.
 elim (p_is_some_anti_convert p).
 intros x H.
 rewrite H.
 rewrite nat_of_P_o_P_of_succ_nat_eq_succ.
 apply NEG_anti_convert.
Qed.

Lemma surj_eq:forall (n m:nat),
((Z_of_nat n)=(Z_of_nat m))%Z -> n=m.
Proof.
 intros n m.
 intuition; auto with *.
Qed.

Lemma surj_le:forall (n m:nat),
((Z_of_nat n)<=(Z_of_nat m))%Z -> n<=m.
Proof.
 intros n m.
 intuition; auto with *.
Qed.

Lemma surj_lt:forall (n m:nat),
((Z_of_nat n)<(Z_of_nat m))%Z -> n<m.
Proof.
 intros n m.
 intuition; auto with *.
Qed.

Lemma surj_not:forall (n m:nat),
((Z_of_nat n)<>(Z_of_nat m))%Z -> n<>m.
Proof.
 intros n m.
 intuition.
Qed.

Lemma lt_lt_minus:forall(q p l:nat),
q<l -> p<q -> p+(l-q)<l.
Proof.
 intros q p l H H0.
 intuition; auto with *.
Qed.

Lemma inject_nat_convert :
 forall p : positive, Z_of_nat (nat_of_P p) = BinInt.Zpos p.
Proof.
 intros.
 elim (ZL4 p); intros.
 rewrite H.
 simpl in |- *.
 apply (f_equal BinInt.Zpos).
 apply nat_of_P_inj.
 rewrite H.
 apply nat_of_P_o_P_of_succ_nat_eq_succ.
Qed.

Definition Z_to_nat: forall (z:Z),(0<=z)%Z->nat.
Proof.
 intros z.
 case z.
   intro H.
   exact 0.
  intros p H.
  exact (nat_of_P p).
 intros p H.
 cut False.
  intuition.
 intuition.
Defined.

Lemma Z_to_nat_correct:forall (z:Z)(H:(0<=z)%Z),
   z=(Z_of_nat (Z_to_nat H)).
Proof.
 intro z.
 case z.
   intro H.
   unfold Z_to_nat.
   reflexivity.
  intros p H.
  unfold Z_to_nat.
  cut ( Z_of_nat (nat_of_P p)= Zpos p).
   intuition.
  apply inject_nat_convert.
 intros p H.
 cut False.
  intuition.
 intuition.
Qed.

Lemma Z_exh : forall z : Z, (exists n : nat, z = n) \/ (exists n : nat, z = (- n)%Z).
Proof.
 intro z.
 elim z.
   left.
   exists 0.
   auto.
  intro p.
  left.
  exists (nat_of_P p).
  rewrite convert_is_POS.
  reflexivity.
 intro p.
 right.
 exists (nat_of_P p).
 rewrite min_convert_is_NEG.
 reflexivity.
Qed.

Lemma nats_Z_ind : forall P : Z -> Prop,
 (forall n : nat, P n) -> (forall n : nat, P (- n)%Z) -> forall z : Z, P z.
Proof.
 intros P H H0 z.
 elim (Z_exh z); intro H1.
  elim H1; intros x H2.
  rewrite H2.
  apply H.
 elim H1; intros x H2.
 rewrite H2.
 apply H0.
Qed.

Lemma pred_succ_Z_ind : forall P : Z -> Prop, P 0%Z ->
 (forall n : Z, P n -> P (n + 1)%Z) -> (forall n : Z, P n -> P (n - 1)%Z) -> forall z : Z, P z.
Proof.
 intros P H H0 H1 z.
 apply nats_Z_ind.
  intro n.
  elim n.
   exact H.
  intros n0 H2.
  replace (S n0:Z) with (n0 + 1)%Z.
   apply H0.
   assumption.
  rewrite Znat.inj_S.
  reflexivity.
 intro n.
 elim n.
  exact H.
 intros n0 H2.
 replace (- S n0)%Z with (- n0 - 1)%Z.
  apply H1.
  assumption.
 rewrite Znat.inj_S.
 unfold Z.succ in |- *.
 rewrite Zopp_plus_distr.
 reflexivity.
Qed.

Lemma Zmult_minus_distr_r : forall n m p : Z, (p * (n - m))%Z = (p * n - p * m)%Z.
Proof.
 intros n m p.
 rewrite Zmult_comm.
 rewrite Zmult_minus_distr_r.
 rewrite Zmult_comm.
 rewrite (Zmult_comm m p).
 reflexivity.
Qed.

Lemma Zodd_Zeven_min1 : forall x : Z, Zeven.Zodd x -> Zeven.Zeven (x - 1).
Proof.
 intro x.
 elim x.
   simpl in |- *.
   auto.
  simple induction p.
    simpl in |- *.
    auto.
   intros p0 H H0.
   simpl in H0.
   tauto.
  simpl in |- *; auto.
 simple induction p.
   simpl in |- *; auto.
  simpl in |- *; auto.
 auto.
Qed.

(* begin hide *)
Set Implicit Arguments.
Unset Strict Implicit.
(* end hide *)

Definition caseZ_diff (A : Type) (z : Z) (f : nat -> nat -> A) :=
  match z with
  | Z0 => f 0 0
  | Zpos m => f (nat_of_P m) 0
  | Zneg m => f 0 (nat_of_P m)
  end.

(* begin hide *)
Set Strict Implicit.
Unset Implicit Arguments.
(* end hide *)

Lemma caseZ_diff_O : forall (A : Type) (f : nat -> nat -> A), caseZ_diff 0 f = f 0 0.
Proof.
 auto.
Qed.

Lemma caseZ_diff_Pos : forall (A : Type) (f : nat -> nat -> A) (n : nat),
  caseZ_diff n f = f n 0.
Proof.
 intros A f n.
 elim n.
  reflexivity.
 intros n0 H.
 simpl in |- *.
 rewrite nat_of_P_o_P_of_succ_nat_eq_succ.
 reflexivity.
Qed.

Lemma caseZ_diff_Neg : forall (A : Type) (f : nat -> nat -> A) (n : nat),
 caseZ_diff (- n) f = f 0 n.
Proof.
 intros A f n.
 elim n.
  reflexivity.
 intros n0 H.
 simpl in |- *.
 rewrite nat_of_P_o_P_of_succ_nat_eq_succ.
 reflexivity.
Qed.

Lemma proper_caseZ_diff : forall (A : Type) (f : nat -> nat -> A),
 (forall m n p q : nat, m + q = n + p -> f m n = f p q) ->
 forall m n : nat, caseZ_diff (m - n) f = f m n.
Proof.
 intros A F H m n.
 pattern m, n in |- *.
 apply nat_double_ind.
   intro n0.
   replace (0%nat - n0)%Z with (- n0)%Z.
    rewrite caseZ_diff_Neg.
    reflexivity.
   simpl in |- *.
   reflexivity.
  intro n0.
  replace (S n0 - 0%nat)%Z with (Z_of_nat (S n0)).
   rewrite caseZ_diff_Pos.
   reflexivity.
  simpl in |- *.
  reflexivity.
 intros n0 m0 H0.
 rewrite (H (S n0) (S m0) n0 m0).
  rewrite <- H0.
  replace (S n0 - S m0)%Z with (n0 - m0)%Z.
   reflexivity.
  repeat rewrite Znat.inj_S.
  auto with zarith.
 auto with zarith.
Qed.

Lemma diff_Z_ind : forall P : Z -> Prop, (forall m n : nat, P (m - n)%Z) -> forall z : Z, P z.
Proof.
 intros P H z.
 apply nats_Z_ind.
  intro n.
  replace (Z_of_nat n) with (n - 0%nat)%Z.
   apply H.
  simpl in |- *.
  auto with zarith.
 intro n.
 replace (- n)%Z with (0%nat - n)%Z.
  apply H.
 simpl in |- *.
 reflexivity.
Qed.

Lemma Zlt_reg_mult_l : forall x y z : Z,
 (x > 0)%Z -> (y < z)%Z -> (x * y < x * z)%Z.
Proof.
 intros x y z H H0.
 case (Zcompare_Gt_spec x 0).
  unfold Z.gt in H.
  assumption.
 intros x0 H1.
 cut (x = Zpos x0).
  intro H2.
  rewrite H2.
  unfold Z.lt in H0.
  unfold Z.lt in |- *.
  cut ((Zpos x0 * y ?= Zpos x0 * z)%Z = (y ?= z)%Z).
   intro H3.
   exact (trans_eq H3 H0).
  apply Zcompare_mult_compat.
 cut (x = (x + - (0))%Z).
  intro H2.
  exact (trans_eq H2 H1).
 simpl in |- *.
 apply (sym_eq (A:=Z)).
 exact (Zplus_0_r x).
Qed.

Lemma Zlt_opp : forall x y : Z, (x < y)%Z -> (- x > - y)%Z.
Proof.
 intros x y H.
 red in |- *.
 apply sym_eq.
 cut (Datatypes.Gt = (y ?= x)%Z).
  intro H0.
  cut ((y ?= x)%Z = (- x ?= - y)%Z).
   intro H1.
   exact (trans_eq H0 H1).
  exact (Zcompare_opp y x).
 apply sym_eq.
 exact (Z.lt_gt x y H).
Qed.

Lemma Zlt_conv_mult_l : forall x y z : Z,
 (x < 0)%Z -> (y < z)%Z -> (x * y > x * z)%Z.
Proof.
 intros x y z H H0.
 cut (- x > 0)%Z.
  intro H1.
  cut (- x * y < - x * z)%Z.
   intro H2.
   cut (- (- x * y) > - (- x * z))%Z.
    intro H3.
    cut (- - (x * y) > - - (x * z))%Z.
     intro H4.
     cut ((- - (x * y))%Z = (x * y)%Z).
      intro H5.
      rewrite H5 in H4.
      cut ((- - (x * z))%Z = (x * z)%Z).
       intro H6.
       rewrite H6 in H4.
       assumption.
      exact (Z.opp_involutive (x * z)).
     exact (Z.opp_involutive (x * y)).
    cut ((- (- x * y))%Z = (- - (x * y))%Z).
     intro H4.
     rewrite H4 in H3.
     cut ((- (- x * z))%Z = (- - (x * z))%Z).
      intro H5.
      rewrite H5 in H3.
      assumption.
     cut ((- x * z)%Z = (- (x * z))%Z).
      intro H5.
      exact (f_equal Z.opp H5).
     exact (Zopp_mult_distr_l_reverse x z).
    cut ((- x * y)%Z = (- (x * y))%Z).
     intro H4.
     exact (f_equal Z.opp H4).
    exact (Zopp_mult_distr_l_reverse x y).
   exact (Zlt_opp (- x * y) (- x * z) H2).
  exact (Zlt_reg_mult_l (- x) y z H1 H0).
 exact (Zlt_opp x 0 H).
Qed.

Lemma Zgt_not_eq : forall x y : Z, (x > y)%Z -> x <> y.
Proof.
 intros x y H.
 cut (y < x)%Z.
  intro H0.
  cut (y <> x).
   intro H1.
   red in |- *.
   intro H2.
   cut (y = x).
    intro H3.
    apply H1.
    assumption.
   exact (sym_eq H2).
  exact (Zorder.Zlt_not_eq y x H0).
 exact (Z.gt_lt x y H).
Qed.

Lemma Zmult_absorb : forall x y z : Z,
 x <> 0%Z -> (x * y)%Z = (x * z)%Z -> y = z.
Proof.
 intros x y z H H0.
 case (dec_eq y z).
  intro H1.
  assumption.
 intro H1.
 case (not_Zeq y z).
   assumption.
  intro H2.
  case (not_Zeq x 0).
    assumption.
   intro H3.
   exfalso.
   cut (x * y > x * z)%Z.
    intro H4.
    cut ((x * y)%Z <> (x * z)%Z).
     intro H5.
     apply H5.
     assumption.
    exact (Zgt_not_eq (x * y) (x * z) H4).
   exact (Zlt_conv_mult_l x y z H3 H2).
  intro H3.
  exfalso.
  cut (x * y < x * z)%Z.
   intro H4.
   cut ((x * y)%Z <> (x * z)%Z).
    intro H5.
    apply H5.
    assumption.
   exact (Zorder.Zlt_not_eq (x * y) (x * z) H4).
  apply Zlt_reg_mult_l.
   exact (Z.lt_gt 0 x H3).
  assumption.
 intro H2.
 apply False_ind.
 cut (x * z < x * y)%Z.
  intro H3.
  cut ((x * z)%Z <> (x * y)%Z).
   intro H4.
   apply H4.
   apply (sym_eq (A:=Z)).
   assumption.
  exact (Zorder.Zlt_not_eq (x * z) (x * y) H3).
 apply False_ind.
 case (not_Zeq x 0).
   assumption.
  intro H3.
  cut (x * z > x * y)%Z.
   intro H4.
   cut ((x * z)%Z <> (x * y)%Z).
    intro H5.
    apply H5.
    apply (sym_eq (A:=Z)).
    assumption.
   exact (Zgt_not_eq (x * z) (x * y) H4).
  exact (Zlt_conv_mult_l x z y H3 H2).
 intro H3.
 cut (x * z < x * y)%Z.
  intro H4.
  cut ((x * z)%Z <> (x * y)%Z).
   intro H5.
   apply H5.
   apply (sym_eq (A:=Z)).
   assumption.
  exact (Zorder.Zlt_not_eq (x * z) (x * y) H4).
 apply Zlt_reg_mult_l.
  exact (Z.lt_gt 0 x H3).
 auto.
Qed.

Section Well_foundedT.

 Variable A : Type.
 Variable R : A -> A -> Prop.

 (** The accessibility predicate is defined to be non-informative *)

 Inductive Acc : A -> Prop :=
     Acc_intro : forall x : A, (forall y : A, R y x -> Acc y) -> Acc x.
End Well_foundedT.

Section AccT.
Variable A : Type.
Definition well_founded (P : A -> A -> Prop) := forall a : A, Acc _ P a.
End AccT.
Arguments Acc [A].

Section IndT.
Variable A : Type.
Variable R : A -> A -> Prop.
Section AccIter.
  Variable P : A -> Type.
  Variable F : forall x : A, (forall y : A, R y x -> P y) -> P x.
Lemma Acc_inv : forall x : A, Acc R x -> forall y : A, R y x -> Acc R y.
Proof.
 destruct 1; trivial.
 Defined.

  Fixpoint Acc_iter (x : A) (a : Acc R x) {struct a} :
   P x := F x (fun (y : A) (h : R y x) => Acc_iter y (Acc_inv x a y h)).

 End AccIter.

Hypothesis Rwf : well_founded A R.

Theorem well_founded_induction_type :
 forall P : A -> Type,
 (forall x : A, (forall y : A, R y x -> P y) -> P x) -> forall a : A, P a.
Proof.
 Proof.
 intros; apply (Acc_iter P); auto.
 Defined.
End IndT.

Section InductionT.
Variable A : Type.

Variable f : A -> nat.
Definition ltof (a b : A) := f a < f b.

Theorem well_founded_ltof : well_founded A ltof.
Proof.
 red in |- *.
 cut (forall (n : nat) (a : A), f a < n -> Acc ltof a).
  intros H a; apply (H (S (f a))); auto with arith.
 induction n.
  intros; absurd (f a < 0); auto with arith.
 intros a ltSma.
 apply Acc_intro.
 unfold ltof in |- *; intros b ltfafb.
 apply IHn.
 apply Nat.lt_le_trans with (f a); auto with arith.
Qed.


Theorem induction_ltof2T : forall P : A -> Type,
 (forall x : A, (forall y : A, ltof y x -> P y) -> P x) -> forall a : A, P a.
Proof.
 exact (well_founded_induction_type A ltof well_founded_ltof).
Defined.
End InductionT.

Section InductionTT.
Lemma lt_wf_rect : forall (p : nat) (P : nat -> Type),
 (forall n : nat, (forall m : nat, m < n -> P m) -> P n) -> P p.
Proof.
 exact (fun (p : nat) (P : nat -> Type) (F : forall n : nat, (forall m : nat, m < n -> P m) -> P n) =>
   induction_ltof2T nat (fun m : nat => m) P F p).
Defined.
End InductionTT.

(** This new version of postive recursion gives access to
both n and n+1 for the 2n+1 case, while still maintaining efficency.
*)

Fixpoint positive_rect2_helper
 (P : positive -> Type)
 (c1 : forall p : positive, P (Pos.succ p) -> P p -> P (xI p))
 (c2 : forall p : positive, P p -> P (xO p))
 (c3 : P 1%positive)
 (b : bool) (p : positive) {struct p} : P (if b then Pos.succ p else p) :=
 match p with
 | xH    => match b with true => c2 _ c3 | false => c3 end
 | xO p' => match b with
             | true => c1 _ (positive_rect2_helper P c1 c2 c3 true _) (positive_rect2_helper P c1 c2 c3 false _)
             | false => c2 _ (positive_rect2_helper P c1 c2 c3 false _)
             end
 | xI p' => match b with
             | true => c2 _ (positive_rect2_helper P c1 c2 c3 true _)
             | false =>c1 _ (positive_rect2_helper P c1 c2 c3 true _) (positive_rect2_helper P c1 c2 c3 false _)
             end
 end.

Definition positive_rect2
 (P : positive -> Type)
 (c1 : forall p : positive, P (Pos.succ p) -> P p -> P (xI p))
 (c2 : forall p : positive, P p -> P (xO p))
 (c3 : P 1%positive) (p : positive) : P p :=
positive_rect2_helper P c1 c2 c3 false p.

Lemma positive_rect2_helper_bool : forall P c1 c2 c3 p,
positive_rect2_helper P c1 c2 c3 true p =
positive_rect2_helper P c1 c2 c3 false (Pos.succ p).
Proof.
 intros P c1 c2 c3.
 induction p; try reflexivity.
 simpl.
 rewrite IHp.
 reflexivity.
Qed.

Lemma positive_rect2_red1 : forall P c1 c2 c3 p,
positive_rect2 P c1 c2 c3 (xI p) =
c1 p (positive_rect2 P c1 c2 c3 (Pos.succ p)) (positive_rect2 P c1 c2 c3 p).
Proof.
 intros P c1 c2 c3 p.
 unfold positive_rect2.
 simpl.
 rewrite positive_rect2_helper_bool.
 reflexivity.
Qed.

Lemma positive_rect2_red2 : forall P c1 c2 c3 p,
positive_rect2 P c1 c2 c3 (xO p) =
c2 p (positive_rect2 P c1 c2 c3 p).
Proof.
 reflexivity.
Qed.

Lemma positive_rect2_red3 : forall P c1 c2 c3,
positive_rect2 P c1 c2 c3 (xH) = c3.
Proof.
 reflexivity.
Qed.

(** Iteration for natural numbers. *)

Fixpoint iterateN A (f:A -> A) (z:A) (n:nat) : list A :=
match n with
 O => nil
|S m => z :: (iterateN A f (f z) m)
end.
(* begin hide *)
Arguments iterateN [A].
(* end hide *)
Lemma iterateN_f : forall A f (z:A) n, iterateN f (f z) n = map f (iterateN f z n).
Proof.
 intros A f z n.
 revert f z.
 induction n.
  reflexivity.
 simpl.
 intros f z.
 rewrite <- IHn.
 reflexivity.
Qed.

(* Some purely logical reasoning aids: *)

Lemma iff_under_forall {X} (P Q: X -> Prop): (forall x, P x <-> Q x) -> ((forall x, P x) <-> (forall x, Q x)).
Proof. firstorder. Qed.

Lemma conjunction_under_forall {X} (P Q: X -> Prop): ((forall x, P x) /\ (forall x, Q x)) <-> (forall x, P x /\ Q x).
Proof. firstorder. Qed.
