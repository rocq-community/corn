(*
Copyright © 2006-2008 Russell O’Connor

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

From Coq Require Export Zmin.
From Coq Require Export Zmax.
From Coq Require Import ZArith.
Require Import CoRN.order.TotalOrder.

Opaque Z_lt_le_dec.
(**
** Example of a Total Order: <Z, Zle, Zmin, Zmax>
*)
Section ZTotalOrder.

Local Open Scope Z_scope.

Definition Zle_total x y : {x <= y} + {y <= x} :=
match Z_lt_le_dec x y with
| left p => left _ (Zlt_le_weak _ _ p)
| right p => right _ p
end.

Lemma Zeq_le_def : forall x y, x = y <-> x <= y /\ y <= x.
Proof.
 intros.
 split.
  intros H; rewrite H.
  firstorder using Z.le_refl.
 firstorder using Zle_antisym.
Qed.

Definition Zmonotone : (Z -> Z) -> Prop := Default.monotone Z.le.
Definition Zantitone : (Z -> Z) -> Prop := Default.antitone Z.le.

Definition ZTotalOrder : TotalOrder.
Proof.
 apply makeTotalOrder with Z (@eq Z) Z.le Zmonotone Zantitone Z.min Z.max. 1-3, 5-6: solve [auto with *].
     apply Zle_total.
    intros. apply Z.min_case_strong; auto with *.
    intros. apply Z.min_case_strong; auto with *.
   intros. apply Z.max_case_strong; auto with *.
  intros. apply Z.max_case_strong; auto with *.
Defined.

Let Zto := ZTotalOrder.

Definition Zmin_lb_l : forall x y : Z, Z.min x y <= x := @meet_lb_l Zto.
Definition Zmin_lb_r : forall x y : Z, Z.min x y <= y := @meet_lb_r Zto.
Definition Zmin_glb : forall x y z : Z, z <= x -> z <= y -> z <= (Z.min x y) :=
 @meet_glb Zto.
Definition Zmin_comm : forall x y : Z, Z.min x y = Z.min y x := @meet_comm Zto.
Definition Zmin_assoc : forall x y z : Z, Z.min x (Z.min y z) = Z.min (Z.min x y) z:=
 @meet_assoc Zto.
Definition Zmin_idem : forall x : Z, Z.min x x = x := @meet_idem Zto.
Definition Zle_min_l : forall x y : Z, x <= y <-> Z.min x y = x := @le_meet_l Zto.
Definition Zle_min_r : forall x y : Z, y <= x <-> Z.min x y = y := @le_meet_r Zto.
Definition Zmin_irred : forall x y: Z, {Z.min x y = x} + {Z.min x y = y} := @meet_irred Zto.
Definition Zmin_monotone_r : forall a : Z, Zmonotone (Z.min a) :=
 @meet_monotone_r Zto.
Definition Zmin_monotone_l : forall a : Z, Zmonotone (fun x => Z.min x a) :=
 @meet_monotone_l Zto.
Definition Zmin_le_compat : forall w x y z : Z, w <= y -> x <= z -> Z.min w x <= Z.min y z :=
 @meet_le_compat Zto.

Definition Zmax_ub_l : forall x y : Z, x <= Z.max x y := @join_ub_l Zto.
Definition Zmax_ub_r : forall x y : Z, y <= Z.max x y := @join_ub_r Zto.
Definition Zmax_glb : forall x y z : Z, x <= z -> y <= z -> (Z.max x y) <= z :=
 @join_lub Zto.
Definition Zmax_comm : forall x y : Z, Z.max x y = Z.max y x := @join_comm Zto.
Definition Zmax_assoc : forall x y z : Z, Z.max x (Z.max y z) = Z.max (Z.max x y) z:=
 @join_assoc Zto.
Definition Zmax_idem : forall x : Z, Z.max x x = x := @join_idem Zto.
Definition Zle_max_l : forall x y : Z, y <= x <-> Z.max x y = x := @le_join_l Zto.
Definition Zle_max_r : forall x y : Z, x <= y <-> Z.max x y = y := @le_join_r Zto.
Definition Zmax_irred : forall x y: Z, {Z.max x y = x} + {Z.max x y = y} := @join_irred Zto.
Definition Zmax_monotone_r : forall a : Z, Zmonotone (Z.max a) :=
 @join_monotone_r Zto.
Definition Zmax_monotone_l : forall a : Z, Zmonotone (fun x => Z.max x a) :=
 @join_monotone_l Zto.
Definition Zmax_le_compat : forall w x y z : Z, w <= y -> x <= z -> Z.max w x <= Z.max y z :=
 @join_le_compat Zto.

Definition Zmin_max_absorb_l_l : forall x y : Z, Z.min x (Z.max x y) = x :=
 @meet_join_absorb_l_l Zto.
Definition Zmax_min_absorb_l_l : forall x y : Z, Z.max x (Z.min x y) = x :=
 @join_meet_absorb_l_l Zto.
Definition Zmin_max_absorb_l_r : forall x y : Z, Z.min x (Z.max y x) = x :=
 @meet_join_absorb_l_r Zto.
Definition Zmax_min_absorb_l_r : forall x y : Z, Z.max x (Z.min y x) = x :=
 @join_meet_absorb_l_r Zto.
Definition Zmin_max_absorb_r_l : forall x y : Z, Z.min (Z.max x y) x = x :=
 @meet_join_absorb_r_l Zto.
Definition Zmax_min_absorb_r_l : forall x y : Z, Z.max (Z.min x y) x = x :=
 @join_meet_absorb_r_l Zto.
Definition Zmin_max_absorb_r_r : forall x y : Z, Z.min (Z.max y x) x = x :=
 @meet_join_absorb_r_r Zto.
Definition Zmax_min_absorb_r_r : forall x y : Z, Z.max (Z.min y x) x = x :=
 @join_meet_absorb_r_r Zto.

Definition Zmax_min_distr_r : forall x y z : Z,
 Z.max x (Z.min y z) = Z.min (Z.max x y) (Z.max x z) :=
 @join_meet_distr_r Zto.
Definition Zmax_min_distr_l : forall x y z : Z,
 Z.max (Z.min y z) x = Z.min (Z.max y x) (Z.max z x) :=
 @join_meet_distr_l Zto.
Definition Zmin_max_distr_r : forall x y z : Z,
 Z.min x (Z.max y z) = Z.max (Z.min x y) (Z.min x z) :=
 @meet_join_distr_r Zto.
Definition Zmin_max_distr_l : forall x y z : Z,
 Z.min (Z.max y z) x = Z.max (Z.min y x) (Z.min z x) :=
 @meet_join_distr_l Zto.

(*I don't know who wants modularity laws, but here they are *)
Definition Zmax_min_modular_r : forall x y z : Z,
 Z.max x (Z.min y (Z.max x z)) = Z.min (Z.max x y) (Z.max x z) :=
 @join_meet_modular_r Zto.
Definition Zmax_min_modular_l : forall x y z : Z,
 Z.max (Z.min (Z.max x z) y) z = Z.min (Z.max x z) (Z.max y z) :=
 @join_meet_modular_l Zto.
Definition Zmin_max_modular_r : forall x y z : Z,
 Z.min x (Z.max y (Z.min x z)) = Z.max (Z.min x y) (Z.min x z) :=
 @meet_join_modular_r Zto.
Definition Zmin_max_modular_l : forall x y z : Z,
 Z.min (Z.max (Z.min x z) y) z = Z.max (Z.min x z) (Z.min y z) :=
 @meet_join_modular_l Zto.

Definition Zmin_max_disassoc : forall x y z : Z, Z.min (Z.max x y) z <= Z.max x (Z.min y z) :=
 @meet_join_disassoc Zto.

Lemma Zsucc_monotone : Zmonotone Z.succ.
Proof.
 unfold Zmonotone, Default.monotone.
 auto with *.
Qed.
Definition Zsucc_min_distr : forall x y : Z,
 Z.succ (Z.min x y) = Z.min (Z.succ x ) (Z.succ y) :=
 @monotone_meet_distr Zto _ Zsucc_monotone.
Definition Zsucc_max_distr : forall x y : Z,
 Z.succ (Z.max x y) = Z.max (Z.succ x ) (Z.succ y) :=
 @monotone_join_distr Zto _ Zsucc_monotone.

Lemma Zpred_monotone : Zmonotone Z.pred.
Proof.
 unfold Zmonotone, Default.monotone.
 intros x y H.
 rewrite (Zsucc_pred x) in H.
 rewrite (Zsucc_pred y) in H.
  auto with zarith. 
Qed.
Definition Zpred_min_distr : forall x y : Z,
 Z.pred (Z.min x y) = Z.min (Z.pred x ) (Z.pred y) :=
 @monotone_meet_distr Zto _ Zpred_monotone.
Definition Zpred_max_distr : forall x y : Z,
 Z.pred (Z.max x y) = Z.max (Z.pred x ) (Z.pred y) :=
 @monotone_join_distr Zto _ Zpred_monotone.

Lemma Zplus_monotone_r : forall a, Zmonotone (Zplus a).
Proof.
 do 2 red. auto with zarith.
Qed.
Lemma Zplus_monotone_l : forall a, Zmonotone (fun x => Zplus x a).
Proof.
 unfold Zmonotone, Default.monotone.
 auto with *.
Qed.
Definition Zmin_plus_distr_r : forall x y z : Z, x + Z.min y z = Z.min (x+y) (x+z)  :=
 fun a => @monotone_meet_distr Zto _ (Zplus_monotone_r a).
Definition Zmin_plus_distr_l : forall x y z : Z, Z.min y z + x = Z.min (y+x) (z+x) :=
 fun a => @monotone_meet_distr Zto _ (Zplus_monotone_l a).
Definition Zmax_plus_distr_r : forall x y z : Z, x + Z.max y z = Z.max (x+y) (x+z)  :=
 fun a => @monotone_join_distr Zto _ (Zplus_monotone_r a).
Definition Zmax_plus_distr_l : forall x y z : Z, Z.max y z + x = Z.max (y+x) (z+x) :=
 fun a => @monotone_join_distr Zto _ (Zplus_monotone_l a).
Definition Zmin_minus_distr_l : forall x y z : Z, Z.min y z - x = Z.min (y-x) (z-x) :=
 (fun x => Zmin_plus_distr_l (-x)).
Definition Zmax_minus_distr_l : forall x y z : Z, Z.max y z - x = Z.max (y-x) (z-x) :=
 (fun x => Zmax_plus_distr_l (-x)).

Lemma Zopp_le_compat : forall x y : Z, x <= y -> -y <= -x.
Proof.
 auto with *.
Qed.
Definition Zmin_max_de_morgan : forall x y : Z, -(Z.min x y) = Z.max (-x) (-y) :=
 @antitone_meet_join_distr Zto _ Zopp_le_compat.
Definition Zmax_min_de_morgan : forall x y : Z, -(Z.max x y) = Z.min (-x) (-y) :=
 @antitone_join_meet_distr Zto _ Zopp_le_compat.

Lemma Zminus_antitone : forall a : Z, Zantitone (fun x => a - x).
Proof.
 change (forall a x y : Z, x <= y -> a + - y <= a + - x).
 intros.
 apply Zplus_le_compat; firstorder using Z.le_refl, Zopp_le_compat.
Qed.

Definition Zminus_min_max_antidistr_r : forall x y z : Z, x - Z.min y z = Z.max (x-y) (x-z) :=
 fun a => @antitone_meet_join_distr Zto _ (Zminus_antitone a).
Definition Zminus_max_min_antidistr_r : forall x y z : Z, x - Z.max y z = Z.min (x-y) (x-z) :=
 fun a => @antitone_join_meet_distr Zto _ (Zminus_antitone a).

End ZTotalOrder.

Transparent Z_lt_le_dec.
