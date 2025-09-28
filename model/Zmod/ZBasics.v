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
(* ZBasics.v, by Vince Barany *)

From Coq Require Export ZArith.
Require Export CoRN.logic.CLogic.
From Coq Require Import Lia.

(**
* Basic facts on Z
** Arithmetic over nat
*)

Section narith.

Lemma le_trans : forall l k n : nat, k <= l -> l <= n -> k <= n.
Proof.
 intros l k n Hkl Hln.
 induction  n as [| n Hrecn].
  inversion Hln.
  rewrite <- H.
  exact Hkl.
 inversion Hln.
  rewrite <- H.
  exact Hkl.
 apply le_S.
 apply Hrecn.
 assumption.
Qed.

Lemma minus_n_Sk : forall n k : nat, k < n -> n - k = S (n - S k).
Proof.
 intros n k Hlt.
 induction  n as [| n Hrecn].
  inversion Hlt.
 rewrite <- Nat.sub_succ_l.
  simpl in |- *.
  reflexivity.
 unfold lt in Hlt.
 inversion Hlt.
  auto.
 apply (le_trans (S k)).
  auto.
 assumption.
Qed.

Lemma le_minus : forall n k : nat, n - k <= n.
Proof.
 intros n.
 induction  n as [| n Hrecn].
  simpl in |- *.
  auto.
 intro k.
 case k.
  simpl in |- *.
  auto.
 intro k'.
 simpl in |- *.
 apply (le_trans n).
  apply Hrecn.
 auto.
Qed.

Lemma minus_n_minus_n_k : forall k n : nat, k <= n -> k = n - (n - k).
Proof.
 intros k n Hle.
 induction  k as [| k Hreck].
  rewrite Nat.sub_0_r.
  symmetry in |- *.
  apply Nat.sub_diag.
 set (K := k) in |- * at 2.
 rewrite Hreck.
  unfold K in |- *; clear K.
  rewrite (minus_n_Sk n k).
   rewrite (minus_n_Sk n (n - S k)).
    reflexivity.
   unfold lt in |- *.
   rewrite <- (minus_n_Sk n k).
    apply le_minus.
   unfold lt in |- *.
   exact Hle.
  unfold lt in |- *.
  exact Hle.
 apply (le_trans (S k)).
  auto.
 exact Hle.
Qed.


End narith.

#[global]
Hint Resolve Nat.le_trans: zarith.
#[global]
Hint Resolve minus_n_Sk: zarith.
#[global]
Hint Resolve le_minus: zarith.
#[global]
Hint Resolve minus_n_minus_n_k: zarith.

(**
** Arithmetic over Z
*)

Section zarith.

Definition Zdec : forall a : Z, {a = 0%Z} + {a <> 0%Z}.
Proof.
 intro a.
 case a.
   left; reflexivity.
  intro; right; discriminate.
 intro; right; discriminate.
Defined.


(* True in any ring *)
Lemma unique_unit : forall u : Z, (forall a : Z, (a * u)%Z = a) -> u = 1%Z.
Proof.
 intros.
 rewrite <- (Zmult_1_l u).
 rewrite (H 1%Z).
 reflexivity.
Qed.

Lemma Zmult_zero_div : forall a b : Z, (a * b)%Z = 0%Z -> a = 0%Z \/ b = 0%Z.
Proof.
 intros a b.
 case a; case b; intros; auto; try discriminate.
Qed.

Lemma Zmult_no_zero_div :
 forall a b : Z, a <> 0%Z -> b <> 0%Z -> (a * b)%Z <> 0%Z.
Proof.
 intros a b Ha Hb.
 intro Hfalse.
 generalize (Zmult_zero_div a b Hfalse).
 tauto.
Qed.

Lemma Zmult_unit_oneforall :
 forall u a : Z, a <> 0%Z -> (a * u)%Z = a -> forall b : Z, (b * u)%Z = b.
Proof.
 intros u a H0 Hu b.
 apply (Zmult_absorb a).
  assumption.
 rewrite Zmult_assoc.
 rewrite (Zmult_comm a b).
 rewrite <- Zmult_assoc.
 rewrite Hu.
 reflexivity.
Qed.

Lemma Zunit_eq_one : forall u a : Z, a <> 0%Z -> (a * u)%Z = a -> u = 1%Z.
Proof.
 intros u a H1 H2.
 apply unique_unit.
 intro.
 apply (Zmult_unit_oneforall u a H1 H2).
Qed.


Lemma Zmult_intro_lft :
 forall a b c : Z, a <> 0%Z -> (a * b)%Z = (a * c)%Z -> b = c.
Proof.
 intros a b c Ha Habc.
 cut ((b - c)%Z = 0%Z); auto with zarith.
 elim (Zmult_zero_div a (b - c)).
   intro; elim Ha; assumption.
  tauto.
 rewrite Zmult_comm; rewrite BinInt.Zmult_minus_distr_r;
   rewrite (Zmult_comm b a); rewrite (Zmult_comm c a).
 auto with zarith.
Qed.

Lemma Zmult_intro_rht :
 forall a b c : Z, a <> 0%Z -> (b * a)%Z = (c * a)%Z -> b = c.
Proof.
 intros a b c.
 rewrite (Zmult_comm b a); rewrite (Zmult_comm c a); apply Zmult_intro_lft.
Qed.

Lemma succ_nat: forall (m:nat),Zpos (P_of_succ_nat m) = (Z_of_nat m + 1)%Z.
Proof.
 intro m.
 induction m.
  reflexivity.
 simpl.
 case (P_of_succ_nat m).
   simpl.
   reflexivity.
  simpl.
  reflexivity.
 simpl.
 reflexivity.
Qed.

End zarith.


#[global]
Hint Resolve Zdec: zarith.
#[global]
Hint Resolve unique_unit: zarith.
#[global]
Hint Resolve Zmult_zero_div: zarith.
#[global]
Hint Resolve Zmult_no_zero_div: zarith.
#[global]
Hint Resolve Zmult_unit_oneforall: zarith.
#[global]
Hint Resolve Zunit_eq_one: zarith.
#[global]
Hint Resolve Zmult_intro_lft: zarith.
#[global]
Hint Resolve Zmult_intro_rht: zarith.

(**
** Facts on inequalities over Z
*)

Section zineq.

Lemma Zgt_Zge: forall (n m:Z), (n>m)%Z -> (n>=m)%Z.
Proof.
 intros n m.
 intuition; auto with *.
Qed.

Lemma Zle_antisymm : forall a b : Z, (a >= b)%Z -> (b >= a)%Z -> a = b.
Proof.
 auto with zarith.
Qed.

Definition Zlt_irref : forall a : Z, ~ (a < a)%Z := Z.lt_irrefl.

Lemma Zgt_irref : forall a : Z, ~ (a > a)%Z.
Proof.
 intro a.
 intro Hlt.
 generalize (Z.gt_lt a a Hlt).
 apply Zlt_irref.
Qed.

Lemma Zlt_NEG_0 : forall p : positive, (Zneg p < 0)%Z.
Proof.
 intro p; unfold Z.lt in |- *; simpl in |- *; reflexivity.
Qed.

Lemma Zgt_0_NEG : forall p : positive, (0 > Zneg p)%Z.
Proof.
 intro p; unfold Z.gt in |- *; simpl in |- *; reflexivity.
Qed.

Lemma Zle_NEG_0 : forall p : positive, (Zneg p <= 0)%Z.
Proof.
 intro p; intro H0; inversion H0.
Qed.

Lemma Zge_0_NEG : forall p : positive, (0 >= Zneg p)%Z.
Proof.
 intro p; intro H0; inversion H0.
Qed.

Lemma Zle_NEG_1 : forall p : positive, (Zneg p <= -1)%Z.
Proof.
 intro p.
 case p; intros; intro H0; inversion H0.
Qed.

Lemma Zge_1_NEG : forall p : positive, (-1 >= Zneg p)%Z.
Proof.
 intro p.
 case p; intros; intro H0; inversion H0.
Qed.

Lemma Zlt_0_POS : forall p : positive, (0 < Zpos p)%Z.
Proof.
 intro p; unfold Z.lt in |- *; simpl in |- *; reflexivity.
Qed.

Lemma Zgt_POS_0 : forall p : positive, (Zpos p > 0)%Z.
Proof.
 intro p; unfold Z.gt in |- *; simpl in |- *; reflexivity.
Qed.

Lemma Zle_0_POS : forall p : positive, (0 <= Zpos p)%Z.
Proof.
 intro p; intro H0; inversion H0.
Qed.

Lemma Zge_POS_0 : forall p : positive, (Zpos p >= 0)%Z.
Proof.
 intro p; intro H0; inversion H0.
Qed.

Lemma Zle_1_POS : forall p : positive, (1 <= Zpos p)%Z.
Proof.
 intro p.
 case p; intros; intro H0; inversion H0.
Qed.

Lemma Zge_POS_1 : forall p : positive, (Zpos p >= 1)%Z.
Proof.
 intro p.
 case p; intros; intro H0; inversion H0.
Qed.

Lemma Zle_neg_pos : forall p q : positive, (Zneg p <= Zpos q)%Z.
Proof.
 intros; unfold Z.le in |- *; simpl in |- *; discriminate.
Qed.

Lemma ZPOS_neq_ZERO : forall p : positive, Zpos p <> 0%Z.
Proof.
 intros; intro; discriminate.
Qed.

Lemma ZNEG_neq_ZERO : forall p : positive, Zneg p <> 0%Z.
Proof.
 intros; intro; discriminate.
Qed.

Lemma Zge_gt_succ : forall a b : Z, (a >= b + 1)%Z -> (a > b)%Z.
Proof.
 auto with zarith.
Qed.

Lemma Zge_gt_pred : forall a b : Z, (a - 1 >= b)%Z -> (a > b)%Z.
Proof.
 auto with zarith.
Qed.

Lemma Zgt_ge_succ : forall a b : Z, (a + 1 > b)%Z -> (a >= b)%Z.
Proof.
 auto with zarith.
Qed.

Lemma Zgt_ge_pred : forall a b : Z, (a > b - 1)%Z -> (a >= b)%Z.
Proof.
 auto with zarith.
Qed.

Lemma Zlt_asymmetric : forall a b : Z, {(a < b)%Z} + {a = b} + {(a > b)%Z}.
Proof.
 intros a b.
 set (d := (a - b)%Z).
 replace a with (b + d)%Z; [ idtac | unfold d in |- *; lia ].
 case d; simpl in |- *.
   left; right; auto with zarith.
  intro p.
  right.
  rewrite <- (Zplus_0_r b).
  replace (b + 0 + Zpos p)%Z with (b + Zpos p)%Z; auto with zarith.
 intro p.
 left; left.
 rewrite <- (Zplus_0_r b).
 replace (b + 0 + Zneg p)%Z with (b + Zneg p)%Z by auto with zarith.
 cut (Zneg p < 0)%Z. auto with zarith.
 apply Zlt_NEG_0.
Qed.

Lemma Zle_neq_lt : forall a b : Z, (a <= b)%Z -> a <> b -> (a < b)%Z.
Proof.
 auto with zarith.
Qed.

Lemma Zmult_pos_mon_le_lft :
 forall a b c : Z, (a >= b)%Z -> (c >= 0)%Z -> (c * a >= c * b)%Z.
Proof.
 auto with zarith.
Qed.

Lemma Zmult_pos_mon_le_rht :
 forall a b c : Z, (a >= b)%Z -> (c >= 0)%Z -> (a * c >= b * c)%Z.
Proof.
 auto with zarith.
Qed.

Lemma Zmult_pos_mon_lt_lft :
 forall a b c : Z, (a > b)%Z -> (c > 0)%Z -> (c * a > c * b)%Z.
Proof.
 intros a b c.
 induction  c as [| p| p]. auto with zarith.
  intros Hab H0.
  induction  p as [p Hrecp| p Hrecp| ]. 3: auto with zarith.
   replace (Zpos (xI p)) with (2 * Zpos p + 1)%Z by auto with zarith.
   repeat rewrite Zmult_plus_distr_l.
   cut (2 * Zpos p * a > 2 * Zpos p * b)%Z. auto with zarith.
   repeat rewrite <- Zmult_assoc.
   cut (Zpos p * a > Zpos p * b)%Z; auto with zarith.
  replace (Zpos (xO p)) with (2 * Zpos p)%Z by auto with zarith.
  repeat rewrite <- Zmult_assoc.
  cut (Zpos p * a > Zpos p * b)%Z; auto with zarith.
 intros Hab H0.
 inversion H0.
Qed.

Lemma Zmult_pos_mon_lt_rht :
 forall a b c : Z, (a > b)%Z -> (c > 0)%Z -> (a * c > b * c)%Z.
 intros a b c; rewrite (Zmult_comm a c); rewrite (Zmult_comm b c); apply Zmult_pos_mon_lt_lft.
Qed.

Lemma Zmult_pos_mon : forall a b : Z, (a * b > 0)%Z -> (a * b >= a)%Z.
Proof.
 intros a b.
 case a.
   auto with zarith.
  case b.
    auto with zarith.
   intros.
   set (pp := Zpos p0) in |- * at 2.
   rewrite <- (Zmult_1_l pp).
   unfold pp in |- *; clear pp.
   rewrite Zmult_comm.
   apply Zmult_pos_mon_le_rht.
    apply Zge_POS_1.
   apply Zge_POS_0.
  intros p q; simpl in |- *; intro H0; inversion H0.
 intros p H0.
 apply (Zge_trans (Zneg p * b) 0 (Zneg p)).
  auto with zarith.
 apply Zge_0_NEG.
Qed.

Lemma Zdiv_pos_pos : forall a b : Z, (a * b > 0)%Z -> (a > 0)%Z -> (b > 0)%Z.
Proof.
 intros a b; induction  a as [| p| p]; [ induction  b as [| p| p] | induction  b as [| p0| p0]
   | induction  b as [| p0| p0] ]; unfold Z.lt, Z.gt in |- *;
     simpl in |- *; intros; try discriminate; auto.
Qed.

Lemma Zdiv_pos_nonneg :
 forall a b : Z, (a * b > 0)%Z -> (a >= 0)%Z -> (b > 0)%Z.
Proof.
 intros a b; induction  a as [| p| p]; [ induction  b as [| p| p] | induction  b as [| p0| p0]
   | induction  b as [| p0| p0] ]; unfold Z.lt, Z.gt, Z.le, Z.ge in |- *;
     simpl in |- *; intros H0 H1; (try discriminate; auto); ( try elim H1; auto).
Qed.

Lemma Zdiv_pos_neg : forall a b : Z, (a * b > 0)%Z -> (a < 0)%Z -> (b < 0)%Z.
Proof.
 intros a b; induction  a as [| p| p]; [ induction  b as [| p| p] | induction  b as [| p0| p0]
   | induction  b as [| p0| p0] ]; unfold Z.lt, Z.gt in |- *;
     simpl in |- *; intros; try discriminate; auto.
Qed.

Lemma Zdiv_pos_nonpos :
 forall a b : Z, (a * b > 0)%Z -> (a <= 0)%Z -> (b < 0)%Z.
Proof.
 intros a b; induction  a as [| p| p]; [ induction  b as [| p| p] | induction  b as [| p0| p0]
   | induction  b as [| p0| p0] ]; unfold Z.lt, Z.gt, Z.le, Z.ge in |- *;
     simpl in |- *; intros H0 H1; (try discriminate; auto); ( try elim H1; auto).
Qed.

Lemma Zdiv_neg_pos : forall a b : Z, (a * b < 0)%Z -> (a > 0)%Z -> (b < 0)%Z.
Proof.
 intros a b; induction  a as [| p| p]; [ induction  b as [| p| p] | induction  b as [| p0| p0]
   | induction  b as [| p0| p0] ]; unfold Z.lt, Z.gt in |- *;
     simpl in |- *; intros; try discriminate; auto.
Qed.

Lemma Zdiv_neg_nonneg :
 forall a b : Z, (a * b < 0)%Z -> (a >= 0)%Z -> (b < 0)%Z.
Proof.
 intros a b; induction  a as [| p| p]; [ induction  b as [| p| p] | induction  b as [| p0| p0]
   | induction  b as [| p0| p0] ]; unfold Z.lt, Z.gt, Z.le, Z.ge in |- *;
     simpl in |- *; intros H0 H1; (try discriminate; auto); ( try elim H1; auto).
Qed.

Lemma Zdiv_neg_neg : forall a b : Z, (a * b < 0)%Z -> (a < 0)%Z -> (b > 0)%Z.
Proof.
 intros a b; induction  a as [| p| p]; [ induction  b as [| p| p] | induction  b as [| p0| p0]
   | induction  b as [| p0| p0] ]; unfold Z.lt, Z.gt in |- *;
     simpl in |- *; intros; try discriminate; auto.
Qed.

Lemma Zdiv_neg_nonpos :
 forall a b : Z, (a * b < 0)%Z -> (a <= 0)%Z -> (b > 0)%Z.
Proof.
 intros a b; induction  a as [| p| p]; [ induction  b as [| p| p] | induction  b as [| p0| p0]
   | induction  b as [| p0| p0] ]; unfold Z.lt, Z.gt, Z.le, Z.ge in |- *;
     simpl in |- *; intros H0 H1; (try discriminate; auto); ( try elim H1; auto).
Qed.

Lemma Zcompat_lt_plus: forall (n m p:Z),(n < m)%Z-> (p+n < p+m)%Z.
Proof.
 intros n m p.
 intuition; auto with *.
Qed.

Transparent Zplus.

Lemma lt_succ_Z_of_nat: forall (m:nat)( k n:Z),
  (Z_of_nat (S m)<(k+n))%Z -> (Z_of_nat m <(k+n))%Z.
Proof.
 intros m k n.
 simpl.
 set (H:=(succ_nat m)).
 rewrite H.
 intuition; auto with *.
Qed.

Opaque Zplus.

End zineq.


#[global]
Hint Resolve Z.lt_gt: zarith.
#[global]
Hint Resolve Z.gt_lt: zarith.
#[global]
Hint Resolve Z.le_ge: zarith.
#[global]
Hint Resolve Z.ge_le: zarith.
#[global]
Hint Resolve Z.lt_irrefl: zarith.

#[global]
Hint Resolve Zle_antisymm: zarith.
#[global]
Hint Resolve Zlt_irref: zarith.
#[global]
Hint Resolve Zgt_irref: zarith.
#[global]
Hint Resolve Zlt_NEG_0: zarith.
#[global]
Hint Resolve Zgt_0_NEG: zarith.
#[global]
Hint Resolve Zle_NEG_0: zarith.
#[global]
Hint Resolve Zge_0_NEG: zarith.
#[global]
Hint Resolve Zle_NEG_1: zarith.
#[global]
Hint Resolve Zge_1_NEG: zarith.
#[global]
Hint Resolve Zlt_0_POS: zarith.
#[global]
Hint Resolve Zgt_POS_0: zarith.
#[global]
Hint Resolve Zle_0_POS: zarith.
#[global]
Hint Resolve Zge_POS_0: zarith.
#[global]
Hint Resolve Zle_1_POS: zarith.
#[global]
Hint Resolve Zge_POS_1: zarith.
#[global]
Hint Resolve ZBasics.Zle_neg_pos: zarith.
#[global]
Hint Resolve ZPOS_neq_ZERO: zarith.
#[global]
Hint Resolve ZNEG_neq_ZERO: zarith.
#[global]
Hint Resolve Zgt_ge_succ: zarith.
#[global]
Hint Resolve Zgt_ge_pred: zarith.
#[global]
Hint Resolve Zge_gt_succ: zarith.
#[global]
Hint Resolve Zge_gt_pred: zarith.
#[global]
Hint Resolve Zlt_asymmetric: zarith.
#[global]
Hint Resolve Zle_neq_lt: zarith.
#[global]
Hint Resolve Zmult_pos_mon_le_lft: zarith.
#[global]
Hint Resolve Zmult_pos_mon_le_rht: zarith.
#[global]
Hint Resolve Zmult_pos_mon_lt_lft: zarith.
#[global]
Hint Resolve Zmult_pos_mon_lt_rht: zarith.
#[global]
Hint Resolve Zmult_pos_mon: zarith.
#[global]
Hint Resolve Zdiv_pos_pos: zarith.
#[global]
Hint Resolve Zdiv_pos_neg: zarith.
#[global]
Hint Resolve Zdiv_pos_nonpos: zarith.
#[global]
Hint Resolve Zdiv_pos_nonneg: zarith.
#[global]
Hint Resolve Zdiv_neg_pos: zarith.
#[global]
Hint Resolve Zdiv_neg_neg: zarith.
#[global]
Hint Resolve Zdiv_neg_nonpos: zarith.
#[global]
Hint Resolve Zdiv_neg_nonneg: zarith.


(**
** Facts on the absolute value-function over Z
*)

Section zabs.


Lemma Zabs_idemp : forall a : Z, Z.abs (Z.abs a) = Z.abs a.
Proof.
 intro a; case a; auto.
Qed.

Lemma Zabs_nonneg : forall (a : Z) (p : positive), Z.abs a <> Zneg p.
Proof.
 intros; case a; intros; discriminate.
Qed.

Lemma Zabs_geq_zero : forall a : Z, (0 <= Z.abs a)%Z.
Proof.
 intro a.
 case a; unfold Z.abs in |- *; auto with zarith.
Qed.


Lemma Zabs_elim_nonneg : forall a : Z, (0 <= a)%Z -> Z.abs a = a.
Proof.
 intro a.
 case a; auto.
 intros p Hp; elim Hp.
 apply Zgt_0_NEG.
Qed.

Lemma Zabs_zero : forall a : Z, Z.abs a = 0%Z -> a = 0%Z.
Proof.
 intro a.
 case a.
   tauto.
  intros; discriminate.
 intros; discriminate.
Qed.

Lemma Zabs_Zopp : forall a : Z, Z.abs (- a) = Z.abs a.
Proof.
 intro a.
 case a; auto with zarith.
Qed.

Lemma Zabs_geq : forall a : Z, (a <= Z.abs a)%Z.
Proof.
 intro a.
 unfold Z.abs in |- *.
 case a; auto with zarith.
 Qed.
 Lemma Zabs_Zopp_geq : forall a : Z, (- a <= Z.abs a)%Z.
 intro a.
 rewrite <- Zabs_Zopp.
 apply Zabs_geq.
 Qed.
 Lemma Zabs_Zminus_symm : forall a b : Z, Z.abs (a - b) = Z.abs (b - a).
 intros a b.
 replace (a - b)%Z with (- (b - a))%Z by auto with zarith.
 apply Zabs_Zopp.
Qed.

Lemma Zabs_lt_pos : forall a b : Z, (Z.abs a < b)%Z -> (0 < b)%Z.
Proof.
 intros a b Hab.
 unfold Z.lt in |- *.
 elim (Zcompare_Gt_Lt_antisym b 0).
 intros H1 H2.
 apply H1.
 fold (b > 0)%Z in |- *.
 apply (Zgt_le_trans b (Z.abs a) 0); auto with zarith.
Qed.

Lemma Zabs_le_pos : forall a b : Z, (Z.abs a <= b)%Z -> (0 <= b)%Z.
Proof.
 intros a b Hab.
 apply (Z.le_trans 0 (Z.abs a) b).
  auto with zarith.
 assumption.
Qed.

Lemma Zabs_lt_elim :
 forall a b : Z, (a < b)%Z -> (- a < b)%Z -> (Z.abs a < b)%Z.
Proof.
 intros a b.
 case a; auto with zarith.
Qed.

Lemma Zabs_le_elim :
 forall a b : Z, (a <= b)%Z -> (- a <= b)%Z -> (Z.abs a <= b)%Z.
Proof.
 intros a b.
 case a; auto with zarith.
Qed.

Lemma Zabs_mult_compat : forall a b : Z, (Z.abs a * Z.abs b)%Z = Z.abs (a * b).
Proof.
 intros a b.
 case a; case b; intros; auto with zarith.
Qed.


(* triangle inequality (with Zplus) *)

Let case_POS :
  forall p q r : positive,
  (Zpos q + Zneg p)%Z = Zpos r ->
  (Z.abs (Zpos q + Zneg p) <= Z.abs (Zpos q) + Z.abs (Zneg p))%Z.
Proof.
 intros p q r Hr.
 rewrite Hr.
 simpl in |- *.
 rewrite <- Hr.
 fold (Zpos q + Zpos p)%Z in |- *.
 unfold Z.le in |- *.
 rewrite (Zcompare_plus_compat (Zneg p) (Zpos p) (Zpos q)).
 apply (ZBasics.Zle_neg_pos p).
 Defined.
 Let case_NEG : forall p q r : positive, (Zpos q + Zneg p)%Z = Zneg r ->
   (Z.abs (Zpos q + Zneg p) <= Z.abs (Zpos q) + Z.abs (Zneg p))%Z.
 intros p q r Hr.
 rewrite <- (Z.opp_involutive (Zpos q + Zneg p)) in Hr.
 rewrite <- (Z.opp_involutive (Zneg r)) in Hr.
 generalize (Z.opp_inj (- (Zpos q + Zneg p)) (- Zneg r) Hr).
 intro Hr'. rewrite Zopp_plus_distr in Hr'. unfold Z.opp in Hr'.
 rewrite <- (Zabs_Zopp (Zpos q + Zneg p)). rewrite Zopp_plus_distr. unfold Z.opp in |- *.
 rewrite <- (Zabs_Zopp (Zpos q)). unfold Z.opp in |- *.
 rewrite <- (Zabs_Zopp (Zneg p)). unfold Z.opp in |- *.
 rewrite (Zplus_comm (Zneg q) (Zpos p)).
 rewrite (Zplus_comm (Z.abs (Zneg q)) (Z.abs (Zpos p))).
 rewrite Zplus_comm in Hr'.
 apply (case_POS _ _ _ Hr').
 Defined.
 Lemma Zabs_triangle : forall a b : Z, (Z.abs (a + b) <= Z.abs a + Z.abs b)%Z.
 intros a b.
 case a; case b. 1-5, 7, 9: auto with zarith.
  intros p q.
  generalize (case_POS p q) (case_NEG p q).
  case (Zpos q + Zneg p)%Z.
    auto with zarith.
   intros p0 case_POS0 case_NEG0. apply (case_POS0 p0). reflexivity.
   intros p0 case_POS0 case_NEG0. apply (case_NEG0 p0). reflexivity.
   intros p q.
   rewrite (Zplus_comm (Zneg q) (Zpos p)).
   rewrite (Zplus_comm (Z.abs (Zneg q)) (Z.abs (Zpos p))).
   generalize (case_POS q p) (case_NEG q p).
   case (Zpos p + Zneg q)%Z.
     auto with zarith.
     intros p0 case_POS0 case_NEG0. apply (case_POS0 p0). reflexivity.
     intros p0 case_POS0 case_NEG0. apply (case_NEG0 p0). reflexivity.
     Qed.
     (* triangle inequality with Zminus *)
     Lemma Zabs_Zminus_triangle : forall a b : Z, (Z.abs (Z.abs a - Z.abs b) <= Z.abs (a - b))%Z.
 assert (case : forall a b : Z, (Z.abs a - Z.abs b <= Z.abs (a - b))%Z).
  intros a b.
  unfold Z.le in |- *.
  unfold Zminus in |- *.
  rewrite <- (Zcompare_plus_compat (Z.abs a + - Z.abs b) (Z.abs (a + - b)) (Z.abs b)) .
  rewrite (Zplus_comm (Z.abs a) (- Z.abs b)).
  rewrite Zplus_assoc.
  rewrite (Zplus_comm (Z.abs b) (- Z.abs b)).
  rewrite Zplus_opp_l.
  rewrite Zplus_0_l.
  assert (l : forall a b : Z, a = (b + (a - b))%Z).
   auto with zarith.
  set (a' := a) in |- * at 2.
  rewrite (l a b).
  unfold a' in |- *.
  fold (a - b)%Z in |- *.
  apply (Zabs_triangle b (a - b)).
 intros a b.
 apply Zabs_le_elim.
  apply case.
 replace (- (Z.abs a - Z.abs b))%Z with (Z.abs b - Z.abs a)%Z by auto with zarith.
 rewrite Zabs_Zminus_symm.
 apply case.
Qed.


End zabs.


#[global]
Hint Resolve Zabs_idemp: zarith.
#[global]
Hint Resolve Zabs_nonneg: zarith.
#[global]
Hint Resolve Zabs_geq_zero: zarith.
#[global]
Hint Resolve Zabs_elim_nonneg: zarith.
#[global]
Hint Resolve Zabs_zero: zarith.
#[global]
Hint Resolve Zabs_Zopp: zarith.
#[global]
Hint Resolve Zabs_geq: zarith.
#[global]
Hint Resolve Zabs_Zopp_geq: zarith.
#[global]
Hint Resolve Zabs_Zminus_symm: zarith.
#[global]
Hint Resolve Zabs_lt_pos: zarith.
#[global]
Hint Resolve Zabs_le_pos: zarith.
#[global]
Hint Resolve Zabs_lt_elim: zarith.
#[global]
Hint Resolve Zabs_le_elim: zarith.
#[global]
Hint Resolve Zabs_mult_compat: zarith.
#[global]
Hint Resolve Zabs_triangle: zarith.
#[global]
Hint Resolve Zabs_Zminus_triangle: zarith.


(**
** Facts on the sign-function over Z
*)


Section zsign.

Lemma Zsgn_mult_compat : forall a b : Z, (Z.sgn a * Z.sgn b)%Z = Z.sgn (a * b).
Proof.
 intros a b.
 case a; case b; intros; auto with zarith.
Qed.

Lemma Zmult_sgn_abs : forall a : Z, (Z.sgn a * Z.abs a)%Z = a.
Proof.
 intro a.
 case a; intros; auto with zarith.
Qed.

Lemma Zmult_sgn_eq_abs : forall a : Z, Z.abs a = (Z.sgn a * a)%Z.
Proof.
 intro a.
 case a; intros; auto with zarith.
Qed.

Lemma Zsgn_plus_l : forall a b : Z, Z.sgn a = Z.sgn b -> Z.sgn (a + b) = Z.sgn a.
Proof.
 intros a b.
 case a; case b; simpl in |- *; auto; intros; try discriminate.
Qed.

Lemma Zsgn_plus_r : forall a b : Z, Z.sgn a = Z.sgn b -> Z.sgn (a + b) = Z.sgn b.
Proof.
 intros.
 rewrite Zplus_comm.
 apply Zsgn_plus_l.
 auto.
Qed.

Lemma Zsgn_opp : forall z : Z, Z.sgn (- z) = (- Z.sgn z)%Z.
Proof.
 intro z.
 case z; simpl in |- *; auto.
Qed.

Lemma Zsgn_ZERO : forall z : Z, Z.sgn z = 0%Z -> z = 0%Z.
Proof.
 intros z.
 case z; simpl in |- *; intros; auto; try discriminate.
Qed.

Lemma Zsgn_pos : forall z : Z, Z.sgn z = 1%Z -> (z > 0)%Z.
Proof.
 intros z.
 case z; simpl in |- *; intros; auto with zarith; try discriminate.
Qed.

Lemma Zsgn_neg : forall z : Z, Z.sgn z = (-1)%Z -> (z < 0)%Z.
Proof.
 intros z.
 case z; simpl in |- *; intros; auto with zarith; try discriminate.
Qed.

End zsign.


#[global]
Hint Resolve Zsgn_mult_compat: zarith.
#[global]
Hint Resolve Zmult_sgn_abs: zarith.
#[global]
Hint Resolve Zmult_sgn_eq_abs: zarith.
#[global]
Hint Resolve Zsgn_plus_l: zarith.
#[global]
Hint Resolve Zsgn_plus_r: zarith.
#[global]
Hint Resolve Zsgn_opp: zarith.
#[global]
Hint Resolve Zsgn_ZERO: zarith.
#[global]
Hint Resolve Zsgn_pos: zarith.
#[global]
Hint Resolve Zsgn_neg: zarith.

