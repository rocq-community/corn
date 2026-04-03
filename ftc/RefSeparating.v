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

(* begin hide *)

Require Export CoRN.ftc.COrdLemmas.
Require Export CoRN.ftc.Partitions.
From Coq Require Import Lia.

Section Separating_Partition.

Variables a b : IR.
Hypothesis Hab : a[<=]b.
Let I := compact a b Hab.

Variable F : PartIR.
Hypothesis contF : Continuous_I Hab F.
Hypothesis incF : included (compact a b Hab) (Dom F).

Hypothesis Hab' : a[<]b.
Variable n : nat.
Variable P : Partition Hab n.

Variable alpha : IR.
Hypothesis Halpha : [0][<]alpha.

Variable csi : IR.
Hypothesis Hcsi : [0][<]csi.

Let M := Norm_Funct contF.

Lemma RS'_pos_n : 0 < n.
Proof.
 apply partition_less_imp_gt_zero with a b Hab; assumption.
Qed.

Lemma SPap_n : n <> 0.
Proof.
 intro.
 apply (Nat.neq_0_lt_0 n).
  exact RS'_pos_n.
 auto.
Qed.

Let delta :=
  Min csi
    (alpha[/] _[//]
     mult_resp_ap_zero _ _ _ (nring_ap_zero _ _ SPap_n) (max_one_ap_zero M)).

Lemma RS'_delta_pos : [0][<]delta.
Proof.
 unfold delta in |- *; apply less_Min.
  assumption.
 apply div_resp_pos.
  apply mult_resp_pos.
   astepl (nring (R:=IR) 0); apply nring_less; apply RS'_pos_n.
  apply pos_max_one.
 assumption.
Qed.

Lemma RS'_delta_csi : delta[<=]csi.
Proof.
 unfold delta in |- *; apply Min_leEq_lft.
Qed.

Hypothesis Hab'' : delta [/]TwoNZ[<]b[-]a.

Lemma sep__part_lemma :
 forall (i : nat) (Hi : i <= n),
 {j : nat |
 {Hj : j <= n |
 delta [/]FourNZ[<]P j Hj[-]P i Hi
 and (forall (j' : nat) (Hj' : j' <= n),
      j' < j -> P j' Hj'[-]P i Hi[<]delta [/]TwoNZ)}}
 or P n (le_n n)[-]P i Hi[<]delta [/]TwoNZ.
Proof.
 intros.
 elim (str_finite_or_elim _ (fun (j : nat) (Hj : j <= n) => delta [/]FourNZ[<]P j Hj[-]P i Hi)
   (fun (j : nat) (Hj : j <= n) => P j Hj[-]P i Hi[<]delta [/]TwoNZ)); intros.
     left.
     elim a0; intros j a'.
     elim a'; intros Hj Hj'.
     elim Hj'; clear a0 a' Hj'; intros Hj' H0.
     exists j; exists Hj.
     split; assumption.
    right; auto.
   red in |- *; intros. rename X into H1.
   eapply less_wdr.
    apply H1.
   apply cg_minus_wd; apply prf1; auto.
  red in |- *; intros. rename X into H1.
  eapply less_wdl.
   apply H1.
  apply cg_minus_wd; apply prf1; auto.
 apply less_cotransitive_unfolded.
 apply shift_div_less.
  apply pos_four.
 rstepr (delta[+]delta).
 astepl ([0][+]delta).
 apply plus_resp_less_leEq.
  apply RS'_delta_pos.
 apply leEq_reflexive.
Qed.

Definition sep__part_h : nat -> nat.
Proof.
 intro i; induction  i as [| i Hreci].
  apply 0.
 elim (le_lt_dec Hreci n); intro.
  elim (sep__part_lemma Hreci a0); intro.
   apply (ProjT1 a1).
  apply n.
 apply n.
Defined.

Lemma sep__part_h_bnd : forall i : nat, sep__part_h i <= n.
Proof.
 intro.
 induction  i as [| i Hreci].
  apply Nat.le_0_l.
 simpl in |- *.
 elim (le_lt_dec (sep__part_h i) n); intro; simpl in |- *.
  elim (sep__part_lemma (sep__part_h i) a0); intro; simpl in |- *.
   set (j := ProjT1 a1) in *; fold j in |- *.
   elim (ProjT2 a1); intros Hj Hj'; fold j in Hj, Hj'.
   assumption.
  apply le_n.
 apply le_n.
Qed.

Lemma sep__part_h_mon_1 : forall i : nat, sep__part_h i <= sep__part_h (S i).
Proof.
 intros; simpl in |- *.
 elim (le_lt_dec (sep__part_h i) n); intro; simpl in |- *.
  elim (sep__part_lemma (sep__part_h i) a0); intro; simpl in |- *.
   set (j := ProjT1 a1) in *; fold j in |- *.
   elim (ProjT2 a1); intros Hj Hj'; fold j in Hj, Hj'.
   elim Hj'; clear Hj'; intros Hj0 Hj1.
   cut (sep__part_h i < j); intros.
    apply Nat.lt_le_incl; assumption.
   apply (Partition_Points_mon _ _ _ _ P) with a0 Hj.
   apply less_transitive_unfolded with (P (sep__part_h i) a0[+]delta [/]FourNZ).
    apply shift_less_plus'; astepl ZeroR.
    apply pos_div_four; exact RS'_delta_pos.
   apply shift_plus_less'; assumption.
  assumption.
 apply sep__part_h_bnd.
Qed.

Lemma sep__part_h_mon_2 :
 forall i : nat, sep__part_h i < n -> sep__part_h i < sep__part_h (S i).
Proof.
 intros; simpl in |- *.
 elim (le_lt_dec (sep__part_h i) n); intro; simpl in |- *.
  elim (sep__part_lemma (sep__part_h i) a0); intro; simpl in |- *.
   set (j := ProjT1 a1) in *; fold j in |- *.
   elim (ProjT2 a1); intros Hj Hj'; fold j in Hj, Hj'.
   elim Hj'; clear Hj'; intros Hj0 Hj1.
   apply (Partition_Points_mon _ _ _ _ P) with a0 Hj.
   apply less_transitive_unfolded with (P (sep__part_h i) a0[+]delta [/]FourNZ).
    apply shift_less_plus'; astepl ZeroR.
    apply pos_div_four; exact RS'_delta_pos.
   apply shift_plus_less'; assumption.
  assumption.
 assumption.
Qed.

Lemma sep__part_h_mon_3 :
 forall i j : nat,
 sep__part_h i < n -> i < j -> sep__part_h i < sep__part_h j.
Proof.
 intros; induction  j as [| j Hrecj].
  exfalso; inversion H0.
 cut (sep__part_h j <= sep__part_h (S j)); intros.
  2: apply sep__part_h_mon_1.
 elim (le_lt_eq_dec _ _ H0); intro.
  apply Nat.lt_le_trans with (sep__part_h j); auto.
  apply Hrecj; auto with arith.
 rewrite <- b0; apply sep__part_h_mon_2; auto.
Qed.

Lemma sep__part_app_n :
 {m : nat |
 sep__part_h (S m) = n /\ (forall i : nat, i <= m -> sep__part_h i < n)}.
Proof.
 elim (weird_mon_covers _ _ sep__part_h_mon_2); intros m Hm Hm'.
 set (m' := pred m) in *.
 exists m'.
 cut (m <> 0); intro.
  split.
   cut (S m' = m); [ intro | unfold m' in |- *; apply Nat.lt_succ_pred with 0; apply Nat.neq_0_lt_0;
     auto ].
   rewrite H0; clear H0 m'.
   cut (n <= sep__part_h m).
    cut (sep__part_h m <= n); intros.
     auto with arith.
    apply sep__part_h_bnd.
   assumption.
  intros; apply Hm'.
  unfold m' in H0; rewrite <- (Nat.lt_succ_pred 0 m); auto with arith.
  apply Nat.neq_0_lt_0; auto.
 apply SPap_n.
 rewrite H in Hm.
 simpl in Hm.
 apply Nat.le_antisymm; auto with arith.
Qed.

Lemma sep__part_h_lemma :
 forall i : nat,
 sep__part_h (S i) < n ->
 forall Hi Hi', P (sep__part_h i) Hi[<]P (sep__part_h (S i)) Hi'.
Proof.
 do 3 intro; simpl in |- *.
 elim (le_lt_dec (sep__part_h i) n); intro; simpl in |- *.
  elim (sep__part_lemma (sep__part_h i) a0); intro; simpl in |- *.
   set (m' := ProjT1 a1) in *.
   change (forall Hi' : m' <= n, P (sep__part_h i) Hi[<]P m' Hi') in |- *; intros.
   elim (ProjT2 a1); fold m' in |- *; intros Hm' Hm''.
   elim Hm''; clear Hm''; intros H0 H1.
   apply less_transitive_unfolded with (P (sep__part_h i) Hi[+]delta [/]FourNZ).
    apply shift_less_plus'; astepl ZeroR; apply pos_div_four; exact RS'_delta_pos.
   apply shift_plus_less'; eapply less_wdr.
    apply H0.
   apply cg_minus_wd; apply prf1; auto.
  generalize H.
  simpl in |- *.
  elim (le_lt_dec (sep__part_h i) n); intro; simpl in |- *.
   elim (sep__part_lemma (sep__part_h i) a1); intro; simpl in |- *.
    2: intro; exfalso; apply (Nat.lt_irrefl n); auto.
   2: intro; exfalso; apply (Nat.lt_irrefl n); auto.
  set (m' := ProjT1 a2) in *.
  change (m' < n -> forall Hi' : n <= n, P (sep__part_h i) Hi[<]P n Hi') in |- *; intros.
  elim (ProjT2 a2); fold m' in |- *; intros Hm' Hm''.
  elim Hm''; clear Hm''; intros H1 H2.
  apply less_leEq_trans with (P _ Hm').
   apply less_transitive_unfolded with (P (sep__part_h i) Hi[+]delta [/]FourNZ).
    apply shift_less_plus'; astepl ZeroR; apply pos_div_four; exact RS'_delta_pos.
   apply shift_plus_less'; eapply less_wdr.
    apply H1.
   apply cg_minus_wd; apply prf1; auto.
  apply local_mon'_imp_mon'2_le with (f := fun (i : nat) Hi => P i Hi).
   intros; apply prf2.
  assumption.
 exfalso; lia.
Qed.

Lemma sep__part_h_lemma2 :
 forall (i : nat) Hi Hi',
 P (pred (sep__part_h (S i))) Hi'[-]P (sep__part_h i) Hi[<=]delta [/]TwoNZ.
Proof.
 do 2 intro; simpl in |- *.
 elim (le_lt_dec (sep__part_h i) n); intro; simpl in |- *.
  elim (sep__part_lemma (sep__part_h i) a0); intro; simpl in |- *.
   set (j := ProjT1 a1) in *.
   elim (ProjT2 a1); fold j in |- *; intros Hj Hj'; elim Hj'; clear Hj'; intros H H0.
   change (forall Hi', P (pred j) Hi'[-]P _ Hi[<=]delta [/]TwoNZ) in |- *.
   intros; apply less_leEq.
   apply less_wdl with (P (pred j) Hi'[-]P _ a0); intros.
    2: apply cg_minus_wd; apply prf1; auto.
   apply H0.
   apply Nat.lt_pred_l. apply Nat.neq_0_lt_0.
   apply Nat.le_lt_trans with (sep__part_h i).
    apply Nat.le_0_l.
   apply Partition_Points_mon with (P := P) (Hi := a0) (Hj := Hj).
   apply less_transitive_unfolded with (P (sep__part_h i) a0[+]delta [/]FourNZ).
    apply shift_less_plus'; astepl ZeroR; apply pos_div_four; exact RS'_delta_pos.
   apply shift_plus_less'; assumption.
  intros; eapply leEq_transitive.
   2: apply less_leEq; apply b0.
  unfold cg_minus in |- *; apply plus_resp_leEq_both.
   apply Partition_mon; assumption.
  apply inv_resp_leEq; apply eq_imp_leEq; apply prf1; auto.
 exfalso; lia.
Qed.

Lemma sep__part_h_lemma3 :
 forall (i k : nat) Hk Hk',
 sep__part_h i <= k ->
 k < pred (sep__part_h (S i)) -> P (S k) Hk'[-]P k Hk[<=]delta [/]TwoNZ.
Proof.
 intros.
 cut (sep__part_h i <= n).
  cut (pred (sep__part_h (S i)) <= n); intros.
   eapply leEq_transitive.
    2: apply sep__part_h_lemma2 with (Hi := H2) (Hi' := H1).
   unfold cg_minus in |- *; apply plus_resp_leEq_both.
    apply Partition_mon; assumption.
   apply inv_resp_leEq; apply Partition_mon; assumption.
  apply Nat.le_trans with (sep__part_h (S i)).
   auto with arith.
  apply sep__part_h_bnd.
 apply sep__part_h_bnd.
Qed.

Lemma RS'_delta2_delta4 :
  forall m : nat,
  delta [/]FourNZ[<]P _ (sep__part_h_bnd (S m))[-]P _ (sep__part_h_bnd m)
  or P _ (sep__part_h_bnd (S m))[-]P _ (sep__part_h_bnd m)[<]delta [/]TwoNZ.
Proof.
 intro; apply less_cotransitive_unfolded.
 rstepl ((delta [/]TwoNZ) [/]TwoNZ).
 apply pos_div_two'; apply pos_div_two; exact RS'_delta_pos.
Qed.

Definition RS'_m1 := ProjT1 sep__part_app_n.

Definition RS'_m : nat.
Proof.
 elim (RS'_delta2_delta4 RS'_m1); intro.
  apply (S RS'_m1).
 apply RS'_m1.
Defined.

Notation m := RS'_m.

Definition sep__part_length := m.

Lemma RS'_m_m1 : {m = RS'_m1} + {m = S RS'_m1}.
Proof.
 unfold m in |- *.
 elim (RS'_delta2_delta4 RS'_m1); intro; simpl in |- *.
  right; auto.
 left; auto.
Qed.

Lemma RS'_pos_m : 0 < m.
Proof.
 unfold m in |- *.
 elim (RS'_delta2_delta4 RS'_m1); intro; simpl in |- *.
  auto with arith.
 elim (ProjT2 sep__part_app_n); fold RS'_m1 in |- *; intros.
 cut (0 <> RS'_m1); intro.
  auto with arith.
 exfalso.
 apply less_irreflexive_unfolded with (x := delta [/]TwoNZ).
 apply less_transitive_unfolded with (b[-]a).
  assumption.
 eapply less_wdl.
  apply b0.
 apply cg_minus_wd.
  eapply eq_transitive_unfolded.
   2: apply finish with (p := P) (H := le_n n).
  apply prf1.
  auto.
 eapply eq_transitive_unfolded.
  2: apply start with (p := P) (H := Nat.le_0_l n).
 apply prf1.
 rewrite <- H1.
 simpl in |- *; auto.
Qed.

Definition sep__part_fun : forall i : nat, i <= m -> nat.
Proof.
 intros i Hi.
 elim (le_lt_eq_dec _ _ Hi); intro.
  apply (sep__part_h i).
 apply n.
Defined.

Lemma sep__part_fun_bnd :
 forall (i : nat) (H : i <= m), sep__part_fun i H <= n.
Proof.
 intros.
 unfold sep__part_fun in |- *.
 elim (le_lt_eq_dec _ _ H); intro; simpl in |- *.
  apply sep__part_h_bnd.
 apply le_n.
Qed.

Lemma sep__part_fun_0 : forall H : 0 <= m, sep__part_fun 0 H = 0.
Proof.
 intros.
 unfold sep__part_fun in |- *.
 elim (le_lt_eq_dec _ _ H); intro; simpl in |- *.
  reflexivity.
 exfalso.
 generalize b0.
 apply Nat.neq_sym.
 apply Nat.neq_0_lt_0; apply RS'_pos_m.
Qed.

Lemma sep__part_fun_i :
 forall (i : nat) (H : i <= m), i < m -> sep__part_fun i H = sep__part_h i.
Proof.
 intros.
 unfold sep__part_fun in |- *.
 elim (le_lt_eq_dec _ _ H); intro; simpl in |- *.
  reflexivity.
 rewrite b0 in H0; elim (Nat.lt_irrefl _ H0).
Qed.

Lemma sep__part_fun_m : forall H : m <= m, sep__part_fun m H = n.
Proof.
 intros.
 unfold sep__part_fun in |- *.
 elim (le_lt_eq_dec _ _ H); intro; simpl in |- *.
  elim (Nat.lt_irrefl _ a0).
 reflexivity.
Qed.

Lemma sep__part_fun_i' :
 forall (i : nat) (H : i <= m), sep__part_h i <= sep__part_fun i H.
Proof.
 intros.
 unfold sep__part_fun in |- *.
 elim (le_lt_eq_dec _ _ H); intro; simpl in |- *.
  apply le_n.
 apply sep__part_h_bnd.
Qed.

Lemma sep__part_fun_bnd' :
 forall (i : nat) (H : i <= m), i < m -> sep__part_fun i H < n.
Proof.
 intros.
 unfold sep__part_fun in |- *.
 elim (le_lt_eq_dec _ _ H); intro; simpl in |- *.
  elim (ProjT2 sep__part_app_n).
  intros.
  apply H2.
  generalize a0; clear a0.
  unfold m in |- *; elim (RS'_delta2_delta4 RS'_m1); intro; simpl in |- *.
   auto with arith.
  auto with arith.
 rewrite b0 in H0; elim (Nat.lt_irrefl _ H0).
Qed.

Lemma sep__part_fun_wd :
 forall (i j : nat) Hi Hj, i = j -> sep__part_fun i Hi = sep__part_fun j Hj.
Proof.
 intros.
 unfold sep__part_fun in |- *.
 elim (le_lt_eq_dec _ _ Hi); elim (le_lt_eq_dec _ _ Hj); intros; simpl in |- *.
    rewrite H; auto.
   rewrite H in a0; rewrite b0 in a0; elim (Nat.lt_irrefl _ a0).
  rewrite <- H in a0; rewrite b0 in a0; elim (Nat.lt_irrefl _ a0).
 auto.
Qed.

Lemma sep__part_fun_mon :
 forall (i j : nat) Hi Hj, i < j -> sep__part_fun i Hi < sep__part_fun j Hj.
Proof.
 intros.
 apply less_nring with (IR:COrdField).
 apply local_mon_imp_mon_le with
   (f := fun (i : nat) (Hi : i <= m) => nring (R:=IR) (sep__part_fun i Hi)).
  clear H Hj Hi j i; intros; apply nring_less.
  2: assumption.
 elim (le_lt_eq_dec _ _ H'); intro.
  rewrite (sep__part_fun_i (S i)).
   2: assumption.
  simpl in |- *; elim (le_lt_dec (sep__part_h i) n); intro; simpl in |- *.
   elim (sep__part_lemma (sep__part_h i) a1); intro; simpl in |- *.
    elim (ProjT2 a2); set (j := ProjT1 a2) in *.
    intros Hj Hj'.
    elim Hj'; clear Hj'; intros H0 H1.
    rewrite sep__part_fun_i.
     2: auto with arith.
    apply (Partition_Points_mon _ _ _ _ P) with a1 Hj.
    apply less_transitive_unfolded with (P _ a1[+]delta [/]FourNZ).
     apply shift_less_plus'; astepl ZeroR; apply pos_div_four; exact RS'_delta_pos.
    apply shift_plus_less'; apply H0.
   apply sep__part_fun_bnd'; auto with arith.
  apply sep__part_fun_bnd'; auto with arith.
 generalize H'; rewrite b0.
 intro; rewrite sep__part_fun_m.
 apply sep__part_fun_bnd'.
 auto with arith.
Qed.

Definition sep__part : Partition Hab sep__part_length.
Proof.
 apply Build_Partition with (fun (i : nat) (Hi : i <= m) => P _ (sep__part_fun_bnd i Hi)).
    intros; apply prf1.
    apply sep__part_fun_wd; auto.
   intros.
   apply local_mon'_imp_mon'2_le with (f := fun (i : nat) (Hi : i <= n) => P i Hi).
    intros; apply prf2.
   apply sep__part_fun_mon; auto.
  intro.
  apply eq_transitive_unfolded with (P 0 (Nat.le_0_l _)).
   apply prf1.
   apply sep__part_fun_0.
  apply start.
 intro; eapply eq_transitive_unfolded.
  2: apply finish with (p := P) (H := le_n n).
 apply prf1.
 apply sep__part_fun_m.
Defined.

Lemma sep__part_fun_mon_pts :
 forall (i : nat) Hi Hi' Hi0 Hi'0,
 P (sep__part_fun i Hi) Hi0[<]P (sep__part_fun (S i) Hi') Hi'0.
Proof.
 do 3 intro.
 rewrite sep__part_fun_i.
  2: auto with arith.
 elim (le_lt_eq_dec _ _ Hi'); intro.
  rewrite (sep__part_fun_i (S i)).
   2: assumption.
  intros.
  apply sep__part_h_lemma.
  rewrite <- sep__part_fun_i with (H := Hi').
   apply sep__part_fun_bnd'; assumption.
  assumption.
 generalize Hi'; clear Hi'; rewrite b0.
 intro; rewrite sep__part_fun_m.
 intros.
 cut (m = m).
  2: auto.
 unfold m at 2 in |- *; elim (RS'_delta2_delta4 RS'_m1); intro; simpl in |- *; intro.
  cut (i = RS'_m1); [ clear b0; intro | rewrite <- b0 in H; auto with arith ].
  generalize Hi0; clear Hi0; rewrite H0.
  intro.
  elim (ProjT2 sep__part_app_n); fold RS'_m1 in |- *; intros.
  apply less_transitive_unfolded with (P (sep__part_h RS'_m1) Hi0[+]delta [/]FourNZ).
   apply shift_less_plus'; astepl ZeroR; apply pos_div_four; apply RS'_delta_pos.
  apply shift_plus_less'; eapply less_wdr.
   apply a0.
  apply cg_minus_wd; apply prf1.
   auto.
  auto.
 elim (ProjT2 sep__part_app_n); fold RS'_m1 in |- *; intros.
 generalize Hi'0; clear Hi'0.
 cut (S i = RS'_m1); [ intro | transitivity m; auto ].
 pattern n at 1 5 in |- *; rewrite <- H0.
 rewrite <- H2.
 intro.
 apply less_leEq_trans with (P _ (sep__part_h_bnd (S i))).
  2: apply local_mon'_imp_mon'_le with (f := fun (i : nat) (Hi : i <= n) => P i Hi).
    2: intros; apply prf2.
   2: red in |- *; intros; apply prf1; assumption.
  2: apply sep__part_h_mon_1.
 apply sep__part_h_lemma.
 apply H1.
 rewrite H2; apply le_n.
Qed.

Lemma sep__part_mon :
 forall (i : nat) Hi Hi', sep__part i Hi[<]sep__part (S i) Hi'.
Proof.
 intros.
 unfold sep__part in |- *; simpl in |- *.
 apply sep__part_fun_mon_pts.
Qed.

Lemma sep__part_mon_Mesh : Mesh sep__part[<=]Mesh P[+]csi.
Proof.
 unfold Mesh at 1 in |- *.
 apply maxlist_leEq.
  apply length_Part_Mesh_List.
  apply RS'_pos_m.
 intros x H.
 elim (Part_Mesh_List_lemma _ _ _ _ _ _ H).
 intros i Hi.
 elim Hi; clear Hi; intros Hi Hi'.
 elim Hi'; clear Hi'; intros Hi' Hx.
 eapply leEq_wdl.
  2: apply eq_symmetric_unfolded; apply Hx.
 clear Hx H x.
 simpl in |- *.
 cut (forall Ha Hb, P (sep__part_fun (S i) Hi') Ha[-]P (sep__part_fun i Hi) Hb[<=]Mesh P[+]csi).
  intro.
  apply H.
 rename Hi' into H.
 rewrite (sep__part_fun_i i).
  2: assumption.
 elim (le_lt_eq_dec _ _ H); intro.
  rewrite sep__part_fun_i.
   2: assumption.
  intros.
  cut (pred (sep__part_h (S i)) <= n); [ intro | eapply Nat.le_trans; [ apply Nat.le_pred_l | auto ] ].
  rstepl (P _ Ha[-]P _ H0[+](P _ H0[-]P _ Hb)).
  apply plus_resp_leEq_both.
   generalize Ha; pattern (sep__part_h (S i)) at 1 2 in |- *;
     replace (sep__part_h (S i)) with (S (pred (sep__part_h (S i)))); intros.
    apply Mesh_lemma.
   apply Nat.lt_succ_pred with (sep__part_h i); apply sep__part_h_mon_2.
   rewrite <- sep__part_fun_i with (H := Nat.lt_le_incl _ _ H).
    apply sep__part_fun_bnd'; assumption.
   assumption.
  eapply leEq_transitive.
   apply sep__part_h_lemma2.
  apply less_leEq; apply less_leEq_trans with delta.
   apply pos_div_two'; exact RS'_delta_pos.
  apply RS'_delta_csi.
 generalize H; clear H; rewrite b0; intro H.
 rewrite sep__part_fun_m.
 cut (m = m); [ unfold m at 2 in |- * | auto ].
 elim RS'_delta2_delta4; intro; simpl in |- *; intro.
  intros.
  cut (sep__part_h (S RS'_m1) = n).
   intro; generalize Ha Hb; pattern n at 1 5 in |- *.
   rewrite <- H1.
   cut (i = RS'_m1); [ intro | unfold sep__part_length in b0; rewrite <- b0 in H0; auto with arith ].
   rewrite H2.
   intros.
   cut (pred (sep__part_h (S RS'_m1)) <= n); [ intro | eapply Nat.le_trans; [ apply Nat.le_pred_l | auto ] ].
   rstepl (P _ Ha0[-]P _ H3[+](P _ H3[-]P _ Hb0)).
   apply plus_resp_leEq_both.
    generalize Ha0; pattern (sep__part_h (S RS'_m1)) at 1 2 in |- *;
      replace (sep__part_h (S RS'_m1)) with (S (pred (sep__part_h (S RS'_m1)))); intros.
     apply Mesh_lemma.
    apply Nat.lt_succ_pred with (sep__part_h RS'_m1); apply sep__part_h_mon_2.
    cut (RS'_m1 <= m).
     2: rewrite H0; apply Nat.le_succ_diag_r.
    intro.
    rewrite <- sep__part_fun_i with (H := H4).
     apply sep__part_fun_bnd'.
     rewrite H0; apply Nat.lt_succ_diag_r.
    rewrite H0; apply Nat.lt_succ_diag_r.
   eapply leEq_transitive.
    apply sep__part_h_lemma2.
   apply less_leEq; apply less_leEq_trans with delta.
    apply pos_div_two'; exact RS'_delta_pos.
   apply RS'_delta_csi.
  elim (ProjT2 sep__part_app_n); fold RS'_m1 in |- *; intros.
  auto.
 cut (sep__part_h (S RS'_m1) = n).
  intro; pattern n at 1 5 in |- *.
  rewrite <- H1.
  intros.
  cut (sep__part_h RS'_m1 <= n); [ intro | apply sep__part_h_bnd ].
  rstepl (P _ Ha[-]P _ H2[+](P _ H2[-]P _ Hb)).
  apply leEq_transitive with (delta [/]TwoNZ[+](Mesh P[+]delta [/]TwoNZ)).
   apply plus_resp_leEq_both.
    apply less_leEq; eapply less_wdl.
     apply b1.
    apply cg_minus_wd; apply prf1; auto.
   generalize H2; clear H2; rewrite <- H0; unfold sep__part_length in b0; rewrite <- b0.
   simpl in |- *.
   elim (le_lt_dec (sep__part_h i) n); intro; simpl in |- *.
    elim (sep__part_lemma (sep__part_h i) a0); intro; simpl in |- *.
     set (j := ProjT1 a1) in *.
     change (forall H0, P j H0[-]P (sep__part_h i) Hb[<=]Mesh P[+]delta [/]TwoNZ) in |- *.
     elim (ProjT2 a1); fold j in |- *; intros Hj Hj'.
     elim Hj'; clear Hj'; intros H2 H3.
     intros.
     cut (pred j <= n); [ intro | apply Nat.le_trans with j; auto with arith ].
     rstepl (P j H4[-]P (pred j) H5[+](P (pred j) H5[-]P (sep__part_h i) Hb)).
     cut (0 < j); intros.
      apply plus_resp_leEq_both.
       cut (j = S (pred j)); [ intro | symmetry; apply Nat.lt_succ_pred with 0; auto ].
       generalize H4 H5 H6; rewrite H7; intros.
       apply Mesh_lemma.
      apply less_leEq.
      apply less_wdl with (P (pred j) H5[-]P _ a0).
       2: apply cg_minus_wd; apply prf1; auto.
      apply H3.
      auto with arith.
     apply Nat.le_lt_trans with (sep__part_h i); auto with arith.
     apply Partition_Points_mon with (P := P) (Hi := a0) (Hj := Hj).
     apply less_transitive_unfolded with (P (sep__part_h i) a0[+]delta [/]FourNZ).
      apply shift_less_plus'; astepl ZeroR; apply pos_div_four; exact RS'_delta_pos.
     apply shift_plus_less'; assumption.
    intros.
    apply less_leEq; apply less_leEq_trans with (delta [/]TwoNZ).
     eapply less_wdl.
      apply b2.
     apply cg_minus_wd; apply prf1; auto.
    astepl ([0][+]delta [/]TwoNZ); apply plus_resp_leEq; apply Mesh_nonneg.
   exfalso.
   lia.
  rstepl (Mesh P[+]delta).
  apply plus_resp_leEq_lft; apply RS'_delta_csi.
 elim (ProjT2 sep__part_app_n); fold RS'_m1 in |- *; intros.
 auto.
Qed.

Variable g : forall i : nat, i < n -> IR.
Hypothesis gP : Points_in_Partition P g.
Hypothesis gP' : nat_less_n_fun g.

Definition sep__part_pts (i : nat) (Hi : i < sep__part_length) : IR.
Proof.
 intros.
 cut (pred (sep__part_h (S i)) < n); intros.
  apply (g _ H).
 cut (sep__part_h i < sep__part_h (S i)).
  2: apply sep__part_h_mon_3.
   intro.
   red in |- *.
   replace (S (pred (sep__part_h (S i)))) with (sep__part_h (S i)); intros.
    apply sep__part_h_bnd.
   symmetry; apply Nat.lt_succ_pred with (sep__part_h i); assumption.
  rewrite <- sep__part_fun_i with (H := Nat.lt_le_incl _ _ Hi).
   apply sep__part_fun_bnd'; assumption.
  assumption.
 apply Nat.lt_succ_diag_r.
Defined.

Lemma sep__part_pts_lemma :
 forall (i : nat) Hi Hi',
 sep__part_pts i Hi[=]g (pred (sep__part_h (S i))) Hi'.
Proof.
 intros; unfold sep__part_pts in |- *.
 apply gP'; auto.
Qed.

Lemma sep__part_pts_in_Partition :
 Points_in_Partition sep__part sep__part_pts.
Proof.
 red in |- *; intros i Hi.
 set (H := sep__part_h_mon_3 _ _ (eq_ind (sep__part_fun i (Nat.lt_le_incl _ _ Hi)) (
   fun n0 : nat => n0 < n) (sep__part_fun_bnd' i (Nat.lt_le_incl _ _ Hi) Hi)
     (sep__part_h i) (sep__part_fun_i i (Nat.lt_le_incl _ _ Hi) Hi)) (Nat.lt_succ_diag_r i)) in *.
 set (H0 := eq_sym (Nat.lt_succ_pred (sep__part_h i) (sep__part_h (S i)) H)) in *.
 set (H' := eq_ind (sep__part_h (S i)) (fun j : nat => j <= n) (
   sep__part_h_bnd (S i)) (S (pred (sep__part_h (S i)))) H0) in *.
 elim (gP _ H'); intros.
 simpl in |- *; unfold sep__part_pts in |- *.
 split.
  eapply leEq_transitive.
   2: apply a0.
  apply Partition_mon; apply le_2.
  rewrite sep__part_fun_i; assumption.
 eapply leEq_transitive.
  apply b0.
 apply Partition_mon.
 rewrite <- H0.
 apply sep__part_fun_i'.
Qed.

Lemma RS'_Hsep_S :
  forall (i j : nat) (Hi : S i <= m),
  j <= pred (sep__part_fun (S i) Hi) -> S j <= n.
Proof.
 intros.
 apply Nat.le_trans with (sep__part_fun (S i) Hi).
  2: apply sep__part_fun_bnd.
 rewrite <- (Nat.lt_succ_pred (sep__part_fun i (Nat.lt_le_incl _ _ Hi)) (sep__part_fun (S i) Hi) ) .
  auto with arith.
 apply sep__part_fun_mon; apply Nat.lt_succ_diag_r.
Qed.

Lemma RS'_Hsep :
  forall (i j : nat) (Hi : S i <= m),
  j <= pred (sep__part_fun (S i) Hi) -> j <= n.
Proof.
 intros.
 apply Nat.le_trans with (sep__part_fun (S i) Hi).
  2: apply sep__part_fun_bnd.
 rewrite <- (Nat.lt_succ_pred (sep__part_fun i (Nat.lt_le_incl _ _ Hi)) (sep__part_fun (S i) Hi) ) .
  apply le_S; assumption.
 apply sep__part_fun_mon; apply Nat.lt_succ_diag_r.
Qed.

Definition RS'_h : nat -> IR.
Proof.
 intro i.
 elim (le_lt_dec i n); intro.
  apply (P i a0).
 apply ZeroR.
Defined.

Notation h := RS'_h.
Notation just1 := (incF _ (Pts_part_lemma _ _ _ _ _ _ gP _ _)).
Notation just2 :=
  (incF _ (Pts_part_lemma _ _ _ _ _ _ sep__part_pts_in_Partition _ _)).

Lemma sep__part_suRS'_m1 :
  forall (i : nat) (Hi : i < m),
  Sum2
    (fun (j : nat) (Hj : sep__part_fun i (Nat.lt_le_incl _ _ Hi) <= j)
       (Hj' : j <= pred (sep__part_fun (S i) Hi)) =>
     P _ (RS'_Hsep_S _ _ _ Hj')[-]P _ (RS'_Hsep _ _ _ Hj'))[=]
  sep__part _ Hi[-]sep__part _ (Nat.lt_le_incl _ _ Hi).
Proof.
 intros; simpl in |- *.
 unfold Sum2 in |- *.
 cut (sep__part_fun (S i) Hi = S (pred (sep__part_fun (S i) Hi))).
  2: symmetry; apply Nat.lt_succ_pred with (sep__part_fun i (Nat.lt_le_incl _ _ Hi)); apply sep__part_fun_mon; apply Nat.lt_succ_diag_r.
 intro.
 cut (S (pred (sep__part_fun (S i) Hi)) <= n).
  2: rewrite <- H; apply sep__part_fun_bnd.
 intro.
 apply eq_transitive_unfolded with (P _ H0[-]P _ (sep__part_fun_bnd i (Nat.lt_le_incl _ _ Hi))).
  2: apply cg_minus_wd; apply prf1; auto.
 eapply eq_transitive_unfolded.
  apply str_Mengolli_Sum_gen with (f := h).
   rewrite <- H; apply Nat.lt_le_incl; apply sep__part_fun_mon; apply Nat.lt_succ_diag_r.
  intro j; intros.
  do 2 elim le_lt_dec; intros; simpl in |- *.
     unfold h in |- *.
     do 2 elim le_lt_dec; intros; simpl in |- *.
        apply cg_minus_wd; apply prf1; auto.
       exfalso; apply Nat.le_ngt with j n.
        apply Nat.le_trans with (S j); auto with arith.
       assumption.
      exfalso; apply Nat.le_ngt with (S j) n.
       exact (RS'_Hsep_S _ _ Hi a1).
      assumption.
     exfalso; apply Nat.le_ngt with (S j) n.
      exact (RS'_Hsep_S _ _ Hi a1).
     assumption.
    exfalso; lia.
   exfalso; lia.
  exfalso; lia.
 unfold h in |- *.
 apply cg_minus_wd.
  elim le_lt_dec; simpl in |- *; intros.
   apply prf1; auto.
  exfalso; lia.
 elim le_lt_dec; intro; simpl in |- *.
  apply prf1; auto.
 exfalso; rewrite <- H in H0; apply Nat.le_ngt with (sep__part_fun i (Nat.lt_le_incl _ _ Hi)) n.
  apply sep__part_fun_bnd.
 assumption.
Qed.

Lemma sep__part_Sum2 :
  Partition_Sum gP incF[=]
  Sumx
    (fun (i : nat) (Hi : i < m) =>
     Sum2
       (fun (j : nat) (Hj : sep__part_fun i (Nat.lt_le_incl _ _ Hi) <= j)
          (Hj' : j <= pred (sep__part_fun (S i) Hi)) =>
        F (g j (RS'_Hsep_S _ _ _ Hj')) just1[*]
        (P _ (RS'_Hsep_S _ _ _ Hj')[-]P _ (RS'_Hsep _ _ _ Hj')))).
Proof.
 unfold Partition_Sum in |- *.
 apply eq_symmetric_unfolded.
 unfold Sum2 in |- *.
 apply eq_transitive_unfolded with (Sumx (fun (j : nat) (Hj : j < n) => part_tot_nat_fun _ _
   (fun (i : nat) (H : i < n) => F (g i H) just1[*](P _ H[-]P _ (Nat.lt_le_incl _ _ H))) j)).
  apply str_Sumx_Sum_Sum' with (g := fun (i : nat) (Hi : i < m) (i0 : nat) => sumbool_rect (fun
    _ : {sep__part_fun i (Nat.lt_le_incl i m Hi) <= i0} + {i0 < sep__part_fun i (Nat.lt_le_incl i m Hi)} => IR)
      (fun _ : sep__part_fun i (Nat.lt_le_incl i m Hi) <= i0 => sumbool_rect (fun
        _ : {i0 <= pred (sep__part_fun (S i) Hi)} + {pred (sep__part_fun (S i) Hi) < i0} => IR)
          (fun H0 : i0 <= pred (sep__part_fun (S i) Hi) => F (g i0 (RS'_Hsep_S i i0 Hi H0))
            (incF (g i0 (RS'_Hsep_S i i0 Hi H0))
              (Pts_part_lemma a b Hab n P g gP i0 (RS'_Hsep_S i i0 Hi H0)))[*]
                (P (S i0) (RS'_Hsep_S i i0 Hi H0)[-]P i0 (RS'_Hsep i i0 Hi H0)))
                  (fun _ : pred (sep__part_fun (S i) Hi) < i0 => [0])
                    (le_lt_dec i0 (pred (sep__part_fun (S i) Hi))))
                      (fun _ : i0 < sep__part_fun i (Nat.lt_le_incl i m Hi) => [0])
                        (le_lt_dec (sep__part_fun i (Nat.lt_le_incl i m Hi)) i0))
                          (h := part_tot_nat_fun _ _ (fun (i : nat) (H : i < n) =>
                            F (g i H) just1[*](P _ H[-]P _ (Nat.lt_le_incl _ _ H)))).
      apply sep__part_fun_0.
     intros; apply sep__part_fun_wd; auto.
    intros; apply sep__part_fun_mon; auto.
   intros.
   elim le_lt_dec; intro; simpl in |- *.
    elim le_lt_dec; intro; simpl in |- *.
     unfold part_tot_nat_fun in |- *.
     elim (le_lt_dec n j); intro; simpl in |- *.
      exfalso.
      apply Nat.le_ngt with n j.
       assumption.
      apply Nat.lt_le_trans with (sep__part_fun (S i) Hi'').
       assumption.
      apply sep__part_fun_bnd.
     apply mult_wd; algebra.
     apply cg_minus_wd; apply prf1; auto.
    exfalso.
    apply Nat.le_ngt with (sep__part_fun i Hi') j.
     assumption.
    cut (sep__part_fun i Hi' = sep__part_fun i (Nat.lt_le_incl _ _ Hi));
      [ intro | apply sep__part_fun_wd; auto ].
    rewrite H1; assumption.
   exfalso.
   apply Nat.le_ngt with (S j) (sep__part_fun (S i) Hi).
    cut (sep__part_fun (S i) Hi = sep__part_fun (S i) Hi''); [ intro | apply sep__part_fun_wd; auto ].
    rewrite H1; apply H0.
   rewrite <- (Nat.lt_succ_pred (sep__part_fun i (Nat.lt_le_incl _ _ Hi)) (sep__part_fun (S i) Hi)) .
    auto with arith.
   apply sep__part_fun_mon; apply Nat.lt_succ_diag_r.
  intros; symmetry  in |- *; apply sep__part_fun_m.
 apply Sumx_wd; intros.
 unfold part_tot_nat_fun in |- *.
 elim (le_lt_dec n i); intro; simpl in |- *.
  exfalso; apply Nat.le_ngt with n i; auto.
 apply mult_wd; algebra.
 apply cg_minus_wd; apply prf1; auto.
Qed.

Lemma sep__part_Sum3 :
  AbsIR
    (Partition_Sum gP incF[-]Partition_Sum sep__part_pts_in_Partition incF)[=]
  AbsIR
    (Sumx
       (fun (i : nat) (Hi : i < m) =>
        Sum2
          (fun (j : nat) (Hj : sep__part_fun i (Nat.lt_le_incl _ _ Hi) <= j)
             (Hj' : j <= pred (sep__part_fun (S i) Hi)) =>
           (F (g j (RS'_Hsep_S _ _ _ Hj')) just1[-]F (sep__part_pts i Hi) just2)[*]
           (P _ (RS'_Hsep_S _ _ _ Hj')[-]P _ (RS'_Hsep _ _ _ Hj'))))).
Proof.
 apply AbsIR_wd.
 apply eq_transitive_unfolded with (Sumx (fun (i : nat) (Hi : i < m) => Sum2
   (fun (j : nat) (Hj : sep__part_fun i (Nat.lt_le_incl _ _ Hi) <= j)
     (Hj' : j <= pred (sep__part_fun (S i) Hi)) => F (g j (RS'_Hsep_S _ _ _ Hj')) just1[*]
       (P _ (RS'_Hsep_S _ _ _ Hj')[-]P _ (RS'_Hsep _ _ _ Hj')))[-] F (sep__part_pts i Hi) just2[*]
         Sum2 (fun (j : nat) (Hj : sep__part_fun i (Nat.lt_le_incl _ _ Hi) <= j)
           (Hj' : j <= pred (sep__part_fun (S i) Hi)) =>
             P _ (RS'_Hsep_S _ _ _ Hj')[-]P _ (RS'_Hsep _ _ _ Hj')))).
  eapply eq_transitive_unfolded.
   2: apply Sumx_minus_Sumx with (f := fun (i : nat) (Hi : i < m) => Sum2
     (fun (j : nat) (Hj : sep__part_fun i (Nat.lt_le_incl _ _ Hi) <= j)
       (Hj' : j <= pred (sep__part_fun (S i) Hi)) => F (g j (RS'_Hsep_S _ _ _ Hj')) just1[*]
         (P _ (RS'_Hsep_S _ _ _ Hj')[-]P _ (RS'_Hsep _ _ _ Hj')))) (g := fun (i : nat) (Hi : i < m) =>
           F (sep__part_pts i Hi) just2[*] Sum2
             (fun (j : nat) (Hj : sep__part_fun i (Nat.lt_le_incl _ _ Hi) <= j)
               (Hj' : j <= pred (sep__part_fun (S i) Hi)) =>
                 P _ (RS'_Hsep_S _ _ _ Hj')[-]P _ (RS'_Hsep _ _ _ Hj'))).
  apply cg_minus_wd.
   apply sep__part_Sum2.
  unfold Partition_Sum in |- *; apply Sumx_wd; intros.
  apply mult_wdr.
  apply eq_symmetric_unfolded; apply sep__part_suRS'_m1.
 apply Sumx_wd; intros i Hi.
 apply eq_transitive_unfolded with (Sum2
   (fun (j : nat) (Hj : sep__part_fun i (Nat.lt_le_incl _ _ Hi) <= j)
     (Hj' : j <= pred (sep__part_fun (S i) Hi)) => F (g j (RS'_Hsep_S _ _ _ Hj')) just1[*]
       (P _ (RS'_Hsep_S _ _ _ Hj')[-]P _ (RS'_Hsep _ _ _ Hj')))[-] Sum2
         (fun (j : nat) (Hj : sep__part_fun i (Nat.lt_le_incl _ _ Hi) <= j)
           (Hj' : j <= pred (sep__part_fun (S i) Hi)) => F (sep__part_pts i Hi) just2[*]
             (P _ (RS'_Hsep_S _ _ _ Hj')[-]P _ (RS'_Hsep _ _ _ Hj')))).
  apply cg_minus_wd.
   algebra.
  apply eq_symmetric_unfolded; eapply eq_transitive_unfolded.
   2: apply Sum2_comm_scal'.
   algebra.
  rewrite (Nat.lt_succ_pred (sep__part_fun i (Nat.lt_le_incl _ _ Hi)) (sep__part_fun (S i) Hi)
    (sep__part_fun_mon _ _ _ _ (Nat.lt_succ_diag_r i))).
  apply Nat.lt_le_incl; apply sep__part_fun_mon; apply Nat.lt_succ_diag_r.
 eapply eq_transitive_unfolded.
  apply Sum2_minus_Sum2.
  rewrite (Nat.lt_succ_pred (sep__part_fun i (Nat.lt_le_incl _ _ Hi)) (sep__part_fun (S i) Hi)
    (sep__part_fun_mon _ _ _ _ (Nat.lt_succ_diag_r i))).
  apply Nat.lt_le_incl; apply sep__part_fun_mon; apply Nat.lt_succ_diag_r.
 apply Sum2_wd; intros.
  rewrite (Nat.lt_succ_pred (sep__part_fun i (Nat.lt_le_incl _ _ Hi)) (sep__part_fun (S i) Hi)
    (sep__part_fun_mon _ _ _ _ (Nat.lt_succ_diag_r i))).
  apply Nat.lt_le_incl; apply sep__part_fun_mon; apply Nat.lt_succ_diag_r.
 algebra.
Qed.

Lemma sep__part_Sum4 :
  Sumx
    (fun (i : nat) (Hi : i < m) =>
     Sum2
       (fun (j : nat) (Hj : sep__part_fun i (Nat.lt_le_incl _ _ Hi) <= j)
          (Hj' : j <= pred (sep__part_fun (S i) Hi)) =>
        (M[+]M)[*]delta [/]TwoNZ))[<=]alpha.
Proof.
 unfold Sum2 in |- *.
 apply leEq_wdl with (Sumx (fun (j : nat) (_ : j < n) => part_tot_nat_fun _ _
   (fun (i : nat) (_ : i < n) => (M[+]M)[*]delta [/]TwoNZ) j)).
  2: apply eq_symmetric_unfolded; apply str_Sumx_Sum_Sum' with
    (g := fun (i : nat) (Hi : i < m) (i0 : nat) => sumbool_rect (fun
      _ : {sep__part_fun i (Nat.lt_le_incl i m Hi) <= i0} +
        {i0 < sep__part_fun i (Nat.lt_le_incl i m Hi)} => IR)
          (fun _ : sep__part_fun i (Nat.lt_le_incl i m Hi) <= i0 => sumbool_rect (fun
            _ : {i0 <= pred (sep__part_fun (S i) Hi)} + {pred (sep__part_fun (S i) Hi) < i0} => IR)
              (fun _ : i0 <= pred (sep__part_fun (S i) Hi) => (M[+]M)[*]delta [/]TwoNZ)
                (fun _ : pred (sep__part_fun (S i) Hi) < i0 => [0])
                  (le_lt_dec i0 (pred (sep__part_fun (S i) Hi))))
                    (fun _ : i0 < sep__part_fun i (Nat.lt_le_incl i m Hi) => [0])
                      (le_lt_dec (sep__part_fun i (Nat.lt_le_incl i m Hi)) i0)) (h := part_tot_nat_fun _ _
                        (fun (i : nat) (_ : i < n) => (M[+]M)[*]delta [/]TwoNZ)).
      apply leEq_wdr with (Sumx (fun (i : nat) (_ : i < n) => alpha[/] _[//]nring_ap_zero _ _ SPap_n)).
       2: rstepr (nring n[*](alpha[/] _[//]nring_ap_zero _ _ SPap_n)); apply sumx_const.
      apply Sumx_resp_leEq; intros.
      unfold part_tot_nat_fun in |- *.
      elim (le_lt_dec n i); intro; simpl in |- *.
       exfalso; lia.
      unfold delta in |- *.
      apply leEq_transitive with ((M[+]M)[*] (alpha[/] _[//]
        mult_resp_ap_zero _ _ _ (nring_ap_zero _ _ SPap_n) (max_one_ap_zero M)) [/]TwoNZ).
       apply mult_resp_leEq_lft.
        apply div_resp_leEq.
         apply pos_two.
        apply Min_leEq_rht.
       astepl (ZeroR[+][0]); apply plus_resp_leEq_both; unfold M in |- *; apply positive_norm.
      rstepl (alpha[*](M[/] _[//]max_one_ap_zero M)[*] ([1][/] _[//]nring_ap_zero _ _ SPap_n)).
      rstepr (alpha[*][1][*]([1][/] _[//]nring_ap_zero _ _ SPap_n)).
      apply mult_resp_leEq_rht.
       apply mult_resp_leEq_lft.
        apply shift_div_leEq.
         apply pos_max_one.
        astepr (Max M [1]); apply lft_leEq_Max.
       apply less_leEq; assumption.
      apply less_leEq; apply recip_resp_pos.
      astepl (nring (R:=IR) 0); apply nring_less; apply RS'_pos_n.
     apply sep__part_fun_0.
    exact sep__part_fun_wd.
   exact sep__part_fun_mon.
  unfold part_tot_nat_fun in |- *.
  intros; elim (le_lt_dec (sep__part_fun i (Nat.lt_le_incl _ _ Hi)) j); intro; simpl in |- *.
   elim (le_lt_dec j (pred (sep__part_fun (S i) Hi))); intro; simpl in |- *.
    elim (le_lt_dec n j); intro; simpl in |- *.
     exfalso; apply (Nat.le_ngt n j).
      assumption.
     eapply Nat.lt_le_trans.
      apply H0.
     apply sep__part_fun_bnd.
    algebra.
   exfalso; apply (proj1 (Nat.le_ngt _ _) H0).
   rewrite <- (Nat.lt_succ_pred (sep__part_fun i Hi') (sep__part_fun (S i) Hi'')).
    cut (sep__part_fun (S i) Hi'' = sep__part_fun (S i) Hi); [ intro | apply sep__part_fun_wd; auto ].
    rewrite H1; auto with arith.
   apply sep__part_fun_mon.
   apply Nat.lt_succ_diag_r.
  exfalso; apply (proj1 (Nat.le_ngt _ _) H).
  rewrite sep__part_fun_i.
   2: assumption.
  rewrite sep__part_fun_i in b0; assumption.
 intros; symmetry  in |- *; apply sep__part_fun_m.
Qed.

Lemma sep__part_aux : forall i : nat, pred (sep__part_h (S i)) < n.
Proof.
 intros.
 red in |- *.
 rewrite Nat.lt_succ_pred with (sep__part_h 0) (sep__part_h (S i)).
  apply sep__part_h_bnd.
 apply sep__part_h_mon_3.
  rewrite <- sep__part_fun_i with (H := Nat.le_0_l m).
   2: apply RS'_pos_m.
  2: apply Nat.lt_0_succ.
 rewrite <- sep__part_fun_m with (H := le_n m).
 apply sep__part_fun_mon.
 apply RS'_pos_m.
Qed.

Lemma sep__part_Sum :
 AbsIR
   (Partition_Sum gP incF[-]Partition_Sum sep__part_pts_in_Partition incF)[<=]
 alpha.
Proof.
 eapply leEq_wdl.
  2: apply eq_symmetric_unfolded; apply sep__part_Sum3.
 eapply leEq_transitive.
  2: apply sep__part_Sum4.
 eapply leEq_transitive.
  apply triangle_SumxIR.
 apply Sumx_resp_leEq; intros.
 eapply leEq_transitive.
  apply triangle_Sum2IR.
  rewrite (Nat.lt_succ_pred (sep__part_fun i (Nat.lt_le_incl _ _ H)) (sep__part_fun (S i) H)
    (sep__part_fun_mon _ _ _ _ (Nat.lt_succ_diag_r i))).
  apply Nat.lt_le_incl; apply sep__part_fun_mon; apply Nat.lt_succ_diag_r.
 apply Sum2_resp_leEq.
  rewrite (Nat.lt_succ_pred (sep__part_fun i (Nat.lt_le_incl _ _ H)) (sep__part_fun (S i) H)
    (sep__part_fun_mon _ _ _ _ (Nat.lt_succ_diag_r i))).
  apply Nat.lt_le_incl; apply sep__part_fun_mon; apply Nat.lt_succ_diag_r.
 intros k Hk Hk'.
 elim (le_lt_dec m (S i)); intro.
  cut (S i = m); [ intro | clear Hk Hk'; lia ].
  generalize H0.
  unfold m at 1 in |- *; elim RS'_delta2_delta4; intro; simpl in |- *; intro.
   cut (i < m); [ intro | assumption ].
   apply leEq_wdl with (AbsIR
     ((F (g k (RS'_Hsep_S _ _ H Hk')) just1[-]F (g _ (sep__part_aux RS'_m1)) just1)[*]
       (P (S k) (RS'_Hsep_S _ _ H Hk')[-]P k (RS'_Hsep _ _ H Hk')))).
    2: apply AbsIR_wd; apply mult_wdl.
    2: apply cg_minus_wd; [ algebra | idtac ].
    2: cut (i = RS'_m1); [ intro | auto ].
    2: generalize H; rewrite H3; intro.
    2: unfold sep__part_pts in |- *; simpl in |- *; algebra.
   elim (le_lt_dec (pred (sep__part_h (S RS'_m1))) k); intro.
    cut (pred (sep__part_h (S RS'_m1)) = k); intros.
     apply leEq_wdl with ZeroR.
      astepl (([0][+][0])[*]ZeroR).
      apply mult_resp_leEq_both.
         apply eq_imp_leEq; algebra.
        apply leEq_reflexive.
       apply plus_resp_leEq_both; unfold M in |- *; apply positive_norm.
      apply less_leEq; astepr (delta [/]TwoNZ); apply pos_div_two; exact RS'_delta_pos.
     apply eq_symmetric_unfolded; eapply eq_transitive_unfolded.
      2: apply AbsIRz_isz.
     apply AbsIR_wd.
     rstepr ((F (g _ (sep__part_aux RS'_m1)) just1[-]F (g _ (sep__part_aux RS'_m1)) just1)[*]
       (P (S k) (RS'_Hsep_S _ _ H Hk')[-]P k (RS'_Hsep _ _ H Hk'))).
     algebra.
    cut (forall H, sep__part_fun (S i) H = n).
     intro.
     cut (sep__part_h (S RS'_m1) = n); intros.
      rewrite H4 in a2.
      rewrite H3 in Hk'.
      rewrite H4.
      apply Nat.le_antisymm; auto.
     elim (ProjT2 sep__part_app_n); fold RS'_m1 in |- *; intros.
     auto.
    rewrite H0; exact sep__part_fun_m.
   eapply leEq_wdl.
    2: apply eq_symmetric_unfolded; apply AbsIR_resp_mult.
   apply mult_resp_leEq_both; try apply AbsIR_nonneg.
    eapply leEq_transitive.
     apply triangle_IR_minus.
    apply plus_resp_leEq_both; unfold M, I in |- *; apply norm_bnd_AbsIR;
      apply Pts_part_lemma with n P; apply gP.
   eapply leEq_wdl.
    2: apply eq_symmetric_unfolded; apply AbsIR_eq_x.
    2: apply shift_leEq_minus; astepl (P k (RS'_Hsep i k H Hk')); apply prf2.
   apply sep__part_h_lemma3 with i.
    rewrite sep__part_fun_i in Hk; assumption.
   rewrite H1; assumption.
  apply leEq_wdl with (AbsIR
    ((F (g k (RS'_Hsep_S _ _ H Hk')) just1[-]F (g _ (sep__part_aux i)) just1)[*]
      (P (S k) (RS'_Hsep_S _ _ H Hk')[-]P k (RS'_Hsep _ _ H Hk')))).
   2: apply AbsIR_wd; apply mult_wd.
    2: apply cg_minus_wd; apply pfwdef; [ algebra | unfold sep__part_pts in |- *; apply gP' ]; auto.
   2: apply cg_minus_wd; apply prf1; auto.
  elim (le_lt_dec (pred (sep__part_h RS'_m1)) k); intro.
   elim (le_lt_eq_dec _ _ a1); intro.
    eapply leEq_wdl.
     2: apply eq_symmetric_unfolded; apply AbsIR_resp_mult.
    apply mult_resp_leEq_both; try apply AbsIR_nonneg.
     eapply leEq_transitive.
      apply triangle_IR_minus.
     apply plus_resp_leEq_both; unfold M, I in |- *; apply norm_bnd_AbsIR;
       apply Pts_part_lemma with n P; assumption.
    eapply leEq_wdl.
     2: apply eq_symmetric_unfolded; apply AbsIR_eq_x.
     2: apply shift_leEq_minus; astepl (P k (RS'_Hsep i k H Hk')); apply prf2.
    apply less_leEq; eapply leEq_less_trans.
     2: apply b0.
    unfold cg_minus in |- *; apply plus_resp_leEq_both.
     apply Partition_mon.
     rewrite <- (Nat.lt_succ_pred (sep__part_h RS'_m1) (sep__part_h (S RS'_m1))).
      apply le_n_S.
      cut (forall H, sep__part_h (S RS'_m1) = sep__part_fun (S i) H); intros.
       rewrite (H2 H); assumption.
      generalize H2; rewrite H0.
      intro; rewrite sep__part_fun_m.
      elim (ProjT2 sep__part_app_n); fold RS'_m1 in |- *; auto.
     apply sep__part_h_mon_3.
      elim (ProjT2 sep__part_app_n); fold RS'_m1 in |- *; intros.
      apply H3; apply le_n.
     apply Nat.lt_succ_diag_r.
    apply inv_resp_leEq; apply Partition_mon.
    eapply Nat.le_trans.
     2: apply a2.
    clear Hk Hk'; lia.
   apply leEq_wdl with ZeroR.
    astepl (([0][+][0])[*]ZeroR).
    apply mult_resp_leEq_both.
       apply eq_imp_leEq; algebra.
      apply leEq_reflexive.
     apply plus_resp_leEq_both; unfold M in |- *; apply positive_norm.
    apply less_leEq; astepr (delta [/]TwoNZ); apply pos_div_two; exact RS'_delta_pos.
   apply eq_symmetric_unfolded; eapply eq_transitive_unfolded.
    2: apply AbsIRz_isz.
   apply AbsIR_wd.
   rstepr ((F (g _ (sep__part_aux i)) just1[-]F (g _ (sep__part_aux i)) just1)[*]
     (P (S k) (RS'_Hsep_S _ _ H Hk')[-]P k (RS'_Hsep _ _ H Hk'))).
   apply mult_wdl.
   apply cg_minus_wd; apply pfwdef; apply gP'; auto.
   rewrite H1; auto.
  eapply leEq_wdl.
   2: apply eq_symmetric_unfolded; apply AbsIR_resp_mult.
  apply mult_resp_leEq_both; try apply AbsIR_nonneg.
   eapply leEq_transitive.
    apply triangle_IR_minus.
   apply plus_resp_leEq_both; unfold M, I in |- *; apply norm_bnd_AbsIR;
     apply Pts_part_lemma with n P; assumption.
  eapply leEq_wdl.
   2: apply eq_symmetric_unfolded; apply AbsIR_eq_x.
   2: apply shift_leEq_minus; astepl (P k (RS'_Hsep i k H Hk')); apply prf2.
  apply sep__part_h_lemma3 with i.
   rewrite sep__part_fun_i in Hk; assumption.
  rewrite H1; assumption.
 elim (le_lt_eq_dec _ _ Hk'); intro.
  eapply leEq_wdl.
   2: apply eq_symmetric_unfolded; apply AbsIR_resp_mult.
  apply mult_resp_leEq_both; try apply AbsIR_nonneg.
   eapply leEq_transitive.
    apply triangle_IR_minus.
   apply plus_resp_leEq_both; unfold M, I in |- *; apply norm_bnd_AbsIR.
    apply Pts_part_lemma with n P; assumption.
   apply Pts_part_lemma with sep__part_length sep__part; apply sep__part_pts_in_Partition.
  cut (pred (sep__part_fun (S i) H) <= n); intros.
   eapply leEq_wdl.
    2: apply eq_symmetric_unfolded; apply AbsIR_eq_x.
    2: apply shift_leEq_minus; astepl (P k (RS'_Hsep i k H Hk')); apply prf2.
   apply sep__part_h_lemma3 with i.
    rewrite sep__part_fun_i in Hk; assumption.
   rewrite sep__part_fun_i in a0; assumption.
  apply Nat.le_trans with (sep__part_fun (S i) H).
   auto with arith.
  apply sep__part_fun_bnd.
 apply leEq_wdl with ZeroR.
  astepl (([0][+][0])[*]ZeroR).
  apply mult_resp_leEq_both.
     apply eq_imp_leEq; algebra.
    apply leEq_reflexive.
   apply plus_resp_leEq_both; unfold M in |- *; apply positive_norm.
  apply less_leEq; astepr (delta [/]TwoNZ); apply pos_div_two; exact RS'_delta_pos.
 apply eq_symmetric_unfolded; eapply eq_transitive_unfolded.
  2: apply AbsIRz_isz.
 apply AbsIR_wd.
 rstepr ((F (g _ (sep__part_aux i)) just1[-]F (g _ (sep__part_aux i)) just1)[*]
   (P (S k) (RS'_Hsep_S _ _ H Hk')[-]P k (RS'_Hsep _ _ H Hk'))).
 apply mult_wdl.
 apply cg_minus_wd; apply pfwdef; unfold sep__part_pts in |- *; apply gP'; auto.
 rewrite sep__part_fun_i in b1; assumption.
Qed.

End Separating_Partition.
(* end hide *)
