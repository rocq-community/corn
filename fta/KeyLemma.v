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
From Coq Require Export Compare.
Require Export CoRN.reals.NRootIR.
From Coq Require Import Lia.

(** printing p3m %\ensuremath{\frac13\hat{\ }}% *)
(** printing Halfeps %\ensuremath{\frac\varepsilon2}% *)

(**
* Technical lemmas for the FTA
** Key Lemma
*)

Section Key_Lemma.

(**
%\begin{convention}% Let [a:nat->IR] and [n:nat] such that [0 < n],
[forall (k : nat) ([0] [<=] (a k))], [(a n) [=] [1]] and [a_0 : IR],
and [eps : IR] such that [([0] [<] eps)] and [(eps [<=] a_0)].
%\end{convention}%
*)
Variable a : nat -> IR.
Variable n : nat.
Hypothesis gt_n_0 : 0 < n.
Variable eps : IR.
Hypothesis eps_pos : [0] [<] eps.
Hypothesis a_nonneg : forall k : nat, [0] [<=] a k.
Hypothesis a_n_1 : a n [=] [1].
Variable a_0 : IR.
Hypothesis eps_le_a_0 : eps [<=] a_0.

Lemma a_0_eps_nonneg : [0] [<=] a_0[-]eps.
Proof.
 apply shift_leEq_minus.
 astepl eps; auto.
Qed.

Lemma a_0_eps_fuzz : a_0[-]eps [<] a_0.
Proof.
 astepr (a_0[-][0]).
 apply minus_resp_less_rht.
 apply eps_pos.
Qed.

Lemma lem_1a : n - (n - 1) = 1.
Proof.
 cut (1 <= n).
  lia.
 auto with arith.
Qed.

Lemma lem_1b : forall n j : nat, n - S j <= n - j.
Proof.
 intros.
 lia.
Qed.

Lemma lem_1c : forall n j : nat, n - j <= n.
Proof.
 intros.
 lia.
Qed.

Lemma lem_1 : {t : IR | [0] [<=] t |
 {k : nat | 1 <= k /\ k <= n /\ a k[*]t[^]k [=] a_0[-]eps /\
 (forall i, 1 <= i -> i <= n -> a i[*]t[^]i [<=] a_0)}}.
Proof.
 cut (forall j : nat, let l := n - j in 1 <= l -> l <= n -> {t : IR | [0] [<=] t | {k : nat |
   l <= k /\ k <= n /\ a k[*]t[^]k [=] a_0[-]eps /\
     (forall i : nat, l <= i -> i <= n -> a i[*]t[^]i [<=] a_0)}}).
  intro H.
  rewrite <- lem_1a.
  apply H; rewrite lem_1a; auto with arith.
 intro j. induction  j as [| j Hrecj].
 replace (n - 0) with n.
   2: auto with arith.
  intros l H H0.
  exists (NRoot a_0_eps_nonneg gt_n_0).
   apply NRoot_nonneg.
  exists n.
  split. auto.
   split. auto.
   split.
   astepl ([1][*]NRoot a_0_eps_nonneg gt_n_0[^]n).
   Step_final (NRoot a_0_eps_nonneg gt_n_0[^]n).
  intros i H1 H2.
  replace i with n.
   2: apply Nat.le_antisymm; auto.
  astepl ([1][*]NRoot a_0_eps_nonneg gt_n_0[^]n).
  astepl (NRoot a_0_eps_nonneg gt_n_0[^]n).
  astepl (a_0[-]eps).
  apply less_leEq; apply a_0_eps_fuzz.
 intros l H H0.
 cut (1 <= n - j). intro H1.
  2: apply Nat.le_trans with (n - S j); [ auto | apply lem_1b ].
 cut (n - j <= n). intro H2.
  2: apply lem_1c.
 elim (Hrecj H1 H2). intros t' H4 H5.
 elim H5. intros k' H6.
 elim H6. intros H7 H8. elim H8. intros H9 H10. elim H10. intros H11 H12.
 clear H10 H8 H6 H5.
 elim (less_cotransitive_unfolded _ _ _ a_0_eps_fuzz (a (n - S j) [*]t'[^] (n - S j))); intro H14.
  cut ([0] [<] a (n - S j)). intro H15.
   cut (a (n - S j) [#] [0]). intro H16.
    2: apply pos_ap_zero; auto.
   cut ([0] [<=] (a_0[-]eps[/] a (n - S j) [//]H16)). intro H17.
    cut (0 < n - S j). intro H18.
     2: auto with arith.
    exists (NRoot H17 H18).
     apply NRoot_nonneg.
    exists (n - S j).
    split. auto.
     split. auto.
     split.
     astepl (a (n - S j) [*] (a_0[-]eps[/] a (n - S j) [//]H16)).
     rational.
    intros i H19 H20.
    elim (le_lt_eq_dec _ _ H19); intro H22.
     apply leEq_transitive with (a i[*]t'[^]i).
      apply mult_resp_leEq_lft.
       apply power_resp_leEq.
        apply NRoot_nonneg.
       apply power_cancel_leEq with (n - S j); auto.
       astepl (a_0[-]eps[/] a (n - S j) [//]H16).
       apply shift_div_leEq.
        auto.
       astepr (a (n - S j) [*]t'[^] (n - S j)).
       apply less_leEq; auto.
      apply a_nonneg.
     apply H12.
      replace (n - j) with (S (n - S j)); [auto with arith|].
      rewrite <- Nat.sub_succ_l; auto with arith.
     auto.
    rewrite <- H22.
    astepl (a (n - S j) [*] (a_0[-]eps[/] a (n - S j) [//]H16)).
    astepl (a_0[-]eps).
    apply less_leEq; apply a_0_eps_fuzz.
   apply shift_leEq_div; auto.
   astepl ZeroR; apply a_0_eps_nonneg.
  cut ([0] [<] a (n - S j) [*]t'[^] (n - S j)). intro H15.
   2: apply leEq_less_trans with (a_0[-]eps); auto.
   2: apply a_0_eps_nonneg.
  apply leEq_not_eq.
   apply a_nonneg.
  apply ap_symmetric_unfolded.
  exact (cring_mult_ap_zero _ _ _ (pos_ap_zero _ _ H15)).
 exists t'.
  auto.
 exists k'.
 split.
  apply Nat.le_trans with (n - j).
   unfold l in |- *; apply lem_1b.
  auto.
 split. auto.
  split. auto.
  intros i H15 H16.
 elim (le_lt_eq_dec _ _ H15); intro H18.
  apply H12.
   replace (n - j) with (S (n - S j)); [auto with arith|].
   rewrite <- Nat.sub_succ_l; auto with arith.
  auto.
 rewrite <- H18.
 apply less_leEq; auto.
Qed.

Definition p3m (i : nat) := ([1] [/]ThreeNZ) [^]i:IR.

Lemma p3m_pos : forall i : nat, [0] [<] p3m i.
Proof.
 intros.
 unfold p3m in |- *.
 apply nexp_resp_pos.
 apply div_resp_pos.
  apply pos_three.
 apply pos_one.
Qed.

Lemma p3m_S : forall i : nat, p3m (S i) [=] p3m i [/]ThreeNZ.
Proof.
 intros.
 unfold p3m in |- *.
 astepl (([1] [/]ThreeNZ) [^]i[*] ([1] [/]ThreeNZ:IR)).
 rational.
Qed.

Hint Resolve p3m_S: algebra.

Lemma p3m_P : forall i : nat, p3m i [=] p3m (S i) [*]Three.
Proof.
 intros.
 Step_final (p3m i [/]ThreeNZ[*]Three).
Qed.

Lemma p3m_aux : forall i j : nat, p3m (S i) [^]j [=] p3m j[*]p3m i[^]j.
Proof.
 intros.
 unfold p3m in |- *.
 astepl (([1] [/]ThreeNZ) [^] (S i * j):IR).
 replace (S i * j) with (j + i * j).
  Step_final (([1] [/]ThreeNZ) [^]j[*] ([1] [/]ThreeNZ) [^] (i * j):IR).
 reflexivity.
Qed.

Lemma p3m_pow : forall i j : nat, p3m i[^]j [=] p3m (i * j).
Proof.
 intros.
 unfold p3m in |- *.
 algebra.
Qed.

Hint Resolve p3m_aux: algebra.

Lemma p3m_0 : p3m 0 [=] [1].
Proof.
 unfold p3m in |- *.
 simpl in |- *.
 algebra.
Qed.

Hint Resolve p3m_0: algebra.

Lemma third_pos : ZeroR [<] [1] [/]ThreeNZ.
Proof.
 apply recip_resp_pos.
 apply pos_three.
Qed.

Hint Resolve third_pos: algebra.

Lemma third_less_one : [1] [/]ThreeNZ [<] OneR.
Proof.
 apply pos_div_three'.
 apply pos_one.
Qed.

Hint Resolve third_less_one: algebra.

Lemma p3m_mon : forall i j : nat, i < j -> p3m j [<] p3m i.
Proof.
 intros.
 unfold p3m in |- *.
 apply small_nexp_resp_lt; algebra.
Qed.

Lemma p3m_mon' : forall i j : nat, i <= j -> p3m j [<=] p3m i.
Proof.
 intros.
 unfold p3m in |- *.
 apply small_nexp_resp_le; try apply less_leEq; algebra.
Qed.

Lemma p3m_small : forall i : nat, p3m i [<=] [1].
Proof.
 intro.
 astepr (p3m 0).
 apply p3m_mon'.
 auto with arith.
Qed.

Lemma p3m_smaller : forall i : nat, 0 < i -> p3m i [<=] Half.
Proof.
 intros.
 apply leEq_transitive with (p3m 1).
  apply p3m_mon'.
  auto with arith.
 unfold p3m in |- *.
 astepl ([1] [/]ThreeNZ:IR).
 unfold Half in |- *.
 apply less_leEq.
 apply recip_resp_less.
  apply pos_two.
 apply two_less_three.
Qed.

Definition chfun (k : nat -> nat) (a j i : nat) : nat :=
  match le_gt_dec i j with
  | left _  => k i
  | right _ => a
  end.

Lemma chfun_1 : forall k a j i, i <= j -> k i = chfun k a j i.
Proof.
 intros.
 unfold chfun in |- *.
 elim (le_gt_dec i j).
  auto.
 intro y.
 elim (proj1 (Nat.le_ngt _ _) H y).
Qed.

Lemma chfun_2 : forall k j a i, j < i -> a = chfun k a j i.
Proof.
 intros.
 unfold chfun in |- *.
 elim (le_gt_dec i j).
  intro y.
  elim (proj1 (Nat.le_ngt _ _) y H).
 auto.
Qed.

Lemma chfun_3 : forall k j a, (forall i, 1 <= k i /\ k i <= n) ->
 1 <= a -> a <= n -> forall i, 1 <= chfun k a j i /\ chfun k a j i <= n.
Proof.
 intros.
 unfold chfun in |- *.
 elim (le_gt_dec i j).
  auto.
 auto.
Qed.

Lemma chfun_4 : forall k j a, (forall i, k (S i) <= k i) ->
 a <= k j -> forall i, chfun k a j (S i) <= chfun k a j i.
Proof.
 intros.
 unfold chfun in |- *.
 elim (le_gt_dec i j); elim (le_gt_dec (S i) j); intros; auto.
  cut (i = j). intro.
   rewrite H1.
   auto.
  lia.
 lia.
Qed.

Definition Halfeps := Half[*]eps.

Lemma Halfeps_pos : [0] [<] Halfeps.
Proof.
 unfold Halfeps in |- *.
 apply mult_resp_pos.
  apply pos_half.
 apply eps_pos.
Qed.

Lemma Halfeps_Halfeps : forall x : IR, x[-]Halfeps[-]Halfeps [=] x[-]eps.
Proof.
 intros.
 unfold Halfeps in |- *.
 unfold Half in |- *.
 rational.
Qed.

Hint Resolve Halfeps_Halfeps: algebra.

Lemma Halfeps_eps : forall x y : IR, x[-]Halfeps [<=] y -> x[-]eps [<=] y.
Proof.
 intros.
 astepl (x[-]Halfeps[-]Halfeps).
 apply leEq_transitive with (x[-]Halfeps).
  apply less_leEq.
  apply shift_minus_less.
  apply shift_less_plus'.
  astepl ZeroR.
  apply Halfeps_pos.
 auto.
Qed.

Lemma Halfeps_trans : forall x y z : IR, x[-]Halfeps [<=] y -> y[-]Halfeps [<=] z -> x[-]eps [<=] z.
Proof.
 intros.
 astepl (x[-]Halfeps[-]Halfeps).
 apply leEq_transitive with (y[-]Halfeps).
  apply minus_resp_leEq.
  auto.
 auto.
Qed.

Lemma Key_1a : forall (i j : nat) (a t : IR), a[*] (t[*]p3m (S j)) [^]i [=] p3m i[*] (a[*] (t[*]p3m j) [^]i).
Proof.
 intros.
 astepl (a0[*] (t[^]i[*]p3m (S j) [^]i)).
 astepl (a0[*] (t[^]i[*] (p3m i[*]p3m j[^]i))).
 astepr (p3m i[*] (a0[*] (t[^]i[*]p3m j[^]i))).
 rational.
Qed.

Hint Resolve Key_1a: algebra.

Lemma Key_1b : forall k : nat, 1 <= k -> p3m k[*]eps [<=] Halfeps.
Proof.
 intros.
 unfold Halfeps in |- *.
 apply mult_resp_leEq_rht.
  apply p3m_smaller.
  auto.
 apply less_leEq; apply eps_pos.
Qed.

Lemma Key_1 : forall (i k j : nat) (ai ak t : IR),
 1 <= k -> k < i -> [0] [<=] ai -> [0] [<=] t -> ai[*] (t[*]p3m j) [^]i[-]eps [<=] ak[*] (t[*]p3m j) [^]k ->
 ai[*] (t[*]p3m (S j)) [^]i[-]Halfeps [<=] ak[*] (t[*]p3m (S j)) [^]k.
Proof.
 intros i k j ai ak t H H0 H1 H2 H3.
 apply leEq_transitive with (p3m k[*] (ai[*] (t[*]p3m j) [^]i) [-]p3m k[*]eps).
  apply minus_resp_leEq_both.
   astepl (p3m i[*] (ai[*] (t[*]p3m j) [^]i)).
   apply mult_resp_leEq_rht.
    apply less_leEq.
    apply p3m_mon; auto.
   astepl (ai[*][0]).
   apply mult_resp_leEq_lft; auto.
   apply nexp_resp_nonneg.
   apply mult_resp_nonneg; auto.
   apply less_leEq; apply p3m_pos.
  apply Key_1b; auto.
 astepl (p3m k[*] (ai[*] (t[*]p3m j) [^]i[-]eps)).
 astepr (p3m k[*] (ak[*] (t[*]p3m j) [^]k)).
 apply mult_resp_leEq_lft; auto.
 apply less_leEq; apply p3m_pos.
Qed.

Lemma Key_2 : forall (i k k' j : nat) (ai ak ak' t : IR),
 1 <= k -> k < i -> [0] [<=] ai -> [0] [<=] t ->
 ak[*] (t[*]p3m (S j)) [^]k[-]Halfeps [<=] ak'[*] (t[*]p3m (S j)) [^]k' ->
 ai[*] (t[*]p3m j) [^]i[-]eps [<=] ak[*] (t[*]p3m j) [^]k -> ai[*] (t[*]p3m (S j)) [^]i[-]eps [<=] ak'[*] (t[*]p3m (S j)) [^]k'.
Proof.
 intros.
 apply Halfeps_trans with (ak[*] (t[*]p3m (S j)) [^]k).
  apply Key_1; auto.
 auto.
Qed.

Lemma Key : {t : IR | [0] [<=] t | forall J, {k : nat -> nat |
 (forall i, 1 <= k i /\ k i <= n) /\ (forall i, k (S i) <= k i) /\
 (let k_0 := k 0 in a k_0[*]t[^]k_0 [=] a_0[-]eps) /\
 (forall j,  j <= J -> let k_j := k j in let r := t[*]p3m j in
  forall i, 1 <= i -> i <= n -> a i[*]r[^]i[-]eps [<=] a k_j[*]r[^]k_j)}}.
Proof.
 (* begin hide *)
 elim lem_1. intro t. intros H0 H1.
 elim H1. intros k_0 H2.
 elim H2. intros H3 H4.
 elim H4. intros H5 H6.
 elim H6. intros H7 H8.
 clear H6 H4 H2 H1.
 exists t.
  auto.
 intro J.
 induction  J as [| J HrecJ].
  exists (fun j : nat => k_0).
  split. auto.
   split. auto.
   split. auto.
   intros j H9 k_j r i H10 H11.
  unfold k_j, r in |- *.
  rewrite (proj1 (Nat.le_0_r _) H9).
  replace (p3m 0) with OneR.
   2: auto.
  astepr (a k_0[*] (t[^]k_0[*][1][^]k_0)).
  astepr (a k_0[*] (t[^]k_0[*][1])).
  astepr (a k_0[*]t[^]k_0).
  astepr (a_0[-]eps).
  apply minus_resp_leEq.
  astepl (a i[*] (t[^]i[*][1][^]i)).
  astepl (a i[*] (t[^]i[*][1])).
  astepl (a i[*]t[^]i); auto.
 elim HrecJ. intros k' H9.
 elim H9. intros H10 H11. elim H11. intros H12 H13. elim H13. intros H14 H15.
 clear H9 H11 H13.
 cut (0 < k' J). intro H16.
  2: elim (H10 J); auto.
 elim (maj_upto_eps IR (fun i : nat => a i[*] (t[*]p3m (S J)) [^]i) ( k' J) Halfeps H16 Halfeps_pos).
 intros k_SJ H17.
 elim H17. intros H18 H19. elim H19. intros H20 H21.
 clear H17 H19.
 exists (chfun k' k_SJ J).
 split. intro i.
  apply chfun_3. auto. auto.
    apply Nat.le_trans with (k' J); auto.
  elim (H10 J). auto.
  split.
  intro i. apply chfun_4; auto.
  split.
  replace (chfun k' k_SJ J 0) with (k' 0); auto.
 intros j H22 k_j r i H23 H24.
 unfold k_j, r in |- *.
 elim (le_lt_eq_dec _ _ H22); intro H26.
  replace (chfun k' k_SJ J j) with (k' j).
   apply H15; auto with arith.
  apply chfun_1; auto with arith.
 replace (chfun k' k_SJ J j) with k_SJ.
  rewrite H26.
  elim (le_lt_dec i (k' J)); intro H28.
   apply Halfeps_eps.
   auto.
  apply Key_2 with (k' J) (a (k' J)); auto.
 apply chfun_2.
 rewrite H26.
 auto.
Qed.
(* end hide *)

End Key_Lemma.

#[global]
Hint Resolve p3m_S p3m_P p3m_pow: algebra.
