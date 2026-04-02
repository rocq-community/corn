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

Require Export CoRN.ftc.RefLemma.
From Coq Require Import Lia.

(** printing integral %\ensuremath{\int_I}% #&int;<sub>I</sub># *)
(** printing Integral %\ensuremath{\int_I}% #&int;<sub>I</sub># *)

(* begin hide *)
Section Lemmas.

Let Sumx_wd_weird :
  forall n m : nat,
  m = S n ->
  forall (f : forall i : nat, i < n -> IR) (g : forall i : nat, i < m -> IR),
  (forall H, g 0 H [=] [0]) ->
  (forall (i : nat) H H', f i H [=] g (S i) H') -> Sumx f [=] Sumx g.
Proof.
 intro; induction  n as [| n Hrecn].
  do 2 intro.
  rewrite H.
  intros; simpl in |- *; apply eq_symmetric_unfolded.
  astepr (g 0 (Nat.lt_succ_diag_r 0)); algebra.
 do 2 intro; rewrite H; intros.
 astepl (Sumx (fun (i : nat) (Hi : i < n) => f i (Nat.lt_lt_succ_r _ _ Hi)) [+]f n (Nat.lt_succ_diag_r n)).
 Step_final (Sumx (fun (i : nat) (Hi : i < S n) => g i (Nat.lt_lt_succ_r _ _ Hi)) [+] g (S n) (Nat.lt_succ_diag_r (S n))).
Qed.

Lemma Sumx_weird_lemma :
 forall n m l : nat,
 l = S (m + n) ->
 forall (f1 : forall i : nat, i < n -> IR) (f2 : forall i : nat, i < m -> IR)
   (f3 : forall i : nat, i < l -> IR),
 nat_less_n_fun f1 ->
 nat_less_n_fun f2 ->
 nat_less_n_fun f3 ->
 (forall (i : nat) Hi Hi', f1 i Hi [=] f3 i Hi') ->
 (forall (i : nat) Hi Hi', f2 i Hi [=] f3 (S (n + i)) Hi') ->
 (forall Hi, f3 n Hi [=] [0]) -> Sumx f1[+]Sumx f2 [=] Sumx f3.
Proof.
 intros n m.
 induction  m as [| m Hrecm].
  intros l Hl.
  simpl in Hl; rewrite Hl; intros f1 f2 f3 Hf1 Hf2 Hf3 Hf1_f3 Hf2_f3 Hf3_f3.
  astepl (Sumx f1[+][0]).
  simpl in |- *; apply bin_op_wd_unfolded.
   apply Sumx_wd; intros; apply Hf1_f3.
  apply eq_symmetric_unfolded; apply Hf3_f3.
 set (l' := S m + n) in *.
 intros l Hl.
 rewrite Hl; intros f1 f2 f3 Hf1 Hf2 Hf3 Hf1_f3 Hf2_f3 Hf3_f3.
 apply eq_transitive_unfolded with
   (Sumx f1[+]Sumx (fun (i : nat) (Hi : i < m) => f2 i (Nat.lt_lt_succ_r _ _ Hi)) [+] f2 m (Nat.lt_succ_diag_r m)).
  simpl in |- *; algebra.
 astepr (Sumx (fun (i : nat) (Hi : i < l') => f3 i (Nat.lt_lt_succ_r _ _ Hi)) [+] f3 l' (Nat.lt_succ_diag_r l')).
 apply bin_op_wd_unfolded.
  apply Hrecm.
        unfold l' in |- *; auto.
       assumption.
      red in |- *; intros; apply Hf2; auto.
     red in |- *; intros; apply Hf3; auto.
    red in |- *; intros; apply Hf1_f3.
   red in |- *; intros; apply Hf2_f3.
  red in |- *; intros; apply Hf3_f3.
 unfold l' at 1 in |- *.
 cut (S (n + m) < S l'); [ intro | unfold l' in |- *; simpl in |- *; rewrite Nat.add_comm; auto ].
 apply eq_transitive_unfolded with (f3 _ H).
  apply Hf2_f3.
 apply Hf3; simpl in |- *; auto with arith.
Qed.

End Lemmas.
(* end hide *)

Section Integral.

(**
* Integral

Having proved the main properties of partitions and refinements, we
will define the integral of a continuous function [F] in the interval
[[a,b]] as the limit of the sequence of Sums of $F$ for even
partitions of increasing number of points.

%\begin{convention}% All throughout, [a,b] will be real numbers, the
interval [[a,b]] will be denoted by [I] and [F,G] will be
continuous functions in [I].
%\end{convention}%
*)

Variables a b : IR.
Hypothesis Hab : a [<=] b.
(* begin hide *)
Let I := Compact Hab.

Variable F : PartIR.
Hypothesis contF : Continuous_I Hab F.

Let contF' := contin_prop _ _ _ _ contF.
(* end hide *)

Section Darboux_Sum.

Definition integral_seq : nat -> IR.
Proof.
 intro n.
 apply Even_Partition_Sum with a b Hab F (S n).
  assumption.
 auto.
Defined.

Lemma Cauchy_Darboux_Seq : Cauchy_prop integral_seq.
Proof.
 red in |- *; intros e He.
 set (e' := e[/] _[//]mult_resp_ap_zero _ _ _ (two_ap_zero _) (max_one_ap_zero (b[-]a))) in *.
 cut ([0] [<] e').
  intro He'.
  set (d := proj1_sig2T _ _ _ (contF' e' He')) in *.
  generalize (proj2b_sig2T _ _ _ (contF' e' He'));
    generalize (proj2a_sig2T _ _ _ (contF' e' He')); fold d in |- *; intros H0 H1.
  set (N := ProjT1 (Archimedes (b[-]a[/] _[//]pos_ap_zero _ _ H0))) in *.
  exists N; intros.
  apply AbsIR_imp_AbsSmall.
  apply leEq_transitive with (Two[*]e'[*] (b[-]a)).
   rstepr (e'[*] (b[-]a) [+]e'[*] (b[-]a)).
   unfold integral_seq in |- *.
   elim (even_partition_refinement _ _ Hab _ _ (O_S m) (O_S N)).
   intros w Hw.
   elim Hw; clear Hw; intros Hw H2 H3.
   unfold Even_Partition_Sum in |- *.
   unfold I in |- *; apply second_refinement_lemma with (a := a) (b := b) (F := F) (contF := contF)
     (Q := Even_Partition Hab w Hw) (He := He') (He' := He').
      assumption.
     assumption.
    eapply leEq_wdl.
     2: apply eq_symmetric_unfolded; apply even_partition_Mesh.
    apply shift_div_leEq.
     apply pos_nring_S.
    apply shift_leEq_mult' with (pos_ap_zero _ _ H0).
     assumption.
    apply leEq_transitive with (nring (R:=IR) N).
     exact (ProjT2 (Archimedes (b[-]a[/] d[//]pos_ap_zero _ _ H0))).
    apply nring_leEq; apply le_S; assumption.
   eapply leEq_wdl.
    2: apply eq_symmetric_unfolded; apply even_partition_Mesh.
   apply shift_div_leEq.
    apply pos_nring_S.
   apply shift_leEq_mult' with (pos_ap_zero _ _ H0).
    assumption.
   apply leEq_transitive with (nring (R:=IR) N).
    exact (ProjT2 (Archimedes (b[-]a[/] d[//]pos_ap_zero _ _ H0))).
   apply nring_leEq; apply Nat.le_succ_diag_r.
  unfold e' in |- *.
  rstepl (e[*] (b[-]a) [/] _[//]max_one_ap_zero (b[-]a)).
  apply shift_div_leEq.
   apply pos_max_one.
  apply mult_resp_leEq_lft.
   apply lft_leEq_Max.
  apply less_leEq; assumption.
 unfold e' in |- *.
 apply div_resp_pos.
  apply mult_resp_pos.
   apply pos_two.
  apply pos_max_one.
 assumption.
Qed.

Definition integral := Lim (Build_CauchySeq _ _ Cauchy_Darboux_Seq).

End Darboux_Sum.

Section Integral_Thm.

(**
The following shows that in fact the integral of [F] is the limit of
any sequence of partitions of mesh converging to 0.

%\begin{convention}% Let [e] be a positive real number and [P] be a
partition of [I] with [n] points and mesh smaller than the
modulus of continuity of [F] for [e].  Let [fP] be a choice of points
respecting [P].
%\end{convention}%
*)

Variable n : nat.

Variable P : Partition Hab n.

Variable e : IR.
Hypothesis He : [0] [<] e.

(* begin hide *)
Let d := proj1_sig2T _ _ _ (contF' e He).
(* end hide *)

Hypothesis HmeshP : Mesh P [<] d.

Variable fP : forall i : nat, i < n -> IR.
Hypothesis HfP : Points_in_Partition P fP.
Hypothesis HfP' : nat_less_n_fun fP.

Hypothesis incF : included (Compact Hab) (Dom F).

Lemma partition_Sum_conv_integral : AbsIR (Partition_Sum HfP incF[-]integral) [<=] e[*] (b[-]a).
Proof.
 apply leEq_wdl with (AbsIR (Partition_Sum HfP (contin_imp_inc _ _ _ _ contF) [-]integral)).
  apply leEq_wdl with (AbsIR (Lim (Cauchy_const (Partition_Sum HfP (contin_imp_inc _ _ _ _ contF))) [-]
    integral)).
   2: apply AbsIR_wd; apply cg_minus_wd; [ apply eq_symmetric_unfolded; apply Lim_const | algebra ].
  unfold integral in |- *.
  apply leEq_wdl with (AbsIR (Lim (Build_CauchySeq _ _ (Cauchy_minus (Cauchy_const
    (Partition_Sum HfP (contin_imp_inc _ _ _ _ contF))) (Build_CauchySeq _ _ Cauchy_Darboux_Seq))))).
   2: apply AbsIR_wd; apply Lim_minus.
  eapply leEq_wdl.
   2: apply Lim_abs.
  astepr ([0][+]e[*] (b[-]a)); apply shift_leEq_plus; apply approach_zero_weak.
  intros e' He'.
  set (ee := e'[/] _[//]max_one_ap_zero (b[-]a)) in *.
  apply leEq_transitive with (ee[*] (b[-]a)).
   cut ([0] [<] ee).
    intro Hee.
    set (d' := proj1_sig2T _ _ _ (contF' _ Hee)) in *.
    generalize (proj2b_sig2T _ _ _ (contF' _ Hee));
      generalize (proj2a_sig2T _ _ _ (contF' _ Hee)); fold d' in |- *; intros Hd' Hd'0.
    elim (Archimedes (b[-]a[/] _[//]pos_ap_zero _ _ Hd')); intros k Hk.
    apply shift_minus_leEq.
    eapply leEq_wdr.
     2: apply cag_commutes_unfolded.
    apply str_seq_leEq_so_Lim_leEq.
    exists k; simpl in |- *; intros.
    unfold integral_seq, Even_Partition_Sum in |- *.
    apply refinement_lemma with contF He Hee.
       assumption.
      fold d' in |- *.
      eapply less_wdl.
       2: apply eq_symmetric_unfolded; apply even_partition_Mesh.
      apply shift_div_less.
       apply pos_nring_S.
      apply shift_less_mult' with (pos_ap_zero _ _ Hd').
       assumption.
      apply leEq_less_trans with (nring (R:=IR) k).
       assumption.
      apply nring_less; auto with arith.
     assumption.
    red in |- *; do 3 intro.
    rewrite H0; intros; simpl in |- *; algebra.
   unfold ee in |- *; apply div_resp_pos.
    apply pos_max_one.
   assumption.
  unfold ee in |- *.
  rstepl (e'[*] (b[-]a[/] _[//]max_one_ap_zero (b[-]a))).
  rstepr (e'[*][1]).
  apply mult_resp_leEq_lft.
   apply shift_div_leEq.
    apply pos_max_one.
   astepr (Max (b[-]a) [1]); apply lft_leEq_Max.
  apply less_leEq; assumption.
 apply AbsIR_wd; apply cg_minus_wd.
  unfold Partition_Sum in |- *.
  apply Sumx_wd; intros.
  algebra.
 algebra.
Qed.

End Integral_Thm.

End Integral.

Section Basic_Properties.

(**
The usual extensionality and strong extensionality results hold.
*)

Variables a b : IR.
Hypothesis Hab : a [<=] b.
(* begin hide *)
Let I := Compact Hab.
(* end hide *)

Notation Integral := (integral _ _ Hab).

Section Well_Definedness.

Variables F G : PartIR.
Hypothesis contF : Continuous_I Hab F.
Hypothesis contG : Continuous_I Hab G.

Lemma integral_strext : Integral F contF [#] Integral G contG ->
 {x : IR | I x | forall Hx Hx', F x Hx [#] G x Hx'}.
Proof.
 intro H.
 unfold integral in H.
 elim (Lim_ap_imp_seq_ap' _ _ H); intros N HN; clear H.
 simpl in HN.
 unfold integral_seq, Even_Partition_Sum, Partition_Sum in HN.
 set (f' := fun (i : nat) (H : i < S N) => Part F _ (contin_imp_inc _ _ _ _ contF _
   (compact_partition_lemma _ _ Hab _ (O_S N) _ (Nat.lt_le_incl _ _ H))) [*]
     (Even_Partition Hab _ (O_S N) _ H[-] Even_Partition Hab _ (O_S N) i (Nat.lt_le_incl _ _ H))) in *.
 set (g' := fun (i : nat) (H : i < S N) => Part G _ (contin_imp_inc _ _ _ _ contG _
   (compact_partition_lemma _ _ Hab _ (O_S N) _ (Nat.lt_le_incl _ _ H))) [*]
     (Even_Partition Hab _ (O_S N) _ H[-] Even_Partition Hab _ (O_S N) i (Nat.lt_le_incl _ _ H))) in *.
 cut (nat_less_n_fun f'); intros.
  cut (nat_less_n_fun g'); intros.
   cut (Sumx f' [#] Sumx g'). intros H1.
    elim (Sumx_strext _ _ _ _ H H0 H1).
    intros n Hn.
    elim Hn; clear Hn; intros Hn H'.
    exists (a[+]nring n[*] (b[-]a[/] nring _[//]nring_ap_zero' _ _ (O_S N))).
     unfold I in |- *; apply compact_partition_lemma; auto.
     apply Nat.lt_le_incl; assumption.
    intros.
    elim (bin_op_strext_unfolded _ _ _ _ _ _ H'); clear H'; intro.
     eapply ap_wdl_unfolded.
      eapply ap_wdr_unfolded.
       apply a0.
      algebra.
     algebra.
    exfalso; generalize b0; exact (ap_irreflexive_unfolded _ _).
   eapply ap_wdl_unfolded.
    eapply ap_wdr_unfolded.
     apply HN.
    unfold g', Partition_imp_points in |- *; apply Sumx_wd; intros; simpl in |- *; rational.
   unfold f', Partition_imp_points in |- *; apply Sumx_wd; intros; simpl in |- *; rational.
  do 3 intro.
  rewrite H0; unfold g' in |- *; intros; algebra.
 do 3 intro.
 rewrite H; unfold f' in |- *; intros; algebra.
Qed.

Lemma integral_strext' : forall c d Hcd HF1 HF2,
 integral a b Hab F HF1 [#] integral c d Hcd F HF2 -> a [#] c or b [#] d.
Proof.
 intros c d Hcd HF1 HF2 H.
 clear contF contG.
 unfold integral in H.
 elim (Lim_strext _ _ H).
 clear H; intros N HN.
 simpl in HN.
 unfold integral_seq, Even_Partition_Sum, Partition_Sum in HN.
 set (f1 := fun (i : nat) (Hi : i < S N) => Part _ _ (contin_imp_inc _ _ _ _ HF1 _
   (Pts_part_lemma _ _ _ _ _ _ (Partition_imp_points_1 _ _ _ _ (Even_Partition Hab _ (O_S N))) i
     Hi)) [*] (Even_Partition Hab _ (O_S N) _ Hi[-]
       Even_Partition Hab _ (O_S N) _ (Nat.lt_le_incl _ _ Hi))) in *.
 set (f2 := fun (i : nat) (Hi : i < S N) => Part _ _ (contin_imp_inc _ _ _ _ HF2 _
   (Pts_part_lemma _ _ _ _ _ _ (Partition_imp_points_1 _ _ _ _ (Even_Partition Hcd _ (O_S N))) i
     Hi)) [*] (Even_Partition Hcd _ (O_S N) _ Hi[-]
       Even_Partition Hcd _ (O_S N) _ (Nat.lt_le_incl _ _ Hi))) in *.
 cut (nat_less_n_fun f1); intros.
  cut (nat_less_n_fun f2); intros.
   elim (Sumx_strext _ _ _ _ H H0 HN).
   clear H0 H HN; intros i Hi.
   elim Hi; clear Hi; intros Hi Hi'.
   unfold f1, f2 in Hi'; clear f1 f2.
   elim (bin_op_strext_unfolded _ _ _ _ _ _ Hi'); clear Hi'; intro.
    assert (H := pfstrx _ _ _ _ _ _ a0).
    clear a0; simpl in H.
    elim (bin_op_strext_unfolded _ _ _ _ _ _ H); clear H; intro.
     left; auto.
    elim (bin_op_strext_unfolded _ _ _ _ _ _ b0); clear b0; intro.
     exfalso; generalize a0; apply ap_irreflexive_unfolded.
    elim (div_strext _ _ _ _ _ _ _ b0); clear b0; intro.
     elim (cg_minus_strext _ _ _ _ _ a0); clear a0; intro.
      right; auto.
     left; auto.
    exfalso; generalize b0; apply ap_irreflexive_unfolded.
   elim (cg_minus_strext _ _ _ _ _ b0); clear b0; intro.
    simpl in a0.
    elim (bin_op_strext_unfolded _ _ _ _ _ _ a0); clear a0; intro.
     left; auto.
    elim (bin_op_strext_unfolded _ _ _ _ _ _ b0); clear b0; intro.
     exfalso; generalize a0; apply ap_irreflexive_unfolded.
    elim (div_strext _ _ _ _ _ _ _ b0); clear b0; intro.
     elim (cg_minus_strext _ _ _ _ _ a0); clear a0; intro.
      right; auto.
     left; auto.
    exfalso; generalize b0; apply ap_irreflexive_unfolded.
   elim (bin_op_strext_unfolded _ _ _ _ _ _ b0); clear b0; intro.
    left; auto.
   elim (bin_op_strext_unfolded _ _ _ _ _ _ b0); clear b0; intro.
    exfalso; generalize a0; apply ap_irreflexive_unfolded.
   elim (div_strext _ _ _ _ _ _ _ b0); clear b0; intro.
    elim (cg_minus_strext _ _ _ _ _ a0); clear a0; intro.
     right; auto.
    left; auto.
   elim (bin_op_strext_unfolded _ _ _ _ _ _ b0); clear b0; intro.
    exfalso; generalize a0; apply ap_irreflexive_unfolded.
   exfalso; generalize b0; apply ap_irreflexive_unfolded.
  red in |- *.
  do 3 intro.
  rewrite H0; clear H0; intros.
  unfold f2 in |- *.
  algebra.
 red in |- *.
 do 3 intro.
 rewrite H; clear H; intros.
 unfold f1 in |- *.
 algebra.
Qed.

Lemma integral_wd : Feq (Compact Hab) F G -> Integral F contF [=] Integral G contG.
Proof.
 intro H.
 apply not_ap_imp_eq.
 intro H0.
 elim (integral_strext H0).
 intros x H1 H2.
 elim H; intros H3 H4.
 inversion_clear H4.
 generalize (H2 (contin_imp_inc _ _ _ _ contF x H1) (contin_imp_inc _ _ _ _ contG x H1)).
 apply eq_imp_not_ap.
 auto.
Qed.

Lemma integral_wd' : forall a' b' Hab' contF',
 a [=] a' -> b [=] b' -> Integral F contF [=] integral a' b' Hab' F contF'.
Proof.
 intros.
 unfold integral in |- *.
 apply Lim_wd'.
 intro; simpl in |- *.
 unfold integral_seq, Even_Partition_Sum, Partition_Sum in |- *.
 apply Sumx_wd; intros; apply mult_wd.
  apply pfwdef; simpl in |- *; algebra.
 simpl in |- *.
 repeat first [ apply cg_minus_wd | apply bin_op_wd_unfolded | apply mult_wd
   | apply div_wd ]; algebra.
Qed.

End Well_Definedness.

Section Linearity_and_Monotonicity.

Opaque Even_Partition.

(**
The integral is a linear and monotonous function; in order to prove these facts we also need the important equalities $\int_a^bdx=b-a$#&int;<sub>a</sub><sup>b</sup>dx=b-a# and $\int_a^af(x)dx=0$#&int;<sub>a</sub><sup>a</sup>=0#.
*)

Lemma integral_one : forall H, Integral ( [-C-] [1]) H [=] b[-]a.
Proof.
 intro.
 unfold integral in |- *.
 eapply eq_transitive_unfolded.
  2: apply eq_symmetric_unfolded; apply Lim_const.
 apply Lim_wd'.
 intro; simpl in |- *.
 unfold integral_seq, Even_Partition_Sum, Partition_Sum in |- *.
 eapply eq_transitive_unfolded.
  apply Mengolli_Sum with (f := fun (i : nat) (Hi : i <= S n) => Even_Partition Hab _ (O_S n) i Hi).
   red in |- *; intros.
   apply prf1; auto.
  intros; simpl in |- *; rational.
 apply cg_minus_wd; [ apply finish | apply start ].
Qed.

Variables F G : PartIR.
Hypothesis contF : Continuous_I Hab F.
Hypothesis contG : Continuous_I Hab G.

Lemma integral_comm_scal : forall (c : IR) Hf', Integral (c{**}F) Hf' [=] c[*]Integral F contF.
Proof.
 intros.
 apply eq_transitive_unfolded with (Lim (Cauchy_const c) [*]Integral F contF);
   unfold integral in |- *.
  eapply eq_transitive_unfolded.
   2: apply Lim_mult.
  apply Lim_wd'; intro; simpl in |- *.
  unfold integral_seq, Even_Partition_Sum, Partition_Sum in |- *.
  eapply eq_transitive_unfolded.
   2: apply Sumx_comm_scal'.
  apply Sumx_wd; intros; simpl in |- *; rational.
 apply mult_wdl.
 apply eq_symmetric_unfolded; apply Lim_const.
Qed.

Lemma integral_plus : forall Hfg, Integral (F{+}G) Hfg [=] Integral F contF[+]Integral G contG.
Proof.
 intros.
 unfold integral in |- *.
 eapply eq_transitive_unfolded.
  2: apply Lim_plus.
 apply Lim_wd'; intro; simpl in |- *.
 unfold integral_seq, Even_Partition_Sum, Partition_Sum in |- *.
 eapply eq_transitive_unfolded.
  2: apply eq_symmetric_unfolded; apply Sumx_plus_Sumx.
 apply Sumx_wd; intros; simpl in |- *; rational.
Qed.

Transparent Even_Partition.

Lemma integral_empty : a [=] b -> Integral F contF [=] [0].
Proof.
 intros.
 unfold integral in |- *.
 eapply eq_transitive_unfolded.
  2: apply eq_symmetric_unfolded; apply Lim_const.
 apply Lim_wd'.
 intros; simpl in |- *.
 unfold integral_seq, Even_Partition_Sum, Partition_Sum in |- *.
 apply eq_transitive_unfolded with (Sumx (fun (i : nat) (H : i < S n) => ZeroR)).
  apply Sumx_wd; intros; simpl in |- *.
  eapply eq_transitive_unfolded.
   apply dist_2a.
  apply x_minus_x.
  apply mult_wdr.
  apply bin_op_wd_unfolded.
   algebra.
  astepl (nring (S i) [*] (b[-]b[/] _[//]nring_ap_zero' _ _ (O_S n))).
  astepr (nring i[*] (b[-]b[/] _[//]nring_ap_zero' _ _ (O_S n))).
  rational.
 eapply eq_transitive_unfolded.
  apply sumx_const.
 algebra.
Qed.

End Linearity_and_Monotonicity.

Section Linearity_and_Monotonicity'.

Variables F G : PartIR.
Hypothesis contF : Continuous_I Hab F.
Hypothesis contG : Continuous_I Hab G.

(**
%\begin{convention}% Let [alpha, beta : IR] and assume that
[h := alpha{**}F{+}beta{**}G] is continuous.
%\end{convention}%
*)

Variables alpha beta : IR.
(* begin hide *)
Let h := alpha{**}F{+}beta{**}G.
(* end hide *)
Hypothesis contH : Continuous_I Hab h.

Lemma linear_integral : Integral h contH [=] alpha[*]Integral F contF[+]beta[*]Integral G contG.
Proof.
 assert (H : Continuous_I Hab (alpha{**}F)). Contin.
  assert (H0 : Continuous_I Hab (beta{**}G)). Contin.
  apply eq_transitive_unfolded with (Integral _ H[+]Integral _ H0).
  unfold h in |- *.
  apply integral_plus.
 apply bin_op_wd_unfolded; apply integral_comm_scal.
Qed.

Lemma monotonous_integral : (forall x, I x -> forall Hx Hx', F x Hx [<=] G x Hx') ->
 Integral F contF [<=] Integral G contG.
Proof.
 intros.
 unfold integral in |- *.
 apply Lim_leEq_Lim.
 intro n; simpl in |- *.
 unfold integral_seq, Even_Partition_Sum, Partition_Sum in |- *.
 apply Sumx_resp_leEq; intros i Hi.
 apply mult_resp_leEq_rht.
  apply H.
  Opaque nring.
  unfold I, Partition_imp_points in |- *; simpl in |- *.
  apply compact_partition_lemma; auto with arith.
 apply leEq_transitive with (AntiMesh (Even_Partition Hab (S n) (O_S n))).
  apply AntiMesh_nonneg.
 apply AntiMesh_lemma.
Qed.

Transparent nring.

End Linearity_and_Monotonicity'.

Section Corollaries.

Variables F G : PartIR.
Hypothesis contF : Continuous_I Hab F.
Hypothesis contG : Continuous_I Hab G.

(**
As corollaries we can calculate integrals of group operations applied to functions.
*)

Lemma integral_const : forall c H, Integral ( [-C-]c)H [=] c[*] (b[-]a).
Proof.
 intros.
 assert (H0 : Continuous_I Hab (c{**}[-C-][1])). Contin.
  apply eq_transitive_unfolded with (Integral _ H0).
  apply integral_wd; FEQ.
 eapply eq_transitive_unfolded.
  apply integral_comm_scal with (contF := Continuous_I_const a b Hab [1]).
 apply mult_wdr.
 apply integral_one.
Qed.

Lemma integral_minus : forall H, Integral (F{-}G) H [=] Integral F contF[-]Integral G contG.
Proof.
 intro.
 assert (H0 : Continuous_I Hab ([1]{**}F{+}[--][1]{**}G)). Contin.
  apply eq_transitive_unfolded with (Integral _ H0).
  apply integral_wd; FEQ.
 eapply eq_transitive_unfolded.
  apply linear_integral with (contF := contF) (contG := contG).
 rational.
Qed.

Lemma integral_inv : forall H, Integral ( {--}F) H [=] [--] (Integral F contF).
Proof.
 intro.
 assert (H0 : Continuous_I Hab ([0]{**}F{+}[--][1]{**}F)). Contin.
  apply eq_transitive_unfolded with (Integral _ H0).
  apply integral_wd; FEQ.
 eapply eq_transitive_unfolded.
  apply linear_integral with (contF := contF) (contG := contF).
 rational.
Qed.

(**
We can also bound integrals by bounding the integrated functions.
*)

Lemma lb_integral : forall c, (forall x, I x -> forall Hx, c [<=] F x Hx) -> c[*] (b[-]a) [<=] Integral F contF.
Proof.
 intros.
 apply leEq_wdl with (Integral _ (Continuous_I_const a b Hab c)).
  2: apply integral_const.
 apply monotonous_integral.
 simpl in |- *; auto.
Qed.

Lemma ub_integral : forall c, (forall x, I x -> forall Hx, F x Hx [<=] c) -> Integral F contF [<=] c[*] (b[-]a).
Proof.
 intros.
 apply leEq_wdr with (Integral _ (Continuous_I_const a b Hab c)).
  2: apply integral_const.
 apply monotonous_integral.
 simpl in |- *; auto.
Qed.

Lemma integral_leEq_norm : AbsIR (Integral F contF) [<=] Norm_Funct contF[*] (b[-]a).
Proof.
 simpl in |- *; unfold ABSIR in |- *.
 apply Max_leEq.
  apply ub_integral.
  intros; eapply leEq_transitive.
   apply leEq_AbsIR.
  unfold I in |- *; apply norm_bnd_AbsIR; assumption.
 astepr ( [--][--] (Norm_Funct contF[*] (b[-]a))).
 astepr ( [--] ( [--] (Norm_Funct contF) [*] (b[-]a))).
 apply inv_resp_leEq.
 apply lb_integral.
 intros; astepr ( [--][--] (Part F x Hx)).
 apply inv_resp_leEq.
 eapply leEq_transitive.
  apply inv_leEq_AbsIR.
 unfold I in |- *; apply norm_bnd_AbsIR; assumption.
Qed.

End Corollaries.

Section Integral_Sum.

(**
We now relate the sum of integrals in adjoining intervals to the
integral over the union of those intervals.

%\begin{convention}% Let [c] be a real number such that
$c\in[a,b]$#c&isin;[a,b]#.
%\end{convention}%
*)

Variable F : PartIR.

Variable c : IR.

Hypothesis Hac : a [<=] c.
Hypothesis Hcb : c [<=] b.

Hypothesis Hab' : Continuous_I Hab F.
Hypothesis Hac' : Continuous_I Hac F.
Hypothesis Hcb' : Continuous_I Hcb F.

Section Partition_Join.

(**
We first prove that every pair of partitions, one of [[a,c]]
and another of [[c,b]] defines a partition of [[a,b]] the mesh
of which is less or equal to the maximum of the mesh of the original
partitions (actually it is equal, but we don't need the other
inequality).

%\begin{convention}% Let [P,Q] be partitions respectively of
[[a,c]] and [[c,b]] with [n] and [m] points.
%\end{convention}%
*)

Variables n m : nat.
Variable P : Partition Hac n.
Variable Q : Partition Hcb m.

(* begin hide *)
Lemma partition_join_aux : forall i n m, n < i -> i <= S (n + m) -> i - S n <= m.
Proof.
 intros; lia.
Qed.
(* end hide *)

Definition partition_join_fun : forall i, i <= S (n + m) -> IR.
Proof.
 intros.
 elim (le_lt_dec i n); intros.
  apply (P i a0).
 cut (i - S n <= m); [ intro | apply partition_join_aux; assumption ].
 apply (Q _ H0).
Defined.

(* begin hide *)
Lemma pjf_1 : forall (i : nat) Hi Hi', partition_join_fun i Hi [=] P i Hi'.
Proof.
 intros; unfold partition_join_fun in |- *.
 elim le_lt_dec; intro; simpl in |- *.
  apply prf1; auto.
 exfalso; apply Nat.le_ngt with i n; auto.
Qed.

Lemma pjf_2 : forall (i : nat) Hi, i = n -> partition_join_fun i Hi [=] c.
Proof.
 intros; unfold partition_join_fun in |- *.
 generalize Hi; clear Hi.
 rewrite H; clear H; intro.
 elim le_lt_dec; intro; simpl in |- *.
  apply finish.
 exfalso; apply Nat.lt_irrefl with n; auto.
Qed.

Lemma pjf_2' : forall (i : nat) Hi, i = S n -> partition_join_fun i Hi [=] c.
Proof.
 intros; unfold partition_join_fun in |- *.
 generalize Hi; clear Hi.
 rewrite H; clear H; intro.
 elim le_lt_dec; intro; simpl in |- *.
  exfalso; apply (Nat.nle_succ_diag_l _ a0).
 cut (forall H, Q (n - n) H [=] c); auto.
 cut (n - n = 0); [ intro | auto with arith ].
 rewrite H; intros; apply start.
Qed.

Lemma pjf_3 : forall (i j : nat) Hi Hj,
 n < i -> j = i - S n -> partition_join_fun i Hi [=] Q j Hj.
Proof.
 intros; unfold partition_join_fun in |- *.
 generalize Hj; rewrite H0; clear Hj; intros.
 elim le_lt_dec; intro; simpl in |- *.
  exfalso; apply Nat.le_ngt with i n; auto.
 apply prf1; auto.
Qed.

Lemma partition_join_prf1 : forall i j : nat,
 i = j -> forall Hi Hj, partition_join_fun i Hi [=] partition_join_fun j Hj.
Proof.
 intros.
 unfold partition_join_fun in |- *.
 elim (le_lt_dec i n); elim (le_lt_dec j n); intros; simpl in |- *.
    apply prf1; auto.
   exfalso; apply Nat.le_ngt with i n.
    assumption.
   rewrite H; assumption.
  exfalso; apply Nat.le_ngt with j n.
   assumption.
  rewrite <- H; assumption.
 apply prf1; auto.
Qed.

Lemma partition_join_prf2 : forall (i : nat) H H',
 partition_join_fun i H [<=] partition_join_fun (S i) H'.
Proof.
 intros.
 unfold partition_join_fun in |- *.
 elim (le_lt_dec i n); elim (le_lt_dec (S i) n); intros; simpl in |- *.
    apply prf2.
   cut (n = i); [ intro | apply Nat.le_antisymm; auto with arith ].
   change (P i a0 [<=] Q (S i - S n) (partition_join_aux _ _ _ b0 H')) in |- *.
   generalize H' a0 b0; clear H' a0 b0.
   rewrite <- H0; intros.
   apply eq_imp_leEq.
   apply eq_transitive_unfolded with c.
    apply finish.
   apply eq_transitive_unfolded with (Q 0 (Nat.le_0_l _)).
    apply eq_symmetric_unfolded; apply start.
   apply prf1; auto with arith.
  exfalso; apply Nat.le_ngt with n i; auto with arith.
 cut (i - n = S (i - S n)); [ intro | lia ].
 cut (S (i - S n) <= m); [ intro | lia ].
 apply leEq_wdr with (Q _ H1).
  apply prf2.
 apply prf1; auto.
Qed.

Lemma partition_join_start : forall H, partition_join_fun 0 H [=] a.
Proof.
 intro.
 unfold partition_join_fun in |- *.
 elim (le_lt_dec 0 n); intro; simpl in |- *.
  apply start.
 exfalso; apply (Nat.nlt_0_r _ b0).
Qed.

Lemma partition_join_finish : forall H, partition_join_fun (S (n + m)) H [=] b.
Proof.
 intro.
 unfold partition_join_fun in |- *.
 elim le_lt_dec; intro; simpl in |- *.
  exfalso; apply Nat.nle_succ_diag_l with n; apply Nat.le_trans with (S (n + m)); auto with arith.
 apply eq_transitive_unfolded with (Q _ (le_n _)).
  apply prf1; auto with arith.
 apply finish.
Qed.

Definition partition_join : Partition Hab (S (n + m)).
Proof.
 intros.
 apply Build_Partition with partition_join_fun.
    exact partition_join_prf1.
   exact partition_join_prf2.
  exact partition_join_start.
 exact partition_join_finish.
Defined.
(* end hide *)

(**
%\begin{convention}% [fP, fQ] are choices of points respecting [P] and [Q].
%\end{convention}%
*)

Variable fP : forall i : nat, i < n -> IR.
Hypothesis HfP : Points_in_Partition P fP.
Hypothesis HfP' : nat_less_n_fun fP.

Variable fQ : forall i : nat, i < m -> IR.
Hypothesis HfQ : Points_in_Partition Q fQ.
Hypothesis HfQ' : nat_less_n_fun fQ.

(* begin hide *)
Lemma partition_join_aux' : forall i n m, n < i -> i < S (n + m) -> i - S n < m.
Proof.
 intros; lia.
Qed.
(* end hide *)

Definition partition_join_pts : forall i, i < S (n + m) -> IR.
Proof.
 intros.
 elim (le_lt_dec i n); intros.
  elim (le_lt_eq_dec _ _ a0); intro.
   apply (fP i a1).
  apply c.
 cut (i - S n < m); [ intro | apply partition_join_aux'; assumption ].
 apply (fQ _ H0).
Defined.

(* begin hide *)
Lemma pjp_1 : forall (i : nat) Hi Hi', partition_join_pts i Hi [=] fP i Hi'.
Proof.
 intros; unfold partition_join_pts in |- *.
 elim le_lt_dec; intro; simpl in |- *.
  elim le_lt_eq_dec; intro; simpl in |- *.
   algebra.
  exfalso; rewrite b0 in Hi'; apply (Nat.lt_irrefl _ Hi').
 exfalso; apply Nat.le_ngt with i n; auto with arith.
Qed.

Lemma pjp_2 : forall (i : nat) Hi, i = n -> partition_join_pts i Hi [=] c.
Proof.
 intros; unfold partition_join_pts in |- *.
 elim le_lt_dec; intro; simpl in |- *.
  elim le_lt_eq_dec; intro; simpl in |- *.
   exfalso; rewrite H in a1; apply (Nat.lt_irrefl _ a1).
  algebra.
 exfalso; rewrite H in b0; apply (Nat.lt_irrefl _ b0).
Qed.

Lemma pjp_3 : forall (i : nat) Hi Hi',
  n < i -> partition_join_pts i Hi [=] fQ (i - S n) Hi'.
Proof.
 intros; unfold partition_join_pts in |- *.
 elim le_lt_dec; intro; simpl in |- *.
  exfalso; apply Nat.le_ngt with i n; auto.
 cut (fQ _ (partition_join_aux' _ _ _ b0 Hi) [=] fQ _ Hi').
  2: apply HfQ'; auto.
 algebra.
Qed.
(* end hide *)

Lemma partition_join_Pts_in_partition : Points_in_Partition partition_join partition_join_pts.
Proof.
 red in |- *; intros.
 rename Hi into H.
 cut (forall H', compact (partition_join i (Nat.lt_le_incl _ _ H)) (partition_join (S i) H) H'
   (partition_join_pts i H)); auto.
 unfold partition_join in |- *; simpl in |- *.
 unfold partition_join_fun in |- *.
 elim le_lt_dec; elim le_lt_dec; intros; simpl in |- *.
    elim (le_lt_eq_dec _ _ a1); intro.
     elim (HfP _ a2); intros.
     apply compact_wd with (fP i a2).
      2: apply eq_symmetric_unfolded; apply pjp_1.
     split.
      eapply leEq_wdl.
       apply a3.
      apply prf1; auto.
     eapply leEq_wdr.
      apply b0.
     apply prf1; auto.
    exfalso; clear H'; rewrite b0 in a0; apply (Nat.nle_succ_diag_l _ a0).
   cut (i = n); [ intro | clear H'; apply Nat.le_antisymm; auto with arith ].
   generalize H a0 b0 H'; clear H' a0 b0 H; rewrite H0; intros.
   apply compact_wd with c.
    2: apply eq_symmetric_unfolded; apply pjp_2; auto.
   split.
    apply eq_imp_leEq; apply finish.
   apply eq_imp_leEq; apply eq_symmetric_unfolded.
   cut (forall H, Q (n - n) H [=] c); auto.
   cut (n - n = 0); [ intro | auto with arith ].
   rewrite H1; intros; apply start.
  exfalso; apply Nat.le_ngt with n i; auto with arith.
 elim (HfQ _ (partition_join_aux' _ _ _ b1 H)); intros.
 apply compact_wd with (fQ _ (partition_join_aux' _ _ _ b1 H)).
  2: apply eq_symmetric_unfolded; apply pjp_3; assumption.
 split.
  eapply leEq_wdl.
   apply a0.
  apply prf1; auto.
 eapply leEq_wdr.
  apply b2.
 apply prf1; rewrite <- Nat.sub_succ_l; auto with arith.
Qed.

Lemma partition_join_Pts_wd : forall i j,
 i = j -> forall Hi Hj, partition_join_pts i Hi [=] partition_join_pts j Hj.
Proof.
 intros.
 elim (le_lt_dec i n); intro.
  elim (le_lt_eq_dec _ _ a0); intro.
   cut (j < n); [ intro | rewrite <- H; assumption ].
   eapply eq_transitive_unfolded.
    apply pjp_1 with (Hi' := a1).
   eapply eq_transitive_unfolded.
    2: apply eq_symmetric_unfolded; apply pjp_1 with (Hi' := H0).
   apply HfP'; auto.
  cut (j = n); [ intro | rewrite <- H; assumption ].
  eapply eq_transitive_unfolded.
   apply pjp_2; auto.
  eapply eq_transitive_unfolded.
   2: apply eq_symmetric_unfolded; apply pjp_2; auto.
  algebra.
 cut (n < j); [ intro | rewrite <- H; assumption ].
 cut (i - S n < m); [ intro | lia ].
 cut (j - S n < m); [ intro | lia ].
 eapply eq_transitive_unfolded.
  apply pjp_3 with (Hi' := H1); assumption.
 eapply eq_transitive_unfolded.
  2: apply eq_symmetric_unfolded; apply pjp_3 with (Hi' := H2); assumption.
 apply HfQ'; auto.
Qed.

Lemma partition_join_Sum_lemma :
 Partition_Sum HfP (contin_imp_inc _ _ _ _ Hac') [+] Partition_Sum HfQ (contin_imp_inc _ _ _ _ Hcb') [=]
 Partition_Sum partition_join_Pts_in_partition (contin_imp_inc _ _ _ _ Hab').
Proof.
 unfold Partition_Sum in |- *; apply Sumx_weird_lemma.
       auto with arith.
      Opaque partition_join.
      red in |- *; intros; apply mult_wd; algebra; apply cg_minus_wd; apply prf1; auto.
     red in |- *; intros; apply mult_wd; algebra; apply cg_minus_wd; apply prf1; auto.
    red in |- *; intros; apply mult_wd; try apply cg_minus_wd; try apply pfwdef; algebra.
      apply partition_join_Pts_wd; auto.
     apply prf1; auto.
    apply prf1; auto.
   Transparent partition_join.
   intros; apply mult_wd.
    apply pfwdef; apply eq_symmetric_unfolded; apply pjp_1.
   apply cg_minus_wd; simpl in |- *.
    unfold partition_join_fun in |- *; elim le_lt_dec; simpl in |- *; intro; [ apply prf1; auto
      | exfalso; apply Nat.le_ngt with n i; auto with arith ].
   unfold partition_join_fun in |- *; elim le_lt_dec; simpl in |- *; intro; [ apply prf1; auto
     | exfalso; apply Nat.le_ngt with i n; auto with arith ].
  intros; apply mult_wd.
   apply pfwdef.
   cut (i = S (n + i) - S n); [ intro | lia ].
   generalize Hi; clear Hi; pattern i at 1 2 in |- *; rewrite H; intro.
   apply eq_symmetric_unfolded; apply pjp_3; auto with arith.
  apply cg_minus_wd; simpl in |- *.
   Opaque minus.
   unfold partition_join, partition_join_fun in |- *.
   elim le_lt_dec; simpl in |- *; intro.
    exfalso; apply Nat.nle_succ_diag_l with n; eapply Nat.le_trans.
     2: apply a0.
    auto with arith.
   Transparent minus.
   apply prf1; transitivity (S (n + i) - n); auto with arith.
  Opaque minus.
  unfold partition_join, partition_join_fun in |- *.
  elim le_lt_dec; simpl in |- *; intro.
   exfalso; apply Nat.nle_succ_diag_l with n; eapply Nat.le_trans.
    2: apply a0.
   auto with arith.
  Transparent minus.
  apply prf1; transitivity (n + i - n); auto with arith.
 intro; apply x_mult_zero.
 astepr (partition_join _ Hi[-]partition_join _ Hi).
 apply cg_minus_wd.
  algebra.
 unfold partition_join in |- *; simpl in |- *.
 apply eq_transitive_unfolded with c; unfold partition_join_fun in |- *;
   elim le_lt_dec; simpl in |- *.
    intro; apply finish.
   intro; exfalso; apply (Nat.lt_irrefl _ b0).
  intro; exfalso; apply (Nat.nle_succ_diag_l _ a0).
 intro; apply eq_symmetric_unfolded.
 apply eq_transitive_unfolded with (Q _ (Nat.le_0_l _)).
  apply prf1; auto with arith.
 apply start.
Qed.

Lemma partition_join_mesh : Mesh partition_join [<=] Max (Mesh P) (Mesh Q).
Proof.
 unfold Mesh at 1 in |- *.
 apply maxlist_leEq.
  apply length_Part_Mesh_List.
  apply Nat.lt_0_succ.
 intros x H.
 elim (Part_Mesh_List_lemma _ _ _ _ _ _ H); intros i Hi.
 elim Hi; clear Hi; intros Hi Hi'.
 elim Hi'; clear Hi'; intros Hi' Hx.
 eapply leEq_wdl.
  2: apply eq_symmetric_unfolded; apply Hx.
 unfold partition_join in |- *; simpl in |- *.
 unfold partition_join_fun in |- *.
 elim le_lt_dec; intro; simpl in |- *.
  elim le_lt_dec; intro; simpl in |- *.
   eapply leEq_transitive.
    apply Mesh_lemma.
   apply lft_leEq_Max.
  exfalso; apply Nat.le_ngt with i n; auto with arith.
 elim le_lt_dec; intro; simpl in |- *.
  cut (i = n); [ intro | apply Nat.le_antisymm; auto with arith ].
  generalize a0 b0 Hi'; clear Hx Hi Hi' a0 b0.
  rewrite H0; intros.
  apply leEq_wdl with ZeroR.
   eapply leEq_transitive.
    2: apply lft_leEq_Max.
   apply Mesh_nonneg.
  astepl (c[-]c).
  apply eq_symmetric_unfolded; apply cg_minus_wd.
   cut (forall H, Q (n - n) H [=] c); auto.
   cut (n - n = 0); [ intro | auto with arith ].
   rewrite H1; intros; apply start.
  apply finish.
 cut (i - n = S (i - S n)); [ intro | lia ].
 cut (forall H, Q (i - n) H[-]Q _ (partition_join_aux _ _ _ b1 Hi) [<=] Max (Mesh P) (Mesh Q)); auto.
 rewrite H0; intros; eapply leEq_transitive.
  apply Mesh_lemma.
 apply rht_leEq_Max.
Qed.

End Partition_Join.

(**
With these results in mind, the following is a trivial consequence:
*)

Lemma integral_plus_integral : integral _ _ Hac _ Hac'[+]integral _ _ Hcb _ Hcb' [=] Integral _ Hab'.
Proof.
 unfold integral at 1 2 in |- *.
 eapply eq_transitive_unfolded.
  apply eq_symmetric_unfolded; apply Lim_plus.
 apply cg_inv_unique_2.
 apply AbsIR_approach_zero.
 intros e' He'.
 set (e := e'[/] _[//]max_one_ap_zero (b[-]a)) in *.
 cut ([0] [<] e).
  intro He.
  set (d := proj1_sig2T _ _ _ (contin_prop _ _ _ _ Hab' e He)) in *.
  generalize (proj2b_sig2T _ _ _ (contin_prop _ _ _ _ Hab' e He));
    generalize (proj2a_sig2T _ _ _ (contin_prop _ _ _ _ Hab' e He)).
  fold d in |- *; intros Hd Haux.
  clear Haux.
  apply leEq_transitive with (e[*] (b[-]a)).
   elim (Archimedes (b[-]c[/] _[//]pos_ap_zero _ _ Hd)); intros n1 Hn1.
   elim (Archimedes (c[-]a[/] _[//]pos_ap_zero _ _ Hd)); intros n2 Hn2.
   apply leEq_wdl with (Lim (Build_CauchySeq _ _ (Cauchy_abs (Build_CauchySeq _ _ (Cauchy_plus
     (Build_CauchySeq _ _ (Cauchy_plus (Build_CauchySeq _ _ (Cauchy_Darboux_Seq _ _ Hac _ Hac'))
       (Build_CauchySeq _ _ (Cauchy_Darboux_Seq _ _ Hcb _ Hcb'))))
         (Cauchy_const [--] (Integral _ Hab'))))))).
    apply str_seq_leEq_so_Lim_leEq.
    set (p := Nat.max n1 n2) in *; exists p; intros.
    astepl (AbsIR (integral_seq _ _ Hac _ Hac' i[+]integral_seq _ _ Hcb _ Hcb' i[-] Integral _ Hab')).
    unfold integral_seq, Even_Partition_Sum in |- *.
    set (EP1 := Even_Partition Hac (S i) (O_S i)) in *.
    set (EP2 := Even_Partition Hcb (S i) (O_S i)) in *.
    set (P := partition_join _ _ EP1 EP2) in *.
    cut (nat_less_n_fun (Partition_imp_points _ _ _ _ EP1)); [ intro | apply Partition_imp_points_2 ].
    cut (nat_less_n_fun (Partition_imp_points _ _ _ _ EP2)); [ intro | apply Partition_imp_points_2 ].
    apply leEq_wdl with (AbsIR (Partition_Sum (partition_join_Pts_in_partition _ _ _ _ _
      (Partition_imp_points_1 _ _ _ _ EP1) H0 _ (Partition_imp_points_1 _ _ _ _ EP2) H1)
        (contin_imp_inc _ _ _ _ Hab') [-]Integral _ Hab')).
     apply partition_Sum_conv_integral with He; fold d in |- *.
      eapply leEq_less_trans.
       apply partition_join_mesh.
      apply Max_less.
       unfold EP1 in |- *; eapply less_wdl.
        2: apply eq_symmetric_unfolded; apply even_partition_Mesh.
       apply swap_div with (pos_ap_zero _ _ Hd).
         apply pos_nring_S.
        assumption.
       apply leEq_less_trans with (nring (R:=IR) n2).
        assumption.
       apply nring_less.
       apply Nat.le_lt_trans with p.
        unfold p in |- *; apply Nat.le_max_r.
       auto with arith.
      unfold EP2 in |- *; eapply less_wdl.
       2: apply eq_symmetric_unfolded; apply even_partition_Mesh.
      apply swap_div with (pos_ap_zero _ _ Hd).
        apply pos_nring_S.
       assumption.
      apply leEq_less_trans with (nring (R:=IR) n1).
       assumption.
      apply nring_less.
      apply Nat.le_lt_trans with p.
       unfold p in |- *; apply Nat.le_max_l.
      auto with arith.
     red in |- *; do 3 intro.
     rewrite H2; clear H2; intros.
     apply partition_join_Pts_wd; auto.
    apply AbsIR_wd.
    apply cg_minus_wd.
     2: algebra.
    apply eq_symmetric_unfolded.
    unfold Partition_Sum in |- *; apply Sumx_weird_lemma.
          auto.
         red in |- *; do 3 intro.
         rewrite H2; clear H2; intros; algebra.
        red in |- *; do 3 intro.
        rewrite H2; clear H2; intros; algebra.
       red in |- *; do 3 intro.
       rewrite H2; clear H2; intros; algebra.
      Opaque Even_Partition.
      intros; apply mult_wd.
       apply pfwdef; unfold partition_join_pts in |- *.
       elim le_lt_dec; intro; simpl in |- *.
        elim le_lt_eq_dec; intro; simpl in |- *.
         apply Partition_imp_points_2; auto.
        exfalso; rewrite b0 in Hi; apply (Nat.lt_irrefl _ Hi).
       exfalso; apply Nat.le_ngt with i0 (S i); auto with arith.
      apply cg_minus_wd; simpl in |- *.
       apply eq_symmetric_unfolded; apply pjf_1.
      apply eq_symmetric_unfolded; apply pjf_1.
     intros; apply mult_wd.
      apply pfwdef; unfold Partition_imp_points in |- *.
      unfold partition_join_pts in |- *.
      elim le_lt_dec; intro; simpl in |- *.
       elim le_lt_eq_dec; intro; simpl in |- *.
        exfalso; apply Nat.nle_succ_diag_l with (S i); eapply Nat.le_trans.
         2: apply a0.
        auto with arith.
       exfalso; apply Nat.lt_irrefl with (S i); pattern (S i) at 2 in |- *;
         rewrite <- b0; auto with arith.
      unfold Partition_imp_points in |- *; apply prf1.
      auto with arith.
     apply cg_minus_wd; simpl in |- *.
      apply eq_symmetric_unfolded; apply pjf_3; [ auto with arith | lia ].
     apply eq_symmetric_unfolded; apply pjf_3; auto with arith.
    intro; apply x_mult_zero.
    astepr (c[-]c).
    apply cg_minus_wd.
     simpl in |- *; apply pjf_2'; auto.
    simpl in |- *; apply pjf_2; auto.
   eapply eq_transitive_unfolded.
    apply Lim_abs.
   apply AbsIR_wd.
   unfold cg_minus in |- *.
   eapply eq_transitive_unfolded.
    apply Lim_plus.
   apply bin_op_wd_unfolded.
    algebra.
   apply eq_symmetric_unfolded; apply Lim_const.
  unfold e in |- *.
  rstepl (e'[*] (b[-]a) [/] _[//]max_one_ap_zero (b[-]a)).
  apply shift_div_leEq.
   apply pos_max_one.
  apply mult_resp_leEq_lft.
   apply lft_leEq_Max.
  apply less_leEq; assumption.
 unfold e in |- *.
 apply div_resp_pos.
  apply pos_max_one.
 assumption.
Qed.

End Integral_Sum.

Transparent Even_Partition.

End Basic_Properties.

(**
The following are simple consequences of this result and of previous ones.
*)

Lemma integral_less_norm : forall a b Hab (F : PartIR) contF,
 let N := Norm_Funct contF in a [<] b -> forall x, Compact Hab x -> forall Hx,
 AbsIR (F x Hx) [<] N -> AbsIR (integral a b Hab F contF) [<] N[*] (b[-]a).
Proof.
 (* begin hide *)
 intros a b Hab F contF N Hless x H Hx H0.
 set (e := (N[-]AbsIR (F x Hx)) [/]TwoNZ) in *.
 cut ([0] [<] e); intros.
  2: unfold e in |- *; apply pos_div_two; apply shift_less_minus.
  2: astepl (AbsIR (F x Hx)); auto.
 elim (contin_prop _ _ _ _ contF e); auto.
 intros d H2 H3.
 set (mid1 := Max a (x[-]d)) in *.
 set (mid2 := Min b (x[+]d)) in *.
 cut (a [<=] mid1); [ intro leEq1 | unfold mid1 in |- *; apply lft_leEq_Max ].
 cut (mid1 [<=] mid2); [ intro leEq2
   | unfold mid1, mid2 in |- *; inversion_clear H; apply leEq_transitive with x ].
   2: apply Max_leEq; auto.
   2: apply less_leEq; apply shift_minus_less.
   2: apply shift_less_plus'; astepl ZeroR; auto.
  2: apply leEq_Min; auto.
  2: apply less_leEq; apply shift_less_plus'.
  2: astepl ZeroR; auto.
 cut (mid2 [<=] b); [ intro leEq3 | unfold mid2 in |- *; apply Min_leEq_lft ].
 cut (Continuous_I leEq1 F).
  cut (Continuous_I leEq2 F).
   cut (Continuous_I leEq3 F).
    intros cont3 cont2 cont1.
    cut (Continuous_I (leEq_transitive _ _ _ _ leEq1 leEq2) F). intro H4.
     apply less_wdl with (AbsIR (integral _ _ _ _ cont1[+]integral _ _ _ _ cont2[+]
       integral _ _ _ _ cont3)).
      2: apply AbsIR_wd.
      2: apply eq_transitive_unfolded with (integral _ _ _ _ H4[+]integral _ _ _ _ cont3).
       2: apply bin_op_wd_unfolded.
        2: apply integral_plus_integral.
       2: algebra.
      2: apply integral_plus_integral.
     rstepr (N[*] (mid1[-]a) [+]N[*] (mid2[-]mid1) [+]N[*] (b[-]mid2)).
     eapply leEq_less_trans.
      apply triangle_IR.
     apply plus_resp_less_leEq.
      eapply leEq_less_trans.
       apply triangle_IR.
      apply plus_resp_leEq_less.
       eapply leEq_transitive.
        apply integral_leEq_norm.
       unfold N in |- *; apply mult_resp_leEq_rht.
        2: apply shift_leEq_minus; astepl a; auto.
       apply included_imp_norm_leEq.
       apply included_compact.
        apply compact_inc_lft.
       split.
        unfold mid1 in |- *; apply lft_leEq_Max.
       apply leEq_transitive with mid2; auto.
      2: eapply leEq_transitive.
       2: apply integral_leEq_norm.
      2: unfold N in |- *; apply mult_resp_leEq_rht.
       3: apply shift_leEq_minus; astepl mid2; auto.
      2: apply included_imp_norm_leEq.
      2: apply included_compact.
       2: split.
        2: apply leEq_transitive with mid1; auto.
       2: auto.
      2: apply compact_inc_rht.
     eapply leEq_less_trans.
      apply integral_leEq_norm.
     apply mult_resp_less.
      apply leEq_less_trans with (N[-]e).
       2: apply shift_minus_less; apply shift_less_plus'.
       2: astepl ZeroR; auto.
      apply leEq_Norm_Funct; intros y Hy Hy'.
      apply leEq_wdr with (AbsIR (F x Hx) [+]e).
       2: unfold e in |- *; rational.
      apply AbsIR_bnd_AbsIR.
      apply H3; auto.
       cut (included (Compact leEq2) (Compact Hab)); auto.
       apply included_compact.
        split; auto.
        apply leEq_transitive with mid2; auto.
       split; auto.
       apply leEq_transitive with mid1; auto.
      cut (x[-]d [<=] x[+]d). intro H5.
       apply compact_bnd_AbsIR with H5.
       cut (included (Compact leEq2) (Compact H5)); auto.
       apply included_compact; unfold mid1, mid2 in |- *; split.
          apply rht_leEq_Max.
         apply leEq_transitive with mid2; auto.
         unfold mid2 in |- *; apply Min_leEq_rht.
        apply leEq_transitive with mid1; auto.
        unfold mid1 in |- *; apply rht_leEq_Max.
       apply Min_leEq_rht.
      apply leEq_transitive with x.
       apply shift_minus_leEq; apply shift_leEq_plus'.
       astepl ZeroR; apply less_leEq; auto.
      apply shift_leEq_plus'.
      astepl ZeroR; apply less_leEq; auto.
     unfold mid2, mid1 in |- *.
     astepl (x[-]x).
     unfold cg_minus at 1 2 in |- *.
     inversion_clear H.
     elim (less_cotransitive_unfolded _ _ _ Hless x); intro.
      apply plus_resp_leEq_less.
       apply leEq_Min; auto.
       apply shift_leEq_plus'; astepl ZeroR; apply less_leEq; auto.
      apply inv_resp_less; apply Max_less; auto.
      apply shift_minus_less; apply shift_less_plus'.
      astepl ZeroR; auto.
     apply plus_resp_less_leEq.
      apply less_Min; auto.
      apply shift_less_plus'; astepl ZeroR; auto.
     apply inv_resp_leEq; apply Max_leEq; auto.
     apply shift_minus_leEq; apply shift_leEq_plus'.
     astepl ZeroR; apply less_leEq; auto.
    apply included_imp_contin with a b Hab; auto.
    apply included_compact.
     apply compact_inc_lft.
    split; auto.
    apply leEq_transitive with mid1; auto.
   apply included_imp_contin with a b Hab; auto.
   apply included_compact.
    split; auto.
    apply leEq_transitive with mid1; auto.
   apply compact_inc_rht.
  apply included_imp_contin with a b Hab; auto.
  apply included_compact.
   split; auto.
   apply leEq_transitive with mid2; auto.
  split; auto.
  apply leEq_transitive with mid1; auto.
 apply included_imp_contin with a b Hab; auto.
 apply included_compact.
  apply compact_inc_lft.
 split; auto.
 apply leEq_transitive with mid2; auto.
Qed.
(* end hide *)

Lemma integral_gt_zero : forall a b Hab (F : PartIR) contF, let N := Norm_Funct contF in
 a [<] b -> forall x, Compact Hab x -> forall Hx, [0] [<] F x Hx ->
 (forall x, Compact Hab x -> forall Hx, [0] [<=] F x Hx) -> [0] [<] integral a b Hab F contF.
Proof.
 (* begin hide *)
 intros a b Hab F contF N Hless x H Hx H0.
 set (e := F x Hx [/]TwoNZ) in *.
 cut ([0] [<] e). intros H1 H2.
  2: unfold e in |- *; apply pos_div_two; auto.
 elim (contin_prop _ _ _ _ contF e); auto.
 intros d H3 H4.
 set (mid1 := Max a (x[-]d)) in *.
 set (mid2 := Min b (x[+]d)) in *.
 cut (a [<=] mid1); [ intro leEq1 | unfold mid1 in |- *; apply lft_leEq_Max ].
 cut (mid1 [<=] mid2); [ intro leEq2
   | unfold mid1, mid2 in |- *; inversion_clear H; apply leEq_transitive with x ].
   2: apply Max_leEq; auto.
   2: apply less_leEq; apply shift_minus_less.
   2: apply shift_less_plus'; astepl ZeroR; auto.
  2: apply leEq_Min; auto.
  2: apply less_leEq; apply shift_less_plus'.
  2: astepl ZeroR; auto.
 cut (mid2 [<=] b); [ intro leEq3 | unfold mid2 in |- *; apply Min_leEq_lft ].
 cut (Continuous_I leEq1 F).
  cut (Continuous_I leEq2 F).
   cut (Continuous_I leEq3 F).
    intros cont3 cont2 cont1.
    cut (Continuous_I (leEq_transitive _ _ _ _ leEq1 leEq2) F). intro H5.
     apply less_wdr with (integral _ _ _ _ cont1[+]integral _ _ _ _ cont2[+]integral _ _ _ _ cont3).
      2: apply eq_transitive_unfolded with (integral _ _ _ _ H5[+]integral _ _ _ _ cont3).
       2: apply bin_op_wd_unfolded.
        2: apply integral_plus_integral.
       2: algebra.
      2: apply integral_plus_integral.
     rstepl ([0][*] (mid1[-]a) [+][0][*] (mid2[-]mid1) [+][0][*] (b[-]mid2)).
     apply plus_resp_less_leEq.
      apply plus_resp_leEq_less.
       apply lb_integral.
       intros x0 H6 Hx0.
       apply H2.
       inversion_clear H6; split; auto.
       apply leEq_transitive with mid1; auto.
       apply leEq_transitive with mid2; auto.
      apply less_leEq_trans with (F x Hx [/]TwoNZ[*] (mid2[-]mid1)).
       apply mult_resp_less.
        apply pos_div_two; auto.
       apply shift_less_minus; astepl mid1.
       elim (less_cotransitive_unfolded _ _ _ Hless x); intro; unfold mid1, mid2 in |- *.
        apply less_leEq_trans with x.
         apply Max_less.
          auto.
         apply shift_minus_less; apply shift_less_plus'.
         astepl ZeroR; auto.
        apply leEq_Min.
         inversion_clear H; auto.
        apply less_leEq; apply shift_less_plus'.
        astepl ZeroR; auto.
       apply leEq_less_trans with x.
        apply Max_leEq.
         inversion_clear H; auto.
        apply shift_minus_leEq; apply shift_leEq_plus'.
        astepl ZeroR; apply less_leEq; auto.
       apply less_Min.
        auto.
       apply shift_less_plus'.
       astepl ZeroR; auto.
      apply lb_integral.
      intros x0 H6 Hx0.
      rstepl (F x Hx[-]F x Hx [/]TwoNZ).
      apply shift_minus_leEq; apply shift_leEq_plus'.
      fold e in |- *; eapply leEq_transitive; [ apply leEq_AbsIR | apply H4 ].
        auto.
       inversion_clear H6; split; auto.
        apply leEq_transitive with mid1; auto.
       apply leEq_transitive with mid2; auto.
      cut (x[-]d [<=] x[+]d); intros.
       apply compact_bnd_AbsIR with H7.
       cut (included (Compact leEq2) (Compact H7)); auto.
       apply included_compact; unfold mid1, mid2 in |- *; split.
          apply rht_leEq_Max.
         apply leEq_transitive with mid2; auto.
         unfold mid2 in |- *; apply Min_leEq_rht.
        apply leEq_transitive with mid1; auto.
        unfold mid1 in |- *; apply rht_leEq_Max.
       apply Min_leEq_rht.
      apply leEq_transitive with x.
       apply shift_minus_leEq; apply shift_leEq_plus'.
       astepl ZeroR; apply less_leEq; auto.
      apply shift_leEq_plus'.
      astepl ZeroR; apply less_leEq; auto.
     apply lb_integral.
     intros x0 H6 Hx0.
     apply H2.
     inversion_clear H6; split; auto.
     apply leEq_transitive with mid1; auto.
     apply leEq_transitive with mid2; auto.
    apply included_imp_contin with a b Hab; auto.
    apply included_compact.
     apply compact_inc_lft.
    split; auto.
    apply leEq_transitive with mid1; auto.
   apply included_imp_contin with a b Hab; auto.
   apply included_compact.
    split; auto.
    apply leEq_transitive with mid1; auto.
   apply compact_inc_rht.
  apply included_imp_contin with a b Hab; auto.
  apply included_compact.
   split; auto.
   apply leEq_transitive with mid2; auto.
  split; auto.
  apply leEq_transitive with mid1; auto.
 apply included_imp_contin with a b Hab; auto.
 apply included_compact.
  apply compact_inc_lft.
 split; auto.
 apply leEq_transitive with mid2; auto.
Qed.
(* end hide *)

(** remove printing Integral *)
