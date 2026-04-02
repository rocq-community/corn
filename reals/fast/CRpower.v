(*
Copyright © 2006-2008 Russell O’Connor
Copyright © 2020 Vincent Semeria

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
From Coq Require Import ZArith.
Require Import CoRN.algebra.RSetoid.
Require Import CoRN.metric2.Metric.
Require Import CoRN.metric2.ProductMetric.
Require Import CoRN.reals.fast.CRArith.
From Coq Require Import Qpower.
From Coq Require Import Qabs.
Require Import CoRN.model.metric2.Qmetric.
Require Import CoRN.model.totalorder.QMinMax.
Require Import CoRN.model.totalorder.QposMinMax.
Require Import MathClasses.interfaces.canonical_names.
Require Import MathClasses.interfaces.additional_operations.

(* Backwards compatibility for Hint Rewrite locality attributes *)
Set Warnings "-unsupported-attributes".

Local Open Scope Q_scope.
Local Open Scope uc_scope.

(**
** Natural Integer Powers
Positive integer powers is faster than repeated multiplication.

It is uniformly continuous on an interval [[-c,c]].
*)

(* We first define repeated multiplication to prove correctness. *)
Fixpoint CRpower_slow (x : CR) (n : nat) { struct n }
  := match n with
     | O => 1%CR
     | S p => (x * CRpower_slow x p)%CR
     end.

Lemma CRpower_slow_wd : forall (x y : CR) (n : nat),
    msp_eq x y -> msp_eq (CRpower_slow x n) (CRpower_slow y n).
Proof.
  induction n.
  - intros. reflexivity.
  - intros. simpl (CRpower_slow x (S n)). 
    rewrite (IHn H). rewrite H. reflexivity.
Qed.

Lemma Qpower_positive_abs_le : forall (q:Q) (c : Qpos) (n : positive),
    Qabs q <= `c
    -> Qabs (Qpower_positive q n) <= Qpower_positive (` c) n.
Proof.
  intros q c.
  induction n.
  - intros. simpl (Qpower_positive q n~1).
    rewrite Qabs_Qmult.
    simpl (Qpower_positive (` c) n~1).
    apply (Qle_trans _ (`c * Qabs (Qpower_positive q n * Qpower_positive q n))).
    apply Qmult_le_compat_r. exact H.
    apply Qabs_nonneg. apply Qmult_le_l.
    apply Qpos_ispos.
    rewrite Qabs_Qmult.
    apply (Qle_trans _ (Qpower_positive (`c) n * Qabs (Qpower_positive q n))).
    apply Qmult_le_compat_r. apply IHn. exact H.
    apply Qabs_nonneg.
    rewrite Qmult_comm.
    apply Qmult_le_compat_r. apply IHn. exact H.
    apply Qpower_pos_positive, Qpos_nonneg.
  - intros. simpl (Qpower_positive q n~0).
    rewrite Qabs_Qmult. simpl.
    apply (Qle_trans _ (Qpower_positive (`c) n * Qabs (Qpower_positive q n))).
    apply Qmult_le_compat_r. apply IHn. exact H.
    apply Qabs_nonneg.
    rewrite Qmult_comm.
    apply Qmult_le_compat_r. apply IHn. exact H.
    apply Qpower_pos_positive, Qpos_nonneg.
  - intros. exact H.
Qed.

 (* The derivative of fun z => z^p is fun z => p * z^(p-1)
   which is bounded by p*c^(p-1) on [-c,c]. *)
Lemma Qdiff_power : forall (n : nat) (x y : Q) (c : Qpos),
    (-`c <= x <= `c)
    -> (-`c <= y <= `c)
    -> Qabs (x^Z.of_nat n - y^Z.of_nat n)
      <= Qabs(x-y) * (Z.of_nat n#1) * (`c) ^ (Z.pred (Z.of_nat n)).
Proof.
  induction n.
  - intros. apply Qmult_le_0_compat.
    apply Qmult_le_0_compat. apply Qabs_nonneg.
    discriminate. apply (Qpos_nonneg (Qpos_power c (Z.pred (Z.of_nat 0)))).
  - intros. change (S n) with (1 + n)%nat.
    rewrite Nat2Z.inj_add, Qpower_plus', Qpower_plus'.
    simpl (x ^ Z.of_nat 1).
    simpl (y ^ Z.of_nat 1).
    setoid_replace (x * x ^ Z.of_nat n - y * y ^ Z.of_nat n)%Q
      with ((x-y)*x ^ Z.of_nat n + y * (x ^ Z.of_nat n - y ^ Z.of_nat n))%Q
      by (unfold equiv, stdlib_rationals.Q_eq; ring).
    apply (Qle_trans _ _ _ (Qabs_triangle _ _)).
    rewrite Qabs_Qmult, Qabs_Qmult.
    apply (Qle_trans _ (Qabs (x-y) * (`c) ^ Z.of_nat n
             + Qabs (x - y) * (Z.of_nat n # 1) * ` c ^ Z.pred (Z.of_nat n) * Qabs y)).
    apply Qplus_le_compat.
    + rewrite Qmult_comm, (Qmult_comm (Qabs (x-y))).
      apply Qmult_le_compat_r. 2: apply Qabs_nonneg.
      destruct n. apply Qle_refl. 
      apply Qpower_positive_abs_le.
      apply AbsSmall_Qabs, H.
    + rewrite Qmult_comm. apply Qmult_le_compat_r.
      2: apply Qabs_nonneg. apply IHn. exact H. exact H0.
    + clear IHn.
      rewrite <- Qmult_assoc, <- Qmult_assoc, <- Qmult_plus_distr_r.
      rewrite Qmult_comm, <- Qmult_assoc, (Qmult_comm (Qabs (x-y))).
      apply Qmult_le_compat_r. 2: apply Qabs_nonneg.
      apply (Qle_trans _ (` c ^ Z.of_nat n + (Z.of_nat n # 1) * (` c ^ (Z.of_nat n)))).
      apply Qplus_le_r.
      rewrite Qmult_comm, (Qmult_comm (Z.of_nat n # 1)). 
      apply Qmult_le_compat_r. 
      apply (Qle_trans _ (`c ^ Z.of_nat 1 * ` c ^ Z.pred (Z.of_nat n))).
      rewrite Qmult_comm. apply Qmult_le_compat_r.
      simpl. apply AbsSmall_Qabs. exact H0.
      apply Qpower_pos. apply Qpos_nonneg.
      rewrite <- Qpower_plus. 2: apply Qpos_nonzero.
      replace (Z.of_nat 1 + Z.pred (Z.of_nat n))%Z with (Z.of_nat n).
      apply Qle_refl.
      rewrite Z.add_1_l. rewrite Z.succ_pred. reflexivity.
      unfold Qle; simpl. rewrite Z.mul_1_r. apply Nat2Z.is_nonneg.
      rewrite <- (Qmult_1_l (` c ^ Z.of_nat n)) at 1.
      rewrite <- Qmult_plus_distr_l.
      setoid_replace (1 + (Z.of_nat n # 1)) with (Z.of_nat 1 + Z.of_nat n#1).
      rewrite Qmult_comm.
      rewrite (Qmult_comm (Z.of_nat 1 + Z.of_nat n#1)).
      apply Qmult_le_compat_r.
      replace (Z.pred (Z.of_nat 1 + Z.of_nat n)) with (Z.of_nat n).
      apply Qle_refl.
      rewrite <- Nat2Z.inj_add. rewrite Nat2Z.inj_succ.
      rewrite <- Zpred_succ. reflexivity.
      rewrite <- Nat2Z.inj_add. discriminate.
      unfold equiv, stdlib_rationals.Q_eq, Qeq, Qplus, Qnum, Qden. 
      simpl (1*1)%Z. rewrite Z.mul_1_r, Z.mul_1_r.
      simpl (1*1)%positive. rewrite Z.mul_1_r. reflexivity.
    + rewrite <- Nat2Z.inj_add. discriminate. 
    + rewrite <- Nat2Z.inj_add. discriminate. 
Qed.

Section CRpower_N.

Variable n : N. (* Binary integers are faster than unary integers *)

(* To compute x^n, we bound x by c and the modulus becomes
   fun e => e / (n * c^(n-1)) *)
Definition Qpower_N_modulus (c:Qpos) (e:Qpos) : QposInf :=
  match n with 
  | N0 => QposInfinity
  | Npos p => Qpos2QposInf (e* Qpos_inv ((p#1)*Qpos_power c (Z.pred (Zpos p))))
  end.

Lemma Qpower_N_uc_prf (c:Qpos) : 
  @is_UniformlyContinuousFunction
    Q_as_MetricSpace Q_as_MetricSpace
    (fun x => Qpower (QboundAbs c x) (Z_of_N n)) (Qpower_N_modulus c).
Proof.
 unfold Qpower_N_modulus.
 destruct n as [|p].
 - simpl. intros e x y E. apply ball_refl, Qpos_nonneg. 
 - clear n. intros e x y E. unfold ball_ex in E. 
   simpl (Z.of_N (N.pos p)).
   apply AbsSmall_Qabs.
   apply AbsSmall_Qabs in E.
   assert (-` c <= QboundAbs c x ∧ QboundAbs c x <= ` c).
   { split. apply Qmax_ub_l.
     apply Qmax_lub.
     apply (Qle_trans _ 0). apply (Qopp_le_compat 0), Qpos_nonneg.
     apply Qpos_nonneg. apply Qmin_lb_l. }
   assert (- ` c <= QboundAbs c y ∧ QboundAbs c y <= ` c).
   { split. apply Qmax_ub_l.
     apply Qmax_lub.
     apply (Qle_trans _ 0). apply (Qopp_le_compat 0), Qpos_nonneg.
     apply Qpos_nonneg. apply Qmin_lb_l. }
   pose proof (positive_nat_Z p).
   rewrite <- H1.
   apply (Qle_trans _ _ _ (Qdiff_power (Pos.to_nat p) _ _ c H H0)).
   clear H H0.
   rewrite <- Qmult_assoc.
   apply (Qle_trans _ (Qabs (x-y) * ((Z.pos p # 1) * ` c ^ Z.pred (Z.pos p)))).
   rewrite H1.
   apply Qmult_le_compat_r.
   apply QboundAbs_contract.
   apply (Qpos_nonneg ((p#1) * Qpos_power c (Z.pred (Z.pos p)))).
   apply (Qle_trans _ (`e * / proj1_sig ((Z.pos p # 1)%Q ↾ eq_refl * Qpos_power c (Z.pred (Z.pos p)))%Qpos * ((Z.pos p # 1) * ` c ^ Z.pred (Z.pos p)))).
   apply Qmult_le_compat_r.
   apply E.
   apply (Qpos_nonneg ((p#1) * Qpos_power c (Z.pred (Z.pos p)))).
   rewrite Qmult_comm, Qmult_assoc.
   apply Qle_shift_div_r.
   apply (Qpos_ispos ((p#1) * Qpos_power c (Z.pred (Z.pos p)))).
   rewrite Qmult_comm. apply Qle_refl.
Qed.

Definition Qpower_N_uc (c:Qpos) :  Q_as_MetricSpace --> Q_as_MetricSpace :=
Build_UniformlyContinuousFunction (Qpower_N_uc_prf c).

(** CRpower_positive_bounded works on [[-c,c]]. *)
Definition CRpower_N_bounded (c:Qpos) : CR --> CR :=
Cmap QPrelengthSpace (Qpower_N_uc c).

End CRpower_N.

Lemma Cmap_wd_bounded
  : forall (Y : MetricSpace)
      (f g : Q_as_MetricSpace --> Y) (x : CR) (c : Qpos),
    (forall q:Q, -`c <= q <= `c -> msp_eq (f q) (g q))
    -> (- ' (proj1_sig c) <= x /\ x <= ' (proj1_sig c))%CR
    -> msp_eq (Cmap_fun QPrelengthSpace f x) (Cmap_fun QPrelengthSpace g x).
Proof.
  intros.
  setoid_replace x with (CRboundAbs c x).
  2: symmetry; apply CRboundAbs_Eq; apply H0.
  pose (fun e => QposInf_min (mu f e) (mu g e)) as mufg.
  assert (∀ e : Qpos, QposInf_le (mufg e) (mu f e)).
  { intro e. unfold QposInf_le, mufg.
    destruct (mu f e). 2: trivial.
    simpl. destruct (mu g e). 2: apply Qle_refl.
    apply Qpos_min_lb_l. }
  pose proof (uc_prf_smaller f mufg H1). clear H1.
  setoid_replace f with (Build_UniformlyContinuousFunction H2).
  2: apply ucEq_equiv; intro q; reflexivity.
  assert (∀ e : Qpos, QposInf_le (mufg e) (mu g e)).
  { intro e. unfold QposInf_le, mufg.
    destruct (mu g e). 2: trivial.
    simpl. destruct (mu f e). 2: apply Qle_refl.
    apply Qpos_min_lb_r. }
  pose proof (uc_prf_smaller g mufg H1). clear H1.
  setoid_replace g with (Build_UniformlyContinuousFunction H3).
  2: apply ucEq_equiv; intro q; reflexivity.
  intros e1 e2.
  assert (forall y, eq (QposInf_bind (fun e : Qpos => e) y) y) as elim_bind.
  { intro y. destruct y; reflexivity. }
  simpl. 
  rewrite elim_bind, elim_bind. clear elim_bind.
  assert (forall a, Qmax (- ` c) (Qmin (` c) a) <= ` c).
  { intro a. apply Qmax_lub.
    apply (Qle_trans _ 0). apply (Qopp_le_compat 0), Qpos_nonneg.
    apply Qpos_nonneg. apply Qmin_lb_l. }
  rewrite Qplus_0_r.
  destruct (mufg e1) as [q|] eqn:des. 
  - rewrite H.
    apply (mu_sum QPrelengthSpace e2 (cons e1 nil)
                  (Build_UniformlyContinuousFunction H3)).
    simpl. rewrite des. simpl. destruct (mufg e2) eqn:des2.
    simpl. apply AbsSmall_Qabs.
    apply (Qle_trans _ (Qabs (approximate x q - approximate x q0))).
    apply QboundAbs_contract.
    apply AbsSmall_Qabs. apply (regFun_prf x).
    simpl. trivial.
    split. apply Qmax_ub_l. apply H1.
  - rewrite <- H.
    apply (mu_sum QPrelengthSpace e2 (cons e1 nil) f).
    simpl. unfold mufg in des.
    destruct (mu f e1) as [q|]. exfalso.
    simpl in des. destruct (mu g e1); inversion des.
    simpl. trivial. 
    split. apply Qmax_ub_l. apply H1.
Qed. 

Lemma CRpower_N_bounded_step : forall (n:N) (c:Qpos) (x : CR),
    (forall e, - (proj1_sig c) <= approximate x e)
    -> (forall e, approximate x e <= proj1_sig c)
    -> (CRpower_N_bounded (1+n) c x
       == x * CRpower_N_bounded n c x)%CR.
Proof.
  assert (forall i j : Q, i<=j -> Qmax i j == j)%Q as elim_max.
  { intros. apply (Qle_max_r i j), H. }
  assert (forall i j : Q, j<=i -> Qmin i j == j)%Q as elim_min.
  { intros. apply (Qle_min_r i j), H. } 
  intros.
  assert (x <= ' ` c)%CR as xupper.
  { intro e. simpl. unfold Cap_raw. simpl.
    apply (Qle_trans _ 0). apply (Qopp_le_compat 0), Qpos_nonneg.
    rewrite <- Qle_minus_iff. apply H0. }
  assert (- ' ` c <= x)%CR as xlower.
  { intro e. simpl. unfold Cap_raw. simpl.
    apply (Qle_trans _ 0). apply (Qopp_le_compat 0), Qpos_nonneg.
    rewrite <- Qle_minus_iff. apply H. }
  destruct n as [|n].
  - setoid_replace (CRpower_N_bounded 0 c x) with 1%CR.
    2: intros e1 e2; apply Qball_Reflexive; rewrite Qplus_0_r; apply (Qpos_nonneg (e1+e2)). 
    rewrite CRmult_1_r. simpl (1+0)%N. 
    intros e1 e2. simpl.
    rewrite Qplus_0_r.
    rewrite elim_min. 2: apply H0.
    rewrite elim_max. 2: apply H.
    setoid_replace (` e1 + ` e2)%Q
      with (` (e1 * Qpos_inv (1 ↾ eq_refl * Qpos_power c 0))%Qpos + ` e2).
    apply (regFun_prf x).
    apply Qplus_comp. 2: reflexivity.
    simpl. change (/ (1*1)) with 1.
    rewrite Qmult_1_r. reflexivity.
  - rewrite CRmult_comm.
    pose (Qpos_max c (Qpos_power c (Z_of_N (N.pos n)))) as b.
    rewrite <- (CRmult_bounded_mult c). 
    2: exact xlower. 2: exact xupper.
    rewrite (CRmult_bounded_weaken c b).
    2: exact xlower. 2: exact xupper. 2: apply Qpos_max_ub_l.
    rewrite (CRmult_uncurry_eq b).
    unfold CRpower_N_bounded.
    transitivity (Cmap QPrelengthSpace 
                       (uc_compose (Qmult_uncurry b)
                                   (uc_compose (together (Qpower_N_uc (N.pos n) c)
                                                        (uc_id Q_as_MetricSpace))
                                               (diag Q_as_MetricSpace)))
                       x).
    + apply Cmap_wd_bounded with (c:=c).
      intros q H1. destruct H1.
      apply Qball_0.
      change (Qpower_positive (Qmax (- ` c) (Qmin (` c) q)) (1+n)
              ==
  Qmax (- ` b) (Qmin (` b) (Qpower_positive (Qmax (- ` c) (Qmin (` c) q)) n)) *
  Qmax (- ` b) (Qmin (` b) q)).
      rewrite (elim_min _ q). 2: exact H2.
      rewrite (elim_max _ q). 2: exact H1.
      2: exact (conj xlower xupper).
      rewrite (elim_min _ q).
      rewrite (elim_max _ q).
      rewrite Qpower_plus_positive. simpl.
      rewrite Qmult_comm. apply Qmult_comp. 2: reflexivity.
      assert (Qabs q <= `c).
      { apply AbsSmall_Qabs. split. exact H1. exact H2. }
      pose proof (Qpower_positive_abs_le q c n H3). clear H3.
      apply AbsSmall_Qabs in H4. destruct H4.
      rewrite elim_min, elim_max. reflexivity.
      apply (Qle_trans _ (-(Qpower_positive (`c) n))).
      apply Qopp_le_compat. 
      apply (Qpos_max_ub_r c (Qpower_positive (` c) n ↾ Qpos_power_ispos c (Z.pos n))).
      exact H3.
      apply (Qle_trans _ (Qpower_positive (`c) n)).
      exact H4. 
      apply (Qpos_max_ub_r c (Qpower_positive (` c) n ↾ Qpos_power_ispos c (Z.pos n))).
      apply (Qle_trans _ (-`c)). apply Qopp_le_compat, Qpos_max_ub_l.
      exact H1.
      apply (Qle_trans _ (`c)). apply H2. apply Qpos_max_ub_l.
    + rewrite (fast_MonadLaw2 QPrelengthSpace
                              (ProductMS_prelength QPrelengthSpace QPrelengthSpace)).
      apply Cmap_wd. apply ucEq_equiv. intro a; reflexivity.
      intros e1 e2. split. 
      rewrite Qplus_0_r.
      apply (mu_sum QPrelengthSpace e2 (cons e1 nil) (Qpower_N_uc (N.pos n) c)).
      apply (@ball_weak_le Q_as_MetricSpace
            (proj1_sig (Qpos_min
                   (e1 *
                    Qpos_inv
                      ((n # 1) *
                       Qpos_power c (Z.pred (Zpos n)) )) e1
             + (e2 *
                    Qpos_inv
                      ((n # 1) *
                       Qpos_power c (Z.pred (Zpos n)) )))%Qpos)).
      apply Qplus_le_l.
      apply Qpos_min_lb_l.
      apply (regFun_prf x).
      apply (@ball_weak_le Q_as_MetricSpace
            (proj1_sig (Qpos_min
                   (e1 *
                    Qpos_inv
                      ((n # 1) *
                       Qpos_power c (Z.pred (Zpos n)) )) e1
             + e2)%Qpos)).
      apply Qplus_le_l.
      rewrite Qplus_0_r.
      apply Qpos_min_lb_r.
      apply (regFun_prf x).
    + intro e. simpl.
      unfold Cap_raw; simpl.
      apply (Qle_trans _ 0).
      apply (Qopp_le_compat 0), Qpos_nonneg.
      rewrite <- Qle_minus_iff.
      apply (Qle_trans _ (-Qpower_positive (` c) n)).
      apply Qopp_le_compat.
      apply (Qpos_max_ub_r c (Qpower_positive (` c) n ↾ Qpos_power_ispos c (Z.pos n))).
      assert (forall i j :Q, -j <= i -> -i <= j).
      { intros. rewrite <- (Qopp_involutive j).
        apply Qopp_le_compat, H1. } 
      apply H1. clear H1.
      apply (Qle_trans _ _ _ (Qle_Qabs _)).
      rewrite Qabs_opp. 
      apply (Qpower_positive_abs_le 
                    (Qmax (- ` c)
                          (Qmin (` c)
          (approximate x
             ((1 # 2) * e *
              Qpos_inv
                ((n # 1) *
                 Qpos_power c
                            (Z.pred (Zpos n)) ))%Qpos))) c n).
      apply AbsSmall_Qabs. split. apply Qmax_ub_l.
      apply Qmax_lub.
      apply (Qle_trans _ 0). apply (Qopp_le_compat 0), Qpos_nonneg.
      apply Qpos_nonneg. apply Qmin_lb_l.
    + intro e. simpl.
      unfold Cap_raw; simpl.
      apply (Qle_trans _ 0).
      apply (Qopp_le_compat 0), Qpos_nonneg.
      rewrite <- Qle_minus_iff.
      apply (Qle_trans _ _ _ (Qle_Qabs _)).
      apply (Qle_trans _ (Qpower_positive (` c) n)).
      apply (Qpower_positive_abs_le 
                    (Qmax (- ` c)
                          (Qmin (` c)
          (approximate x
             ((1 # 2) * e *
              Qpos_inv
                ((n # 1) *
                 Qpos_power c
                            (Z.pred (Zpos n)) ))%Qpos))) c n).
      apply AbsSmall_Qabs. split. apply Qmax_ub_l.
      apply Qmax_lub.
      apply (Qle_trans _ 0). apply (Qopp_le_compat 0), Qpos_nonneg.
      apply Qpos_nonneg. apply Qmin_lb_l.
      apply (Qpos_max_ub_r c (Qpower_positive (` c) n ↾ Qpos_power_ispos c (Z.pos n))).
Qed.

Lemma CRpower_N_bounded_correct : forall (n:N) (c:Qpos) (x : CR),
    (- (' (proj1_sig c)) <= x /\ x <= 'proj1_sig c)%CR
    -> (CRpower_slow x (N.to_nat n) == CRpower_N_bounded n c x)%CR.
Proof.
  assert (∀ (n : nat) (c : Qpos) (x : CR),
    (forall e, - (proj1_sig c) <= approximate x e)
    -> (forall e, approximate x e <= proj1_sig c)
    → msp_eq (CRpower_slow x n) (CRpower_N_bounded (N.of_nat n) c x)).
  induction n.
  - intros. intros e1 e2. simpl. apply Qball_Reflexive.
    rewrite Qplus_0_r.
    apply (Qpos_nonneg (e1+e2)).
  - intros. change (S n) with (1+n)%nat.
    rewrite Nnat.Nat2N.inj_add.
    change (N.of_nat 1) with 1%N.
    rewrite CRpower_N_bounded_step. 2: exact H.
    change (CRpower_slow x (1 + n)) with (x * CRpower_slow x n)%CR.
    apply CRmult_wd. reflexivity. apply IHn. exact H.
    exact H0. exact H0.
  - intros. 
    transitivity (CRpower_N_bounded (N.of_nat (N.to_nat n)) c x).
    2: rewrite Nnat.N2Nat.id; reflexivity.
    transitivity (CRpower_N_bounded (N.of_nat (N.to_nat n)) c (CRboundAbs c x)).
    transitivity (CRpower_slow (CRboundAbs c x) (N.to_nat n)).
    apply CRpower_slow_wd. symmetry.
    apply CRboundAbs_Eq. apply H0. apply H0.
    apply H. intro e. simpl. apply Qmax_ub_l.
    intros e. apply Qmax_lub.
    apply (Qle_trans _ 0). apply (Qopp_le_compat 0), Qpos_nonneg.
    apply Qpos_nonneg. apply Qmin_lb_l.
    apply Cmap_wd. apply ucEq_equiv; intro a; reflexivity.
    apply CRboundAbs_Eq. apply H0. apply H0.
Qed.

Lemma CRpower_N_bounded_weaken : forall (n:N) (c1 c2:Qpos) x,
    ((- (' (proj1_sig c1)) <= x /\ x <= 'proj1_sig c1)
     -> (proj1_sig c1 <= proj1_sig c2)%Q ->
     CRpower_N_bounded n c1 x == CRpower_N_bounded n c2 x)%CR.
Proof.
 intros n c1 c2 x Hx Hc.
 simpl in x.
 rewrite <- CRpower_N_bounded_correct.
 rewrite <- CRpower_N_bounded_correct.
 reflexivity. 2: exact Hx. destruct Hx.
 split. 
 - apply (@CRle_trans _ (-'(proj1_sig c1))%CR).
   apply CRopp_le_compat, CRle_Qle, Hc. exact H.
 - apply (CRle_trans H0). apply CRle_Qle, Hc.
Qed.


(** [CRpower_positive_bounded] is should be used when a known bound
on the absolute value of x is available. *)
#[global]
Instance CRpower_N: Pow CR N := λ x n, ucFun (CRpower_N_bounded n (CR_b (1#1) x)) x.
Arguments CRpower_N x%_type n%_N.

Lemma CRpower_N_bounded_N_power : forall (n : N) (c:Qpos) (x:CR),
((- (' (proj1_sig c)) <= x /\ x <= 'proj1_sig c) ->
CRpower_N_bounded n c x == CRpower_N x n)%CR.
Proof.
 intros n c x Hc.
 assert (- ('proj1_sig (CR_b (1#1) x)) <= x
         /\ x <= ('proj1_sig (CR_b (1#1) x)))%CR as Hx.
 { split.
   rewrite -> CRopp_Qopp.
   apply CR_b_lowerBound.
  apply CR_b_upperBound. }
 unfold CRpower_N.
 generalize (CR_b (1#1) x) Hx.
 clear Hx.
 intros d Hd.
 destruct (Qlt_le_dec (proj1_sig c) (proj1_sig d)).
 apply CRpower_N_bounded_weaken. exact Hc. apply Qlt_le_weak, q.
 symmetry. apply CRpower_N_bounded_weaken; assumption.
Qed.

Lemma CRpower_N_correct : forall (n:N) x,
    (CRpower_slow x (N.to_nat n) == CRpower_N x n)%CR.
Proof.
 intros n x.
 rewrite <- (CRpower_N_bounded_N_power n (CR_b (1#1) x)).
 apply CRpower_N_bounded_correct.
 split. apply (CR_b_lowerBound (1#1) x).
 apply CR_b_upperBound.
 split. apply (CR_b_lowerBound (1#1) x).
 apply CR_b_upperBound.
Qed.

Lemma CRpower_N_correct' : forall (n:nat) x,
    (CRpower_slow x n == CRpower_N x (N_of_nat n))%CR.
Proof.
 intros n x.
 etransitivity; [| apply CRpower_N_correct].
 now rewrite Nnat.nat_of_N_of_nat.
Qed.

#[global]
Hint Rewrite CRpower_N_correct' : IRtoCR.

#[global]
Instance: Proper (eq ==> QposEq ==> @msp_eq _) Qpower_N_uc.
Proof.
  intros p1 p2 Ep e1 e2 Ee. apply ucEq_equiv.
  intro x.
  apply ball_closed.
  intros e epos.
  simpl. unfold QposEq in Ee.
  rewrite Ep, Ee.
  apply Qball_Reflexive.
  rewrite Qplus_0_l.
  apply Qlt_le_weak, epos.
Qed.

#[global]
Instance: Proper (eq ==> QposEq ==> @msp_eq _) CRpower_N_bounded. 
Proof. 
  intros p1 p2 Ep e1 e2 Ee.
  apply ucEq_equiv.
  intro x. simpl. rewrite Ep, Ee. reflexivity.
Qed. 

#[global]
Instance: Proper (@msp_eq _ ==> eq ==> @msp_eq _) CRpower_N.
Proof.
 intros x1 x2 Hx ? n Hn. subst.
 transitivity (CRpower_N_bounded n (CR_b (1 # 1) x1) x2).
  change (ucFun (CRpower_N_bounded n (CR_b (1#1) x1)) x1==ucFun (CRpower_N_bounded n (CR_b (1#1) x1)) x2)%CR.
  apply uc_wd; assumption.
 apply CRpower_N_bounded_N_power.
 split; rewrite <- Hx.
  rewrite -> CRopp_Qopp.
  apply CR_b_lowerBound.
 apply CR_b_upperBound.
Qed.
(* end hide *)

#[global]
Instance: NatPowSpec CR N _.
Proof.
  split; unfold pow. 
    apply _.
   intros x. change (cast Q CR 1 = CR1). now apply rings.preserves_1.
  intros x n.
  rewrite <- CRpower_N_correct.
  rewrite Nnat.nat_of_Nplus.
  simpl.
  rewrite CRpower_N_correct. reflexivity.
Qed.
