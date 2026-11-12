(*
Copyright © 2008 Russell O’Connor

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
Require Import CoRN.model.totalorder.QposMinMax.
Require Import CoRN.metric2.Limit.
Require Export CoRN.metric2.FinEnum.
From Coq Require Import Zpow_facts.
Require Export CoRN.metric2.Complete.
Require Import CoRN.logic.Classic.
From Coq Require Import Qpower.
From Coq Require Import Qround.

Set Implicit Arguments.

Local Open Scope uc_scope.

(**
* Compact sets
This module formalizes compact sets as the completion of a finitely
enumerables sets.
*)
Section BishopCompact.

(**
** Bishop Compactness
This section formalizes Bishops definition of compactness to serve as a
reference specification for our definition of compactness.
*)

Variable X : MetricSpace.

Variable P : X -> Prop.

Definition CompleteSubset :=
 forall (f:Complete X), (forall e, P (approximate f e)) ->
 {y:X | P y & msp_eq (Cunit y) f}.

Definition ExtSubset :=
 forall x y, (msp_eq x y) -> (P x <-> P y).

Definition TotallyBoundedSubset :=
  forall (e:Qpos),
    {l : list X | forall y, In y l -> P y & forall x, P x -> exists y, In y l /\ ball (proj1_sig e) x y }.

(** A Bishop compact set is an (extensional) predicate that is complete
 and totally bounded. *)
Record CompactSubset :=
 {completeSubset : CompleteSubset
 ;totallyBoundedSubset : TotallyBoundedSubset
 ;extSubset : ExtSubset
 }.

End BishopCompact.

(* end hide *)
(**
** Definition of Compact
A compact set is defined as the completion of finite enumerations as
a metric space *)
Definition Compact X := Complete (FinEnum X).

(** This predicate says that the distance between x and s is zero
    (less than arbitrary e1+e2).
    As a compact s is closed, so it implies that x is in s.
    inCompact also converts the abstract s:Compact X into a usual
    subset Complete X -> Prop. *)
Definition inCompact {X : MetricSpace} (x:Complete X) (s:Compact X) : Prop :=
  forall (e1 e2:Qpos), FinSubset_ball (proj1_sig e1 + proj1_sig e2)
                                 (approximate x e1) (approximate s e2).
#[global] Instance: Params (@inCompact) 1 := {}.
(* begin hide *)
Add Parametric Morphism {X : MetricSpace} : (@inCompact X)
    with signature (@msp_eq _) ==> (@msp_eq _) ==> iff as inCompact_wd.
Proof.
 cut (forall x1 x2 : Complete X, msp_eq x1 x2 -> forall x3 x4 : Complete (FinEnum X),
   msp_eq x3 x4 -> (inCompact x1 x3 -> inCompact x2 x4)).
  intros Z x1 x2 Hx y1 y2 Hy.
  split.
   apply Z; assumption.
  apply Z; symmetry; assumption.
 intros x1 x2 Hx y1 y2 Hy H e1 e2.
 apply FinSubset_ball_closed.
 intros d dpos.
 set (d':=((1#4) * exist _ _ dpos)%Qpos).
 assert (Qeq (proj1_sig e1 + proj1_sig e2 + d)%Q
             (proj1_sig ((e1 + d') + (d' + d') +  (d' + e2))%Qpos))
   by (unfold d'; unfold QposEq; simpl; ring).
 apply (@FinSubset_ball_wd_full _
           (proj1_sig e1 + proj1_sig e2 + d)
           (proj1_sig ((e1 + d') + (d' + d') +  (d' + e2))%Qpos)
           H0 _ _ (reflexivity _) _ _ (reflexivity _)).
 apply regFunEq_equiv in Hy.
 apply FinSubset_ball_triangle_r with (approximate y1 d');[|apply Hy].
 symmetry in Hx.
 apply regFunEq_equiv in Hx.
 apply FinSubset_ball_triangle_l with (approximate x1 d');[apply Hx|].
 apply H.
Qed.
(* end hide *)
Section Compact.

Variable X : MetricSpace.

Let inCompact := @inCompact X.

Lemma inCompact_stable : forall x s, ~~inCompact x s -> inCompact x s.
Proof.
 intros x s H e1 e2.
 intros H0.
 contradict H.
 intros H1.
 revert H0.
 apply H1.
Qed.

(**
** Compact is Bishop Compact.
Here we show that our definiton of compactness satifies Bishop's compactness.

First we show that our compact sets are complete.
*)

Lemma CompactCompleteSubset : forall x, CompleteSubset _ (fun z => inCompact z x).
Proof.
 intros x a H.
 pose (exist (Qlt 0) (1#2) eq_refl) as half.
 exists (Cjoin a).
  abstract ( intros e1 e2; unfold inCompact in H; eapply FinSubset_ball_weak_le;
    [|apply (H (half*e1) (half*e1) e2)%Qpos]; simpl; rewrite -> Qle_minus_iff;
      ring_simplify; auto with *; apply Qmult_le_0_compat; auto with * ).
 apply CunitCjoin.
Defined.

Section CompactTotallyBounded.

(** In order to show that compact sets are totally bounded we need to assume
that the underlying metric space is located.  According to Bishop's
definition, every metric space is located.  Therefore this is a fair
assumption to make. *)
Hypothesis locatedX : locatedMetric X.

(** Finite subsets are located (and even compact), so their distance
    to a point is realized constructively by a point in the subset. *)
Lemma AlmostInExists : forall (e d:Q) x (s:FinEnum X),
    e < d -> FinSubset_ball e x s
    -> { n:nat | match nth_error s n with
              | None => False
              | Some y => ball d x y end }.
Proof.
  intros e d x s Hed.
  induction s.
  intro abs; exfalso; exact (FinSubset_ball_nil abs).
  intros H.
  destruct (@locatedX _ _ x a Hed) as [close|far].
  exists O. exact close.
  destruct IHs as [n Hy].
  abstract (intros H0; apply FinSubset_ball_orC in H; apply H; split; auto).
  exists (S n). exact Hy.
Defined.

Lemma AlmostInExists_weak : forall (e d:Q) x (s:FinEnum X),
    e < d -> FinSubset_ball e x s
    -> { y:X | In y s /\ ball d x y }.
Proof.
  intros. destruct (AlmostInExists H H0) as [n H1].
  pose proof (nth_error_In s n).
  destruct (nth_error s n) as [y|]. 2: contradiction.
  exists y. split. exact (H2 y eq_refl). exact H1.
Defined.
 
(* If we want to improve this with d = e, we have to double negate,
   because it would require finding the minimum of the distance function,
   which reduces to proving CRmin a b=a \/ CRmin a b=b. *)
Lemma InCompact_approx
  : forall (Y : Compact X) (x : Complete X) (d:Qpos) (e:Q),
    inCompact x Y
    -> proj1_sig d < e
    -> {y:X | In y (approximate Y d) /\ ball e x (Cunit y)}.
Proof.
  intros.
  unfold inCompact in H.
  assert (0 < (1#4) * (e - proj1_sig d)).
  { apply Qlt_minus_iff in H0.
    apply (Qpos_ispos ((1#4)*exist _ _ H0)). }
  specialize (H (exist _ _ H1) d).
  simpl in H.
  assert ((1#4) * (e - proj1_sig d) + proj1_sig d
          < (1#2) * (proj1_sig d + e)).
  { apply (Qplus_lt_l _ _ (-(1#4)*e - (1#2)*proj1_sig d)).
    ring_simplify. apply Qmult_lt_l.
    reflexivity. exact H0. }
  pose proof (AlmostInExists_weak H2 H) as [y [H3 H4]].
  exists y. split.
  exact H3.
  intros d1 d2. simpl.
  apply (@ball_weak_le _ (proj1_sig d1
                          + ((1 # 4) * (e - proj1_sig d))
                          + (1 # 2) * (proj1_sig d + e))).
  rewrite <- Qplus_assoc, <- Qplus_assoc.
  apply Qplus_le_r.
  apply (Qle_trans _ (e + 0)).
  rewrite Qplus_0_r.
  apply (Qplus_le_r _ _ (-(3#4)*e)).
  ring_simplify.
  setoid_replace (2#8) with (1#4) by reflexivity.
  apply Qmult_le_l. reflexivity.
  apply Qlt_le_weak, H0.
  apply Qplus_le_r, Qpos_nonneg.
  apply ball_triangle with (b:=(approximate x (Qpos2QposInf (exist _ _ H1)))).
  - apply (regFun_prf x d1 (exist _ _ H1)).
  - exact H4.
Qed.

Lemma InCompact_approxC
  : forall (Y : Compact X) (x : Complete X) (d:Qpos),
    inCompact x Y
    -> ~~exists y:X, In y (approximate Y d) /\ ball (proj1_sig d) x (Cunit y).
Proof.
  intros. intro abs.
  apply (infinitePidgeonHolePrinicple
                _ (approximate Y d)
                (fun n y => ball (proj1_sig d+(1#Pos.of_nat n)) x (Cunit y))).
  - intros n. apply existsWeaken.
    destruct (@InCompact_approx Y x d (proj1_sig d + (1 # Pos.of_nat n)) H)
      as [t [H0 H1]].
    apply (Qle_lt_trans _ (proj1_sig d+0)).
    rewrite Qplus_0_r. apply Qle_refl.
    apply Qplus_lt_r. reflexivity.
    exists t. split. intro H3; contradiction. exact H1.
  - intros t [H0 H1].
    contradict abs. exists t. split. exact H0.
    apply ball_closed. intros e epos.
    destruct e as [a n].
    specialize (H1 (Pos.to_nat n)).
    apply (msp_stable (msp (Complete X))).
    intro abs.
    unfold existsC in H1.
    contradict H1; intros k [H1 H3].
    contradict abs.
    apply (ball_weak_le) with (e:=proj1_sig d + (1 # Pos.of_nat k)).
    apply Qplus_le_r.
    apply (Qle_trans _ (1#n)).
    unfold Qle; simpl.
    apply Pos2Nat.inj_le.
    rewrite Nat2Pos.id.
    exact H1. 
    apply (Nat.lt_le_trans _ _ _ (Pos2Nat.is_pos n)) in H1.
    destruct k. inversion H1. discriminate.
    unfold Qle; simpl.
    apply (Z.mul_le_mono_nonneg_r 1 a (Z.pos n)).
    discriminate.
    unfold Qlt in epos. simpl in epos.
    rewrite Z.mul_1_r in epos.
    apply (Zlt_le_succ 0 a), epos.
    exact H3.
Qed.


(** The limit of this sequence constructs a point inside the compact set
    close to any point pt inside an approximation of the compact.
    The next point pt' is in approximate s (k*d), which converges to s
    when k < 1. By regularity of the compact s, the distance between
    the approximations at d and k*d is (1+k)*d. To constructively pick
    pt' we must bump the distance a bit by e and we get
    ball ((1+k)*d+e) pt pt'.
    Continuing we get
    ball ((1+k)*k*d+k*e) pt' pt''.
    By summing we see that the stream of points stays within distance
    (1+k)*d+e of pt, which we can take arbitrarily close to d,
    the initial distance between pt and the compact s.
 *)
Fixpoint CompactImproveApproximation (s:Compact X) (k d e:Qpos)
         (pt:X) (Hpt : InFinEnumC pt (approximate s d))
         (n : nat) { struct n } : X
  := match n with
     | O => pt
     | S p => let (f,_) := HausdorffBallHausdorffBallStrong
                            locatedX (regFun_prf s d (k*d)%Qpos) in
             let (pt',HptX) := f pt Hpt e in
             let (Hpt',_) := HptX in
             @CompactImproveApproximation s k (k*d) (k*e) pt' Hpt' p
     end.

(** This stream is Cauchy *)
Lemma CompactTotallyBoundedStreamCauchyLemma : forall n (k d:Qpos),
proj1_sig k < 1 ->
0 < (proj1_sig d*(1-proj1_sig k^Z.of_nat (S n))/(1-proj1_sig k)).
Proof.
 intros n k d Hk.
 unfold Qdiv. rewrite <- Qmult_assoc.
 apply (Qle_lt_trans _ (proj1_sig d * 0)).
 rewrite Qmult_0_r. apply Qle_refl.
 apply Qmult_lt_l.
 apply Qpos_ispos.
 apply (Qle_lt_trans _ ((1 - proj1_sig k ^ Z.of_nat (S n)) * 0)).
 rewrite Qmult_0_r. apply Qle_refl.
 apply Qmult_lt_l.
  unfold Qminus.
  rewrite <- Qlt_minus_iff.
  induction n.
   assumption.
  simpl.
  rewrite Pplus_one_succ_l.
  rewrite -> Qpower_plus_positive.
  apply Qlt_trans with (proj1_sig k*1).
  apply Qmult_lt_l. apply Qpos_ispos.
  exact IHn.
  rewrite Qmult_1_r. exact Hk.
 apply Qlt_shift_inv_l.
  unfold Qminus.
  rewrite <- Qlt_minus_iff.
  assumption.
 ring_simplify.
 constructor.
Qed.

(* In a friendlier notation, the distance is
((1+k)*d1+d2) * (1-k^(S n)) / (1-k)
*)
Lemma CompactImproveApproxCauchy1
  : forall n s (k d1 d2:Qpos) pt Hpt,
    proj1_sig k < 1 ->
    ball ((((1#1)+proj1_sig k)*proj1_sig d1+ proj1_sig d2)
          * (1-proj1_sig k^Z.of_nat(S n))/(1-proj1_sig k))
         pt (@CompactImproveApproximation s k d1 d2 pt Hpt n).
Proof.
  induction n; intros s k d1 d2 pt Hpt Hk.
  apply ball_refl.
  apply Qlt_le_weak.
  apply (CompactTotallyBoundedStreamCauchyLemma
           O k (((1#1) + k) * d1 + d2)%Qpos), Hk.
  simpl (CompactImproveApproximation s k d1 d2 Hpt (S n)).
  set (e:=(((1#1) + proj1_sig k) * proj1_sig d1 + proj1_sig d2)
          * (1 - proj1_sig k ^ Z.of_nat (S (S n))) / (1 - proj1_sig k)) in *.
  set (e0:=((d1 + k * d1 + d2)
            + exist _ _ (CompactTotallyBoundedStreamCauchyLemma
                           n _ (((1#1) + k)*(k*d1) + (k*d2)) Hk))%Qpos).
  setoid_replace e with (proj1_sig e0).
  - simpl.
    destruct (@HausdorffBallHausdorffBallStrong X locatedX
               (@proj1_sig Q (Qlt 0) d1 +
                @proj1_sig Q (Qlt 0) k * @proj1_sig Q (Qlt 0) d1)
               (@approximate _ (FinEnum_ball X) s (Qpos2QposInf d1))
               (@approximate _ (FinEnum_ball X) s (Qpos2QposInf (k * d1)))
               (@regFun_prf _ (FinEnum_ball X) s d1 (k * d1)%Qpos))
      as [f _].
    destruct (f pt Hpt d2) as [pt' [Hpt' Hpt'']].
    unfold e0.
    apply ball_triangle with pt'.
    assumption.
    apply (IHn s k (k * d1)%Qpos (k * d2)%Qpos pt' Hpt' Hk).
  - unfold e0, e.
    simpl. 
    assert (~proj1_sig k==0).
    { destruct k. simpl. intro abs. apply (Qlt_not_le _ _ q).
      rewrite abs. apply Qle_refl. }
    rewrite <- Pos.add_1_l.
    rewrite Qpower_plus_positive. simpl.
    field.
    intros H0.
    apply (Qlt_not_le _ _ Hk).
    rewrite -> Qle_minus_iff.
    setoid_replace (proj1_sig k + - (1))
      with (-(1-proj1_sig k)) by (simpl; ring).
    rewrite -> H0.
    discriminate.
Qed.

Lemma CompactImproveApproxCauchy2
  : forall (m n:nat) s (k d1 d2:Qpos) pt Hpt,
    proj1_sig k < 1 ->
    ball (proj1_sig k ^ (Z.of_nat m)
          * ((((1#1)+proj1_sig k)*proj1_sig d1+proj1_sig d2)
             *(1-proj1_sig k^Z.of_nat (S n))/(1-proj1_sig k)))
         (@CompactImproveApproximation s k d1 d2 pt Hpt m)
         (@CompactImproveApproximation s k d1 d2 pt Hpt (m + n)).
Proof.
  induction m; intros n s k d1 d2 pt Hpt Hk.
  simpl (proj1_sig k ^ Z.of_nat 0). rewrite Qmult_1_l.
  apply CompactImproveApproxCauchy1; assumption.
  pose (e':=(CompactTotallyBoundedStreamCauchyLemma
               n _ (((1#1)+k)*(k*d1) + (k*d2)) Hk)%Qpos).
  assert (~proj1_sig k==0) as knz.
  { destruct k. simpl. intro abs. apply (Qlt_not_le _ _ q).
    rewrite abs. apply Qle_refl. }
  assert (Qeq (proj1_sig k ^ (Z.of_nat (S m))
               * ((((1#1)+proj1_sig k)*proj1_sig d1+proj1_sig d2)
                  *(1-proj1_sig k^Z.of_nat (S n))/(1-proj1_sig k)))
              (proj1_sig (Qpos_power k (Z.of_nat m)*exist _ _ e')%Qpos)).
  { rewrite Nat2Z.inj_succ. simpl.
    setoid_replace (proj1_sig k ^ (Z.succ (Z.of_nat m)))
      with (proj1_sig k ^ (1+Z.of_nat m)).
    rewrite Qpower_plus. simpl. field.
    intros H0.
    apply (Qlt_not_le _ _ Hk).
    rewrite -> Qle_minus_iff.
    setoid_replace (proj1_sig k + - (1))
      with (-(1-proj1_sig k)) by (simpl; ring).
    rewrite -> H0.
    discriminate. exact knz.
    rewrite <- Z.add_1_l. reflexivity. }
  rewrite H. clear H.
  change (S m + n)%nat with (S (m + n))%nat.
  unfold Str_nth.
  simpl.
  destruct (@HausdorffBallHausdorffBallStrong X locatedX
               (@proj1_sig Q (Qlt 0) d1 +
                @proj1_sig Q (Qlt 0) k * @proj1_sig Q (Qlt 0) d1)
               (@approximate _ (FinEnum_ball X) s d1)
               (@approximate _ (FinEnum_ball X) s (k * d1)%Qpos)
               (@regFun_prf _ (FinEnum_ball X) s d1 (k * d1)%Qpos))
    as [f _].
  destruct (f pt Hpt d2) as [pt' [Hpt' _]].
  simpl.
  apply (IHm n s k (k*d1)%Qpos (k*d2)%Qpos pt' Hpt'); assumption.
Qed.

(* All points in the stream are in the approximations of s, 
   at precisions k^n * d1. *)
Lemma StreamInCompactApprox : forall n s k d1 d2 pt Hpt,
    {q:Qpos | InFinEnumC (@CompactImproveApproximation s k d1 d2 pt Hpt n)
                         (approximate s q)
              & QposEq q (Qpos_power k (Z.of_nat n)*d1) }.
Proof.
 induction n.
  intros.
  exists d1.
   assumption.
  unfold QposEq; simpl; ring.
 intros.
 unfold Str_nth.
 simpl.
 destruct (@HausdorffBallHausdorffBallStrong
             X locatedX
             (@proj1_sig Q (Qlt 0) d1 +
              @proj1_sig Q (Qlt 0) k * @proj1_sig Q (Qlt 0) d1)
             (@approximate _ (FinEnum_ball X) s d1)
             (@approximate _ (FinEnum_ball X) s (k * d1)%Qpos)
             (@regFun_prf _ (FinEnum_ball X) s d1 (k * d1)%Qpos))
   as [f _].
 destruct (f pt Hpt d2) as [pt' [Hpt' _]].
 destruct (IHn s k (k*d1) (k*d2) pt' Hpt')%Qpos as [q Hq Hq0].
 exists q.
  apply Hq.
 rewrite Zpos_P_of_succ_nat.
 unfold Z.succ.
 unfold QposEq, Qpos_power, proj1_sig. simpl.
 rewrite Z.add_comm.
 rewrite -> Qpower_plus. simpl. 
 unfold QposEq, proj1_sig in Hq0. simpl in Hq0.
 rewrite Hq0. unfold proj1_sig. ring.
 destruct k. simpl. intro abs.
 apply (Qlt_not_le _ _ q0).
 rewrite abs. apply Qle_refl.
Qed.

(* This is the index at which the stream has converged within e. *)
Definition CompactTotallyBoundedIndex (e d1 d2:Qpos) : Z :=
  Z.log2_up (Qceiling (((3#1)*proj1_sig d1+(2#1)*proj1_sig d2) / proj1_sig e)).

Hint Resolve Qinv_lt_0_compat. (* todo: move, and put in appropriate hint db *)

Lemma Qpower_inc : forall (n : nat) (a b : Q),
    0 < a
    -> a <= b
    -> a ^ Z.of_nat n <= b ^ Z.of_nat n.
Proof.
  induction n.
  - intros. discriminate.
  - intros. rewrite Nat2Z.inj_succ.
    rewrite <- Z.add_1_l.
    rewrite Qpower_plus, Qpower_plus.
    apply (Qle_trans _ (a * b ^ Z.of_nat n)).
    apply Qmult_le_l. exact H.
    apply IHn. exact H. exact H0.
    apply Qmult_le_compat_r. exact H0.
    apply Qpower_pos.
    refine (Qle_trans _ _ _ _ H0).
    apply Qlt_le_weak, H.
    intro abs. rewrite abs in H0.
    apply (Qlt_irrefl 0). exact (Qlt_le_trans _ _ _ H H0).
    intro abs. rewrite abs in H.
    apply (Qlt_irrefl 0 H).
Qed.

Lemma CompactTotallyBoundedIndexLemma : forall (e k d1 d2:Qpos),
    proj1_sig k <= 1#2 ->
    ((1+proj1_sig k)*proj1_sig d1 + proj1_sig d2)
    *proj1_sig k^(CompactTotallyBoundedIndex e d1 d2)/(1-proj1_sig k)
    <= proj1_sig e.
Proof.
 intros e k d1 d2 khalf.
 unfold Qdiv.
 rewrite Qmult_comm, Qmult_assoc.
 apply (Qle_trans
          _  (((3#1)*proj1_sig d1+(2#1)*proj1_sig d2)
              * proj1_sig k ^(CompactTotallyBoundedIndex e d1 d2))).
 - apply Qmult_le_compat_r.
   2: apply Qpower_pos, Qpos_nonneg.
   apply (Qle_trans _ ((2#1) * ((1 + proj1_sig k) * proj1_sig d1 + proj1_sig d2))).
   apply Qmult_le_compat_r.
   2: apply (Qpos_nonneg (((1#1)+k)*d1+d2)%Qpos).
   apply Qle_shift_inv_r.
   unfold Qminus. rewrite <- Qlt_minus_iff.
   apply (Qle_lt_trans _ _ _ khalf). reflexivity.
   setoid_replace 1%Q with ((2#1)*(1#2)) at 1 by reflexivity.
   apply Qmult_le_l. reflexivity.
   apply (Qplus_le_l _ _ (proj1_sig k - (1#2))).
   ring_simplify. exact khalf.
   rewrite Qmult_plus_distr_r.
   apply Qplus_le_l. rewrite Qmult_assoc.
   apply Qmult_le_r. apply Qpos_ispos.
   apply (Qplus_le_r _ _ (-(2#1))). ring_simplify.
   setoid_replace 1%Q with ((2#1)*(1#2)) by reflexivity.
   apply Qmult_le_l. reflexivity. exact khalf.
 - apply (Qle_trans _ (((3#1) * proj1_sig d1 + (2#1) * proj1_sig d2) *
                       (1#2) ^ (CompactTotallyBoundedIndex e d1 d2))).
   apply Qmult_le_l.
   apply (Qpos_ispos ((3#1) * d1 + (2#1) * d2)%Qpos).
   rewrite <- (Z2Nat.id (CompactTotallyBoundedIndex e d1 d2)).
   apply Qpower_inc.
   apply Qpos_ispos. exact khalf.
   apply Z.log2_up_nonneg.
   rewrite <- (Qmult_1_r (proj1_sig e)).
   rewrite <- (Qpower_1 (CompactTotallyBoundedIndex e d1 d2)).
   setoid_replace (1#1)%Q with ((2#1)*(1#2))%Q by reflexivity.
   rewrite Qmult_power, Qmult_assoc.
   apply Qmult_le_compat_r.
   2: apply Qpower_pos; discriminate.
   rewrite <- (Zpower_Qpower 2 (CompactTotallyBoundedIndex e d1 d2)).
   2: apply Z.log2_up_nonneg.
   rewrite (Qmult_comm (proj1_sig e)).
   apply (Qmult_le_r _ _ (/proj1_sig e)).
   apply Qinv_lt_0_compat, Qpos_ispos.
   rewrite <- Qmult_assoc, Qmult_inv_r, Qmult_1_r.
   unfold CompactTotallyBoundedIndex.
   unfold Qdiv.
   assert (0 < ((3#1) * proj1_sig d1 + (2#1) * proj1_sig d2) * / proj1_sig e).
   { apply (Qle_lt_trans _ (((3#1) * proj1_sig d1 + (2#1) * proj1_sig d2)*0)).
     rewrite Qmult_0_r. discriminate.
     apply Qmult_lt_l. apply (Qpos_ispos ((3#1)*d1 + (2#1)*d2)).
     apply Qinv_lt_0_compat, Qpos_ispos. }
   revert H.
   generalize (((3#1) * proj1_sig d1 + (2#1) * proj1_sig d2) * / proj1_sig e).
   intros q qpos.
   apply (Qle_trans _ _ _ (Qle_ceiling q)).
   rewrite <- Q.Zle_Qle.
   apply Z.log2_up_le_pow2.
   rewrite Q.Zlt_Qlt.
   exact (Qlt_le_trans _ _ _ qpos (Qle_ceiling q)).
   apply Z.le_refl.
   apply Qpos_nonzero.
Qed.

Definition CompactTotallyBounded_raw (s:Compact X) (k d1 d2:Qpos)
           (pt:X) Hpt (e:QposInf)
  : X
  := match e with
     | QposInfinity => pt
     | Qpos2QposInf e' => @CompactImproveApproximation
                           s k d1 d2 pt Hpt
                           (Z.to_nat (CompactTotallyBoundedIndex e' d1 d2))
     end.

(** This stream forms a regular function *)
Lemma CompactTotallyBounded_prf : forall (s:Compact X) (k d1 d2:Qpos) (pt:X) Hpt,
    proj1_sig k <= 1#2 ->
    is_RegularFunction (@ball X) (@CompactTotallyBounded_raw s k d1 d2 pt Hpt).
Proof.
 unfold CompactTotallyBounded_raw, is_RegularFunction.
 cut (forall (s : Compact X) (k d1 d2 : Qpos) (pt : X)
        (Hpt : InFinEnumC pt (approximate s d1)) (e1 e2 : Qpos),
         proj1_sig k <= 1#2 ->
     (Z.to_nat (CompactTotallyBoundedIndex e1 d1 d2) <= Z.to_nat (CompactTotallyBoundedIndex e2 d1 d2))%nat ->
     ball (proj1_sig e1 + proj1_sig e2)
          (@CompactImproveApproximation
             s k d1 d2 pt Hpt
             (Z.to_nat (CompactTotallyBoundedIndex e1 d1 d2)))
          (@CompactImproveApproximation
               s k d1 d2 pt Hpt
               (Z.to_nat (CompactTotallyBoundedIndex e2 d1 d2)))).
  - intros Z s k d1 d2 pt Hpt khalf e1 e2.
    destruct (le_lt_dec (Z.to_nat (CompactTotallyBoundedIndex e1 d1 d2))
                        (Z.to_nat (CompactTotallyBoundedIndex e2 d1 d2))).
    apply Z; auto.
    rewrite Qplus_comm.
    apply ball_sym.
    apply Z; auto with *.
  - intros s k d1 d2 pt Hpt e1 e2 khalf H.
 set (A:=Z.to_nat (CompactTotallyBoundedIndex e1 d1 d2)) in *.
 set (B:=Z.to_nat (CompactTotallyBoundedIndex e2 d1 d2)) in *.
 rewrite <- (Nat.sub_add _ _ H).
 rewrite Nat.add_comm.
 assert (proj1_sig k < 1) as Y.
 { apply (Qle_lt_trans _ _ _ khalf). reflexivity. }
  assert (Y0:= (CompactTotallyBoundedStreamCauchyLemma
                  (B-A) k (((1#1)+k)*d1 + d2) Y)%Qpos).
  apply ball_weak_le with (proj1_sig (Qpos_power k (Z.of_nat A)*(exist _ _ Y0))%Qpos).
  2: apply CompactImproveApproxCauchy2; exact Y.
  simpl.
 unfold Qdiv.
 set (C:=(((1 + proj1_sig k) * proj1_sig d1 + proj1_sig d2)
          * proj1_sig k ^ Z.of_nat A * / (1 - proj1_sig k))).
 setoid_replace ( proj1_sig k ^ Z.of_nat A *
  (((1 + proj1_sig k) * proj1_sig d1 + proj1_sig d2) *
   (1 - Qpower_positive (proj1_sig k) (Pos.of_succ_nat (B - A))) * 
   / (1 - proj1_sig k)))
   with ((1 - proj1_sig k ^ Z.of_nat (S (B - A))) * C)
   by (unfold C; simpl; ring).
 apply Qle_trans with (1*C).
 apply Qmult_le_r.
  unfold C.
  apply (Qle_lt_trans _ (0 *(/(1-proj1_sig k)))).
  rewrite Qmult_0_l. discriminate.
  apply Qmult_lt_r.
  apply Qinv_lt_0_compat.
  unfold Qminus. rewrite <- Qlt_minus_iff.
  exact Y.
  apply (Qpos_ispos ((((1#1) + k) * d1 + d2) * Qpos_power k (Z.of_nat A))). 
   rewrite -> Qle_minus_iff.
   ring_simplify.
   apply Qpower_pos_positive.
   apply Qpos_nonneg.
  rewrite Qmult_1_l.
 apply Qle_trans with (proj1_sig e1).
 unfold A in C.
 unfold C.
 rewrite Z2Nat.id.
  apply CompactTotallyBoundedIndexLemma.
  exact khalf.
  apply Z.log2_up_nonneg.
  rewrite <- Qplus_0_r at 1.
  apply Qplus_le_r, Qpos_nonneg.
Qed.

Definition CompactTotallyBounded_fun
           (s:Compact X) (k d1 d2:Qpos) (khalf : proj1_sig k <= 1#2)
           (pt:X) (Hpt : InFinEnumC pt (approximate s d1)) 
  : Complete X
  := Build_RegularFunction (@CompactTotallyBounded_prf s k d1 d2 pt Hpt khalf).

(** The limit is inside the compact set *)
Lemma CompactTotallyBoundedInCompact
  : forall (s:Compact X) (k d1 d2:Qpos) (khalf : proj1_sig k <= 1#2) (pt:X) Hpt,
 inCompact (@CompactTotallyBounded_fun s k d1 d2 khalf pt Hpt) s.
Proof.
 intros s k d1 d2 khalf pt Hpt e1 e2.
 simpl. 
 destruct (@StreamInCompactApprox
             (Z.to_nat (CompactTotallyBoundedIndex e1 d1 d2)) s k d1 d2 pt Hpt)
   as [q Hq Hq0].
 apply FinSubset_ball_closed.
 intros d dpos.
 apply FinSubset_ball_weak_le with (d + (proj1_sig q + proj1_sig e2)).
  simpl.
  rewrite -> Qle_minus_iff.
  setoid_replace (proj1_sig e1 + proj1_sig e2 + d + - (d + (proj1_sig q + proj1_sig e2)))
    with (proj1_sig e1 + - proj1_sig q) by (simpl; ring).
  rewrite <- Qle_minus_iff.
  unfold QposEq in Hq0. rewrite -> Hq0.
  eapply Qle_trans;[|apply (CompactTotallyBoundedIndexLemma e1 k d1 d2)].
  simpl.
  rewrite Z2Nat.id.
  cut (0 <= proj1_sig k ^ (CompactTotallyBoundedIndex e1 d1 d2)).
  { generalize ( proj1_sig k ^ (CompactTotallyBoundedIndex e1 d1 d2)).
   intros z Hz.
   clear - Hz khalf.
   apply Qle_shift_div_l.
   unfold Qminus. rewrite <- Qlt_minus_iff.
   apply (Qle_lt_trans _ _ _ khalf). reflexivity.
   rewrite <- Qmult_assoc, Qmult_comm.
   apply Qmult_le_compat_r. 2: exact Hz.
   apply (Qle_trans _ ((1 + proj1_sig k) * proj1_sig d1 + 0)).
   rewrite Qplus_0_r, Qmult_comm.
   apply Qmult_le_compat_r. 2: apply Qpos_nonneg.
   apply Qplus_le_r.
   apply (Qle_trans _ 0).
   apply (Qopp_le_compat 0), Qpos_nonneg.
   apply Qpos_nonneg.
   apply Qplus_le_r, Qpos_nonneg. }
  apply Qpower_pos.
  apply Qpos_nonneg.
  apply Z.log2_up_nonneg.
  exact khalf.
 eapply FinSubset_ball_triangle_r;[|apply regFun_prf].
 replace d with (proj1_sig (exist _ _ dpos)) by reflexivity.
 apply FinSubset_ball_weak_le with (e1:=0).
 apply Qpos_nonneg. assumption.
Qed.

(** The limit is close to the initial starting point *)
Lemma CompactTotallyBoundedNotFar
  : forall (s:Compact X) (k d1 d2:Qpos) (khalf : proj1_sig k <= 1#2)
      (pt:X) (Hpt : InFinEnumC pt (approximate s d1)),
    ball (((1 + proj1_sig k)*proj1_sig d1 + proj1_sig d2)
            / (1 - proj1_sig k))
         (Cunit pt) (@CompactTotallyBounded_fun s k d1 d2 khalf pt Hpt).
Proof.
 intros s k d1 d2 khalf pt Hpt e1 e2.
 simpl.
 assert (proj1_sig k < 1) as Z.
 { apply (Qle_lt_trans _ _ _ khalf). reflexivity. }
 pose proof (CompactTotallyBoundedStreamCauchyLemma
               (Z.to_nat (CompactTotallyBoundedIndex e2 d1 d2))
               _ (((1#1)+k)*d1 + d2)%Qpos Z) as Z0.
 apply ball_weak_le with (proj1_sig (exist _ _ Z0)).
 2: apply CompactImproveApproxCauchy1; exact Z.
 simpl.
 apply Qle_trans with (((1 + proj1_sig k) * proj1_sig d1 + proj1_sig d2) / (1 - proj1_sig k)).
 apply Qmult_le_compat_r.
 - rewrite <- (Qmult_1_r ( (1 + proj1_sig k) * proj1_sig d1 + proj1_sig d2)) at 2.
  apply Qmult_le_l.
  apply (Qpos_ispos (((1#1)+k)*d1 + d2)).
   rewrite -> Qle_minus_iff.
   ring_simplify.
   apply Qpower_pos_positive.
   apply Qpos_nonneg.
 - apply Qlt_le_weak, Qinv_lt_0_compat.
   unfold Qminus. rewrite <- Qlt_minus_iff. exact Z.
 - apply (Qle_trans _ (0 + (((1 + proj1_sig k) * proj1_sig d1 + proj1_sig d2) / (1 - proj1_sig k)) + 0)).
   rewrite Qplus_0_l, Qplus_0_r.
   apply Qle_refl.
   apply Qplus_le_compat. 2: apply Qpos_nonneg.
   apply Qplus_le_compat. apply Qpos_nonneg.
   apply Qle_refl.
Qed.

Fixpoint MapInFinEnumC {Y : Type} (l : list X)
         (f : forall pt : X, InFinEnumC pt l -> Y) { struct l } : list Y.
Proof.
  destruct l as [|m l].
  - exact nil.
  - apply cons.
    apply (f m).
    apply InFinEnumC_weaken; left; reflexivity.
    exact (MapInFinEnumC Y l (fun pt H => (f pt (FinSubset_ball_cons H)))).
Defined.

Lemma QuarterLeHalf : 1#4 <= 1#2.
Proof. discriminate. Qed.

(** Using CompactTotallyBounded_fun we can map the approximation of
a compact set to a new enumeration that contains only points inside
the compact sets, without moving the points too much *)
Definition CompactTotalBound (s:Compact X) (e:Qpos) : list (Complete X)
  := MapInFinEnumC (CompactTotallyBounded_fun
                      s (1#4)%Qpos ((1#5)*e) ((1#5)*e) QuarterLeHalf).

Lemma CompactTotalBoundNotFar : forall (s:Compact X) (e:Qpos),
    @ball (FinEnum (Complete X))
          ((3#5)*proj1_sig e)
          (map Cunit (approximate s ((1#5)*e)%Qpos))
          (CompactTotalBound s e).
Proof.
 intros s e.
 unfold CompactTotalBound.
 generalize (CompactTotallyBoundedNotFar
               s (1#4)%Qpos ((1#5)*e) ((1#5)*e) QuarterLeHalf).
 generalize (CompactTotallyBounded_fun s (1 # 4) ((1 # 5) * e) 
          ((1 # 5) * e) QuarterLeHalf).
 induction (approximate s ((1 # 5) * e)%Qpos) as [|a s0]; intros H L.
 - apply ball_refl. apply (Qpos_nonneg ((3#5)*e)).
 - unfold Qdiv in L.
   split. apply (Qpos_nonneg ((3#5)*e)).
 split; intros x Hx.
   + apply FinSubset_ball_orC in Hx.
  destruct Hx as [G | Hx | Hx] using orC_ind.
    auto using existsC_stable.
   apply existsWeaken.
   exists (H a (InFinEnumC_weaken X a (a :: s0) (or_introl eq_refl))).
   split.
   intro abs; contradict abs.
   exists (H a (InFinEnumC_weaken X a (a :: s0) (or_introl eq_refl))).
   split. left. reflexivity. reflexivity.
   rewrite -> Hx.
   setoid_replace ((3 # 5) * proj1_sig e)
     with (((5 # 4) * proj1_sig ((1 # 5) * e)%Qpos + proj1_sig ((1 # 5) * e)%Qpos) *
         (4 # 3)) by (simpl; ring).
   apply L.
   set (H':=(fun pt (Hpt : InFinEnumC pt s0)
             => H pt (FinSubset_ball_cons Hpt))).
  assert (L':forall (pt : X) (Hpt : InFinEnumC pt s0),
    ball (m:=Complete X) (((1 + proj1_sig (1 # 4)%Qpos) * proj1_sig ((1 # 5) * e)%Qpos +
          proj1_sig ((1 # 5) * e)%Qpos) * / (1 - proj1_sig (1 # 4)%Qpos)) (Cunit pt) (H' pt Hpt)).
  { intros pt Hpt. apply L. }
  destruct (IHs0 H' L') as [_ [A _]].
  destruct (A x Hx) as [G | y [Hy0 Hy1]] using existsC_ind.
   auto using existsC_stable.
  apply existsWeaken.
  exists y.
  split; auto.
  exact (FinSubset_ball_cons Hy0).
   + apply FinSubset_ball_orC in Hx.
 destruct Hx as [G | Hx | Hx] using orC_ind.
   auto using existsC_stable.
  apply existsWeaken.
  exists (Cunit a).
  split.
  intro abs; contradict abs.
  exists (Cunit a). split. left. reflexivity. reflexivity.
  rewrite -> Hx.
  setoid_replace ((3 # 5) * proj1_sig e)
    with (((5 # 4) * proj1_sig ((1 # 5) * e)%Qpos + proj1_sig ((1 # 5) * e)%Qpos) *
          (4 # 3)) by (simpl; ring).
  apply ball_sym, L.
  set (H':=(fun pt (Hpt : InFinEnumC pt s0)
            => H pt (FinSubset_ball_cons Hpt))).
 assert (L':forall (pt : X) (Hpt : InFinEnumC pt s0),
   ball (m:=Complete X) (((1 + proj1_sig (1 # 4)%Qpos) * proj1_sig ((1 # 5) * e)%Qpos +
          proj1_sig ((1 # 5) * e)%Qpos) * / (1 - proj1_sig (1 # 4)%Qpos)) (Cunit pt) (H' pt Hpt)).
  intros pt Hpt.
  apply L.
 destruct (IHs0 H' L') as [_ [_ A]].
 destruct (A x Hx) as [G | y [Hy0 Hy1]] using existsC_ind.
  auto using existsC_stable.
 apply existsWeaken.
 exists y.
 split; auto.
 exact (FinSubset_ball_cons Hy0).
Qed.

(** This means that our compact sets are totally bounded. *)
Lemma CompactTotallyBoundedA : forall s e y, In y (CompactTotalBound s e) -> inCompact y s.
Proof.
 intros s e y.
 unfold CompactTotalBound.
 generalize (CompactTotallyBoundedInCompact
               s (1#4)%Qpos ((1#5)*e) ((1#5)*e) QuarterLeHalf).
 generalize (CompactTotallyBounded_fun s (1#4)%Qpos ((1#5)*e) ((1#5)*e) QuarterLeHalf).
 generalize (approximate s ((1 # 5) * e)%Qpos).
 intros l.
 induction l.
  contradiction.
 intros F L [H|H].
  rewrite <- H.
  apply L.
 eapply (IHl);[|apply H].
 intros pt Hpt.
 apply L.
Qed.

Lemma CompactTotallyBoundedB : forall s e x,
    (inCompact x s) -> exists y, In y (CompactTotalBound s e) /\ ball (proj1_sig e) x y.
Proof.
 intros s e x Hx.
 assert (Z:proj1_sig ((1 # 20) * e + (1 # 5) * e)%Qpos < proj1_sig ((7 # 20) * e)%Qpos).
  rewrite -> Qlt_minus_iff.
  simpl.
  ring_simplify.
  apply (Qpos_ispos ((200#2000)*e)).
 destruct (AlmostInExists_weak Z (Hx _ _)) as [y [Hy0 Hy1]].
 clear Z.
 unfold CompactTotalBound.
 revert Hy0.
 cut (forall pt Hpt, ball ((3#5)*proj1_sig e) (Cunit pt)
                     (@CompactTotallyBounded_fun s (1#4)%Qpos ((1#5)*e) ((1#5)*e)
                                                 QuarterLeHalf pt Hpt)).
 { generalize (CompactTotallyBounded_fun s (1#4)%Qpos ((1#5)*e) ((1#5)*e) QuarterLeHalf).
  generalize (approximate s ((1 # 5) * e)%Qpos).
  intros l.
  induction l.
   contradiction.
  intros F HF [H|H].
   econstructor.
   split.
    left.
    reflexivity.
   rewrite <- H in Hy1.
   clear - Hy1 HF.
   assert (QposEq e ((1#20)*e + (7#20)*e + (3#5)*e))
     by (unfold QposEq; simpl; ring).
   unfold QposEq in H. rewrite H. clear H.
   apply ball_triangle with (Cunit a);[|apply HF].
   apply ball_triangle with (Cunit (approximate x ((1#20)*e)%Qpos)).
    apply ball_approx_r.
   rewrite -> ball_Cunit.
   assumption.
  edestruct (fun F HF => IHl F HF H) as [y' [Hy'0 Hy'1]];
    [|exists y';split;[right;apply Hy'0|assumption]].
  intros pt Hpt.
  apply HF. }
 intros pt Hpt.
 assert (QposEq ((3#5)*e) ((5#3)*((1#5)*e) + (4#3)*((1#5)*e)))
   by (unfold QposEq; simpl; ring).
 unfold QposEq in H. rewrite H. clear H.
 pose proof (CompactTotallyBoundedNotFar
               s (1#4)%Qpos ((1 # 5) * e) ((1 # 5) * e) QuarterLeHalf Hpt).
 setoid_replace (proj1_sig ((5 # 3) * ((1 # 5) * e) + (4 # 3) * ((1 # 5) * e))%Qpos)
   with (((1 + proj1_sig (1 # 4)%Qpos) * proj1_sig ((1 # 5) * e)%Qpos +
          proj1_sig ((1 # 5) * e)%Qpos) / (1 - proj1_sig (1 # 4)%Qpos)).
 apply H.
 simpl. 
 unfold Qdiv.
 setoid_replace (/ (1 - (1 # 4))) with (4#3) by reflexivity.
 ring.
Qed.

Lemma CompactTotallyBounded : forall s, TotallyBoundedSubset _ (fun z => inCompact z s).
Proof.
 intros s e.
 exists (CompactTotalBound s e).
  apply CompactTotallyBoundedA.
 apply CompactTotallyBoundedB.
Defined.

(** And hence our compact sets are Bishop compact. *)
Lemma CompactAsBishopCompact : forall s, CompactSubset _ (fun z => inCompact z s).
Proof.
 intros s.
 split.
   apply CompactCompleteSubset.
  apply CompactTotallyBounded.
 abstract ( intros a b Hab; unfold inCompact; rewrite -> Hab; reflexivity).
Defined.

End CompactTotallyBounded.

(**
** Bishop Compact is Compact.
Next we must show that Bishop compact sets are compact according to our
definition.

Given a Bishop compact set we construct finite enumerations that approximate
that set. *)
Definition BishopCompactAsCompact_raw
 (P:Complete X->Prop) (HP:CompactSubset _ P) (e:QposInf) : (FinEnum X) :=
match e with
|QposInfinity => nil
|Qpos2QposInf e' =>
  (let (l,_,_) := (totallyBoundedSubset HP ((1#2)*e')) in
   map (fun x => approximate x (Qpos2QposInf ((1#2)*e'))) l)%Qpos
end.

(** These approximations are coherent *)
Lemma BishopCompactAsCompact_prf :
  forall P (HP:CompactSubset _ P),
    is_RegularFunction (@ball (FinEnum X)) (BishopCompactAsCompact_raw HP).
Proof.
 cut (forall (P : RegularFunction (@ball X) -> Prop) (HP : CompactSubset (Complete X) P) (e1 e2 : Qpos),
   hemiMetric X (proj1_sig e1 + proj1_sig e2) (fun a : X => InFinEnumC a
     (let (l, _, _) := totallyBoundedSubset HP ((1 # 2) * e1)%Qpos in
       map (fun x : RegularFunction (@ball X) => approximate x ((1 # 2) * e1)%Qpos) l)) (fun a : X =>
         InFinEnumC a (let (l, _, _) := totallyBoundedSubset HP ((1 # 2) * e2)%Qpos in
           map (fun x : RegularFunction (@ball X) => approximate x ((1 # 2) * e2)%Qpos) l))).
  intros Z P [HP0 HP HP1] e1 e2.
  split. apply (Qpos_nonneg (e1+e2)). split.
   apply Z.
  apply (hemiMetric_wd1 X (proj1_sig (e2+e1)%Qpos)).
   simpl; ring.
  apply Z.
 intros P [HP0 HP HP1] e1 e2 x Hx.
 unfold totallyBoundedSubset in Hx.
 destruct (HP ((1 # 2) * e1)%Qpos) as [l Hl0 Hl1].
 unfold totallyBoundedSubset.
 destruct (HP ((1 # 2) * e2)%Qpos) as [r Hr0 Hr1].
 simpl in *.
 assert (Z0:existsC (Complete X) (fun x' => In x' l /\ ball ((1#2)*proj1_sig e1) (Cunit x) x')).
  clear - Hx HP1.
  induction l.
   exfalso; exact (FinSubset_ball_nil Hx).
   simpl in Hx. apply FinSubset_ball_orC in Hx.
  destruct Hx as [ G | Hx | Hx] using orC_ind.
    auto using existsC_stable.
   apply existsWeaken.
   exists a.
   split; auto with *.
   rewrite -> Hx.
   apply (@ball_approx_l _ _ ((1#2)*e1)%Qpos).
  destruct (IHl Hx) as [G | z [Hz0 Hz1]] using existsC_ind.
   auto using existsC_stable.
  apply existsWeaken.
  exists z.
  auto with *.
 destruct Z0 as [ G | z [Hz0 Hz1] ] using existsC_ind.
  auto using existsC_stable.
 destruct (Hr1 _ (Hl0 _ Hz0)) as [ y [Hy0 Hy1]].
 apply existsWeaken.
 exists (approximate y (Qpos2QposInf ((1#2)%Qpos*e2))).
 split.
  clear - Hy0.
  induction r.
   elim Hy0.
  destruct Hy0 as [Hy0 | Hy0].
   rewrite Hy0.
   intro abs; contradict abs.
   exists (approximate y ((1 # 2) * e2)%Qpos).
   split. left. reflexivity. reflexivity.
   apply FinSubset_ball_cons.
  apply IHr; auto.
  setoid_replace (proj1_sig e1+proj1_sig e2)
    with (proj1_sig ((1#2)*e1 + (1#2)*e2 + (1#2)*e2 + (1#2)*e1))%Qpos
    by (simpl; ring).
 apply ball_weak. apply Qpos_nonneg.
 rewrite <- ball_Cunit.
 repeat eapply ball_triangle.
   apply Hz1.
  change (ball (proj1_sig ((1 # 2) * e2)%Qpos) z y) in Hy1.
  apply Hy1.
 apply ball_approx_r.
Qed.

(** Hence Bishop compact sets are compact in our sense. *)
Definition BishopCompactAsCompact
 (P:Complete X->Prop) (HP:CompactSubset _ P) : Compact X :=
Build_RegularFunction (BishopCompactAsCompact_prf HP).

Section Isomorphism.

(**
** Isomorphism
We claim that Bishop compact sets correspond to our compact sets, but
to be sure we need to show that the definitions are isomoprhic.  We
need to show that the conversions back and forth are equivalent to the
identity. *)
Hypothesis locatedX : locatedMetric X.

Lemma BishopCompact_Compact_BishopCompact1 :
 forall (P:Complete X->Prop) (HP:CompactSubset _ P) x,
  P x -> inCompact x (BishopCompactAsCompact HP).
Proof.
 intros P [HP1 HP2 HP3] x Hx e1 e2.
 unfold BishopCompactAsCompact, approximate, BishopCompactAsCompact_raw,
 totallyBoundedSubset.
 destruct (HP2 ((1 # 2) * e2)%Qpos) as [l Hl0 Hl1].
 destruct (Hl1 x Hx) as [y [Hy0 Hy1]].
 clear - Hy0 Hy1.
 induction l.
  contradiction.
 destruct Hy0 as [Hy0|Hy0].
 rewrite Hy0.
 intro abs; contradict abs.
 exists (approximate y ((1 # 2) * e2)%Qpos).
 split. left. reflexivity.
  rewrite <- ball_Cunit.
  assert (QposEq (e1+e2) (e1 + ((1 # 2) * e2 + (1 # 2) * e2)))
    by (unfold QposEq; simpl; ring).
  unfold QposEq in H. rewrite H. clear H.
  apply ball_triangle with x.
   apply ball_approx_l.
  apply ball_triangle with y.
   assumption.
  apply ball_approx_r.
  apply FinSubset_ball_cons.
 apply IHl.
 auto with *.
Qed.

Lemma BishopCompact_Compact_BishopCompact2 :
 forall (P:Complete X->Prop) (HP:CompactSubset _ P) x,
  inCompact x (BishopCompactAsCompact HP) -> P x.
Proof.
 intros P [HP1 HP2 HP3] x Hx.
 assert (Y:forall e:Qpos, proj1_sig ((7#8)*e)%Qpos < proj1_sig e).
  intros.
  rewrite -> Qlt_minus_iff.
  simpl.
  ring_simplify.
  apply (Qpos_ispos ((1#8)*e)).
 assert (A:forall (e:Qpos), {y | P y /\ ball (m:=Complete X) (proj1_sig e) x y}).
  intros e.
  assert (Hx':=Hx ((1#16)*e)%Qpos ((1#2)*e)%Qpos).
  unfold BishopCompactAsCompact, approximate, BishopCompactAsCompact_raw,
  totallyBoundedSubset in Hx'.
  clear - Hx' locatedX Y.
  destruct (HP2 ((1 # 2) * ((1 # 2) * e))%Qpos) as [l Hl0 Hl1].
  clear Hl1.
  induction l.
  exfalso; exact (FinSubset_ball_nil Hx').
  destruct (@Complete_located _ locatedX _ _ x a (Y e)) as [A|A].
   exists a.
   split; auto.
  apply IHl.
   intros y Hy.
   apply Hl0; auto with *.
   apply FinSubset_ball_orC in Hx'.
  destruct Hx' as [G | Hx' | Hx'] using orC_ind.
 intro abs; contradict G; intro G; contradiction.
   elim A.
   clear - Hx'.
   rewrite <- ball_Cunit in Hx'.
   assert (QposEq ((7 # 8) * e)
                  ((1#16)*e + ((1 # 16) * e + (1 # 2) * e) + (((1 # 2) * ((1 # 2) * e)))))
     by (unfold QposEq; simpl; ring).
   unfold QposEq in H. rewrite H. clear H.
   eapply ball_triangle.
    eapply ball_triangle.
     apply ball_approx_r.
    apply Hx'.
   apply ball_approx_l.
  assumption.
 set (f:=fun e => (let (y,_):= (A e) in y)).
 assert (Hf0:forall e:Qpos, ball (m:=Complete X) (proj1_sig e) (f e) x).
  intros e.
  unfold f.
  destruct (A e) as [y [_ Hy]].
  apply ball_sym.
  assumption.
 assert (Hf: is_RegularFunction (@ball (Complete X)) (fun e => match e with QposInfinity => f (1#1)%Qpos | Qpos2QposInf e' => f e' end)).
  intros e1 e2.
  apply ball_triangle with x.
   apply Hf0.
  apply ball_sym.
  apply Hf0.
 set (f':=(Build_RegularFunction Hf)).
 assert (Hf1 : forall (e:Qpos), P (approximate f' e)).
  intros e.
  simpl; unfold f.
  destruct (A e).
  tauto.
 destruct (HP1 f') as [y Hy].
  intros [e|]; apply Hf1.
 unfold ExtSubset in HP3.
 rewrite -> (HP3 x y); auto.
 rewrite <- Cunit_eq.
 rewrite -> m.
 intros e1 e2.
 apply ball_sym.
 rewrite Qplus_comm.
 apply ball_weak.
 rewrite Qplus_0_r. apply Qpos_nonneg.
 apply Hf0.
Qed.

Lemma BishopCompact_Compact_BishopCompact :
 forall (P:Complete X->Prop) (HP:CompactSubset _ P) x,
  P x <-> inCompact x (BishopCompactAsCompact HP).
Proof.
 intros P HP x.
 split.
  apply BishopCompact_Compact_BishopCompact1.
 apply BishopCompact_Compact_BishopCompact2.
Qed.

Lemma Compact_BishopCompact_Compact : forall s,
 msp_eq s (BishopCompactAsCompact (CompactAsBishopCompact locatedX s)).
Proof.
 intros s e1 e2.
 rewrite Qplus_0_r.
 assert (QposEq (e1 + e2)
                (e1 + (1#5)*((1#2)*e2) + ((3#5)*((1#2)*e2) + (1#2)*e2) + (1#10)*e2))
   by (unfold QposEq; simpl; ring).
 unfold QposEq in H. rewrite H. clear H. 
 apply ball_weak. apply Qpos_nonneg.
 apply ball_triangle with (approximate s ((1#5)*((1#2)*e2))%Qpos).
  apply regFun_prf.
 clear e1.
 rewrite -> FinEnum_map_Cunit.
 apply ball_triangle with (CompactTotalBound locatedX s ((1 # 2) * e2)).
  apply CompactTotalBoundNotFar.
  unfold ball, FinEnum.
  unfold BishopCompactAsCompact, approximate, BishopCompactAsCompact_raw.  
  unfold totallyBoundedSubset, CompactAsBishopCompact, CompactTotallyBounded.
 change (FinEnum_ball (Complete X)) with (@ball (FinEnum (Complete X))).
 induction (CompactTotalBound locatedX s ((1 # 2) * e2)). 
  apply ball_refl. apply Qpos_nonneg.
 destruct IHl as [_ [IHlA IHlB]].
 split. apply Qpos_nonneg.
 split; intros x Hx; apply FinSubset_ball_orC in Hx;
   (destruct Hx as [G | Hx | Hx] using orC_ind; [auto using existsC_stable
   |apply existsWeaken |]).
    exists (Cunit (approximate a ((1 # 2) * e2)%Qpos)).
    split.
    intro abs; contradict abs.
    exists (Cunit (approximate a ((1 # 2) * e2)%Qpos)).
    split. left. reflexivity. reflexivity.
    rewrite -> Hx.
    apply ball_approx_r.
   destruct (IHlA x Hx) as [ G | y [Hy0 Hy1]] using existsC_ind.
    auto using existsC_stable.
   apply existsWeaken.
   exists y.
   split; auto.
   apply FinSubset_ball_cons.
   exact Hy0.
  exists a.
  split.
  intro abs; contradict abs.
  exists a. split. left. reflexivity. reflexivity.
  rewrite -> Hx.
  apply ball_approx_l.
 destruct (IHlB x Hx) as [ G | y [Hy0 Hy1]] using existsC_ind.
  auto using existsC_stable.
 apply existsWeaken.
 exists y.
 split; auto.
 apply FinSubset_ball_cons.
 exact Hy0.
Qed.

End Isomorphism.

End Compact.

Require Import CoRN.metric2.Prelength.

Section CompactDistr.

Variable X : MetricSpace.

(**
** FinEnum distributes over Complete
The FiniteEnumeration monad distributes over the Completion monad.
This corresponds to a function from FinEnum (Complete X) to
Complete (FinEnum X).
*)
Definition FinCompact_raw (x: FinEnum (Complete X)) (e:QposInf) : FinEnum X :=
map (fun x => approximate x e) x.

Lemma FinCompact_prf : forall x,
    is_RegularFunction (@ball (FinEnum X)) (FinCompact_raw x).
Proof.
 intros x.
 cut (forall (e1 e2:Qpos), hemiMetric X (proj1_sig e1 + proj1_sig e2) (fun a : X => InFinEnumC a (FinCompact_raw x e1))
   (fun a : X => InFinEnumC a (FinCompact_raw x e2))).
  intros L e1 e2.
  split. apply (Qpos_nonneg (e1+e2)).
  split; auto.
  eapply hemiMetric_wd1;[|apply L].
  unfold QposEq; simpl; ring.
 intros e1 e2.
 induction x.
  apply hemiMetric_refl. apply (Qpos_nonneg (e1+e2)).
 intros b Hb.
 apply FinSubset_ball_orC in Hb.
 destruct Hb as [G | Hb | Hb] using orC_ind.
   auto using existsC_stable.
  apply existsWeaken.
  exists (approximate a e2).
  split.
  intro abs; contradict abs.
  exists (approximate a e2). split. left. reflexivity. reflexivity.
  rewrite -> Hb.
  apply regFun_prf.
 destruct (IHx b Hb) as [G | y [Hy0 Hy1]] using existsC_ind.
  auto using existsC_stable.
 apply existsWeaken.
 exists y.
 split; auto.
 apply FinSubset_ball_cons.
 exact Hy0.
Qed.

Definition FinCompact_fun (x: FinEnum (Complete X)) : Compact X :=
 Build_RegularFunction (FinCompact_prf x).

Lemma FinCompact_uc : is_UniformlyContinuousFunction FinCompact_fun Qpos2QposInf.
Proof.
 cut (forall e (d1 d2:Qpos) (a b : FinEnum (Complete X)), (hemiMetric (Complete X) e
   (fun a0 : Complete X => InFinEnumC a0 a) (fun a : Complete X => InFinEnumC a b)) ->
     (hemiMetric X (proj1_sig d1 + e + proj1_sig d2) (fun a0 : X => InFinEnumC a0 (approximate (FinCompact_fun a) d1))
       (fun a0 : X => InFinEnumC a0 (approximate (FinCompact_fun b) d2)))).
 - intros L e a b [_ [Hab0 Hab1]] d1 d2.
  split. apply (Qpos_nonneg (d1+e+d2)).
  split; auto.
  eapply hemiMetric_wd1;[|apply L;apply Hab1].
  unfold QposEq; simpl; ring.
 - intros e d1 d2 a b Hab c Hc.
 simpl in Hc.
 unfold FinCompact_raw in Hc.
 assert (existsC (Complete X) (fun d => InFinEnumC d a /\ msp_eq c (approximate d d1))).
  clear - Hc.
  induction a as [|a a0].
  exfalso; exact (FinSubset_ball_nil Hc).
  simpl in Hc. apply FinSubset_ball_orC in Hc.
  destruct Hc as [ G | Hc | Hc] using orC_ind.
    auto using existsC_stable.
   apply existsWeaken.
   exists a.
   split; auto.
   intro abs; contradict abs.
   exists a. split. left. reflexivity. reflexivity.
  destruct (IHa0 Hc) as [G | y [Hy0 Hy1]] using existsC_ind.
   auto using existsC_stable.
  apply existsWeaken.
  exists y.
  split; auto.
  apply FinSubset_ball_cons.
  exact Hy0.
 destruct H as [ G | d [Hd0 Hd1]] using existsC_ind.
  auto using existsC_stable.
 destruct (Hab d Hd0) as [ G | z [Hz0 Hz1]] using existsC_ind.
  auto using existsC_stable.
 clear - Hd1 Hz0 Hz1.
 induction b.
 exfalso; exact (FinSubset_ball_nil Hz0).
 apply FinSubset_ball_orC in Hz0.
 destruct Hz0  as [ G | Hz0 | Hz0] using orC_ind.
   auto using existsC_stable.
  apply existsWeaken.
  exists (approximate a d2).
  split.
  intro abs; contradict abs.
  exists (approximate a d2). split. left. reflexivity. reflexivity.
  rewrite -> Hz0 in Hz1.
  rewrite -> Hd1.
  apply Hz1.
 destruct (IHb Hz0) as [G | y [Hy0 Hy1]] using existsC_ind.
  auto using existsC_stable.
 apply existsWeaken.
 exists y.
 split; auto.
 apply FinSubset_ball_cons.
 exact Hy0.
Qed.

Definition FinCompact : FinEnum (Complete X) --> Compact X :=
 Build_UniformlyContinuousFunction FinCompact_uc.

Lemma FinCompact_correct : forall x (s:FinEnum (Complete X)),
 InFinEnumC x s <-> inCompact x (FinCompact s).
Proof.
 intros x s.
 split.
  intros H e1 e2.
  simpl.
  induction s.
  exfalso; exact (FinSubset_ball_nil H).
  move H after IHs.
  apply FinSubset_ball_orC in H.
  destruct H as [G | H | H] using orC_ind.
 intro abs; contradict G; intro G; contradiction.
 intro abs; contradict abs.
 exists (approximate a e2). split.
 left. reflexivity.
 specialize (H e1 e2).
 rewrite Qplus_0_r in H. exact H.
 apply FinSubset_ball_cons.
  apply IHs; auto.
 intros H.
 induction s.
  exfalso; exact (FinSubset_ball_nil (H (1#1) (1#1))%Qpos).
 unfold inCompact in H.
 simpl in H.
 set (P:= fun n (b:bool) => if b
   then (let e1 := (1#P_of_succ_nat n)%Qpos in let e2 := e1 in (ball (m:=X) (proj1_sig e1 + proj1_sig e2) (approximate x (Qpos2QposInf e1)) (approximate a (Qpos2QposInf e2))))
     else (let e1 := (1#P_of_succ_nat n)%Qpos in let e2 := e1 in (FinSubset_ball (proj1_sig e1 + proj1_sig e2) (approximate x (Qpos2QposInf e1)) (FinCompact_raw s (Qpos2QposInf e2))))).
 assert (L: (forall n : nat, existsC bool (fun x => ~ ~ In x (true :: false :: nil) /\ P n x))).
 { intros n.
   specialize (H (1#P_of_succ_nat n)%Qpos (1#P_of_succ_nat n)%Qpos).
   apply FinSubset_ball_orC in H.
   destruct H as [ G | L | L] using orC_ind.
    auto using existsC_stable.
   apply existsWeaken.
   exists true.
   split; auto with *.
  apply existsWeaken.
  exists false.
  split; auto with *. }
 destruct (infinitePidgeonHolePrinicple _ _ _ L) as [G | c [_ Hc]] using existsC_ind.
 intro abs. contradict G; intro G. contradiction.
 destruct c.
 - intro abs; contradict abs. exists a.
   split.
  left. reflexivity.
  unfold P in Hc.
  apply ball_eq.
  intros e epos.
  destruct (((1#4)*exist _ _ epos)%Qpos) as [[en ed] He] eqn:des.
  destruct en as [|en|en]. inversion He. 2: inversion He.
  simpl in He.
  destruct (Hc (pred (nat_of_P ed))) as [G | m [Hm0 Hm1]] using existsC_ind.
  apply (msp_stable (msp _)), G.
  set (m' := (1#P_of_succ_nat m)%Qpos).
  apply ball_weak_le with (proj1_sig (m' + (m' + m') + m')%Qpos).
   unfold m'.
   simpl.
   setoid_replace ((1 # Pos.of_succ_nat m) + ((1 # Pos.of_succ_nat m) + (1 # Pos.of_succ_nat m)) + (1 # Pos.of_succ_nat m))
     with ((1#P_of_succ_nat m)/(1#4)) by (simpl; field).
   apply Qle_shift_div_r.
    reflexivity.
   rewrite -> Qmult_comm. 
   setoid_replace ((1#4)*e) with (proj1_sig ((1#4)*exist _ _ epos)%Qpos)
     by reflexivity.
   rewrite des.
   unfold Qle; simpl.
   rewrite Zpos_mult_morphism.
   apply Z.le_trans with (Z.pos en * Z.pos ed)%Z.
   rewrite Z.mul_comm, <- Z.le_mul_diag_r.
   apply Pos.le_1_l. reflexivity.
   apply Zmult_le_compat_l. 2: discriminate.
   rewrite Pos.of_nat_succ.
   apply Pos2Nat.inj_le.
   rewrite Nat2Pos.id.
   rewrite <- (Nat.lt_succ_pred O _).
   apply le_n_S.
   exact Hm0.
   apply Pos2Nat.is_pos.
   discriminate.
  eapply ball_triangle;[|apply ball_approx_l].
  eapply ball_triangle;[apply ball_approx_r|].
  rewrite -> ball_Cunit.
  apply Hm1.
 - apply FinSubset_ball_cons.
 apply IHs.
 unfold P in Hc.
 intros e1 e2.
 apply FinSubset_ball_closed.
 intros d dpos.
 destruct (((1#4)*exist _ _ dpos)%Qpos) as [[dn dd] Hd] eqn:des.
 destruct dn as [|dn|dn]. inversion Hd. 2: inversion Hd. 
 destruct (Hc (pred (nat_of_P dd))) as [G | m [Hm0 Hm1]] using existsC_ind.
 intro abs; contradict G; intro G; contradiction.
 set (m' := (1#P_of_succ_nat m)%Qpos).
 apply FinSubset_ball_weak_le with (proj1_sig ((e1 + m') + (m' + m') + (m' + e2))%Qpos).
 simpl.
  rewrite -> Qle_minus_iff.
  setoid_replace ( proj1_sig e1 + proj1_sig e2 + d + -
  (proj1_sig e1 + (1 # Pos.of_succ_nat m) +
   ((1 # Pos.of_succ_nat m) + (1 # Pos.of_succ_nat m)) +
   ((1 # Pos.of_succ_nat m) + proj1_sig e2)))
    with (d + - (proj1_sig m' + (proj1_sig m' + proj1_sig m') + proj1_sig m'))
    by (simpl; ring).
  rewrite <- Qle_minus_iff.
  unfold m'.
  autorewrite with QposElim.
  setoid_replace (proj1_sig (1 # Pos.of_succ_nat m)%Qpos +
  (proj1_sig (1 # Pos.of_succ_nat m)%Qpos + proj1_sig (1 # Pos.of_succ_nat m)%Qpos) +
  proj1_sig (1 # Pos.of_succ_nat m)%Qpos)
    with ((1#P_of_succ_nat m)/(1#4)) by (simpl; field).
  apply Qle_shift_div_r.
   constructor.
  rewrite -> Qmult_comm.
  setoid_replace ((1#4)*d) with (proj1_sig ((1#4)*exist _ _ dpos)%Qpos) by reflexivity.
  rewrite des.
  unfold Qle; simpl.
  rewrite Zpos_mult_morphism.
  apply Z.le_trans with (Z.pos dn * Z.pos dd)%Z.
  rewrite Z.mul_comm, <- Z.le_mul_diag_r.
  apply Pos.le_1_l. reflexivity.
  apply Zmult_le_compat_l. 2: auto with *.
   rewrite Pos.of_nat_succ.
   apply Pos2Nat.inj_le.
   rewrite Nat2Pos.id.
   rewrite <- (Nat.lt_succ_pred O _).
   apply le_n_S.
   exact Hm0.
   apply Pos2Nat.is_pos.
   discriminate.
 eapply FinSubset_ball_triangle_r;[|apply regFun_prf].
 eapply FinSubset_ball_triangle_l;[apply regFun_prf|].
 apply Hm1.
Qed.

Lemma CompactCompleteCompact_prf : forall x,
    is_RegularFunction (@ball (Compact X)) (Cmap_raw FinCompact x).
Proof.
 intros x e1 e2.
 unfold Cmap_raw.
 simpl.
 apply (@FinCompact_uc (e1+e2)%Qpos).
 unfold ball_ex.
 apply regFun_prf.
Qed.

Definition CompactCompleteCompact_fun x : Complete (Compact X) :=
 Build_RegularFunction (CompactCompleteCompact_prf x).

Lemma CompactCompleteCompact_uc :
 is_UniformlyContinuousFunction CompactCompleteCompact_fun Qpos2QposInf.
Proof.
 intros e a b H d1 d2.
 simpl in *.
 apply (@FinCompact_uc (d1+e+d2)%Qpos).
 apply H.
Qed.

Definition CompactCompleteCompact : Compact (Complete X) --> Compact X :=
 uc_compose Cjoin (Build_UniformlyContinuousFunction CompactCompleteCompact_uc).

Lemma CompactCompleteCompact_correct : forall x s,
 inCompact x s <-> inCompact (Cjoin x) (CompactCompleteCompact s).
Proof.
 intros x s.
 split.
  intros H e1 e2.
  simpl.
  unfold Cjoin_raw.
  simpl.
  assert (Z:=(H ((1#2)*e1) ((1#2)*e2))%Qpos).
  intro abs.
  unfold FinSubset_ball in Z.
  contradict Z; intros [z [Hz1 Hz0]].
  revert abs.
   apply InFinEnumC_weaken in Hz1.
  rewrite -> FinCompact_correct in Hz1.
  apply FinSubset_ball_closed.
  intros d dpos.
  assert (Z0:=(Hz0  ((1#2)*e1) ((1#2)*exist _ _ dpos))%Qpos).
  assert (Z1:=(Hz1 ((1#2)*exist _ _ dpos) ((1#2)*e2))%Qpos).
  simpl in Z1.
  set (w0:=((1 # 2) * e1 + ((1 # 2) * e1 + (1 # 2) * e2) + (1 # 2) * exist _ _ dpos)%Qpos) in *.
  set (w1:= ((1 # 2) * exist _ _ dpos + (1 # 2) * e2)%Qpos) in *.
  assert (Qeq (proj1_sig e1 + proj1_sig e2 + d)
              (proj1_sig (w0 + w1)%Qpos))
    by (unfold w0, w1; simpl; ring).
 apply (@FinSubset_ball_wd_full _ _ _
           H0 _ _ (reflexivity _) _ _ (reflexivity _)).
 clear H0. 
  eapply FinSubset_ball_triangle_l.
   apply Z0.
  apply Z1.
 intros H e1 e2.
 apply FinSubset_ball_closed.
 intros d dpos.
 set (d':=((1#4)*exist _ _ dpos)%Qpos).
 assert (Qeq (proj1_sig e1 + proj1_sig e2 + d)
             (proj1_sig ((e1 + (1#2)*d' + (1#2)*d') + (((d' + d') + (1#2)*d') + ((1#2)*d' + e2)))%Qpos))
   by (unfold d'; simpl; ring).
 apply (@FinSubset_ball_wd_full _ _ _
           H0 _ _ (reflexivity _) _ _ (reflexivity _)).
 clear H0.
 eapply FinSubset_ball_triangle_l.
  eapply ball_triangle.
   apply regFun_prf.
  apply ball_approx_r.
 eapply FinSubset_ball_triangle_r;[|apply regFun_prf].
 assert (Z:= (H d' d')).
 simpl in Z.
 unfold Cjoin_raw in Z.
 intro abs. unfold FinSubset_ball in Z.
 contradict Z; intros [z [Hz1 Hz0]].
 revert abs.
  apply InFinEnumC_weaken in Hz1.
 change (InFinEnumC (X:=X) z (approximate (FinCompact (approximate s ((1 # 2) * d')%Qpos))
   ((1 # 2) * d')%Qpos)) in Hz1.
 apply FinSubset_ball_triangle_l with (Cunit z).
  rewrite -> ball_Cunit.
  assumption.
 clear - Hz1.
 induction ((approximate s ((1 # 2) * d')%Qpos)).
 exfalso; exact (FinSubset_ball_nil Hz1).
 apply FinSubset_ball_orC in Hz1.
 destruct Hz1 as [G | Hz1 | Hz1] using orC_ind.
 intro abs; contradict G; intro G; contradiction.
 intro abs; contradict abs.
 exists a. split. left. reflexivity.
  rewrite -> Hz1.
  apply ball_approx_l.
  apply FinSubset_ball_cons.
 apply IHm; auto.
Qed.

End CompactDistr.

(* A more synthetic presentation of CompactTotallyBounded_fun. *)
Lemma InApproxCompact
  : forall {X : MetricSpace} (K : Compact X) (x : X) (d:Qpos) (e : Q),
    InFinEnumC x (approximate K d)
    -> locatedMetric X
    -> proj1_sig d < e
    -> { y:Complete X | inCompact y K /\ ball e (Cunit x) y }.
Proof.
  intros X K x d e inx locX ltde.
  pose ((1#2)*(e-proj1_sig d)) as d2.
  pose (d2 / (proj1_sig d + e)) as k.
  assert (0 < proj1_sig d + e) as depos.
  { apply (Qlt_trans _ (proj1_sig d+0)).
    rewrite Qplus_0_r. apply Qpos_ispos.
    apply Qplus_lt_r. apply (Qlt_trans _ (proj1_sig d)).
    apply Qpos_ispos. exact ltde. }
  assert (0 < d2) as d2pos.
  { unfold d2. apply (Qle_lt_trans _ ((1#2)*0)).
    discriminate. apply Qmult_lt_l. reflexivity.
    unfold Qminus. rewrite <- Qlt_minus_iff. exact ltde. } 
  assert (0 < k) as kpos.
  { unfold k.
    apply (Qpos_ispos (exist _ _ d2pos * Qpos_inv (exist _ _ depos))%Qpos). }
  assert (k <= 1#2) as khalf.
  { unfold k. apply Qle_shift_div_r. exact depos.
    unfold d2. apply Qmult_le_l. reflexivity.
    unfold Qminus. rewrite Qplus_comm.
    apply Qplus_le_l. apply (Qle_trans _ 0).
    apply (Qopp_le_compat 0), Qpos_nonneg. apply Qpos_nonneg. }
  exists (CompactTotallyBounded_fun
       locX K (exist _ _ kpos) d (exist _ _ d2pos) khalf inx).
  split.
  apply CompactTotallyBoundedInCompact.
  pose proof (CompactTotallyBoundedNotFar
                locX K (exist _ _ kpos) d (exist _ _ d2pos) khalf inx) as H. 
  apply (ball_weak_le)
    with (e:= (((1 + proj1_sig (exist (Qlt 0) k kpos)) * proj1_sig d +
          proj1_sig (exist (Qlt 0) d2 d2pos)) /
         (1 - proj1_sig (exist (Qlt 0) k kpos)))).
  2: exact H.
  simpl.
  apply Qle_shift_div_r.
  unfold Qminus. rewrite <- Qlt_minus_iff.
  apply (Qle_lt_trans _ _ _ khalf). reflexivity.
  apply (Qplus_le_l _ _ (e*k - proj1_sig d)).
  ring_simplify.
  rewrite <- Qmult_plus_distr_r.
  unfold k, Qdiv.
  rewrite <- Qmult_assoc.
  rewrite <- (Qmult_comm (proj1_sig d + e)), Qmult_inv_r, Qmult_1_r.
  unfold d2.
  rewrite <- Qmult_plus_distr_l.
  setoid_replace ((1 # 2) + (1 # 2)) with 1%Q by reflexivity.
  rewrite Qmult_1_l.
  ring_simplify. apply Qle_refl.
  intro abs.
  rewrite abs in depos.
  exact (Qlt_irrefl 0 depos).
Qed.


Section CompactImage.

(**
** Compact Image

Given a function f : X -> Y, the image by f of a subset A : X -> Prop could
be defined as fun y:Y => exists x:X, A x /\ y = f x. When the subset A is
compact and f is uniformly continuous, we want to prove that the image f(A)
is also compact.

However this is hard to do with those definitions and the notion of Bishop
compactness given above, because we have to lift exists x:X, A x /\ y = f x
from Prop to Type, by developing an algorithm that constructs x. 

Our definition of compact by finite approximations allows to define the
compact images directly in Prop, simply by mapping f over the approximations.
In that definition, the function really applied is
Cmap f : Complete X -> Complete Y.
So a good example is X = Y = Q here. For more interesting continuous
functions we will need X = Q and Y = R, which we will handle by joining
the double completion in section CompactImageBind below.
*)
Variable z : Qpos.
Variable X Y : MetricSpace.
Hypothesis plX : PrelengthSpace X.
Hypothesis plFEX : PrelengthSpace (FinEnum X).

Variable f : X --> Y.

Lemma FinSubset_ball_map : forall (e d:Qpos) a (b:FinEnum X),
    (QposInf_le d (mu f e)) -> FinSubset_ball (proj1_sig d) a b ->
    FinSubset_ball (proj1_sig e) (f a) (FinEnum_map z f b).
Proof.
 intros e d a b Hd Hab.
 induction b.
 exfalso; exact (FinSubset_ball_nil Hab).
 apply FinSubset_ball_orC in Hab.
 destruct Hab as [G | Hab | Hab] using orC_ind.
 intro abs; contradict G; intro G; contradiction.
 intro abs; contradict abs.
 exists (f a0). split. left. reflexivity.
  apply uc_prf.
  eapply ball_ex_weak_le.
   apply Hd.
  assumption.
  apply FinSubset_ball_cons.
 apply IHb.
 auto.
Qed.

Lemma FinSubset_ball_map2 : forall (e1 e2 d:Qpos) a (b:FinEnum X),
    (QposInf_le d ((mu f e1) + (mu f e2))) -> FinSubset_ball (proj1_sig d) a b ->
 FinSubset_ball (proj1_sig e1 + proj1_sig e2) (f a) (FinEnum_map z f b).
Proof.
 intros e1 e2 d a b Hd Hab.
 induction b.
 exfalso; exact (FinSubset_ball_nil Hab).
 apply FinSubset_ball_orC in Hab.
 destruct Hab as [G | Hab | Hab] using orC_ind.
 intro abs; contradict G; intro G; contradiction.
 intro abs; contradict abs.
 exists (f a0). split. left. reflexivity.
  apply (mu_sum plX e2 (e1::nil) f).
  eapply ball_ex_weak_le.
   apply Hd.
  assumption.
  apply FinSubset_ball_cons.
 apply IHb.
 auto.
Qed.

(* The approximations of K : Compact X are finite lists of X which do not
   have to be exactly inside K. When mapping a function f over those
   approximations, we must make sure that they converge towards the exact
   images of points of K by f. *)
Definition CompactImage : Compact X --> Compact Y :=
  Cmap plFEX (FinEnum_map z f).

Lemma CompactImage_approx : forall (s : Compact X) (e : Qpos),
    approximate (CompactImage s) e
    = map f (approximate s (match mu f e with
                            | QposInfinity => z
                            | Qpos2QposInf d => d end)).
Proof.
  intros. simpl. unfold FinEnum_map_modulus.
  destruct (mu f e); reflexivity.
Qed.

(* The image of s by Cmap f is included in CompactImage s. *)
Lemma CompactImage_correct1 : forall (x : Complete X) (s : Compact X),
    inCompact x s
    -> inCompact (Cmap plX f x) (CompactImage s).
Proof.
 intros x s H e1 e2.
 apply FinSubset_ball_closed.
 intros d1 d1pos.
 assert (Qeq (proj1_sig e1 + proj1_sig e2 + d1)
             (proj1_sig ((e1 + (1#4)*exist _ _ d1pos)
                    + ((1#4)*exist _ _ d1pos
                       + ((1#4)*exist _ _ d1pos)) + ((1#4)*exist _ _ d1pos + e2))%Qpos))
   by (simpl; ring).
 apply (@FinSubset_ball_wd_full _ _ _
           H0 _ _ (reflexivity _) _ _ (reflexivity _)).
 clear H0. 
 apply FinSubset_ball_triangle_r with (approximate (CompactImage s) ((1#4)*exist _ _ d1pos)%Qpos); [|apply regFun_prf].
 apply FinSubset_ball_triangle_l with (approximate (Cmap plX f x) ((1#4)*exist _ _ d1pos)%Qpos); [apply regFun_prf|].
 remember (mu f ((1 # 4) * exist _ _ d1pos)) as dum.
 simpl.
 unfold FinEnum_map_modulus. simpl in Heqdum. rewrite <- Heqdum.
 destruct dum.
 - apply (FinSubset_ball_map2 ((1 # 4) * exist _ _ d1pos)
                        ((1 # 4) * exist _ _ d1pos) (q+q)%Qpos). 2: apply H.
   simpl. simpl in Heqdum. rewrite <- Heqdum. apply Qle_refl.
 - assert (Z:=H z z).
   simpl in Z.
   destruct (@approximate _ (FinEnum_ball X) s z).
   exfalso; exact (FinSubset_ball_nil Z).
   intro abs; contradict abs. exists (f m).
   split. left. reflexivity.
   set (d:=((1 # 4) * exist _ _ d1pos)%Qpos).
   apply (mu_sum plX d (d::nil) f).
   simpl.
   unfold d.
   simpl. rewrite <- Heqdum. constructor.
Qed.

(* The reverse inclusion. To finish the proof, we would need sequential
   compacity, that this produced sequence in Complete X has a converging
   subsequence. *)
Lemma CompactImage_correct2 : forall (y : Complete Y) (s : Compact X),
    locatedMetric Y
    -> inCompact y (CompactImage s)
    -> forall d:Qpos, { x:X | ball (proj1_sig d) (approximate y ((1 # 3) * d)%Qpos) (f x)
                /\ In x (approximate s (FinEnum_map_modulus z (mu f) ((1 # 3) * d))) }.
Proof.
  intros y s locY inys d.
  specialize (inys ((1#3)*d)%Qpos ((1#3)*d)%Qpos).
  simpl in inys.
  assert ((1#3)*proj1_sig d+(1#3)*proj1_sig d < proj1_sig d) as H.
  { rewrite <- Qmult_plus_distr_l.
    rewrite <- (Qmult_1_l (proj1_sig d)) at 2.
    apply Qmult_lt_r. apply Qpos_ispos. reflexivity. }
  destruct (AlmostInExists locY H inys) as [n H0].
  destruct (  @nth_error (msp_car Y)
           (@map (msp_car X) (msp_car Y) 
              (@ucFun X Y f)
              (@approximate (list (msp_car X)) 
                 (FinEnum_ball X) s
                 (Qpos2QposInf
                    (FinEnum_map_modulus z (@mu X Y f)
                       (Qpos_mult
                          (@exist Q (Qlt {| Qnum := Z0; Qden := xH |})
                             {| Qnum := Zpos xH; Qden := xI xH |}
                             (@eq_refl comparison Lt)) d))))) n)
           as [t|] eqn:des.
  2: contradiction.
  destruct (nth_error (approximate s (FinEnum_map_modulus z (mu f) ((1#3)*d))) n)
           eqn:H1.
  - exists m. split.
    2: exact (nth_error_In _ _ H1).
    pose proof (map_nth_error f n _ H1).
    simpl in des. simpl in H2.
    rewrite des in H2. inversion H2.
    subst t. clear H2 des. exact H0.
  - exfalso.
    apply nth_error_None in H1.
    rewrite <- (map_length f) in H1.
    apply nth_error_None in H1.
    simpl in des. simpl in H1.
    rewrite des in H1. discriminate.
Qed.

End CompactImage.

Section CompactImageBind.

Variable z : Qpos.
Variable X Y : MetricSpace.
Hypothesis plX : PrelengthSpace X.
Hypothesis plFEX : PrelengthSpace (FinEnum X).

Variable f : X --> Complete Y.

Definition CompactImage_b : Compact X --> Compact Y :=
 uc_compose (CompactCompleteCompact _) (CompactImage z plFEX f).

Lemma CompactImage_b_correct1 : forall (x : Complete X) (s : Compact X),
    inCompact x s
    -> inCompact (Cbind plX f x) (CompactImage_b s).
Proof.
 intros x s H.
 change (inCompact (Cjoin (Cmap_fun plX f x))
   (CompactCompleteCompact _ (CompactImage z plFEX f s))).
 rewrite <- CompactCompleteCompact_correct.
 apply CompactImage_correct1;assumption.
Qed.

(*
Lemma CompactImage_b_correctC
*)

End CompactImageBind.
