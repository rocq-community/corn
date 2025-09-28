From Coq Require Import ZArith.
Require Import CoRN.stdlib_omissions.List.
From Coq Require Import QArith Qabs.
Require Import CoRN.model.totalorder.QposMinMax
  CoRN.model.metric2.Qmetric.
From Coq Require Import Program.
Require Import CoRN.stdlib_omissions.N
  CoRN.stdlib_omissions.Z
  CoRN.stdlib_omissions.Q.


Open Scope Q_scope.

Definition Qsum := fold_right Qplus 0.

Definition Σ (n: nat) (f: nat -> Q) := Qsum (map f (enum n)).

(** Properties of Σ: *)

Lemma Σ_sub f g n: Σ n f - Σ n g == Σ n (fun x => f x - g x).
Proof.
 unfold Σ. induction n. reflexivity.
 simpl. rewrite <- IHn. ring.
Qed.

Lemma Σ_mult n f k: Σ n f * k == Σ n (Qmult k ∘ f).
Proof.
 unfold Σ, Basics.compose.
 induction n. reflexivity.
 intros. simpl. rewrite <- IHn. ring.
Qed.

Lemma Σ_constant x n f: (forall i, (i < n)%nat -> f i == x) -> Σ n f == inject_Z (Z.of_nat n) * x.
Proof with auto.
 unfold Σ. induction n. reflexivity.
 simpl. intro E.
 rewrite IHn...
 rewrite E...
 rewrite P_of_succ_nat_Zplus.
 rewrite Q.Zplus_Qplus.
 ring.
Qed.

Lemma Σ_const x n: Σ n (fun _ => x) == inject_Z (Z.of_nat n) * x.
Proof. apply Σ_constant. reflexivity. Qed.

Lemma Σ_S_bound_back f n: Σ (S n) f == Σ n f + f n.
Proof. unfold Σ. simpl. ring. Qed.

Lemma Σ_S_bound_front n f: Σ (S n) f == Σ n (f ∘ S) + f O.
Proof.
 unfold Σ, Basics.compose.
 induction n; intros; simpl in *. ring.
 rewrite IHn. ring.
Qed.

Lemma Σ_S_bound_rev n f: Σ n (f ∘ S) == Σ (S n) f - f O.
Proof. rewrite Σ_S_bound_front. ring. Qed.

Lemma Σ_le f n (b: Q):
  (forall x, (x < n)%nat -> f x <= b) -> Σ n f <= inject_Z (Z.of_nat n) * b.
Proof.
 induction n. discriminate.
 intro.
 rewrite Q.S_Qplus.
 change (f n + Σ n f <= (inject_Z (Z.of_nat n) + 1) * b)%Q.
 assert ((inject_Z (Z.of_nat n) + 1) * b == b + inject_Z (Z.of_nat n) * b)%Q as E. ring.
 rewrite E.
 apply Qplus_le_compat; auto.
Qed.

Lemma Σ_abs_le f n (b: Q):
  (forall x, (x < n)%nat -> Qabs (f x) <= b) -> Qabs (Σ n f) <= inject_Z (Z.of_nat n) * b.
Proof.
 induction n.
  discriminate.
 intros.
 rewrite S_Zplus.
 rewrite Q.Zplus_Qplus.
 change (Qabs (f n + Σ n f) <= (inject_Z (Z.of_nat n) + 1) * b)%Q.
 assert ((inject_Z (Z.of_nat n) + 1) * b == b + inject_Z (Z.of_nat n) * b)%Q. ring.
 rewrite H0. clear H0.
 apply Qle_trans with (Qabs (f n) + Qabs (Σ n f))%Q.
  apply Qabs_triangle.
 apply Qplus_le_compat; auto.
Qed. 

Lemma Σ_wd f g n (H: forall x, (x < n)%nat -> f x == g x):
  Σ n f == Σ n g.
Proof with auto with *.
 unfold Σ. induction n; simpl...
 rewrite IHn... rewrite H...
Qed.

Lemma Σ_plus_bound m n f: Σ (m + n) f == Σ n f + Σ m (f ∘ plus n).
Proof with try reflexivity.
 induction m; simpl; intros.
  unfold Σ. simpl. ring.
 do 2 rewrite Σ_S_bound_back.
 rewrite Qplus_assoc.
 rewrite <- IHm.
 unfold Basics.compose.
 replace (f (m + n)%nat) with (f (n + m)%nat)...
 rewrite Nat.add_comm...
Qed.

Lemma Σ_mult_bound n m f:
  Σ (n * m) f == Σ n (fun i => Σ m (fun j => f (i * m + j)%nat)).
Proof.
 induction n; intros.
  reflexivity.
 unfold Σ in *.
 simpl.
 rewrite <- IHn.
 change (Σ (m + n * m) f == Σ m (fun j => f (n * m + j)%nat) + Σ (n * m) f).
 rewrite Σ_plus_bound.
 unfold Basics.compose.
 ring.
Qed.

Lemma Σ_Qball (f g: nat -> Q) (e: Q) (n: nat):
  0 <= e ->
  (forall i: nat, (i < n)%nat -> Qabs (f i - g i) <= e / inject_Z (Z.of_nat n)) ->
  Qball e (Σ n f) (Σ n g).
Proof with auto.
 intros epos H.
 apply Qball_Qabs.
 destruct n. simpl. exact epos.
 rewrite Σ_sub.
 setoid_replace e
   with (inject_Z (Z.of_nat (S n)) * (/ inject_Z (Z.of_nat (S n)) * e)).
  apply Σ_abs_le.
  intros ? E.
  specialize (H x E).
  rewrite Qmult_comm.
  assumption.
  unfold canonical_names.equiv, stdlib_rationals.Q_eq.
 field. discriminate.
Qed.

Lemma Σ_Qball_pos_bounds (f g: nat -> Q) (e: Q) (n: positive):
  (forall i: nat, (i < Pos.to_nat n)%nat -> Qball (e * (1#n)) (f i) (g i)) ->
  Qball e (Σ (Pos.to_nat n) f) (Σ (Pos.to_nat n) g).
Proof with intuition.
  intros.
  assert (0 <= e).
  { specialize (H O (Pos2Nat.is_pos n)).
    apply (msp_nonneg (msp (Q_as_MetricSpace))) in H.
    rewrite <- (Qmult_0_l (1#n)) in H.
    apply Qmult_le_r in H. exact H. reflexivity. }
  apply Σ_Qball. exact H0. intros.
 setoid_replace (e / inject_Z (Z.of_nat (nat_of_P n)))
   with (e * (1#n)).
  apply Qball_Qabs...
  unfold canonical_names.equiv, stdlib_rationals.Q_eq.
 rewrite <- Zpos_eq_Z_of_nat_o_nat_of_P; intuition; auto with *.
Qed.

Lemma Qmult_Σ (f: nat -> Q) n (k: nat):
  Σ n f * inject_Z (Z.of_nat k) == Σ (k * n) (f ∘ flip Nat.div k).
Proof with auto with *.
 unfold Basics.compose.
 rewrite Nat.mul_comm.
 rewrite Σ_mult_bound.
 unfold Qdiv.
 rewrite Σ_mult.
 apply Σ_wd.
 intros.
 unfold Basics.compose.
 rewrite (Σ_constant (f x))...
 intros.
 unfold flip.
 replace ((x * k + i) / k)%nat with x...
 apply (Nat.div_unique (x * k + i)%nat k x i)...
Qed.

Lemma Σ_multiply_bound (n:nat) (k: positive) (f: nat -> Q):
  Σ n f == Σ (Pos.to_nat k * n) (f ∘ flip Nat.div (Pos.to_nat k)) / inject_Z (Zpos k).
Proof.
 rewrite <- Qmult_Σ.
 rewrite <- Zpos_eq_Z_of_nat_o_nat_of_P.
 field. discriminate.
Qed.

Lemma Qball_hetero_Σ (n m: positive) f g (e:Q):
 (forall i: nat, (i < Pos.to_nat (n * m)%positive)%nat ->
   Qball (e * (1# (n * m)%positive))
     (/ inject_Z (Zpos m) * f (i / Pos.to_nat m)%nat)
     (/ inject_Z (Zpos n) * g (i / Pos.to_nat n)%nat)) ->
   Qball e (Σ (Pos.to_nat n) f) (Σ (Pos.to_nat m) g).
Proof.
 intros.
 rewrite (Σ_multiply_bound (Pos.to_nat n) m).
 rewrite (Σ_multiply_bound (nat_of_P m) n).
 rewrite Nat.mul_comm.
 rewrite <- nat_of_P_mult_morphism.
 unfold Qdiv.
 rewrite Σ_mult.
 rewrite Σ_mult.
 apply Σ_Qball_pos_bounds.
 intros.
 unfold Basics.compose.
 unfold flip.
 auto.
Qed.

(** Σ was defined above straightforwardly in terms of ordinary lists and without
 any efficiency consideration. In practice, building up a list with enum only to
 break it down immediately with Qsum is wasteful, and I strongly doubt Coq
 does list deforestation/fusion. Also, summing many Q's quickly yields large
 numerators and denominators. Hence, we now define a faster version
 which avoids the intermediate lists and uses Qred. The idea is to use
 fastΣ in the actual definition of operations, and to immediately rewrite it to Σ
 (using the correctness property) when doing proofs about said operations. *)

Section fastΣ.

  Fixpoint fast (f: nat -> Q) (left: nat) (sofar: Q): Q :=
    match left with
    | O => sofar
    | S n => fast f n (Qred (sofar + f n))
    end.

  Definition fastΣ (n: nat) (f: nat -> Q): Q := fast f n 0.

  Lemma fastΣ_correct n f: fastΣ n f == Σ n f.
  Proof.
   intros.
   rewrite <- (Qplus_0_r (Σ n f)).
   unfold Σ, fastΣ.
   generalize 0.
   induction n; intros.
    simpl. ring.
   change (fast f n (Qred (q + f n)) == Qsum (map f (enum (S n))) + q).
   rewrite IHn.
   rewrite Qred_correct.
   simpl.
   ring.
  Qed.

End fastΣ.
