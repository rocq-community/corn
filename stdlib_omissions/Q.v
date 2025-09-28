From Coq Require Import QArith ZArith NArith Qpower Qround Qround Qabs.
Require Import CoRN.stdlib_omissions.List.

Require CoRN.stdlib_omissions.Z.


Notation "x <= y < z" := (x <= y /\ y < z) : Q_scope.
Notation "x < y <= z" := (x < y /\ y <= z) : Q_scope.
Notation "x < y < z" := (x < y /\ y < z) : Q_scope.

Open Scope Q_scope.

Lemma Qnum_nonneg (x : Q) : (0 <= Qnum x)%Z <-> (0 <= x)%Q.
Proof.
  destruct x as [n d].
  unfold Qle. simpl.
  now rewrite Zmult_1_r.
Qed.

Lemma Qnum_nonpos (x : Q) : (Qnum x <= 0)%Z <-> (x <=  0)%Q.
Proof.
  destruct x as [n d].
  unfold Qle. simpl.
  now rewrite Zmult_1_r.
Qed.

Lemma Qle_dec x y: {Qle x y} + {~Qle x y}.
  intros.
  destruct (Qlt_le_dec y x); [right | left]; [apply Qlt_not_le |]; assumption.
Defined.

(* Proofs that the various injections into Q are homomorphisms w.r.t. the various operations: *)

Lemma Zplus_Qplus (m n: Z): inject_Z (m + n) = inject_Z m + inject_Z n.
Proof.
 unfold Qplus. simpl. unfold inject_Z.
 do 2 rewrite Zmult_1_r. reflexivity.
Qed.

Lemma Zsucc_Qplus (z: Z): inject_Z (Z.succ z) = inject_Z z + 1.
Proof. apply Zplus_Qplus. Qed.

Lemma Zmult_Qmult (x y: Z): inject_Z (x * y) = inject_Z x * inject_Z y.
Proof. reflexivity. Qed.

Lemma S_Qplus (n: nat): inject_Z (Z_of_nat (S n)) = inject_Z (Z_of_nat n) + 1.
Proof. rewrite inj_S. apply Zplus_Qplus. Qed.

Lemma Pmult_Qmult (x y: positive): inject_Z (Zpos (Pmult x y)) = inject_Z (Zpos x) * inject_Z (Zpos y).
Proof. rewrite Zpos_mult_morphism. apply Zmult_Qmult. Qed.

Lemma Zle_Qle (x y: Z): (x <= y)%Z = (inject_Z x <= inject_Z y).
Proof.
 unfold Qle. intros. simpl.
 do 2 rewrite Zmult_1_r. reflexivity.
Qed.

Lemma Zlt_Qlt (x y: Z): (x < y)%Z = (inject_Z x < inject_Z y).
Proof.
 unfold Qlt. intros. simpl.
 do 2 rewrite Zmult_1_r. reflexivity.
Qed.

Lemma Zdiv_Qdiv (n m: Z): (n / m)%Z = Qfloor (inject_Z n / inject_Z m).
Proof with simpl; try reflexivity.
 unfold Qfloor. intros. simpl.
 destruct m...
   rewrite Zdiv_0_r.
   rewrite Zmult_0_r...
  rewrite Zmult_1_r...
 rewrite <- Zopp_eq_mult_neg_1.
 rewrite <- (Z.opp_involutive (Zpos p)).
 rewrite Zdiv_opp_opp...
Qed.

Lemma Qle_nat (n: nat): 0 <= inject_Z (Z_of_nat n).
Proof. rewrite <- (Zle_Qle 0). apply Zle_0_nat. Qed.

Lemma inject_Z_injective (a b: Z): inject_Z a = inject_Z b <-> a = b.
Proof. unfold inject_Z. split; congruence. Qed.

Lemma Qeq_Zeq (a b: Z): (inject_Z a == inject_Z b) = (a = b).
Proof.
 unfold Qeq.
 simpl.
 intros.
 do 2 rewrite Zmult_1_r.
 reflexivity.
Qed.

Lemma positive_nonzero_in_Q (p: positive): ~ inject_Z (Zpos p) == 0.
Proof. discriminate. Qed.

#[global]
Hint Immediate positive_nonzero_in_Q.

(* Properties of arithmetic: *)

Lemma Qmult_injective_l (z: Q) (Znz: ~ z == 0): forall x y, (x * z == y * z <-> x == y).
Proof.
 split; intro E.
  rewrite <- (Qmult_1_r x).
  rewrite <- (Qmult_1_r y).
  rewrite <- (Qmult_inv_r _ Znz).
  do 2 rewrite Qmult_assoc.
  rewrite E. reflexivity.
 rewrite E. reflexivity.
Qed.

Lemma Qmult_injective_r (z: Q) (Znz: ~ z == 0): forall x y, (z * x == z * y <-> x == y).
Proof.
 intros. do 2 rewrite (Qmult_comm z).
 apply Qmult_injective_l. assumption.
Qed.

Lemma Qplus_injective_l (z: Q): forall x y, (x + z == y + z <-> x == y)%Q.
Proof with intuition.
 split; intro E.
  setoid_replace x with (x + z - z)%Q by (simpl; ring).
  setoid_replace y with (y + z - z)%Q by (simpl; ring).
  rewrite E; intuition; auto with *.
 rewrite E; auto with *.
Qed.

Lemma Qminus_eq (x y: Q): (x - y == 0 <-> x == y)%Q.
Proof.
 rewrite <- (Qplus_injective_l (-y) x y).
 rewrite Qplus_opp_r.
 reflexivity.
Qed.

Lemma Qinv_char x q: (x * q == 1) <-> (x == / q /\ ~ q == 0).
Proof with auto.
 split.
  intros A.
  assert (~ q == 0).
   intro B. apply Q_apart_0_1. rewrite <- A, B. ring.
  intuition.
  apply (Qmult_injective_l q)...
  rewrite A. field...
 intros [A ?]. rewrite A. field...
Qed.

Lemma Qdiv_1_r (q: Q): q / 1 == q.
Proof. field. Qed.

Lemma show_is_Qinv x q: x * q == 1 -> x == / q.
Proof. intros. apply Qinv_char. assumption. Qed.

Lemma Qabs_Qinv : forall q, Qabs (/ q) == / (Qabs q).
Proof.
  intros [n d]; simpl.
  unfold Qinv.
  case_eq n; intros; simpl in *; apply Qeq_refl.
Qed.

Lemma Qabs_Qminus x y: Qabs (x - y) == Qabs (y - x).
Proof.
 unfold Qminus.
 intros.
 rewrite <- (Qopp_opp x) at 1.
 rewrite <- Qopp_plus.
 rewrite Qplus_comm.
 apply Qabs_opp.
Qed.

Lemma Qlt_floor_alt (x : Q) :
  x - 1 < inject_Z (Qfloor x).
Proof.
  apply Qplus_lt_l with 1.
  ring_simplify.
  change 1 with (inject_Z 1).
  rewrite <-inject_Z_plus.
  apply Qlt_floor.
Qed.

Lemma Qfloor_pos (x : Q) : 
  1 <= x -> (0 < Qfloor x)%Z.
Proof.
  intros E.
  rewrite Zlt_Qlt.
  apply Qle_lt_trans with (x - 1).
   apply Qplus_le_l with 1.
   now ring_simplify.
  apply Qlt_floor_alt.
Qed.

Lemma Qpower_not_0 (a : Q) (n : Z) : 
  ~a==0 -> ~a ^ n == 0.
Proof.
  intros E1.
  destruct n; simpl.
    discriminate.
   now apply Qpower_not_0_positive.
  intros E2.
  destruct (Qpower_not_0_positive a p).
   easy.
  now rewrite <-Qinv_involutive, E2.
Qed.

Lemma Qpower_0_lt (a : Q) (n : Z) : 
  0 < a -> 0 < a ^ n.
Proof.
  intros E1.
  destruct (Qle_lt_or_eq 0 (a ^ n)) as [E2|E2]; try assumption.
   now apply Qpower_pos, Qlt_le_weak.
  symmetry in E2. contradict E2.
  apply Qpower_not_0.
  intros E3. symmetry in E3. 
  now destruct (Qlt_not_eq 0 a).
Qed.

Lemma Qneq_symmetry (x y : Q) :
  ~x == y -> ~y == x.
Proof. firstorder auto with crelations. Qed.

Lemma Qdiv_flip_le (x y : Q) :
  0 < x -> x <= y -> /y <= /x.
Proof.
  intros E1 E2.
  assert (0 < y) by now apply Qlt_le_trans with x.
  apply Qmult_le_l with x; try assumption.
  apply Qmult_le_l with y; try assumption.
  field_simplify. 
    now try (unfold Qdiv; rewrite 2!Qmult_1_r).
   now apply Qneq_symmetry, Qlt_not_eq.
  now apply Qneq_symmetry, Qlt_not_eq.
Qed.

Lemma Qdiv_flip_lt (x y : Q) :
  0 < x -> x < y -> /y < /x.
Proof.
  intros E1 E2.
  assert (0 < y) by now apply Qlt_trans with x.
  apply Qmult_lt_l with x; try assumption.
  apply Qmult_lt_l with y; try assumption.
  field_simplify. 
    now try (unfold Qdiv; rewrite 2!Qmult_1_r).
   now apply Qneq_symmetry, Qlt_not_eq.
  now apply Qneq_symmetry, Qlt_not_eq.
Qed.

(* Properties of arithmetic w.r.t. order: *)

Lemma Qpos_nonNeg (n d: positive): 0 <= Zpos n # d.
Proof. discriminate. Qed.

#[global]
Hint Immediate Qpos_nonNeg.

Lemma Qplus_le_l (z x y : Q): x + z <= y + z <-> x <= y.
Proof with auto with *.
 split; intros.
  setoid_replace x with (x + z + -z) by (simpl; ring).
  setoid_replace y with (y + z + -z) by (simpl; ring).
  apply Qplus_le_compat...
 apply Qplus_le_compat...
Qed.

Lemma Qplus_le_r (z x y : Q): z + x <= z + y <-> x <= y.
Proof. do 2 rewrite (Qplus_comm z). apply Qplus_le_l. Qed.

Lemma Qplus_lt_r (x y: Q) : x < y -> forall z, z + x < z + y.
Proof. intros E z. do 2 rewrite (Qplus_comm z). apply Qplus_lt_l. assumption. Qed.

Lemma Qmult_le_compat_l (x y z : Q): x <= y -> 0 <= z -> z * x <= z * y.
Proof. do 2 rewrite (Qmult_comm z). apply Qmult_le_compat_r. Qed.

Lemma Qopp_Qlt_0_l (x: Q): 0 < -x <-> x < 0.
Proof.
 split.
  rewrite <- (Qopp_opp x) at 2.
  apply (Qopp_lt_compat 0 (-x)).
 apply (Qopp_lt_compat x 0).
Qed.
 
Lemma Qopp_Qlt_0_r (x: Q): -x < 0 <-> 0 < x.
Proof. rewrite <- Qopp_Qlt_0_l, Qopp_opp. reflexivity. Qed.

Lemma Qmult_lt_0_compat (x y: Q): 0 < x -> 0 < y -> 0 < x * y.
Proof.
 destruct x, y. unfold Qlt. simpl.
 repeat rewrite Zmult_1_r.
 apply Zmult_lt_0_compat.
Qed.

#[global]
Hint Resolve Qmult_lt_0_compat.

Lemma Qmult_nonneg_nonpos (x y: Q):
  0 <= x -> y <= 0 -> x * y <= 0.
Proof with auto.
 unfold Qle. simpl.
 repeat rewrite Zmult_1_r. intros.
 rewrite <- (Zmult_0_r (Qnum x)).
 apply (Zmult_le_compat_l (Qnum y) 0 (Qnum x))...
Qed.

Lemma Qmult_neg_pos (x y : Q) : x < 0 -> 0 < y -> x * y < 0.
Proof.
intros H1 H2.
apply Qopp_Qlt_0_l. setoid_replace (- (x * y)) with ((- x) * y) by ring.
apply Qmult_lt_0_compat; trivial. now apply Qopp_Qlt_0_l.
Qed.

Lemma Qmult_pos_neg (x y : Q) : 0 < x -> y < 0 -> x * y < 0.
Proof. intros H1 H2. rewrite Qmult_comm. now apply Qmult_neg_pos. Qed.

Lemma Qmult_pos_r : forall x y : Q, 0 <= x -> 0 < x * y -> 0 < y.
Proof.
intros x y H1 H2.
destruct (Q_dec y 0) as [[? | ?] | H]; trivial.
+ exfalso. apply (Qlt_irrefl 0), Qlt_le_trans with (y := x * y); trivial.
  now apply Qmult_nonneg_nonpos; [| apply Qlt_le_weak].
+ rewrite H, Qmult_0_r in H2. exfalso; now apply (Qlt_irrefl 0).
Qed.

Lemma Qmult_pos_l : forall x y : Q, 0 <= y -> 0 < x * y -> 0 < x.
Proof. intros x y H1 H2. rewrite Qmult_comm in H2. now apply (Qmult_pos_r y x). Qed.

Lemma Qplus_lt_le_0_compat x y: 0 < x -> 0 <= y -> 0 < x + y.
Proof with auto.
 unfold Qlt, Qle. simpl.
 repeat rewrite Zmult_1_r. intros.
 apply Z.add_pos_nonneg.
  apply Zmult_lt_0_compat...
  reflexivity.
 apply Zmult_le_0_compat...
 discriminate.
Qed.

Lemma Qplus_le_lt_0_compat x y: 0 <= x -> 0 < y -> 0 < x + y.
Proof.
 rewrite Qplus_comm. intros.
 apply (Qplus_lt_le_0_compat y x); assumption.
Qed.

Lemma Qplus_nonneg (x y: Q): 0 <= x -> 0 <= y -> 0 <= x + y.
Proof.
 intros.
 change (0 + 0 <= x + y).
 apply Qplus_le_compat; assumption.
Qed.

Lemma Qplus_pos_compat (x y : Q) : 0 < x -> 0 < y -> 0 < x + y.
Proof. intros; apply Qplus_lt_le_0_compat; [| apply Qlt_le_weak]; trivial. Qed.

Lemma Qminus_less (x y : Q) : 0 <= y -> x - y <= x.
Proof.
intro H. rewrite <- (Qplus_0_r x) at 2. apply Qplus_le_r. change 0 with (-0).
now apply Qopp_le_compat.
Qed.

Lemma Qabs_Qle x y: (Qabs x <= y) <-> (-y <= x <= y).
Proof with intuition.
 split.
  split.
   rewrite <- (Qopp_opp x).
   apply Qopp_le_compat.
   apply Qle_trans with (Qabs (-x)).
    apply Qle_Qabs.
   rewrite Qabs_opp...
  apply Qle_trans with (Qabs x)...
  apply Qle_Qabs.
 intros.
 apply Qabs_case...
 rewrite <- (Qopp_opp y).
 apply Qopp_le_compat...
Qed.

Lemma Qabs_diff_Qle x y r: (Qabs (x - y) <= r) <-> (x - r <= y <= x + r).
Proof with try ring.
 intros.
 rewrite Qabs_Qle.
 rewrite <- (Qplus_le_r (r + y) (-r) (x- y)).
 rewrite <- (Qplus_le_r (y - r) (x-y) r).
 setoid_replace (r + y + -r) with y...
 setoid_replace (r + y + (x - y)) with (x + r)...
 setoid_replace (y - r + (x - y)) with (x - r)...
 setoid_replace (y - r + r) with y...
 intuition.
Qed.

Lemma Qabs_zero (x : Q) : Qabs x == 0 <-> x == 0.
Proof.
split; intro H; [| now rewrite H].
destruct (Q_dec x 0) as [[x_neg | x_pos] | x_zero]; [| | trivial].
+ rewrite Qabs_neg in H; [| apply Qlt_le_weak; trivial].
  now rewrite <- (Qopp_involutive x), H.
+ rewrite Qabs_pos in H; [| apply Qlt_le_weak]; trivial.
Qed.

Lemma Qabs_nonpos (x : Q) : Qabs x <= 0 -> x == 0.
Proof.
intro H. apply Qle_lteq in H. destruct H as [H | H].
+ elim (Qlt_not_le _ _ H (Qabs_nonneg x)).
+ now apply Qabs_zero.
Qed.

Lemma Qabs_le_nonneg (x y : Q) : 0 <= x -> (Qabs x <= y <-> x <= y).
Proof.
 intro A. rewrite Qabs_Qle_condition.
 split; [intros [_ ?]; trivial | intro A1; split; [| trivial]].
 apply Qle_trans with (y := 0); [| trivial].
 apply (Qopp_le_compat 0); eapply Qle_trans; eauto.
Qed.

Lemma Qdiv_le_1 (x y: Q): 0 <= x <= y -> x / y <= 1.
Proof with intuition.
 intros.
 assert (0 <= y) as ynnP by (apply Qle_trans with x; intuition).
 destruct y.
 destruct Qnum.
   change (x * 0 <= 1).
   rewrite Qmult_0_r...
  rewrite <- (Qmult_inv_r (Zpos p # Qden)).
   unfold Qdiv.
   apply Qmult_le_compat_r...
  discriminate.
 exfalso. apply ynnP...
Qed.

(* The following two lemmas are obtained from the lemmas with the same name
in Coq.QArith.QArith_base by replacing -> with <-> *)

Lemma Qle_shift_div_l : forall a b c, 0 < c -> (a * c <= b <-> a <= b / c).
Proof.
intros a b c A; split; [now apply Qle_shift_div_l |].
intro A1. apply (Qmult_le_r _ _ (/c)); [now apply Qinv_lt_0_compat |].
rewrite <- Qmult_assoc, Qmult_inv_r; [now rewrite Qmult_1_r | auto with qarith].
Qed.

Lemma Qle_shift_div_r : forall a b c, 0 < b -> (a <= c * b <-> a / b <= c).
Proof.
intros a b c A; split; [now apply Qle_shift_div_r |].
intro A1. apply (Qmult_le_r _ _ (/b)); [now apply Qinv_lt_0_compat |].
rewrite <- Qmult_assoc, Qmult_inv_r; [now rewrite Qmult_1_r | auto with qarith].
Qed.

Lemma Qle_div_l : forall a b c, 0 < b -> 0 < c -> (a / b <= c <-> a / c <= b).
Proof.
intros a b c A1 A2.
rewrite <- Qle_shift_div_r; [| easy]. rewrite (Qmult_comm c b). rewrite Qle_shift_div_r; easy.
Qed.

Lemma Qle_div_r : forall a b c, 0 < b -> 0 < c -> (b <= a / c <-> c <= a / b).
Proof.
intros a b c A1 A2.
rewrite <- Qle_shift_div_l; [| easy]. rewrite (Qmult_comm b c). rewrite Qle_shift_div_l; easy.
Qed.

Lemma Qle_half (x : Q) : 0 <= x -> (1 # 2) * x <= x.
Proof.
intro H. rewrite <- (Qmult_1_l x) at 2. apply Qmult_le_compat_r; auto with qarith.
Qed.

Lemma nat_lt_Qlt n m: (n < m)%nat -> (inject_Z (Z_of_nat n) + (1#2) < inject_Z (Z_of_nat m))%Q.
Proof with intuition.
 unfold lt.
 intros.
 apply Qlt_le_trans with (inject_Z (Z_of_nat n) + 1).
  do 2 rewrite (Qplus_comm (inject_Z (Z_of_nat n))).
  apply Qplus_lt_l; auto with *.
 pose proof (inj_le _ _ H).
 rewrite Zle_Qle in H0.
 rewrite <- S_Qplus...
Qed.

Lemma inject_Z_nonneg (z: Z): (0 <= z)%Z -> 0 <= inject_Z z.
Proof with auto.
 intro.
 change (inject_Z 0 <= inject_Z z).
 rewrite <- Zle_Qle.
 assumption.
Qed.

#[global]
Hint Resolve inject_Z_nonneg.

Lemma positive_in_Q (p: positive): 0 < inject_Z (Zpos p).
Proof.
 change (inject_Z 0 < inject_Z (Zpos p)).
 rewrite <- Zlt_Qlt.
 reflexivity.
Qed.

#[global]
Hint Immediate positive_in_Q.

Lemma Qlt_Qceiling (q : Q) : inject_Z (Qceiling q) < q + 1.
Proof.
apply Qplus_lt_l with (z := (-1 # 1)). setoid_replace (q + 1 + (-1 # 1))%Q with q.
+ assert (A := Qceiling_lt q). unfold Z.sub in A.
  now rewrite inject_Z_plus, inject_Z_opp in A.
+ now rewrite <- Qplus_assoc, Qplus_opp_r, Qplus_0_r.
Qed.

Lemma Zle_Qle_Qceiling (q : Q) (z : Z) : (Qceiling q <= z)%Z <-> q <= inject_Z z.
Proof.
split; intro A.
+ rewrite Zle_Qle in A. apply Qle_trans with (y := inject_Z (Qceiling q)); [apply Qle_ceiling | trivial].
+ apply Z.lt_pred_le. rewrite Zlt_Qlt. now apply Qlt_le_trans with (y := q); [apply Qceiling_lt |].
Qed.

Lemma le_Qle_Qceiling_to_nat (q : Q) (n : nat) :
  (Z.to_nat (Qceiling q) <= n)%nat <-> q <= inject_Z (Z.of_nat n).
Proof. rewrite Z.le_Zle_to_nat; apply Zle_Qle_Qceiling. Qed.

Lemma Qlt_Zlt_inject_Z (q : Q) (z : Z) : inject_Z z < q <-> (z < Qceiling q)%Z.
Proof.
assert (A : forall (x y : Q), not (x <= y)%Q <-> (y < x)%Q).
+ intros; split; [apply Qnot_le_lt | apply Qlt_not_le].
+ assert (A1 := Zle_Qle_Qceiling q z). apply Z.iff_not in A1.
  now rewrite A, Z.nle_gt in A1.
Qed.

Lemma Qlt_lt_of_nat_inject_Z (q : Q) (n : nat) :
  inject_Z (Z.of_nat n) < q <-> (n < Z.to_nat (Qceiling q))%nat.
Proof. rewrite (Qlt_Zlt_inject_Z q (Z.of_nat n)); apply Z.lt_Zlt_to_nat. Qed.

(** NoDup isn't /directly/ useful for Q because Q does not use a canonical representation
 and NoDup doesn't support setoid equalities such as Qeq. However, since we have Qred,
 which yields canonical representations, we can use: *)

Definition QNoDup (l: list Q): Prop := NoDup (map Qred l).

#[global]
Instance: Proper (Qeq ==> eq) Qred.
Proof. repeat intro. apply Qred_complete. assumption. Qed.

Lemma Qsmallest_less_average : forall a b : Q, a < b -> a < (a + b) * (1#2).
Proof.
  intros. apply (Qmult_lt_r _ _ (2#1)).
  reflexivity. 
  rewrite <- Qmult_assoc, (Qmult_comm (1#2)), Qmult_inv_r .
  apply (Qplus_lt_l _ _ (-a)).
  ring_simplify. exact H. discriminate.
Qed.

Lemma Qaverage_less_greatest : forall a b : Q, a < b -> (a + b) * (1#2) < b.
Proof.
  intros. apply (Qmult_lt_r _ _ (2#1)).
  reflexivity. 
  rewrite <- Qmult_assoc, (Qmult_comm (1#2)), Qmult_inv_r .
  apply (Qplus_lt_l _ _ (-b)).
  ring_simplify. exact H. discriminate.
Qed.
