Require Import CoRN.algebra.RSetoid.
Require Import CoRN.metric2.Metric.
Require Import CoRN.metric2.UniformContinuity.
From Coq Require Import QArith.
Require Import MathClasses.implementations.stdlib_rationals CoRN.model.structures.Qinf CoRN.model.structures.Qpossec CoRN.model.structures.QposInf CoRN.model.structures.QnonNeg MathClasses.interfaces.abstract_algebra MathClasses.implementations.QType_rationals MathClasses.interfaces.additional_operations.
Require Import CoRN.tactics.Qauto.
From Coq Require Import QOrderedType.
Require Import MathClasses.theory.rings MathClasses.theory.dec_fields MathClasses.orders.rings MathClasses.orders.dec_fields MathClasses.theory.nat_pow.
Require Import MathClasses.interfaces.naturals MathClasses.interfaces.orders.
Import peano_naturals.

Require Import CoRN.reals.fast.CRGeometricSum.
Import Qround Qpower.
Require Import CoRN.ode.metric.

Local Notation ball := mspc_ball.
Local Notation "x ²" := (x * x) (at level 30) : mc_scope.

Section BanachFixpoint.

Add Field Q : (stdlib_field_theory Q).

Context `{MetricSpaceClass X} {Xlim : Limit X} {Xcms : CompleteMetricSpaceClass X}.

Context (f : X -> X) `{!IsContraction f q} (x0 : X).

Let x n := Nat.iter n f x0.

Arguments x n%_mc.

Lemma x_Sn : forall n, x (1 + n) = f (x n).
Proof. reflexivity. Qed.

Let d := msd (x 0) (x 1).

Instance : PropHolds (0 ≤ d).
Proof. apply msd_nonneg. Qed.

Instance : PropHolds (0 ≤ q).
Proof. apply (lip_nonneg f q).
(* [apply (lip_nonneg f)] leaves a goal [IsLipschitz f q], which [apply _] solves *)
Qed.

Instance : PropHolds (q < 1).
Proof. apply (contr_lt_1 f q). Qed.

Instance : PropHolds (0 < 1 - q).
Proof.
assert (A := contr_lt_1 f q).
rewrite <- flip_lt_negate in A. apply (strictly_order_preserving (1 +)) in A.
now rewrite plus_negate_r in A.
Qed.

Global Instance : forall q : Q, PropHolds (0 < q) -> PropHolds (q ≠ 0).
Proof. apply lt_ne_flip. Qed.

Lemma dist_xn_xSn : forall n : nat, ball (d * q^n) (x n) (x (1 + n)).
Proof.
induction n using nat_induction.
+ rewrite nat_pow_0, right_identity; subst d; apply mspc_distance.
+ rewrite nat_pow_S. mc_setoid_replace (d * (q * q ^ n)) with (q * (d * q^n)) by ring.
  change (x (1 + n)) with (f (x n)); change (x (1 + (1 + n))) with (f (x (1 + n))).
  now apply contr_prf.
Qed.

Lemma dist_xm_xn : forall m n : nat, ball (d * q^m * (1 - q^n) / (1 - q)) (x m) (x (m + n)).
Proof.
intro m; induction n  as [| n IH] using nat_induction.
+ rewrite right_identity; apply mspc_refl.
  now rewrite nat_pow_0, plus_negate_r, right_absorb, left_absorb.
+ apply (mspc_triangle' (d * q^m * (1 - q^n) / (1 - q))%mc (d * q^(m + n))%mc (x (m + n))); trivial.
  - rewrite nat_pow_S, nat_pow_exp_plus. field; solve_propholds.
  - mc_setoid_replace (m + (1 + n)) with (1 + (m + n)) by ring. apply dist_xn_xSn.
Qed.

Lemma dist_xm_xn' : forall m n : nat, ball (d * q^m / (1 - q)) (x m) (x (m + n)).
Proof.
intros m n. apply (mspc_monotone (d * q^m * (1 - q^n) / (1 - q))%mc); [| apply dist_xm_xn].
apply (order_preserving (.* /(1 - q))). rewrite <- associativity.
apply (order_preserving (d *.)). rewrite <- (mult_1_r (q^m)) at 2.
apply (order_preserving (q^m *.)). rewrite <- (plus_0_r 1) at 2.
apply (order_preserving (1 +)). rewrite <- negate_0.
apply flip_le_negate. solve_propholds.
Qed.

Lemma Qpower_mc_power (e : Q) (n : nat) : (e ^ n)%Q = (e ^ n)%mc.
Proof.
induction n as [| n IH] using nat_induction.
+ now rewrite nat_pow_0.
+ rewrite Nat2Z.inj_add, Qpower_plus'.
  - now rewrite nat_pow_S, IH.
  - rewrite <- Nat2Z.inj_add; change 0%Z with (Z.of_nat 0); rewrite Nat2Z.inj_iff;
    apply not_eq_sym, O_S.
(*
SearchPattern (?x ≢ ?y -> ?y ≢ ?x).
Anomaly: Signature and its instance do not match. Please report.
*)
Qed.

Lemma Qstepl : forall (x y z : Q), x ≤ y -> x = z -> z ≤ y.
Proof. intros ? ? ? ? A2; now rewrite <- A2. Qed.

Lemma Qstepr : forall (x y z : Q), x ≤ y -> y = z -> x ≤ z.
Proof. intros ? ? ? ? A2; now rewrite <- A2. Qed.

Declare Left Step Qstepl.
Declare Right Step Qstepr.

Lemma binom_ineq (a : Q) (n : nat) : -1 ≤ a -> 1 + (inject_Z n) * a ≤ (1 + a)^n.
Proof.
intro A.
assert (A1 : 0 ≤ 1 + a) by (now apply (order_preserving (1 +)) in A; rewrite plus_negate_r in A).
induction n as [| n IH] using nat_induction.
+ rewrite nat_pow_0; change (1 + 0 * a ≤ 1); now rewrite mult_0_l, plus_0_r.
+ rewrite nat_pow_S. transitivity ((1 + a) * (1 + (inject_Z n) * a)).
  - rewrite Nat2Z.inj_add, inject_Z_plus.
    stepr (1 + (1 + (inject_Z n)) * a + (inject_Z n) * a²) by ring.
    (* [apply nonneg_plus_le_compat_r, nonneg_mult_compat.  does not work *)
    apply nonneg_plus_le_compat_r. apply nonneg_mult_compat; [solve_propholds | apply square_nonneg].
  - now apply (order_preserving ((1 + a) *.)) in IH.
Qed.

Lemma nat_pow_recip `{DecField A} `{Naturals B} `{!NatPowSpec A B pw} :
  (∀ x y : A, Decision (x = y)) ->
    forall (a : A) (n : B), (/a) ^ n = /(a ^ n).
Proof.
intros D a. apply naturals.induction.
+ intros n1 n2 E; now rewrite E.
+ rewrite !nat_pow_0; symmetry; apply dec_recip_1.
+ intros n IH. now rewrite !nat_pow_S, dec_recip_distr, IH.
Qed.

(*
Lemma power_tends_to_zero (e : Q) (n : nat) :
  0 < e -> Z.to_nat (Qceiling (q * (1 - e) / (e * (1 - q)))%mc) ≤ n -> q ^ n ≤ e.
Proof.
intros e_pos n_big.
assert (A : /e ≤ (/q)^n).
+ mc_setoid_replace (/ q) with (1 + (/ q - 1)) by ring.
  transitivity (1 + (n : Q) * (/ q - 1)).
  - apply Qle_Qceiling_nat in n_big. set (m := (n : Q)) in *.
    let T := type of n_big in match T with (Qle ?l ?r) => change (l ≤ r) in n_big end.
    apply (order_reflecting (-1 +)). rewrite plus_assoc, plus_negate_l, plus_0_l.
    apply (order_preserving (.* (/q - 1))) in n_big.
    apply (po_proper' n_big); [| easy]. field.
    (* When [plus_assoc : Associative (+)], the last rewrite does not work *)
cut (forall x y z : Q, x + (y + z) = (x + y) + z). intro ass. rewrite ass.
rewrite plus_assoc.
  - apply binom_ineq. rewrite <- (plus_0_l (-1)) at 1.
    apply (order_preserving (+ (-1))); solve_propholds.
+ rewrite nat_pow_recip in A; [| apply _]. apply flip_le_dec_recip in A; [| solve_propholds].
  now rewrite !dec_recip_involutive in A.
Qed.

SearchAbout (/ (/ _) )%mc.
flip_le_dec_recip
*)

Lemma power_tends_to_zero (e : Q) (n : nat) :
  0 < e -> Z.to_nat (Qceiling (/(e * (1 - q)))%mc) ≤ n -> q ^ n ≤ e.
Proof.
intros A1 A2.
assert (A3 : 0 < n).
+ let T := type of A2 in match T with (?lhs ≤ _) => apply lt_le_trans with (y := lhs) end; [| trivial].
  apply Q.Qlt_lt_of_nat_inject_Z; change (0 < / (e * (1 - q))); solve_propholds.
+ destruct n as [| n]; [elim (Nat.lt_irrefl _ A3) |].
  rewrite <- Qpower_mc_power.
  apply GeometricCovergenceLemma with (e := e ↾ A1); [solve_propholds .. |].
  apply (Q.le_Qle_Qceiling_to_nat _ (S n)), A2.
Qed.

Lemma const_x (N : Q -> nat) : d = 0 -> cauchy x N.
Proof.
intro eq_d_0.
assert (A := mspc_distance (x 0) (x 1)).
subst d; rewrite eq_d_0 in A.
assert (C : forall n, x n = x 0).
+ induction n as [| n IH] using nat_induction; [easy |].
  change (x (1 + n)) with (f (x n)). rewrite IH. symmetry; apply A.
+ intros e e_pos m n _ _. rewrite (C m), (C n). (* second "rewrite C" does not work *)
  apply mspc_refl. solve_propholds.
Qed.

Lemma cauchy_x : cauchy x (λ e, Z.to_nat (Qceiling (d / (e * (1 - q)²))%mc)).
Proof.
assert (d_nonneg : 0 ≤ d) by solve_propholds.
assert (d_pos_0 : 0 = d \/ 0 < d) by now apply le_equiv_lt.
destruct d_pos_0 as [d_0 | d_pos]; [now apply const_x |].
intros e e_pos.
(* without loss of generality, m ≤ n *)
match goal with
|- forall m n, @?G m n => intros m n; assert (A : forall m n, m ≤ n -> G m n)
end.
+ clear m n; intros m n le_m_n A _.
  rewrite <- (cut_minus_le n m); trivial. rewrite plus_comm.
  apply (mspc_monotone (d * q^m / (1 - q))%mc); [| apply dist_xm_xn'].
  cut (q ^ m ≤ e * (1 - q) / d).
  - intro A1. apply (order_preserving (d *.)), (order_preserving (.* /(1 - q))) in A1.
    apply (po_proper' A1); [easy | field; split; solve_propholds].
  - apply power_tends_to_zero; [solve_propholds |].
    apply (po_proper' A); [| easy]. apply f_equal, Qceiling_comp.
    match goal with |- (Qeq ?l ?r) => change (l = r) end.
    field; repeat split; solve_propholds.
+ assert (A1 : TotalRelation (A := nat) (≤)) by apply _; destruct (A1 m n).
  - now apply A.
  - intros; apply mspc_symm; now apply A.
Qed.

Definition fp := lim (reg_fun x _ cauchy_x).

Lemma banach_fixpoint : f fp = fp.
Proof.
assert (C := cauchy_x).
(* [Check seq_lim_lim (A := C)] says "Wrong argument name: A", but [About seq_lim_lim] shows A *)
eapply (iter_fixpoint f x); [easy | apply seq_lim_lim].
Qed.

End BanachFixpoint.
