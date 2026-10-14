(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU General Public License Version 2 or later          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** * Escape-window separation for the fast constructive reals

    Mission.  This file transports the escape-window irrationality
    criterion to the fast constructive reals [CR] of CoRN.  Let
    [x : CR] and let [e : nat -> Q] be a family of positive window
    widths with the escape property [crn_escape_window x e]: every
    rational [q] eventually escapes the window of width [e n] centered
    at the [2^(-n)] approximation of [x], while the width dominates
    twice the dyadic resolution at the same index.  Then [x] is apart
    from every embedded rational ['q] in the sense of [CRapartT]: the
    disjoint-sum certificate that exhibits on which side of [q] the
    number [x] lies.

    The main statement is [crn_escape_window_apart].  Compared with the
    corresponding construction for the standard-library [CReal], the
    engine is shorter: the positivity witness of [CRpos_char] is a
    single positive rational value, so no Archimedean index pushdown is
    needed; the witness is the quarter of the escape margin
    [M = e n - 2 * 2^(-n)] at the escape index [n], and the coherence
    of the approximation function transports the escape inequality from
    the [2^(-n)] approximation to the [M/8] approximation.

    Dependencies.  CoRN [metric2]/[model]/[reals.fast] hierarchy
    ([CRmetric], [Qmetric], [QposMinMax], [CRFieldOps], [CRArith]);
    stdlib [QArith], [Qabs], [Qpower].

    Constructivity.  Statements are carried by [Set] and by the sum
    type [CRapartT]; the only [Prop] occurrences are [Qlt] predicates
    inside the sigma type and inside [CRlt].  No axiom and no classical
    logic is used; the main proof is a fully explicit chain of
    rational-order lemmas, decidability of [Q] being used only to
    branch on the sign.

    WARNING: this file is experimental and likely to change in future
    releases. *)

Require Import CoRN.metric2.Metric.
Require Import CoRN.metric2.UniformContinuity.
Require Import CoRN.model.metric2.Qmetric.
Require Import CoRN.model.totalorder.QposMinMax.
Require Import CoRN.model.metric2.CRmetric.
Require Import CoRN.reals.fast.CRFieldOps.
Require Import CoRN.reals.fast.CRArith.
From Coq Require Import QArith Qabs Qpower.

Set Implicit Arguments.

Local Open Scope Q_scope.
Local Open Scope CR_scope.

(* -- Positive-rational packings -- *)

Lemma crn_two_pos : (0 < 2)%Q.
Proof. unfold Qlt. cbn. reflexivity. Qed.

Lemma crn_pow2_pos : forall z : Z, (0 < 2 ^ z)%Q.
Proof. intros z. apply Qpower_0_lt. exact crn_two_pos. Qed.

(** The dyadic resolution [2^(-n)] of index [n], packed as a positive
    rational.  The projection [proj1_sig] of this packing reduces to
    the plain rational [2^(-n)], so the [Q]-side chain runs on the
    unpacked values. *)
Definition crn_dyadic (n : nat) : Qpos :=
  exist (Qlt 0) (2 ^ Z.opp (Z.of_nat n))%Q (crn_pow2_pos (Z.opp (Z.of_nat n))).

(** A positive rational seen as such.  This packing keeps the type of
    the witness the constant [Qpos], which the [Qpos]-to-[QposInf]
    coercion requires. *)
Definition crn_qpos (q : Q) (H : (0 < q)%Q) : Qpos := exist (Qlt 0) q H.

(* -- Definitional reductions of the approximations -- *)

(** The coherence of the approximation function: any two approximations
    of [x] differ by at most the sum of their precisions (the [Q]-side
    form of the record field of [x]). *)
Lemma crn_reg_le : forall (x : CR) (e1 e2 : Qpos),
  (-(proj1_sig e1 + proj1_sig e2)
    <= approximate x e1 - approximate x e2
    <= proj1_sig e1 + proj1_sig e2)%Q.
Proof. intros [xapprox xreg] e1 e2. exact (xreg e1 e2). Qed.

(** Adding two nonnegative rationals stays nonnegative. *)
Lemma crn_add_ge0 : forall a b : Q,
  (0 <= a)%Q -> (0 <= b)%Q -> (0 <= a + b)%Q.
Proof.
  intros a b Ha Hb.
  rewrite <- (Qplus_0_r 0%Q).
  apply (Qplus_le_compat 0%Q a%Q 0%Q b%Q Ha Hb).
Qed.

(** Adding a nonnegative rational increases, or preserves, a bound. *)
Lemma crn_le_add_r : forall x w : Q, (0 <= w)%Q -> (x <= x + w)%Q.
Proof.
  intros x w Hw.
  apply (Qle_trans x%Q (x + 0)%Q (x + w)%Q).
  - rewrite Qplus_0_r. apply Qle_refl.
  - apply (Qplus_le_compat x%Q x%Q 0%Q w%Q (Qle_refl x%Q) Hw).
Qed.

(* -- The escape-window structure and the separation engine -- *)

Definition crn_escape_window (x : CR) (e : nat -> Q) : Set :=
  forall q : Q,
    { n : nat |
      (Qlt (2 * proj1_sig (crn_dyadic n)) (e n)
       /\ Qlt (e n) (Qabs (q - approximate x (crn_dyadic n))))%Q }.

Theorem crn_escape_window_apart :
  forall (x : CR) (e : nat -> Q),
    crn_escape_window x e ->
    forall q : Q, CRapartT x ('q)%CR.
Proof.
  intros x e Hw q.
  destruct (Hw q) as [n0 [Hres Hesc]].
  set (E := e n0) in *.
  assert (Hd0val : proj1_sig (crn_dyadic n0) = (2 ^ Z.opp (Z.of_nat n0))%Q)
    by reflexivity.
  set (d0 := (2 ^ Z.opp (Z.of_nat n0))%Q) in *.
  rewrite Hd0val in Hres.
  assert (Hd0le : (0 <= d0)%Q) by (apply (Qlt_le_weak 0 d0); apply crn_pow2_pos).
  (* The margin [M = E - 2 * d0] is positive. *)
  assert (HM : (0 < E + -2*d0)%Q).
  { pose proof (Qplus_lt_le_compat (2*d0) E (-2*d0) (-2*d0)
                  Hres (Qle_refl (-2*d0))) as HH.
    assert (Heq0 : (2*d0 + -2*d0 == 0)%Q) by ring.
    rewrite Heq0 in HH. exact HH. }
  set (M := (E + -2*d0)%Q) in *.
  assert (Hd2 : (d0 <= 2*d0)%Q).
  { assert (Heq : (2*d0 == d0 + d0)%Q) by ring. rewrite Heq.
    apply (Qle_trans _ (d0 + 0)%Q).
    - rewrite Qplus_0_r. apply Qle_refl.
    - apply (Qplus_le_compat d0 d0 0 d0 (Qle_refl d0) Hd0le). }
  assert (H14 : (0 < (1#4))%Q) by (unfold Qlt; cbn; reflexivity).
  assert (HpM : (0 < M * (1#4))%Q).
  { pose proof (Qmult_lt_compat_r 0 M (1#4) H14 HM) as HH.
    rewrite Qmult_0_l in HH. exact HH. }
  assert (H38le : (0 <= M * (3#8))%Q)
    by (apply Qmult_le_0_compat;
        [apply (Qlt_le_weak 0 M HM)
        | apply (Qlt_le_weak 0 (3#8)); unfold Qlt; cbn; reflexivity]).
  assert (Hval2 : proj1_sig (crn_qpos HpM) = (M * (1#4))%Q)
    by reflexivity.
  destruct (Qlt_le_dec 0 (q - approximate x (crn_dyadic n0))) as [Hs | Hs].
  - (* [q] lies above the approximation: [x < 'q]. *)
    left.
    unfold CRltT.
    apply (CRpos_char (crn_qpos HpM)).
    assert (HabsS :
      (Qabs (q - approximate x (crn_dyadic n0))
       == q - approximate x (crn_dyadic n0))%Q).
    { apply Qabs_pos. apply Qlt_le_weak. exact Hs. }
    rewrite HabsS in Hesc.
    assert (Hgate :
      ((2#1) * (M * (1#4))
       <= q - approximate x (((1#2) * crn_qpos HpM)%Qpos))%Q).
    { remember (approximate x ((1#2) * crn_qpos HpM)%Qpos)
        as b0 eqn:Eb0.
      pose proof (crn_reg_le x (crn_dyadic n0)
                    ((1#2) * crn_qpos HpM)%Qpos) as Hreg.
      destruct Hreg as [Hlow Hupper].
      cbn [proj1_sig Qpos_mult] in Hupper.
      rewrite Hd0val, Hval2 in Hupper.
      rewrite <- Eb0 in Hupper.
      (* Hupper : approximate x (crn_dyadic n0) - b0 <= d0 + (1#2)*(M*(1#4)) *)
      assert (Hlow2 :
        (-(d0 + (1#2)*(M*(1#4))) <= approximate x (crn_dyadic n0) - b0)%Q).
      { cbn [proj1_sig Qpos_mult] in Hlow.
        rewrite Hd0val, Hval2 in Hlow.
        rewrite <- Eb0 in Hlow.
        exact Hlow. }
      assert (Hshift :
        ((q - approximate x (crn_dyadic n0))
         + -(d0 + (1#2)*(M*(1#4))) <= q - b0)%Q).
      { assert (Heq2 : (q - b0
                        == (q - approximate x (crn_dyadic n0))
                           + (approximate x (crn_dyadic n0) - b0))%Q) by ring.
        rewrite Heq2.
        apply (Qplus_le_compat (q - approximate x (crn_dyadic n0))
                               (q - approximate x (crn_dyadic n0))
                               (-(d0 + (1#2)*(M*(1#4))))
                               (approximate x (crn_dyadic n0) - b0)
                               (Qle_refl _) Hlow2). }
      assert (Hesc2 : (E + -(d0 + (1#2)*(M*(1#4))) < q - b0)%Q).
      { pose proof (Qplus_lt_le_compat E (q - approximate x (crn_dyadic n0))
                      (-(d0 + (1#2)*(M*(1#4)))) (-(d0 + (1#2)*(M*(1#4))))
                      Hesc (Qle_refl _)) as HH.
        apply (Qlt_le_trans (E + -(d0 + (1#2)*(M*(1#4))))%Q
                            ((q - approximate x (crn_dyadic n0))
                             + -(d0 + (1#2)*(M*(1#4))))%Q
                            (q - b0)%Q HH Hshift). }
      assert (HzeroW : (0 <= M * (3#8) + d0)%Q).
      { exact (crn_add_ge0 H38le Hd0le). }
      apply (Qle_trans ((2#1) * (M * (1#4)))%Q
                       (M * (7#8) + d0)%Q
                       (q - b0)%Q).
      - assert (HeqL : ((2#1) * (M * (1#4)) == M * (1#2))%Q) by ring.
        rewrite HeqL.
        assert (HeqR : (M * (7#8) + d0
                        == M * (1#2) + (M * (3#8) + d0))%Q) by ring.
        rewrite HeqR.
        apply (crn_le_add_r (M * (1#2))%Q HzeroW).
      - assert (HEM : (M == E + -2*d0)%Q) by reflexivity.
        assert (HEM2 : (E == M + 2*d0)%Q) by (rewrite HEM; ring).
        rewrite HEM2 in Hesc2.
        assert (HeqR2 : (((M + 2*d0) + -(d0 + (1#2)*(M*(1#4))))
                          == M * (7#8) + d0)%Q) by ring.
        rewrite HeqR2 in Hesc2.
        apply (Qlt_le_weak _ _ Hesc2). }
    exact Hgate.
  - (* [q] lies below the approximation: ['q < x]. *)
    right.
    unfold CRltT.
    apply (CRpos_char (crn_qpos HpM)).
    assert (HabsS :
      (Qabs (q - approximate x (crn_dyadic n0))
       == -(q - approximate x (crn_dyadic n0)))%Q).
    { apply Qabs_neg. exact Hs. }
    rewrite HabsS in Hesc.
    assert (HeqH : (-(q - approximate x (crn_dyadic n0))
                    == approximate x (crn_dyadic n0) - q)%Q) by ring.
    rewrite HeqH in Hesc.
    assert (Hgate :
      ((2#1) * (M * (1#4))
       <= approximate x (((1#2) * crn_qpos HpM)%Qpos) - q)%Q).
    { remember (approximate x ((1#2) * crn_qpos HpM)%Qpos)
        as b0 eqn:Eb0.
      pose proof (crn_reg_le x (crn_dyadic n0)
                    ((1#2) * crn_qpos HpM)%Qpos) as Hreg.
      destruct Hreg as [Hlow Hupper].
      cbn [proj1_sig Qpos_mult] in Hupper.
      rewrite Hd0val, Hval2 in Hupper.
      rewrite <- Eb0 in Hupper.
      assert (Hshift :
        ((approximate x (crn_dyadic n0) - q)
         + -(d0 + (1#2)*(M*(1#4))) <= b0 - q)%Q).
      { pose proof (Qopp_le_compat (approximate x (crn_dyadic n0) - b0)
                      (d0 + (1#2)*(M*(1#4))) Hupper) as H1.
        assert (Heq1 : (-(approximate x (crn_dyadic n0) - b0)
                        == b0 - approximate x (crn_dyadic n0))%Q) by ring.
        rewrite Heq1 in H1.
        assert (Heq2 : (b0 - q
                        == (approximate x (crn_dyadic n0) - q)
                           + (b0 - approximate x (crn_dyadic n0)))%Q) by ring.
        rewrite Heq2.
        apply (Qplus_le_compat (approximate x (crn_dyadic n0) - q)
                               (approximate x (crn_dyadic n0) - q)
                               (-(d0 + (1#2)*(M*(1#4))))
                               (b0 - approximate x (crn_dyadic n0))
                               (Qle_refl _) H1). }
      assert (Hesc2 : (E + -(d0 + (1#2)*(M*(1#4))) < b0 - q)%Q).
      { pose proof (Qplus_lt_le_compat E (approximate x (crn_dyadic n0) - q)
                      (-(d0 + (1#2)*(M*(1#4)))) (-(d0 + (1#2)*(M*(1#4))))
                      Hesc (Qle_refl _)) as HH.
        apply (Qlt_le_trans (E + -(d0 + (1#2)*(M*(1#4))))%Q
                            ((approximate x (crn_dyadic n0) - q)
                             + -(d0 + (1#2)*(M*(1#4))))%Q
                            (b0 - q)%Q HH Hshift). }
      assert (HzeroW : (0 <= M * (3#8) + d0)%Q).
      { exact (crn_add_ge0 H38le Hd0le). }
      apply (Qle_trans ((2#1) * (M * (1#4)))%Q
                       (M * (7#8) + d0)%Q
                       (b0 - q)%Q).
      - assert (HeqL : ((2#1) * (M * (1#4)) == M * (1#2))%Q) by ring.
        rewrite HeqL.
        assert (HeqR : (M * (7#8) + d0
                        == M * (1#2) + (M * (3#8) + d0))%Q) by ring.
        rewrite HeqR.
        apply (crn_le_add_r (M * (1#2))%Q HzeroW).
      - assert (HEM : (M == E + -2*d0)%Q) by reflexivity.
        assert (HEM2 : (E == M + 2*d0)%Q) by (rewrite HEM; ring).
        rewrite HEM2 in Hesc2.
        assert (HeqR2 : (((M + 2*d0) + -(d0 + (1#2)*(M*(1#4))))
                          == M * (7#8) + d0)%Q) by ring.
        rewrite HeqR2 in Hesc2.
        apply (Qlt_le_weak _ _ Hesc2). }
    exact Hgate.
Qed.
