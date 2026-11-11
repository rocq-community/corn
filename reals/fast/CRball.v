Require Import CoRN.algebra.RSetoid.
Require Import CoRN.metric2.Metric.
Require Import CoRN.metric2.UniformContinuity.
From Coq Require Import Qabs.
Require Import CoRN.reals.fast.CRArith CoRN.reals.fast.CRabs.

(** Balls with real radii instead of rational radii. *)

Open Scope CR_scope.

Section contents.

  Context {M: MetricSpace}.

  Definition CRball (r: CR) (x y: M): Prop
    := forall (q:Q), r <= ' q -> ball q x y.

  Global Instance proper: Proper (@msp_eq _ ==> @msp_eq _ ==> @msp_eq _ ==> iff) CRball.
  Proof.
   intros ?? E ?? F ?? G.
   split. intros. intros q H0.
   rewrite <- E in H0.
   specialize (H q H0). rewrite <- F, <- G. exact H.
   intros. intros q H0.
   rewrite E in H0.
   specialize (H q H0). rewrite F, G. exact H.
  Qed.

  Global Instance reflexive (r: CR): CRnonNeg r -> Reflexive (CRball r).
  Proof with auto.
   unfold CRball, Reflexive.
   intros.
   apply ball_refl.
   apply CRle_Qle.
   apply CRle_trans with r...
   apply -> CRnonNeg_le_0...
  Qed.

  Lemma zero (x y: M): msp_eq x y <-> CRball 0 x y.
  Proof with auto.
   split. intros H z zpos.
   apply (@ball_weak_le _ 0). apply CRle_Qle, zpos.
   exact H. intros. apply H. apply CRle_refl.
  Qed.

  Lemma weak_le (r r': CR): r <= r' -> forall x y, CRball r x y -> CRball r' x y.
  Proof. intros ??? E ??. apply E. apply CRle_trans with r'; assumption. Qed.

  Lemma rational (r: Q) (x y: M): ball r x y <-> CRball ('r) x y.
  Proof with auto.
   split...
   repeat intro.
   apply CRle_Qle in H0.
   apply ball_weak_le with r...
   intros. apply H, CRle_refl.
  Qed.

End contents.
#[global] Instance: Params (@CRball) 1 := {}.

(* In the CR metric space, CRball is what you'd expect. *)

Lemma as_distance_bound (r x y: CR): CRball r x y <-> CRdistance x y <= r.
Proof with auto.
 unfold CRball.
 rewrite <- CRdistance_CRle.
 assert ((forall x0 : Q, r <= ' x0 -> x - ' x0 <= y /\ y <= x + ' x0) <->
         x - r <= y /\ y <= x + r).
 split; intros.
 - split.
   + apply CRplus_le_l with (r - y).
     CRring_replace (r - y + (x - r)) (x - y).
     CRring_replace (r - y + y) r.
   apply (proj1 (Qle_CRle_r _ _)).
   intros.
   apply CRplus_le_l with (y - ' y').
   CRring_replace (y - 'y' + (x - y)) (x - 'y').
   CRring_replace (y - 'y' + 'y') y.
   now apply (H y').
   + apply CRplus_le_r with (-x).
  CRring_replace (x + r - x) r.
  apply (proj1 (Qle_CRle_r _ _)). intros.
  apply CRplus_le_l with x.
  CRring_replace (x + (y - x)) y...
  apply H...
 - split.
  apply CRle_trans with (x - r).
  apply CRplus_le_compat...
  apply CRle_refl.
   apply -> CRle_opp...
  apply H.
 apply CRle_trans with (x + r).
  apply H.
 apply CRplus_le_compat...
 apply CRle_refl.
 - split. intros. destruct H. apply H.
   intros; rewrite in_CRgball; intuition.
   intros. destruct H.
   rewrite <- in_CRgball. apply H2; assumption. 
Qed. (* todo: clean up *)

Lemma gball_CRabs (r : Q) (x y : CR) : ball r x y <-> CRabs (x - y) <= ' r.
Proof. rewrite rational. apply as_distance_bound. Qed.

Lemma gball_CRmult_Q (e a : Q) (x y : CR) :
  ball e x y -> ball (Qabs a * e) ('a * x) ('a * y).
Proof.
intro A. apply gball_CRabs.
setoid_replace ('a * x - 'a * y) with ('a * (x - y))
  by (unfold canonical_names.equiv, msp_Equiv; ring).
rewrite CRabs_CRmult_Q, <- CRmult_Qmult.
assert (0 <= 'Qabs a) by (apply CRle_Qle, Qabs_nonneg).
apply (orders.order_preserving (CRmult (' Qabs a))).
now apply gball_CRabs.
Qed.

Lemma gball_CRmult_Q_nonneg (e a : Q) (x y : CR) :
  (0 <= a)%Q -> ball e x y -> ball (a * e) ('a * x) ('a * y).
Proof.
intros A1 A2. rewrite <- (Qabs_pos a) at 1; [apply gball_CRmult_Q |]; easy.
Qed.

Module notations.

  Notation CRball := CRball.

End notations.
