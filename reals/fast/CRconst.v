Require Import CoRN.algebra.RSetoid.
Require Import CoRN.metric2.Metric.
Require Import CoRN.metric2.UniformContinuity.
Require Import CoRN.model.totalorder.QposMinMax.
Require Import Coq.Unicode.Utf8 CoRN.model.metric2.Qmetric CoRN.model.metric2.CRmetric CoRN.metric2.UniformContinuity.


Section const_fun_uc.
 Variable X : MetricSpace.
 Variable c : X.

 (** The uniformly continuous constant function *)
 Definition const_raw : X → Complete X := λ _, Cunit c.

 (* Any modulus bigger than 0 will do, so we pick \infty *)
 Definition const_mu (ε:Qpos) : QposInf := QposInfinity.

 Lemma const_uc_prf : is_UniformlyContinuousFunction const_raw const_mu.
 Proof.
  unfold is_UniformlyContinuousFunction; now intuition; auto with *.
 Qed.

 (** [const_uc c] defines the uniformly continuous function [λ _, c] *)
 Open Scope uc_scope.
 Definition const_uc : X --> Complete X :=
   Build_UniformlyContinuousFunction (const_uc_prf).
End const_fun_uc.

Arguments const_uc {X}.
