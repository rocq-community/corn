
Require CoRN.model.structures.QnonNeg.
Import QnonNeg.notations QnonNeg.coercions.

Require Import CoRN.model.structures.QposInf.

Inductive T: Set := Infinite | Finite (q: QnonNeg).

Definition eq (x y: T): Prop :=
  match x, y with
  | Finite x', Finite y' => (x' == y')%Qnn
  | Infinite, Infinite => True
  | _, _ => False
  end.

Global Instance: Equivalence eq.
Proof with intuition.
 unfold eq.
 split; repeat intro.
   destruct x; intuition; auto with *.
  destruct x, y; intuition; auto with *.
 destruct x, y, z...
 transitivity q0...
Qed.

Local Infix "==" := eq.

Definition bind (x: T) (f: QnonNeg -> T): T :=
  match x with
  | Finite x' => f x'
  | Infinite => Infinite
  end.

Section liftM2.

  Context
    (f: QnonNeg -> QnonNeg -> QnonNeg)
    {p: Proper (QnonNeg.eq ==> QnonNeg.eq ==> QnonNeg.eq) f}.

  Definition liftM2 (x y: T): T := bind x (fun x' => bind y (fun y' => Finite (f x' y'))).

  Global Instance liftM2_Proper: Proper (eq ==> eq ==> eq) liftM2.
  Proof with intuition. intros [] [] ? [] [] ?; intuition; auto with *. simpl. apply p... Qed.

  Lemma assoc:
    (forall x y z, f x (f y z) == f (f x y) z)%Qnn ->
    (forall x y z, liftM2 x (liftM2 y z) == liftM2 (liftM2 x y) z).
  Proof. intros H [] [] []; simpl; auto. Qed.

  Lemma comm:
    (forall x y, f x y == f y x)%Qnn ->
    (forall x y, liftM2 x y == liftM2 y x).
  Proof.  intros H [] []; simpl; auto. Qed.

End liftM2.

Definition mult := liftM2 QnonNeg.mult.
Definition plus := liftM2 QnonNeg.plus.

Local Infix "+" := plus.
Local Infix "*" := mult.

Lemma plus_comm: forall x y, x + y == y + x.
Proof comm QnonNeg.plus QnonNeg.plus_comm.
Lemma mult_comm: forall x y, x * y == y * x.
Proof comm QnonNeg.mult QnonNeg.mult_comm.
Lemma plus_assoc: forall x y z, x + (y + z) == (x + y) + z.
Proof assoc QnonNeg.plus QnonNeg.plus_assoc.
Lemma mult_assoc: forall x y z, x * (y * z) == (x * y) * z.
Proof assoc QnonNeg.mult QnonNeg.mult_assoc.

Global Instance: Proper (eq ==> eq ==> eq) plus.
Proof liftM2_Proper _.

Global Instance: Proper (eq ==> eq ==> eq) mult.
Proof liftM2_Proper _.

Definition le (x y: T): Prop :=
  match y with
  | Infinite => True
  | Finite y' =>
    match x with
    | Infinite => False
    | Finite x' => (proj1_sig x' <= proj1_sig y')
    end
  end.

Global Instance: Proper (eq ==> eq ==> iff) le.
Proof with intuition.
 unfold eq, QnonNeg.eq, le.
 repeat intro.
 destruct x0, y0, y, x...
  rewrite <- H.
  rewrite <- H0...
 rewrite H.
 rewrite H0...
Qed.

Module Export coercions.

Definition from_QposInf (q: QposInf): T :=
  match q with
  | Qpos2QposInf q' => Finite (from_Qpos q')
  | QposInfinity => Infinite
  end.

Global Instance Finite_Proper: Proper (QnonNeg.eq ==> eq) Finite.
Proof. repeat intro. assumption. Qed.

End coercions.

Module notations.

  Delimit Scope QnnInf_scope with QnnInf.

  Global Infix "==" := eq: QnnInf_scope.
  Global Infix "<=" := le: QnnInf_scope.
  Global Infix "+" := plus: QnnInf_scope.
  Global Infix "*" := mult: QnnInf_scope.
  Global Notation QnnInf := T.

End notations.
