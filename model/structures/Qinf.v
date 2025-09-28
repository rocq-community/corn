Require Import CoRN.model.totalorder.QposMinMax.
From Coq Require Import Setoid Arith.
Require Import CoRN.model.rings.Qring CoRN.model.structures.QposInf
 CoRN.stdlib_omissions.Q
 MathClasses.interfaces.abstract_algebra
 MathClasses.implementations.stdlib_rationals
 MathClasses.theory.setoids.

Inductive T: Set := finite (q: Q) | infinite.
  (* (This is positive infinity.) *)

#[global]
Instance eq: Equiv T := λ x y,
  match x, y with
  | infinite, infinite => True
  | finite a, finite b => a = b
  | _, _ => False
  end.

#[global]
Instance finite_Proper: Proper (=) finite.
Proof. repeat intro. assumption. Qed.

#[global]
Instance setoid: Setoid T.
Proof with intuition.
 constructor.
   intros []...
  intros [] [] ?; intuition; auto with *.
 intros [x|] [y|] [z|] ??; intuition; auto with *.
 change (x = z).
 transitivity y...
Qed.

Definition le (x y: T): Prop :=
  match x, y with
  | _, infinite => True
  | infinite, finite _ => False
  | finite a, finite b => Qle a b
  end.

#[global]
Instance: Proper (=) le.
Proof.
 intros [|] [|] E [|] [|] F; intuition; auto with *; simpl; try reflexivity.
 unfold equiv in * |-. simpl in *.
 now rewrite E, F.
Qed.

Definition lt (x y : T) : Prop :=
match x, y with
| finite a, finite b => Qlt a b
| finite _, infinite => True
| infinite, _ => False
end.

#[global]
Instance: Proper (=) lt.
Proof.
intros [x1 |] [x2 |] A1 [y1 |] [y2 |] A2; revert A1 A2;
unfold eq, Q_eq, equiv; simpl; intros A1 A2;
try contradiction; try reflexivity.
rewrite A1, A2; reflexivity.
Qed.

#[global]
Instance: Zero T := finite 0%Q.

#[global]
Instance plus: Plus T := λ x y,
  match x, y with
  | finite a, finite b => finite (a + b)
  | _, _ => infinite
  end.

Module Export coercions.

Coercion finite: Q >-> T.

Coercion from_QposInf (q: QposInf): T :=
  match q with
  | QposInfinity => infinite
  | Qpos2QposInf u => proj1_sig u
  end.

End coercions.

Lemma QposInf_le_QinfLe (x y: QposInf): QposInf_le x y → le x y.
Proof. destruct x, y; auto. Qed.

Lemma le_0_plus_compat (x y: T): le 0 x → le 0 y → le 0 (x + y).
Proof with auto.
 destruct x, y...
 simpl. intros. apply Qplus_nonneg...
Qed.

#[global]
Hint Resolve le_0_plus_compat.

Lemma le_0_Qpos (x: Qpos): le 0 x.
Proof.
  destruct x. simpl. apply Qlt_le_weak, q.
Qed.

#[global]
Hint Immediate le_0_Qpos.

Module notations.

  Delimit Scope Qinf_scope with Qinf.

  Global Infix "==" := eq: Qinf_scope.
  Global Infix "<=" := le: Qinf_scope.
  Global Infix "+" := plus: Qinf_scope.
  Global Notation Qinf := T.

End notations.
