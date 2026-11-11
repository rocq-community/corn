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

From Coq Require Export QArith.
Require Import CoRN.algebra.RSetoid.
Require Import MathClasses.interfaces.canonical_names.
Require Import MathClasses.interfaces.abstract_algebra.


Local Open Scope Q_scope.

Set Implicit Arguments.

(**
* Metric Space

We define a metric space over a setoid X by a ball relation B
where B e x y means that the distance between the two points
x and y is less than or equal to the rational number e ( d(x,y) <= e ).

We do not take the usual definition of a distance function d : X^2 -> R_+,
because constructively this function would have to be computable.
For example this would prevent us to define metrics on functions
d(f,g) := inf_x d(f(x), g(x))
where the infinimum does not always exist constructively.
By using ball propositions instead, we make the distance function partial,
it is not always defined. For topological applications, it is often enough
to bound the distance instead of computing it exactly, this is
precisely what the balls do.

Interestingly, this definition by balls also handles infinite distances,
by proving that forall e, not (B e x y). It generalizes the usual distance functions.

This definition uses rational numbers instead of real numbers,
which is simpler. It allows to define the real numbers as a certain metric
space, namely the Cauchy completion of the rational numbers.

Lastly, this definition could include one other property of the distance functions
e < d -> {B d x y}+{~B e x y}.
But those properties are only used late in the proofs, so we move them
as additional definitions in module Classification.v (stability and locatedness). 
*)

Record is_MetricSpace {X : Type} (B: Q -> relation X) : Prop :=
{ msp_refl: forall e, 0 <= e -> Reflexive (B e)
; msp_sym: forall e, Symmetric (B e)
; msp_triangle: forall e1 e2 a b c, B e1 a b -> B e2 b c -> B (e1 + e2) a c
; msp_closed: forall e a b, (forall d, 0 < d -> B (e + d) a b) -> B e a b
; msp_nonneg : forall e a b, B e a b -> 0 <= e
; msp_stable : forall e a b, (~~B e a b) -> B e a b
}.

Record MetricSpace : Type :=
{ msp_car :> Type
; ball : Q -> msp_car -> msp_car -> Prop
; ball_e_wd : forall (e d : Q) (x y : msp_car),
    e == d -> (ball e x y <-> ball d x y)
; msp : is_MetricSpace ball
}.

(* begin hide *)
Arguments ball [m].

Definition msp_eq {m:MetricSpace} (x y : msp_car m) : Prop
  := ball 0 x y.

#[global] Instance: Params (@ball) 1 := {}.
#[global] Instance: Params (@msp_eq) 1 := {}.

#[global]
Instance msp_Equiv (m : MetricSpace) : Equiv m := @msp_eq m.

Add Parametric Morphism {m:MetricSpace} : (@ball m)
    with signature Qeq ==> (@msp_eq m) ==> (@msp_eq m) ==> iff as ball_wd.
Proof.
  unfold msp_eq. split.
  - intros.
    assert (0+(x+0) == y).
    { rewrite Qplus_0_r, Qplus_0_l. exact H. }
    apply (ball_e_wd m y0 y1 H3).
    clear H H3 y.
    apply (msp_triangle (msp m)) with (b:=x0).
    apply (msp_sym (msp m)), H0.
    apply (msp_triangle (msp m)) with (b:=x1).
    exact H2. exact H1.
  - intros.
    assert (0+(y+0) == x).
    { rewrite Qplus_0_r, Qplus_0_l, H. reflexivity. }
    apply (ball_e_wd m x0 x1 H3).
    clear H H3 x.
    apply (msp_triangle (msp m)) with (b:=y0).
    exact H0. clear H0 x0.
    apply (msp_triangle (msp m)) with (b:=y1).
    exact H2.
    apply (msp_sym (msp m)), H1.
Qed.

Lemma msp_eq_refl : forall {m:MetricSpace} (x : m),
    msp_eq x x.
Proof.
  intros. apply (msp_refl (msp m) (Qle_refl 0)).
Qed.

Lemma msp_eq_sym : forall {m:MetricSpace} (x y : m),
    msp_eq x y -> msp_eq y x.
Proof.
  intros. apply (msp_sym (msp m)), H.
Qed.

Lemma msp_eq_trans : forall {m:MetricSpace} (x y z : m),
    msp_eq x y -> msp_eq y z -> msp_eq x z.
Proof.
  unfold msp_eq. intros. 
  rewrite <- (ball_wd m (Qplus_0_r 0)
                     x x (msp_eq_refl x)
                     z z (msp_eq_refl z)).
  exact (msp_triangle (msp m) _ _ _ y _ H H0).
Qed.

Add Parametric Relation {m:MetricSpace} : (msp_car m) msp_eq
    reflexivity proved by (msp_eq_refl)
    symmetry proved by (msp_eq_sym)
    transitivity proved by (msp_eq_trans)
      as msp_eq_rel.
(* end hide *)

#[global]
Instance msp_Setoid (m : MetricSpace) : Setoid m := {}.

Definition msp_as_RSetoid : MetricSpace -> RSetoid
  := fun m => Build_RSetoid (msp_Setoid m).

Section Metric_Space.

(*
** Ball lemmas
*)

Variable X : MetricSpace.

(** These lemmas give direct access to the ball axioms of a metric space
*)

Lemma ball_refl : forall e (a:X), 0 <= e -> ball e a a.
Proof.
 intros. apply (msp_refl (msp X) H).
Qed.

Lemma ball_sym : forall e (a b:X), ball e a b -> ball e b a.
Proof.
 apply (msp_sym (msp X)).
Qed.

Lemma ball_triangle : forall e1 e2 (a b c:X),
    ball e1 a b -> ball e2 b c -> ball (e1 + e2) a c.
Proof.
 apply (msp_triangle (msp X)).
Qed.

Lemma ball_closed :  forall e (a b:X),
    (forall d, 0 < d -> ball (e + d) a b) -> ball e a b.
Proof.
 apply (msp_closed (msp X)).
Qed.

Lemma ball_eq : forall (a b:X), (forall e, 0 < e -> ball e a b) -> msp_eq a b.
Proof.
  intros. apply ball_closed.
  intros. rewrite Qplus_0_l.
  apply H, H0.
Qed.

Lemma ball_eq_iff : forall (a b:X),
    (forall e, 0 < e -> ball e a b) <-> msp_eq a b.
Proof.
 split.
  apply ball_eq.
 intros H e epos.
 rewrite H. apply ball_refl.
 apply Qlt_le_weak, epos.
Qed.

(** The ball constraint on a and b can always be weakened.  Here are
two forms of the weakening lemma.
*)

Lemma ball_weak : forall e d (a b:X),
    0 <= d -> ball e a b -> ball (e + d) a b.
Proof.
 intros e d a b dpos B1.
 eapply ball_triangle.
  apply B1.
 apply ball_refl. exact dpos.
Qed.

Hint Resolve ball_refl ball_triangle ball_weak : metric.

Lemma ball_weak_le : forall (e d:Q) (a b:X),
    e <= d ->  ball e a b -> ball d a b.
Proof.
 intros e d a b Hed B1.
 setoid_replace d with (e + (d-e)) by ring.
 apply (ball_triangle _ _ _ b). exact B1.
 apply ball_refl.
 unfold Qminus. rewrite <- Qle_minus_iff. exact Hed.
Qed.

(* If d(x,y) is infinite and d(x,z) is finite, then d(z,y) is infinite. *)
Lemma ball_infinite
  : forall (x y z : X) (e : Q), 
    (forall d : Q, ~ball d x y)
    -> ball e x z
    -> (forall d : Q, ~ball d z y).
Proof.
  intros. intro abs.
  apply (H (e+d)).
  exact (ball_triangle e d x z y H0 abs).
Qed.

Lemma ball_stable : forall e (x y : X),
    ~~(ball e x y) -> ball e x y.
Proof.
  intros. apply (msp_stable (msp X)), H. 
Qed.


End Metric_Space.
(* begin hide *)
#[global]
Hint Resolve ball_refl ball_sym ball_triangle ball_weak : metric.
(* end hide *)

