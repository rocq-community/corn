(*
Copyright © 2006-2008 Russell O’Connor

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
Set Firstorder Depth 5.

Require Import Coq.Setoids.Setoid.
Require Export CoRN.order.Lattice.

Local Open Scope po_scope.
(**
* Total Order
A total order is a lattice were x <= y or y <= x.
*)
Record TotalOrder : Type :=
{ L :> Lattice
; le_total : forall x y:L, {x <= y}+{y <= x}
}.

Section MinMax.

Variable X : TotalOrder.
(** meet x y is either x or y. *)
Definition meet_irred : forall x y : X, {meet x y == x} + {meet x y == y}.
Proof.
 intros.
 destruct (le_total _ x y) as [H|H].
  left.
  firstorder using le_meet_l.
 right.
 firstorder using le_meet_r.
Defined.

Section Monotone.

Variable f : X -> X.
Hypothesis Hf : monotone X f.

Add Morphism f with signature (@st_eq X) ==> (@st_eq X)  as monotone_compat.
Proof.
  revert Hf;rewrite -> monotone_def;intros Hf ??.
  do 2 rewrite -> equiv_le_def.
  firstorder.
Qed.

(** meet distributes over any monotone function. *)
Lemma monotone_meet_distr : forall x y : X, f (meet x y) == meet (f x) (f y).
Proof.
 set (Hf':=Hf). (* The section hypothesis is used in monotone_compat and hence cannot be changed. *)
 rewrite -> monotone_def in Hf'.
 assert (forall x y : X, x <= y -> f (meet x y) == meet (f x) (f y)).
  intros x y Hxy.
  assert (Hfxfy:=Hf' _ _ Hxy).
   rewrite -> le_meet_l in Hxy.
   rewrite -> le_meet_l in Hfxfy.
   rewrite -> Hfxfy. 
   rewrite -> Hxy.
  reflexivity.
 intros.
 destruct (le_total _ x y).
  auto.
 rewrite -> (meet_comm X).
 rewrite -> (meet_comm _ (f x)).
 auto.
Qed.

End Monotone.

(** join distributes over meet *)
Lemma join_meet_distr_r : forall x y z:X, (join x (meet y z))==(meet (join x y) (join x z)).
Proof (fun a => monotone_meet_distr _ (join_monotone_r X a)). 

Lemma join_meet_distr_l : forall x y z:X, (join (meet y z) x)==(meet (join y x) (join z x)).
Proof (fun a => monotone_meet_distr _ (join_monotone_l X a)).

Section Antitone.

Variable f : X -> X.
Hypothesis Hf : antitone X f.

(* begin hide *)
Add Parametric Morphism: f with signature (@st_eq X) ==> (@st_eq X) as antitone_compat.
Proof.
 revert Hf; rewrite -> antitone_def; intros.
 rewrite -> equiv_le_def in *.
 firstorder.
Qed.
(* end hide *)

(* meet transforms into join for antitone functions *)
Lemma antitone_meet_join_distr : forall x y : X, f (meet x y) == join (f x) (f y).
Proof.
 pose (Hf':=Hf).
 rewrite antitone_def in Hf'. 
 assert (forall x y : X, x <= y -> f (meet x y) == join (f x) (f y)).
  intros x y Hxy.
  assert (Hfxfy:=Hf' _ _ Hxy).
  rewrite -> le_meet_l in Hxy.
  rewrite -> le_join_l in Hfxfy.
  rewrite -> Hfxfy. clear Hfxfy.
  apply antitone_compat. rewrite -> Hxy. reflexivity.
 intros.
 destruct (le_total _ x y).
  auto.
 rewrite -> (meet_comm X).
 rewrite -> (join_comm X).
 auto.
Qed.

End Antitone.

(** Lemmas of distributive lattices *)
Lemma join_meet_modular_r : forall x y z : X, join x (meet y (join x z)) == meet (join x y) (join x z).
Proof.
 intros.
 rewrite -> join_meet_distr_r.
 rewrite -> (join_assoc X).
 rewrite -> (join_idem X).
 reflexivity.
Qed.

Lemma join_meet_modular_l : forall x y z : X, join (meet (join x z) y) z == meet (join x z) (join y z).
Proof.
 intros.
 rewrite -> (join_comm X (meet (join x z) y) z).
 rewrite -> (meet_comm X (join x z) y).
 rewrite -> (meet_comm X (join x z) (join y z)).
 rewrite -> (join_comm X x z).
 rewrite -> (join_comm X y z).
 apply join_meet_modular_r.
Qed.

Lemma meet_join_disassoc : forall x y z : X, meet (join x y) z <= join x (meet y z).
Proof.
 intros.
 rewrite -> join_meet_distr_r.
 apply meet_le_compat.
  apply le_refl.
 apply join_ub_r.
Qed.

End MinMax.

Section MaxMin.

Variable X : TotalOrder.
(**
** Dual Total Order
The dual of a total order is a total order.
*)
Definition Dual : TotalOrder.
Proof.
 eapply Build_TotalOrder with (L:= Dual X).
 intros.
 destruct (le_total _ x y); auto.
Defined.
(** The duals of the previous lemmas hold. *)
Definition join_irred : forall x y : X, {join x y == x} + {join x y == y} :=
meet_irred Dual.

Lemma monotone_join_distr : forall f, monotone X f -> forall x y : X, f (join x y) == join (f x) (f y).
Proof monotone_meet_distr Dual.

Lemma meet_join_distr_r : forall x y z:X, (meet x (join y z))==(join (meet x y) (meet x z)).
Proof join_meet_distr_r Dual.

Lemma meet_join_distr_l : forall x y z:X, (meet (join y z) x)==(join (meet y x) (meet z x)).
Proof join_meet_distr_l Dual.

Lemma antitone_join_meet_distr : forall f, antitone X f -> forall x y : X, f (join x y) == meet (f x) (f y).
Proof antitone_meet_join_distr Dual.

Lemma meet_join_modular_r : forall x y z : X, meet x (join y (meet x z)) == join (meet x y) (meet x z).
Proof join_meet_modular_r Dual.

Lemma meet_join_modular_l : forall x y z : X, meet (join (meet x z) y) z == join (meet x z) (meet y z).
Proof join_meet_modular_l Dual.

End MaxMin.

Section TotalOrderMinDef.

Variable X : PartialOrder.
(** Given a total order, meet and join can be characterized in terms of
the order.*)
Variable min : X -> X -> X.
Hypothesis le_total : forall x y:X, {x <= y}+{y <= x}.
Hypothesis min_def1 : forall x y:X, x <= y -> min x y == x.
Hypothesis min_def2 : forall x y:X, y <= x -> min x y == y.

Lemma min_lb_l : forall x y:X, min x y <= x.
Proof.
 intros.
 destruct (le_total x y).
  rewrite -> min_def1; auto.
  apply le_refl.
 rewrite -> min_def2; auto.
Qed.

Lemma min_lb_r : forall x y:X, min x y <= y.
Proof.
 intros.
 destruct (le_total x y).
  rewrite -> min_def1; auto.
 rewrite -> min_def2; auto.
 apply le_refl.
Qed.

Lemma min_glb : forall x y z, z <= x -> z <= y -> z <= min x y.
Proof.
 intros.
 destruct (le_total x y).
  rewrite -> min_def1; assumption.
 rewrite -> min_def2; assumption.
Qed.

End TotalOrderMinDef.

(** With a total order has a new characterization. *)
Definition makeTotalOrder :
 forall (A : Type) (equiv : A -> A -> Prop) (le : A -> A -> Prop)
  (monotone antitone : (A -> A) -> Prop)
  (meet join : A -> A -> A),
  (forall x y : A, equiv x y <-> (le x y /\ le y x)) ->
  (forall x : A, le x x) ->
  (forall x y z : A, le x y -> le y z -> le x z) ->
  (forall x y : A, {le x y} + {le y x}) ->
  (forall f, monotone f <-> (forall x y, le x y -> le (f x) (f y))) ->
  (forall f, antitone f <-> (forall x y, le x y -> le (f y) (f x))) ->
  (forall x y : A, le x y -> equiv (meet x y) x) ->
  (forall x y : A, le y x -> equiv (meet x y) y) ->
  (forall x y : A, le y x -> equiv (join x y) x) ->
  (forall x y : A, le x y -> equiv (join x y) y) ->
  TotalOrder.
Proof.
 intros A0 eq0 le0 monotone0 antitone0 min max eq0_def refl trans total monotone0_def antitone0_def min_def1 min_def2 max_def1 max_def2.
 pose (PO:=makePartialOrder eq0 le0 monotone0 antitone0 eq0_def refl trans monotone0_def antitone0_def).
 pose (DPO := (PartialOrder.Dual PO)).
 pose (flip_total := fun x y => total y x).
 pose (L0:=makeLattice PO min max (min_lb_l PO min total min_def1 min_def2)
   (min_lb_r PO min total min_def1 min_def2) (min_glb PO min total min_def1 min_def2)
     (min_lb_l DPO max flip_total max_def1 max_def2) (min_lb_r DPO max flip_total max_def1 max_def2)
       (min_glb DPO max flip_total max_def1 max_def2)).
 exact (Build_TotalOrder L0 total).
Defined.

Module Default.
(**
** Default meet and join.
*)
Section MinDefault.
Variable A : Type.
Variable equiv: A -> A -> Prop.
Variable le : A -> A -> Prop.
Hypothesis equiv_le_def : forall x y : A, equiv x y <-> (le x y /\ le y x).
Hypothesis le_total : forall x y:A, {le x y}+{le y x}.

(** Given a total order, meet and join have a default implemenation. *)
Definition min (x y:A) :=
 if (le_total x y) then x else y.

Definition min_case x y (P:A -> Type) (Hx : le x y -> P x) (Hy : le y x -> P y) : P (min x y) :=
match (le_total x y) as s return P (if s then x else y) with
| left p => Hx p
| right p => Hy p
end.

Lemma min_def1 : forall x y, le x y -> equiv (min x y) x.
Proof.
 intros.
 apply min_case; firstorder auto.
Qed.

Lemma min_def2 : forall x y, le y x -> equiv (min x y) y.
Proof.
 intros.
 apply min_case; firstorder auto.
Qed.

End MinDefault.

Section MaxDefault.
Variable A : Type.
Variable equiv: A -> A -> Prop.
Variable le : A -> A -> Prop.
Hypothesis equiv_le_def : forall x y : A, equiv x y <-> (le x y /\ le y x).
Hypothesis le_total : forall x y:A, {le x y}+{le y x}.

Definition max (x y:A) :=
 if le_total y x then x else y.

Let flip_le x y := le y x.
Let flip_le_total x y := le_total y x.

Definition max_case :
 forall x y (P : A -> Type), (le y x -> P x) -> (le x y -> P y) -> P (max x y) :=
 min_case A flip_le flip_le_total.

Lemma max_def1 : forall x y, le y x -> equiv (max x y) x.
Proof.
 refine (min_def1 A equiv flip_le _ flip_le_total).
 firstorder auto.
Qed.

Lemma max_def2 : forall x y, le x y -> equiv (max x y) y.
Proof.
 refine (min_def2 A equiv flip_le _ flip_le_total).
 firstorder auto.
Qed.

End MaxDefault.

End Default.
