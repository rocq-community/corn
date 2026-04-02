Require Export CoRN.algebra.CSetoids.
Delimit Scope corn_scope with corn.
(* Open Scope corn_scope.*)

Arguments cs_ap _ _%_corn_scope _%_corn_scope.
Arguments cs_eq _ _%_corn_scope _%_corn_scope.

(* Infix "#" := cs_ap (at level 70, no associativity) : corn_scope. *)
Infix "==" := cs_eq (at level 70, no associativity) : corn_scope.

Require Import CoRN.algebra.CSemiGroups.
Arguments csg_op _ _%_corn_scope _%_corn_scope : extra scopes.
Infix "+" := csg_op (at level 50, left associativity) : corn_scope.


Require Import CoRN.algebra.CMonoids.
Notation "0" := (cm_unit _) : corn_scope.
Notation "(+)" := csg_op (only parsing) : corn_scope.

Require Import CoRN.algebra.CGroups.
Notation "- x" := (cg_inv x) (at level 35, right associativity) : corn_scope.
Infix "-" := cg_minus (at level 50, left associativity) : corn_scope.

Require Import CoRN.algebra.CRings.
Arguments cr_mult _ _%_corn_scope _%_corn_scope : extra scopes.
Infix "*" := cr_mult (at level 40, left associativity) : corn_scope.
Notation "x ^ n" := (nexp_op _ n x) : corn_scope.
Notation "1" := [1] : corn_scope.
