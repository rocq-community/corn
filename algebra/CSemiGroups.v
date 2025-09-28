(* Copyright © 1998-2006
 * Henk Barendregt
 * Luís Cruz-Filipe
 * Herman Geuvers
 * Mariusz Giero
 * Rik van Ginneken
 * Dimitri Hendriks
 * Sébastien Hinderer
 * Bart Kirkels
 * Pierre Letouzey
 * Iris Loeb
 * Lionel Mamane
 * Milad Niqui
 * Russell O’Connor
 * Randy Pollack
 * Nickolay V. Shmyrev
 * Bas Spitters
 * Dan Synek
 * Freek Wiedijk
 * Jan Zwanenburg
 *
 * This work is free software; you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation; either version 2 of the License, or
 * (at your option) any later version.
 *
 * This work is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License along
 * with this work; if not, write to the Free Software Foundation, Inc.,
 * 51 Franklin Street, Fifth Floor, Boston, MA 02110-1301 USA.
 *)

(** printing [+] %\ensuremath+% #+# *)
(** printing {+} %\ensuremath+% #+# *)

Require Export CoRN.algebra.CSetoidInc.

(* Begin_SpecReals *)

(**
* Semigroups
** Definition of the notion of semigroup
*)

Definition is_CSemiGroup A (op : CSetoid_bin_op A) := associative op.

Record CSemiGroup : Type :=
  {csg_crr   :> CSetoid;
   csg_op    :  CSetoid_bin_op csg_crr;
   csg_proof :  is_CSemiGroup csg_crr csg_op}.

(**
%\begin{nameconvention}%
In the %{\em %names%}% of lemmas, we will denote [[+]] with [plus].
%\end{nameconvention}%
*)

Arguments csg_op {c}.
Infix "[+]" := csg_op (at level 50, left associativity).
(* End_SpecReals *)

(**
** Semigroup axioms
The axiomatic properties of a semi group.

%\begin{convention}% Let [G] be a semi-group.
%\end{convention}%
*)
Section CSemiGroup_axioms.
Variable G : CSemiGroup.

Lemma CSemiGroup_is_CSemiGroup : is_CSemiGroup G csg_op.
Proof.
 elim G; auto.
Qed.

Lemma plus_assoc : associative (csg_op (c:=G)).
Proof.
 exact CSemiGroup_is_CSemiGroup.
Qed.

End CSemiGroup_axioms.

(* Begin_SpecReals *)

(**
** Semigroup basics

%\begin{convention}%
Let [G] be a semi-group.
%\end{convention}%
*)
Section CSemiGroup_basics.
Variable G : CSemiGroup.

(* End_SpecReals *)

Lemma plus_assoc_unfolded : forall (G : CSemiGroup) (x y z : G), x[+] (y[+]z) [=] x[+]y[+]z.
Proof.
 exact plus_assoc.
Qed.

End CSemiGroup_basics.

Section p71R1.

(**
** Morphism
%\begin{convention}%
Let [S1 S2:CSemiGroup].
%\end{convention}%
*)

Variable S1:CSemiGroup.
Variable S2:CSemiGroup.

Definition morphism_of_CSemiGroups (f:(CSetoid_fun S1 S2)):CProp:=
forall (a b:S1), (f (a[+]b))[=] (f a)[+](f b).

End p71R1.

(**
** About the unit
*)

Definition is_rht_unit S (op : CSetoid_bin_op S) Zero : Prop := forall x, op x Zero [=] x.

(* End_SpecReals *)

Definition is_lft_unit S (op : CSetoid_bin_op S) Zero : Prop := forall x, op Zero x [=] x.

Arguments is_lft_unit [S].

(* Begin_SpecReals *)

Arguments is_rht_unit [S].

(** An alternative definition:
*)

Definition is_unit (S:CSemiGroup): S -> Prop :=
fun e => forall (a:S), e[+]a [=] a /\ a[+]e [=]a.

Lemma cs_unique_unit : forall (S:CSemiGroup) (e f:S),
(is_unit S e) /\ (is_unit S f) -> e[=]f.
Proof.
 intros S e f.
 unfold is_unit.
 intros H.
 elim H.
 clear H.
 intros H0 H1.
 elim (H0 f).
 clear H0.
 intros H2 H3.
 elim (H1 e).
 clear H1.
 intros H4 H5.
 astepr (e[+]f).
 astepl (e[+]f).
 apply eq_reflexive.
Qed.


(* End_SpecReals *)

#[global]
Hint Resolve plus_assoc_unfolded: algebra.

(**
** Functional operations
We can also define a similar addition operator, which will be denoted by [{+}], on partial functions.

%\begin{convention}% Whenever possible, we will denote the functional construction corresponding to an algebraic operation by the same symbol enclosed in curly braces.
%\end{convention}%

At this stage, we will always consider automorphisms; we %{\em %could%}% treat this in a more general setting, but we feel that it wouldn't really be a useful effort.

%\begin{convention}% Let [G:CSemiGroup] and [F,F':(PartFunct G)] and denote by [P] and [Q], respectively, the predicates characterizing their domains.
%\end{convention}%
*)

Section Part_Function_Plus.

Variable G : CSemiGroup.
Variables F F' : PartFunct G.

(* begin hide *)
Let P := Dom F.
Let Q := Dom F'.
(* end hide *)

Lemma part_function_plus_strext : forall x y (Hx : Conj P Q x) (Hy : Conj P Q y),
 F x (Prj1 Hx) [+]F' x (Prj2 Hx) [#] F y (Prj1 Hy) [+]F' y (Prj2 Hy) -> x [#] y.
Proof.
 intros x y Hx Hy H.
 case (cs_bin_op_strext  _ _ _ _ _ _  H); intros H1; exact (pfstrx _ _ _ _ _ _ H1).
Qed.

Definition Fplus := Build_PartFunct G _ (conj_wd (dom_wd _ F) (dom_wd _ F'))
  (fun x Hx => F x (Prj1 Hx) [+]F' x (Prj2 Hx)) part_function_plus_strext.

(**
%\begin{convention}% Let [R:G->CProp].
%\end{convention}%
*)

Variable R : G -> CProp.

Lemma included_FPlus : included R P -> included R Q -> included R (Dom Fplus).
Proof.
 intros; simpl in |- *; apply included_conj; assumption.
Qed.

Lemma included_FPlus' : included R (Dom Fplus) -> included R P.
Proof.
 intro H; simpl in H; eapply included_conj_lft; apply H.
Qed.

Lemma included_FPlus'' : included R (Dom Fplus) -> included R Q.
Proof.
 intro H; simpl in H; eapply included_conj_rht; apply H.
Qed.

End Part_Function_Plus.

Arguments Fplus [G].
Infix "{+}" := Fplus (at level 50, left associativity).

#[global]
Hint Resolve included_FPlus : included.

#[global]
Hint Immediate included_FPlus' included_FPlus'' : included.

(**
** Subsemigroups
%\begin{convention}%
Let [csg] a semi-group and [P] a non-empty
predicate on the semi-group which is preserved by [[+]].
%\end{convention}%
*)
Section SubCSemiGroups.
Variable csg : CSemiGroup.
Variable P : csg -> CProp.
Variable op_pres_P : bin_op_pres_pred _ P csg_op.

Let subcrr : CSetoid := Build_SubCSetoid _ P.

Definition Build_SubCSemiGroup : CSemiGroup := Build_CSemiGroup
  subcrr (Build_SubCSetoid_bin_op _ _ _ op_pres_P)
  (restr_f_assoc _ _ _ op_pres_P (plus_assoc csg)).
End SubCSemiGroups.

Section D9S.

(**
** Direct Product
%\begin{convention}%
Let [M1 M2:CSemiGroup]
%\end{convention}%
*)

Variable M1 M2: CSemiGroup.
Definition dprod (x:ProdCSetoid M1 M2)(y:ProdCSetoid M1 M2):
  (ProdCSetoid M1 M2):=
let (x1, x2):= x in
let (y1, y2):= y in
(pairT (x1[+]y1) (x2 [+] y2)).

Lemma dprod_strext:(bin_fun_strext (ProdCSetoid M1 M2)(ProdCSetoid M1 M2)
  (ProdCSetoid M1 M2)dprod).
Proof.
 unfold bin_fun_strext.
 intros x1 x2 y1 y2.
 unfold dprod.
 case x1.
 intros a1 a2.
 case x2.
 intros b1 b2.
 case y1.
 intros c1 c2.
 case y2.
 intros d1 d2.
 simpl.
 intro H.
 elim H.
  clear H.
  intro H.
  cut (a1[#]b1 or c1[#]d1).
   intuition.
  set (H0:= (@csg_op M1)).
  unfold CSetoid_bin_op in H0.
  set (H1:= (@csbf_strext M1 M1 M1 H0)).
  unfold bin_fun_strext in H1.
  apply H1.
  exact H.
 clear H.
 intro H.
 cut (a2[#]b2 or c2[#]d2).
  intuition.
 set (H0:= (@csg_op M2)).
 unfold CSetoid_bin_op in H0.
 set (H1:= (@csbf_strext M2 M2 M2 H0)).
 unfold bin_fun_strext in H1.
 apply H1.
 exact H.
Qed.

Definition dprod_as_csb_fun:
  CSetoid_bin_fun (ProdCSetoid M1 M2) (ProdCSetoid M1 M2)(ProdCSetoid M1 M2):=
  (Build_CSetoid_bin_fun (ProdCSetoid M1 M2)(ProdCSetoid M1 M2)
  (ProdCSetoid M1 M2) dprod dprod_strext).

Lemma direct_product_is_CSemiGroup:
  (is_CSemiGroup (ProdCSetoid M1 M2) dprod_as_csb_fun).
Proof.
 unfold is_CSemiGroup.
 unfold associative.
 intros x y z.
 case x.
 intros x1 x2.
 case y.
 intros y1 y2.
 case z.
 intros z1 z2.
 simpl.
 split.
  apply CSemiGroup_is_CSemiGroup.
 apply CSemiGroup_is_CSemiGroup.
Qed.

Definition direct_product_as_CSemiGroup:=
  (Build_CSemiGroup (ProdCSetoid M1 M2) dprod_as_csb_fun
  direct_product_is_CSemiGroup).

End D9S.


(**
** The SemiGroup of Setoid functions
*)

Lemma FS_is_CSemiGroup:
forall (X:CSetoid),(is_CSemiGroup (FS_as_CSetoid X X) (comp_as_bin_op  X )).
Proof.
 unfold is_CSemiGroup.
 exact assoc_comp.
Qed.

Definition FS_as_CSemiGroup (A : CSetoid) :=
  Build_CSemiGroup (FS_as_CSetoid A A) (comp_as_bin_op A) (assoc_comp A).

Section p66E2b4.

(**
** The Free SemiGroup
%\begin{convention}% Let [A:CSetoid].
%\end{convention}%
*)

Variable A:CSetoid.

Lemma Astar_is_CSemiGroup:
  (is_CSemiGroup (free_csetoid_as_csetoid A) (app_as_csb_fun A)).
Proof.
 unfold is_CSemiGroup.
 unfold associative.
 intros x.
 unfold app_as_csb_fun.
 simpl.
 induction x.
  simpl.
  intros x y.
  apply eq_fm_reflexive.
 simpl.
 intuition; auto with *.
Qed.

Definition Astar_as_CSemiGroup:=
  (Build_CSemiGroup (free_csetoid_as_csetoid A) (app_as_csb_fun A)
   Astar_is_CSemiGroup).

End p66E2b4.
