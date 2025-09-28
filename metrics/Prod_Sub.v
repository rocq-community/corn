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

Require Export CoRN.metrics.IR_CPMSpace.

Section prodpsmetrics.
(**
** Product-Pseudo-Metric-Spaces
*)

(**
The product metric here defined is:
$ d_{prod}((a_1,b_1),(a_2,b_2)):= d_A(a_1,a_2)+d_B(b_1,b_2)$
# d<SUB>prod</SUB>((a<SUB>1</SUB>,b<SUB>1</SUB>),(a<SUB>2</SUB>,b<SUB>2</SUB>)):= d<SUB>A</SUB>(a<SUB>1</SUB>,b<SUB>1</SUB>)+d<SUB>B</SUB>(b<SUB>1</SUB>,b<SUB>2</SUB>)#.
This is %\emph{not}% #<I>not</I># the one used to make the metric of
$\RR^{2}$ #IR<SUP>2</SUP># out of the metric of $\RR$ #IR#.
*)

Definition dprod0 (A B : CPsMetricSpace) (c d : prodT A B) : IR.
Proof.
 case c.
 intros c0 c1.
 case d.
 intros c2 c3.
 exact ((c0[-d]c2)[+](c1[-d]c3)).
Defined.

Lemma dprod0_strext :
 forall A B : CPsMetricSpace,
 bin_fun_strext (ProdCSetoid A B) (ProdCSetoid A B) IR (dprod0 A B).
Proof.
 intros A B.
 unfold bin_fun_strext in |- *.
 intros x1 x2 y1 y2.
 unfold dprod0 in |- *.
 case x1.
 case x2.
 case y1.
 case y2.
 intros c c0 c1 c2 c3 c4 c5 c6 H.
 set (H1 := cs_bin_op_strext IR csg_op (c5[-d]c1) (c3[-d]c) (c6[-d]c2) (c4[-d]c0) H) in *.
 elim H1.
  intros.
  set (H2 := csbf_strext A A IR cms_d c5 c3 c1 c a) in *.
  elim H2.
   intros.
   left.
   simpl in |- *.
   left.
   exact a0.
  intros.
  right.
  simpl in |- *.
  left.
  exact b.
 intros.
 set (H2 := csbf_strext B B IR cms_d c6 c4 c2 c0 b) in *.
 elim H2.
  intros.
  left.
  simpl in |- *.
  right.
  exact a.
 intros.
 right.
 simpl in |- *.
 right.
 exact b0.
Qed.

Definition d_prod0 (A B : CPsMetricSpace) :=
  Build_CSetoid_bin_fun (ProdCSetoid A B) (ProdCSetoid A B) IR (
    dprod0 A B) (dprod0_strext A B).

Lemma prod0cpsmetricspace_is_CPsMetricSpace :
 forall A B : CPsMetricSpace,
 is_CPsMetricSpace (ProdCSetoid A B) (d_prod0 A B).
Proof.
 intros A B.
 apply (Build_is_CPsMetricSpace (ProdCSetoid A B) (d_prod0 A B)).
    unfold com in |- *.
    intros x y.
    unfold d_prod0 in |- *.
    simpl in |- *.
    unfold dprod0 in |- *.
    case x.
    case y.
    intros.
    apply (cs_bin_op_wd IR csg_op).
     apply ax_d_com.
     apply CPsMetricSpace_is_CPsMetricSpace.
    apply ax_d_com.
    apply CPsMetricSpace_is_CPsMetricSpace.
   unfold nneg in |- *.
   intros.
   unfold d_prod0 in |- *.
   simpl in |- *.
   unfold dprod0 in |- *.
   case x.
   case y.
   intros.
   astepl (ZeroR[+][0]).
   apply plus_resp_leEq_both.
    apply ax_d_nneg.
    apply CPsMetricSpace_is_CPsMetricSpace.
   apply ax_d_nneg.
   apply CPsMetricSpace_is_CPsMetricSpace.
  unfold pos_imp_ap in |- *.
  intros x y.
  unfold d_prod0 in |- *.
  simpl in |- *.
  unfold dprod0 in |- *.
  case x.
  case y.
  intros c c0 c1 c2 H.
  unfold prod_ap in |- *.
  unfold prod_rect in |- *.
  set (H0 := positive_Sum_two IR (c1[-d]c) (c2[-d]c0) H) in *.
  elim H0.
   intros.
   left.
   apply ax_d_pos_imp_ap with (d := cms_d (c:=A)).
    apply CPsMetricSpace_is_CPsMetricSpace.
   exact a.
  intros.
  right.
  apply ax_d_pos_imp_ap with (d := cms_d (c:=B)).
   apply CPsMetricSpace_is_CPsMetricSpace.
  exact b.
 unfold tri_ineq in |- *.
 intros.
 unfold d_prod0 in |- *.
 simpl in |- *.
 unfold dprod0 in |- *.
 case x.
 case y.
 case z.
 intros c c0 c1 c2 c3 c4.
 astepr ((c3[-d]c1)[+]((c4[-d]c2)[+]((c1[-d]c)[+](c2[-d]c0)))).
 astepr ((c3[-d]c1)[+]((c4[-d]c2)[+](c1[-d]c)[+](c2[-d]c0))).
 astepr ((c3[-d]c1)[+]((c1[-d]c)[+](c4[-d]c2)[+](c2[-d]c0))).
 astepr ((c3[-d]c1)[+]((c1[-d]c)[+]((c4[-d]c2)[+](c2[-d]c0)))).
 astepr ((c3[-d]c1)[+](c1[-d]c)[+]((c4[-d]c2)[+](c2[-d]c0))).
 apply plus_resp_leEq_both.
  apply ax_d_tri_ineq.
  apply CPsMetricSpace_is_CPsMetricSpace.
 apply ax_d_tri_ineq.
 apply CPsMetricSpace_is_CPsMetricSpace.
Qed.

Definition Prod0CPsMetricSpace (A B : CPsMetricSpace) :=
  Build_CPsMetricSpace (ProdCSetoid A B) (d_prod0 A B)
    (prod0cpsmetricspace_is_CPsMetricSpace A B).


End prodpsmetrics.

Section subpsmetrics.
(**
** Sub-Pseudo-Metric-Spaces
*)

(**
The pseudo metric on a subspace $Y$ #Y# of a pseudo metric space $X$ #X# is
the pseudo metric on $X$ #X# restricted to $Y$ #Y#.
*)

Definition restr_bin_fun (X : CPsMetricSpace) (P : cms_crr X -> CProp)
  (f : CSetoid_bin_fun X X IR) (a b : Build_SubCSetoid X P) : IR :=
  match a, b with
  | Build_subcsetoid_crr _ _ x p, Build_subcsetoid_crr _ _ y q => f x y
  end.


Arguments restr_bin_fun [X].

Definition restr_bin_fun' (X : CPsMetricSpace) (P : cms_crr X -> CProp)
  (f : CSetoid_bin_fun X X IR) (a : X) (b : Build_SubCSetoid X P) : IR :=
  match b with
  | Build_subcsetoid_crr _ _ y q => f a y
  end.

Arguments restr_bin_fun' [X].

Lemma restr_bin_fun_strext :
 forall (X : CPsMetricSpace) (P : cms_crr X -> CProp)
   (f : CSetoid_bin_fun X X IR),
 bin_fun_strext (Build_SubCSetoid X P) (Build_SubCSetoid X P) IR
   (restr_bin_fun P f).
Proof.
 intros X P f.
 red in |- *.
 intros x1 x2 y1 y2.
 case y2.
 case y1.
 case x2.
 case x1.
 do 8 intro. intro H.
 exact (csbf_strext _ _ _ f _ _ _ _ H).
Qed.

Definition Build_SubCSetoid_bin_fun (X : CPsMetricSpace)
  (P : cms_crr X -> CProp) (f : CSetoid_bin_fun X X IR) :
  CSetoid_bin_fun (Build_SubCSetoid X P) (Build_SubCSetoid X P) IR :=
  Build_CSetoid_bin_fun (Build_SubCSetoid X P) (Build_SubCSetoid X P) IR
    (restr_bin_fun P f) (restr_bin_fun_strext X P f).

Definition dsub (X : CPsMetricSpace) (P : cms_crr X -> CProp) :=
  Build_SubCSetoid_bin_fun X P (cms_d (c:=X)).

Arguments dsub [X].

Lemma dsub_com :
 forall (X : CPsMetricSpace) (P : cms_crr X -> CProp), com (dsub P).
Proof.
 intros X P.
 unfold com in |- *.
 intros x y.
 unfold dsub in |- *.
 case y.
 case x.
 intros a H b H0.
 simpl in |- *.
 apply ax_d_com.
 apply CPsMetricSpace_is_CPsMetricSpace.
Qed.

Lemma dsub_nneg :
 forall (X : CPsMetricSpace) (P : cms_crr X -> CProp), nneg (dsub P).
Proof.
 intros X P.
 unfold nneg in |- *.
 intros x y.
 unfold dsub in |- *.
 case y.
 case x.
 intros a H b H0.
 simpl in |- *.
 apply ax_d_nneg.
 apply CPsMetricSpace_is_CPsMetricSpace.
Qed.

Lemma dsub_pos_imp_ap :
 forall (X : CPsMetricSpace) (P : cms_crr X -> CProp), pos_imp_ap (dsub P).
Proof.
 intros X P.
 unfold pos_imp_ap in |- *.
 intros x y.
 unfold dsub in |- *.
 case y.
 case x.
 intros a H b H0.
 simpl in |- *.
 apply ax_d_pos_imp_ap.
 apply CPsMetricSpace_is_CPsMetricSpace.
Qed.

Lemma dsub_tri_ineq :
 forall (X : CPsMetricSpace) (P : cms_crr X -> CProp), tri_ineq (dsub P).
Proof.
 intros X P.
 unfold tri_ineq in |- *.
 intros x y z.
 unfold dsub in |- *.
 case z.
 case y.
 case x.
 intros a H b H0 c H1.
 simpl in |- *.
 apply ax_d_tri_ineq.
 apply CPsMetricSpace_is_CPsMetricSpace.
Qed.

Definition is_SubPsMetricSpace (X : CPsMetricSpace)
  (P : cms_crr X -> CProp) :
  is_CPsMetricSpace (Build_SubCSetoid X P) (dsub P) :=
  Build_is_CPsMetricSpace (Build_SubCSetoid X P) (dsub P) (
    dsub_com X P) (dsub_nneg X P) (dsub_pos_imp_ap X P) (
    dsub_tri_ineq X P).

Definition SubPsMetricSpace (X : CPsMetricSpace) (P : cms_crr X -> CProp) :
  CPsMetricSpace :=
  Build_CPsMetricSpace (Build_SubCSetoid X P) (dsub P)
    (is_SubPsMetricSpace X P).

Arguments SubPsMetricSpace [X].

Definition from_SubPsMetricSpace (X : CPsMetricSpace)
  (P : X -> CProp) : SubPsMetricSpace P -> X.
Proof.
 unfold SubPsMetricSpace in |- *.
 simpl in |- *.
 intro x.
 case x.
 intros y Q.
 exact y.
Defined.

(**
The function [dsub'] is used in the definition of %''located''% #"located"#.
It enables one to speak about a distance between an element of a
pseudo metric space and a certain subspace.
*)

Definition dsub' (X : CPsMetricSpace) (P : X -> CProp)
  (x : X) (y : SubPsMetricSpace P) := from_SubPsMetricSpace X P y[-d]x.

Arguments dsub' [X].

Lemma dsub'_strext :
 forall (X : CPsMetricSpace) (P : X -> CProp) (x : X),
 fun_strext (dsub' P x).
Proof.
 intros X P x.
 unfold fun_strext in |- *.
 intros x0 y.
 unfold dsub' in |- *.
 case y.
 case x0.
 intros a b c d.
 simpl in |- *.
 intro H.
 set (H1 := csbf_strext _ _ _ (cms_d (c:=X)) _ _ _ _ H) in *.
 elim H1.
  intuition.
 intro H2.
 set (H3 := ap_irreflexive_unfolded X x H2) in *.
 intuition.
Qed.

Definition dsub'_as_cs_fun (X : CPsMetricSpace) (P : X -> CProp)
  (x : X) :=
  Build_CSetoid_fun (SubPsMetricSpace P) IR_as_CPsMetricSpace (
    dsub' P x) (dsub'_strext X P x).

Arguments dsub'_as_cs_fun [X].

Lemma dsub'_uni_continuous'' :
 forall (X : CPsMetricSpace) (P : X -> CProp) (x : X),
 uni_continuous'' (dsub'_as_cs_fun P x).
Proof.
 intros X P x.
 unfold dsub'_as_cs_fun in |- *.
 unfold dsub' in |- *.
 apply uni_continuous'_imp_uni_continuous''.
 unfold from_SubPsMetricSpace in |- *.
 unfold uni_continuous' in |- *.
 simpl in |- *.
 intro n.
 exists n.
 intros x0 x1.
 case x0.
 case x1.
 intros.
 generalize H.
 simpl in |- *.
 intro.
 apply leEq_transitive with (scs_elem0[-d]scs_elem).
  2: exact H0.
 unfold dIR in |- *.
 astepl (AbsIR ((scs_elem0[-d]x)[-](scs_elem[-d]x))).
 astepl (AbsIR ((x[-d]scs_elem0)[-](scs_elem[-d]x))).
  astepl (AbsIR ((x[-d]scs_elem0)[-](x[-d]scs_elem))).
   apply AbsSmall_imp_AbsIR.
   apply rev_tri_ineq.
  apply csf_wd.
  apply cg_minus_wd.
   intuition; auto with *.
  apply ax_d_com.
  apply CPsMetricSpace_is_CPsMetricSpace.
 apply csf_wd.
 apply cg_minus_wd.
  apply ax_d_com.
  apply CPsMetricSpace_is_CPsMetricSpace.
 intuition; auto with *.
Qed.


End subpsmetrics.
