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

Require Export CoRN.metrics.Prod_Sub.

Section lists.
(**
** Lists
*)

(**
 List and membership of lists are used in the definition of
%''totally bounded''% #"totally bounded"#. Note that we use the Leibniz equality in the definition
of [MSmember], and not the setoid equality. So we are really talking about
finite sets of representants, instead of finite subsetoids. This seems to make
 the proofs a bit easier.
*)

Fixpoint MSmember (X : CSetoid) (x : X) (l : list X) {struct l} : CProp :=
  match l with
  | nil => False
  | cons y m => MSmember X x m or x = y
  end.

Arguments MSmember [X].

Definition to_IR (P : IR -> CProp) : subcsetoid_crr IR P -> IR.
Proof.
 intro a.
 case a.
 intros b C.
 exact b.
Defined.

Definition from_IR (P : IR -> CProp) (x : IR) (H : P x) : subcsetoid_crr IR P.
Proof.
 set (H0 := Build_subcsetoid_crr IR P) in *.
 set (H1 := H0 x H) in *.
 exact H1.
Defined.

Definition list_IR (P : IR -> CProp) :
  list (SubPsMetricSpace IR_as_CPsMetricSpace P) -> list IR.
Proof.
 intro l.
 induction  l as [| a l Hrecl].
  apply (@nil IR).
 apply (cons (to_IR P a) Hrecl).
Defined.

Lemma is_P :
 forall (P : IR -> CProp)
   (l : list (SubPsMetricSpace IR_as_CPsMetricSpace P))
   (x : IR), pred_wd IR P -> member x (list_IR P l) -> P x.
Proof.
 intros P l x Q.
 induction  l as [| a l Hrecl].
  simpl in |- *.
  intuition.
 case a.
 simpl in |- *.
 intros b C D.
 elim D.
  intro E.
  apply Hrecl.
  exact E.
 unfold pred_wd in Q.
 intro H.
 apply Q with b.
  exact C.
 apply eq_symmetric_unfolded.
 exact H.
Qed.

(**
If a real number is element of a list in the above defined sense,
it is an element of the list in the sense of [member],
that uses the setoid equality.
*)

Lemma member1 :
 forall (P : IR -> CProp) (x0 : subcsetoid_crr IR P)
   (l : list (SubPsMetricSpace IR_as_CPsMetricSpace P)),
 MSmember (X:=SubPsMetricSpace IR_as_CPsMetricSpace P) x0 l ->
 member (to_IR P x0) (list_IR P l).
Proof.
 intros P x0 l.
 induction  l as [| a l Hrecl].
  simpl in |- *.
  intuition.
 simpl in |- *.
 intros H.
 elim H.
  intro H1.
  left.
  apply Hrecl.
  exact H1.
 simpl in |- *.
 intros.
 right.
 rewrite b.
 intuition; auto with *.
Qed.

(**
The image under a certain mapping of an element of a list $l$ #<I>l</I># is member
of the list of images of elements of $l$ #<I>l</I>#.
*)

Lemma map_member :
 forall (X Z : CPsMetricSpace) (f : X -> Z) (l : list X) (m : X),
 MSmember m l -> MSmember (f m) (map f l).
Proof.
 intros X Z f l m.
 induction  l as [| a l Hrecl].
  simpl in |- *.
  auto.
 simpl in |- *.
 intro H.
 elim H.
  intro H1.
  left.
  apply Hrecl.
  exact H1.
 intro H1.
 right.
 rewrite H1.
 intuition.
Qed.

End lists.

Section loc_and_bound.
(**
** Pseudo Metric Space theory
*)

Definition Re_co_do (X Z : CSetoid) (f : CSetoid_fun X Z) :
  X -> Build_SubCSetoid Z (fun y : Z => {x : X | f x[=]y}).
Proof.
 intros x.
 exists (f x).
 exists x.
 apply eq_reflexive.
Defined.

Lemma Re_co_do_strext :
 forall (X Z : CSetoid) (f : CSetoid_fun X Z),
 fun_strext (Re_co_do X Z f).
Proof.
 intros X Z f.
 unfold fun_strext in |- *.
 intros x y.
 simpl in |- *.
 apply (csf_strext X Z f).
Qed.

Definition re_co_do (X Z : CSetoid) (f : CSetoid_fun X Z) :
  CSetoid_fun X (Build_SubCSetoid Z (fun y : Z => {x : X | f x[=]y})) :=
  Build_CSetoid_fun X (Build_SubCSetoid Z (fun y : Z => {x : X | f x[=]y}))
    (Re_co_do X Z f) (Re_co_do_strext X Z f).

Lemma re_co_do_well_def :
 forall (X Z : CSetoid) (f : CSetoid_fun X Z),
 pred_wd Z (fun y : Z => {x : X | f x[=]y}).
Proof.
 intros X Z f.
 unfold pred_wd in |- *.
 intros x y.
 intros H0 H1.
 elim H0.
 intros x0 H3.
 exists x0.
 astepr x.
 exact H3.
Qed.

Arguments MSmember [X].
(**
Again we see that the image under a certain mapping of an element of a list $l$
#<I>l</I># is member of the list of images of elements of $l$ #<I>l</I>#.
*)

Lemma map_member' :
 forall (X Z : CPsMetricSpace) (f : CSetoid_fun X Z) (l : list X) (m : X),
 MSmember m l ->
 MSmember (X:=Build_SubCSetoid Z (fun y : Z => {x0 : X | f x0[=]y}))
   (re_co_do X Z f m) (map (re_co_do X Z f) l).
Proof.
 intros X Z f l m.
 induction  l as [| a l Hrecl].
  simpl in |- *.
  auto.
 simpl in |- *.
 intro H.
 elim H.
  intro H1.
  left.
  apply Hrecl.
  exact H1.
 intro H1.
 right.
 rewrite H1.
 intuition.
Qed.

Definition bounded (X : CPsMetricSpace) : CProp :=
  {n : IR | forall x y : X, x[-d]y[<=]n}.

Definition MStotally_bounded (X : CPsMetricSpace) : CProp :=
  forall n : nat,
  {l : list X |
  forall x : X, {y : X | MSmember y l | x[-d]y[<=]one_div_succ n}}.


(**
Total boundedness is preserved under uniformly continuous mappings.
*)

Arguments SubPsMetricSpace [X].
Lemma unicon_resp_totallybounded :
 forall (X Z : CPsMetricSpace) (f : CSetoid_fun X Z) (H : uni_continuous'' f),
 MStotally_bounded X ->
 MStotally_bounded (SubPsMetricSpace (fun y : Z => {x : X | f x[=]y})).
Proof.
 intros X Z f.
 unfold uni_continuous'' in |- *.
 intro H.
 unfold MStotally_bounded in |- *.
 intro H1.
 intro n.
 elim H.
 intros mod_ H3.
 elim (H1 (mod_ n)).
 intros l H2.
 simpl in |- *.
 exists (map (re_co_do X Z f) l).
 intros x.
 elim x.
 intros r H5.
 elim H5.
 intros k H6.
 elim (H2 k).
 intros m H7 H8.
 exists (re_co_do X Z f m).
  2: simpl in |- *.
  2: astepl (f k[-d]f m).
  2: apply H3.
  2: exact H8.
 apply map_member'.
 exact H7.
Qed.

Lemma MStotallybounded_totallybounded :
 forall (P : IR -> CProp) (H0 : {x : IR | P x}),
 pred_wd IR P ->
 MStotally_bounded (SubPsMetricSpace (X:=IR_as_CPsMetricSpace) P) ->
 totally_bounded P.
Proof.
 intros P H0 Q.
 unfold MStotally_bounded in |- *.
 intro H.
 unfold totally_bounded in |- *.
 constructor.
  exact H0.
 intros e H1.
 set (H2 := OneR[/] e[//]ap_symmetric_unfolded IR [0] e (less_imp_ap IR [0] e H1)) in *.
 unfold AbsSmall in |- *.
 set (H3 := Archimedes H2) in *.
 elim H3.
 intros m H4.
 elim H with m.
 intros l H5.
 exists (list_IR P l).
  intro x.
  apply is_P.
  exact Q.
 intros x H6.
 generalize H5.
 simpl in |- *.
 intro H7.
 elim (H7 (from_IR P x H6)).
 intros x0 H8 H9.
 exists (to_IR P x0).
  apply member1.
  exact H8.
 split.
  generalize H9.
  unfold dIR_as_CSetoid_fun in |- *.
  unfold dIR in |- *.
  case x0.
  intros.
  simpl in |- *.
  apply leEq_transitive with ([--](one_div_succ (R:=IR) m)).
   apply inv_resp_leEq.
   unfold one_div_succ in |- *.
   apply shift_div_leEq.
    unfold Snring in |- *.
    apply less_transitive_unfolded with (nring (R:=IR) m).
     apply less_leEq_trans with H2.
      unfold H2 in |- *.
      apply recip_resp_pos.
      exact H1.
     exact H4.
    simpl in |- *.
    astepl (nring (R:=IR) m[+][0]).
    apply plus_resp_less_lft.
    apply pos_one.
   apply shift_leEq_mult' with (ap_symmetric_unfolded IR [0] e (less_imp_ap IR [0] e H1)).
    exact H1.
   apply leEq_transitive with (nring (R:=IR) m).
    exact H4.
   unfold Snring in |- *.
   simpl in |- *.
   apply less_leEq.
   astepl (nring (R:=IR) m[+][0]).
   apply plus_resp_less_lft.
   apply pos_one.
  apply inv_cancel_leEq.
  astepr (one_div_succ (R:=IR) m).
  apply leEq_transitive with (AbsIR (x[-]scs_elem)).
   apply inv_leEq_AbsIR.
  unfold AbsIR in |- *.
  simpl in |- *.
  generalize H10.
  simpl in |- *.
  intuition.
 generalize H9.
 case x0.
 intros x1 Q0 H10.
 simpl in |- *.
 apply leEq_transitive with (one_div_succ (R:=IR) m).
  generalize H10.
  unfold dIR_as_CSetoid_fun in |- *.
  unfold dIR in |- *.
  simpl in |- *.
  intro H11.
  apply leEq_transitive with (AbsIR (x[-]x1)).
   apply leEq_AbsIR.
  unfold AbsIR in |- *.
  simpl in |- *.
  exact H11.
 unfold one_div_succ in |- *.
 apply shift_div_leEq.
  unfold Snring in |- *.
  apply less_transitive_unfolded with (nring (R:=IR) m).
   apply less_leEq_trans with H2.
    unfold H2 in |- *.
    apply recip_resp_pos.
    exact H1.
   exact H4.
  simpl in |- *.
  astepl (nring (R:=IR) m[+][0]).
  apply plus_resp_less_lft.
  apply pos_one.
 apply shift_leEq_mult' with (ap_symmetric_unfolded IR [0] e (less_imp_ap IR [0] e H1)).
  exact H1.
 apply leEq_transitive with (nring (R:=IR) m).
  exact H4.
 unfold Snring in |- *.
 simpl in |- *.
 apply less_leEq.
 astepl (nring (R:=IR) m[+][0]).
 apply plus_resp_less_lft.
 apply pos_one.
Qed.

(**
Every image under an uniformly continuous function of an totally bounded
pseudo metric space has an infimum and a supremum.
*)

Lemma infimum_exists :
 forall (X : CPsMetricSpace) (f : CSetoid_fun X IR_as_CPsMetricSpace),
 uni_continuous'' f ->
 MStotally_bounded X ->
 forall x : X,
 {z : IR | set_glb_IR (fun y : IR_as_CPsMetricSpace => {x : X | f x[=]y}) z}.
Proof.
 intros X f H0 H1 x.
 apply totally_bounded_has_glb.
 apply MStotallybounded_totallybounded.
   3: apply unicon_resp_totallybounded.
    3: exact H0.
   3: exact H1.
  2: unfold IR_as_CPsMetricSpace in |- *.
  2: simpl in |- *.
  2: apply re_co_do_well_def.
 exists (f x).
 exists x.
 apply eq_reflexive.
Qed.

Lemma supremum_exists :
 forall (X : CPsMetricSpace) (f : CSetoid_fun X IR_as_CPsMetricSpace),
 uni_continuous'' f ->
 MStotally_bounded X ->
 forall x : X,
 {z : IR | set_lub_IR (fun y : IR_as_CPsMetricSpace => {x : X | f x[=]y}) z}.
Proof.
 intros X f H0 H1 x.
 apply totally_bounded_has_lub.
 apply MStotallybounded_totallybounded.
   3: apply unicon_resp_totallybounded.
    3: exact H0.
   3: exact H1.
  2: unfold IR_as_CPsMetricSpace in |- *.
  2: simpl in |- *.
  2: apply re_co_do_well_def.
 exists (f x).
 exists x.
 apply eq_reflexive.
Qed.

(**
A subspace $P$#<I>P</I># of a pseudo metric space $X$#<I>X</I># is said to be located if for all
elements $x$#<I>x</I># of $X$#<I>X</I># there exists an infimum for the distance
between $x$#<I>x</I># and the elements of $P$#<I>P</I>#.
*)

Arguments dsub'_as_cs_fun [X].

Definition located (X : CPsMetricSpace) (P : X -> CProp) :=
  forall (x : X) (r : SubPsMetricSpace P),
  {z : IR |
  set_glb_IR
    (fun v : IR => {y : SubPsMetricSpace P | dsub'_as_cs_fun P x y[=]v}) z}.

Arguments located [X].

Definition located' (X : CPsMetricSpace) (P : X -> CProp) :=
  forall (x : X) (y : SubPsMetricSpace P),
  {z : IR |
  set_glb_IR
    (fun v : IR =>
     {y : SubPsMetricSpace P | x[-d]from_SubPsMetricSpace X P y[=]v}) z}.

Arguments located' [X].

Lemma located_imp_located' :
 forall (X : CPsMetricSpace) (P : X -> CProp), located P -> located' P.
Proof.
 intros X P.
 unfold located in |- *.
 unfold located' in |- *.
 intros H x y.
 set (H0 := H x y) in *.
 elim H0.
 intros x0 H1.
 exists x0.
 unfold dsub' in H1.
 generalize H1.
 unfold dsub'_as_cs_fun in |- *.
 unfold dsub' in |- *.
 simpl in |- *.
 unfold set_glb_IR in |- *.
 intros.
 split.
  intro x1.
  elim H2.
  intros a b H3.
  apply a.
  elim H3.
  intros.
  exists x2.
  astepl (x[-d]from_SubPsMetricSpace X P x2).
   exact p.
  apply ax_d_com.
  apply CPsMetricSpace_is_CPsMetricSpace.
 intros e H3.
 elim H2.
 intros.
 set (H8 := b e H3) in *.
 elim H8.
 intros.
 exists x1.
  elim p.
  intros.
  exists x2.
  astepl (from_SubPsMetricSpace X P x2[-d]x).
   exact p0.
  apply ax_d_com.
  apply CPsMetricSpace_is_CPsMetricSpace.
 exact q.
Qed.

(**
Every totally bounded pseudo metric space is located.
*)

Lemma MStotally_bounded_imp_located :
 forall (X : CPsMetricSpace) (P : X -> CProp),
 MStotally_bounded (SubPsMetricSpace P) -> located P.
Proof.
 intros X P H.
 unfold located in |- *.
 intros x y.
 set (H0 := infimum_exists (SubPsMetricSpace P) (dsub'_as_cs_fun P x)) in *.
 set (H1 := H0 (dsub'_uni_continuous'' X P x) H y) in *.
 elim H1.
 intros x0 H2.
 elim H2.
 intros.
 simpl in |- *.
 exists x0.
 unfold set_glb_IR in |- *.
 split.
  intro x1.
  intro H6.
  apply a.
  generalize b.
  intros.
  elim H6.
  intros.
  exists x2.
  simpl in |- *.
  exact p.
 intros e H3.
 set (H7 := b e H3) in *.
 apply H7.
Qed.

(**
For all $x$#<I>x</I># in a pseudo metric space $X$#<I>X</I>#, for all located subspaces $P$#<I>P</I># of $X$#<I>X</I>#,
[Floc] chooses for a given natural number $n$#<I>n</I># an $y$#<I>y</I># in $P$#<I>P</I># such that:
$d(x,y)\leq \mbox{inf}\{d(x,p)|p \in P\}+(n+1)^{-1}$
#d(x,y) &le; inf&#x007B;d(x,p)&#x007C; p&#x03F5;P&#x007D; + (n+1)<SUP>-1</SUP>#.
[Flocfun] does (almost) the same, but has a different type. This enables
one to use the latter as an argument of [map].
*)

Definition Floc (X : CPsMetricSpace) (P : X -> CProp)
  (H0 : located' P) (H2 : SubPsMetricSpace P) (n : nat)
  (x : X) :
  {y : SubPsMetricSpace P |
  {z : IR |
  set_glb_IR
    (fun v : IR =>
     {y : SubPsMetricSpace P | x[-d]from_SubPsMetricSpace X P y[=]v}) z |
  x[-d]from_SubPsMetricSpace X P y[<=]z[+]one_div_succ n}}.
Proof.
 rename H2 into y.
 unfold located' in H0.
 set (H1 := H0 x y) in *.
 elim H1.
 intros x0 H3.
 unfold set_glb_IR in H3.
 elim H3.
 intros H4 H5.
 elim (H5 (one_div_succ n)).
  intros x1 H6 H7.
  elim H6.
  intros x2 H8.
  eapply existT with (P := fun y0 : SubPsMetricSpace P => {z : IR | set_glb_IR (fun v : IR =>
    {y1 : SubPsMetricSpace P | x[-d]from_SubPsMetricSpace X P y1[=]v}) z |
      x[-d]from_SubPsMetricSpace X P y0[<=]z[+]one_div_succ n}) (x := x2).
  eapply exist2T with (P := fun z : IR => set_glb_IR (fun v : IR => {y1 : SubPsMetricSpace P |
    x[-d]from_SubPsMetricSpace X P y1[=]v}) z) (Q := fun z : IR =>
      x[-d]from_SubPsMetricSpace X P x2[<=]z[+]one_div_succ n) (x := x0).
   unfold set_glb_IR in |- *.
   apply H3.
  apply shift_leEq_plus'.
  astepl (x1[-]x0).
  apply less_leEq.
  apply H7.
 apply one_div_succ_pos.
Defined.

Definition Flocfun (X : CPsMetricSpace) (P : X -> CProp)
  (H0 : located' P) (H2 : SubPsMetricSpace P) (n : nat) :
  X -> SubPsMetricSpace P.
Proof.
 intros.
 set (H1 := Floc X P H0 H2 n X0) in *.
 elim H1.
 intros.
 exact x.
Defined.

(**
A located subset $P$#<I>P</I># of a totally bounded pseudo metric space $X$
#<I>X</I># is totally
bounded.
*)

Lemma locatedsub_totallybounded_imp_totallyboundedsub :
 forall (X : CPsMetricSpace) (P : X -> CProp),
 SubPsMetricSpace P ->
 located' P -> MStotally_bounded X -> MStotally_bounded (SubPsMetricSpace P).
Proof.
 intros X P y H0.
 unfold MStotally_bounded in |- *.
 intros H1 n.
 elim (H1 (3 * n + 2)).
 intros l H2.
 unfold located' in H0.
 simpl in |- *.
 exists (map (Flocfun X P H0 y (3 * n + 2)) l).
 simpl in |- *.
 intro x.
 elim (H2 (from_SubPsMetricSpace X P x)).
 intros xj xjl H3.
 exists (Flocfun X P H0 y (n + (n + (n + 0)) + 2) xj).
  apply map_member with (f := Flocfun X P H0 y (n + (n + (n + 0)) + 2)).
  exact xjl.
 unfold Flocfun in |- *.
 unfold sigT_rec in |- *.
 unfold sigT_rect in |- *.
 case Floc.
 intros.
 elim s.
 intros x2 p0 q.
 generalize H3.
 case x.
 intros xn Pn H4.
 apply leEq_transitive with ((xn[-d]xj)[+](xj[-d]from_SubPsMetricSpace X P x0)).
  case x0.
  intros.
  simpl in |- *.
  apply ax_d_tri_ineq.
  apply CPsMetricSpace_is_CPsMetricSpace.
 astepr (one_div_succ (R:=IR) (n + (n + (n + 0)) + 2)[+] (one_div_succ (n + (n + (n + 0)) + 2)[+]
   one_div_succ (n + (n + (n + 0)) + 2))).
  apply plus_resp_leEq_both.
   apply H4.
  apply leEq_transitive with (x2[+]one_div_succ (n + (n + (n + 0)) + 2)).
   apply leEq_transitive with (xj[-d]from_SubPsMetricSpace X P x0).
    apply eq_imp_leEq.
    apply csbf_wd_unfolded.
     intuition; auto with *.
    intuition; auto with *.
   exact q.
  apply plus_resp_leEq.
  apply leEq_transitive with (from_SubPsMetricSpace X P x[-d]xj).
   unfold set_glb_IR in p0.
   elim p0.
   intros.
   apply a.
   unfold SubPsMetricSpace in |- *.
   simpl in |- *.
   exists x.
   apply ax_d_com.
   apply CPsMetricSpace_is_CPsMetricSpace.
  apply H3.
 astepr ([1][*]one_div_succ (R:=IR) n).
 astepr (((Three:IR)[/] Three:IR[//]three_ap_zero IR)[*]one_div_succ n).
 astepl (one_div_succ (n + (n + (n + 0)) + 2)[+] (Two:IR)[*]one_div_succ (n + (n + (n + 0)) + 2)).
 astepl (OneR[*]one_div_succ (n + (n + (n + 0)) + 2)[+]
   (Two:IR)[*]one_div_succ (n + (n + (n + 0)) + 2)).
 astepl ((OneR[+]Two)[*]one_div_succ (n + (n + (n + 0)) + 2)).
 stepl ((Three:IR)[*]one_div_succ (n + (n + (n + 0)) + 2)).
  2: apply mult_wdl.
  2: rational.
 astepr ((Three:IR)[*]([1][/] Three[//]three_ap_zero IR)[*]one_div_succ n).
  astepr ((Three:IR)[*](([1][/] Three[//]three_ap_zero IR)[*]one_div_succ n)).
  apply mult_wdr.
  unfold one_div_succ in |- *.
  unfold Snring in |- *.
  simpl in |- *.
  astepr (OneR[/] (Three:IR)[*](nring n[+][1])[//]
    mult_resp_ap_zero IR Three (nring n[+][1]) (three_ap_zero IR) (nringS_ap_zero IR n)).
   apply eq_div.
   apply mult_wdr.
   astepl (Three[*]nring (R:=IR) n[+]Three[*][1]).
   simpl in |- *.
   astepr (nring (R:=IR) (n + (n + (n + 0)))[+]Two[+][1]).
   astepr (nring (R:=IR) n[+]nring (n + (n + 0))[+]Two[+][1]).
   astepr (nring (R:=IR) n[+](nring n[+]nring (n + 0))[+]Two[+][1]).
   3: apply mult_wdl.
   3: rational.
  2: simpl in |- *.
  2: rational.
 astepr (nring (R:=IR) n[+](nring n[+]nring (n + 0))[+]Two[+][1]).
 astepr (nring (R:=IR) n[+](nring n[+]nring (n + 0))[+](Two[+][1])).
 astepl ((ZeroR[+][1][+][1][+][1])[*]nring n[+]([0][+][1][+][1][+][1])).
 simpl in |- *.
 astepl (ZeroR[+][1][+][1][+][1][+]([0][+][1][+][1][+][1])[*]nring n).
 astepr (ZeroR[+][1][+][1][+][1][+](nring n[+](nring n[+]nring (n + 0)))).
 apply plus_resp_eq.
 astepr (nring (R:=IR) n[+](nring n[+](nring n[+]nring 0))).
 simpl in |- *.
 rational.
Qed.

(**
Here are some definitions that could come in handy:
*)

Definition MSCauchy_seq (X : CPsMetricSpace) (seq : nat -> X) : CProp :=
  forall n : nat,
  {m : nat |
  forall i j : nat, m <= i -> m <= j -> seq i[-d]seq j[<=]one_div_succ n}.

Arguments MSseqLimit' [X].

Definition MSComplete (X : CPsMetricSpace) : CProp :=
  forall seq : nat -> X,
  MSCauchy_seq X seq -> {lim : X | MSseqLimit' seq lim}.

(**
A compact pseudo metric space is a pseudo metric space which is complete and
totally bounded.
*)

Definition MSCompact (X : CPsMetricSpace) : CProp :=
  MSComplete X and MStotally_bounded X.

(**
A subset $P$#<I>P</I># is %\emph{open}%#<I>open</I># if for all $x$#<I>x</I># in $P$#<I>P</I># there exists an open sphere
with centre $x$#<I>x</I># that is contained in $P$#<I>P</I>#.
*)

Definition open (X : CPsMetricSpace) (P : X -> CProp) :=
  forall x : X,
  P x -> {e : IR | [0][<]e and (forall z : X, z[-d]x[<]e -> P z)}.

Arguments open [X].

(**
The operator [infima] gives the infimum for the distance between an
element $x$#<I>x</I># of a located pseudo metric space $X$#<I>X</I># and the elements of a
subspace $P$#<I>P</I># of $X$#<I>X</I>#.
*)

Definition infima (X : CPsMetricSpace) (P : X -> CProp)
  (H : located' P) (a : SubPsMetricSpace P) : X -> IR.
Proof.
 intros H0.
 unfold located' in H.
 elim (H H0 a).
 intros.
 exact x.
Defined.

Arguments infima [X].
(**
A non-empty totally bounded sub-pseudo-metric-space $P$#<I>P</I># is said to be
%\emph{well contained}% #<I>well contained</I># in an open sub-pseudo-metric-space $Q$#<I>Q</I># if $Q$#<I>Q</I># contains
all points that are in some sense close to $P$#<I>P</I>#.
*)

Definition well_contained (X : CPsMetricSpace) (P Q : X -> CProp)
  (a : SubPsMetricSpace P) :=
  open Q ->
  forall H : MStotally_bounded (SubPsMetricSpace P),
  {r : IR | [0][<]r |
  forall q : X,
  infima P (located_imp_located' X P (MStotally_bounded_imp_located X P H)) a
    q[<=]r -> Q q}.

End loc_and_bound.
