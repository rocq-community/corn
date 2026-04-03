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

(** printing [-S-] %\ensuremath{\int}% #&int;# *)

Require Export CoRN.ftc.MoreIntegrals.
Require Export CoRN.ftc.CalculusTheorems.

Opaque Min.

Section Indefinite_Integral.

(**
* The Fundamental Theorem of Calculus

Finally we can prove the fundamental theorem of calculus and its most
important corollaries, which are the main tools to formalize most of
real analysis.

** Indefinite Integrals

We define the indefinite integral of a function in a proper interval
in the obvious way; we just need to state a first lemma so that the
continuity proofs become unnecessary.

%\begin{convention}% Let [I : interval], [F : PartIR] be continuous in [I]
and [a] be a point in [I].
%\end{convention}%
*)

Variable I : interval.
Variable F : PartIR.

Hypothesis contF : Continuous I F.

Variable a : IR.
Hypothesis Ha : I a.

Lemma prim_lemma : forall x : IR, I x -> Continuous_I (Min_leEq_Max a x) F.
Proof.
 intros.
 elim contF; intros incI contI.
 Included.
Qed.

Lemma Fprim_strext : forall x y Hx Hy,
 Integral (prim_lemma x Hx) [#] Integral (prim_lemma y Hy) -> x [#] y.
Proof.
 intros x y Hx Hy H.
 elim (Integral_strext' _ _ _ _ _ _ _ _ _ H).
  intro; exfalso.
  generalize a0; apply ap_irreflexive_unfolded.
 auto.
Qed.

Definition Fprim : PartIR.
Proof.
 apply Build_PartFunct with (pfpfun := fun (x : IR) (Hx : I x) => Integral (prim_lemma x Hx)).
  apply iprop_wd.
 exact Fprim_strext.
Defined.

End Indefinite_Integral.

Arguments Fprim [I F].

Notation "[-S-] F" := (Fprim F) (at level 20).

Section FTC.

(**
** The FTC

We can now prove our main theorem.  We begin by remarking that the
primitive function is always continuous.

%\begin{convention}% Assume that [J : interval], [F : PartIR] is
continuous in [J] and [x0] is a point in [J].  Denote by [G] the
indefinite integral of [F] from [x0].
%\end{convention}%
*)

Variable J : interval.
Variable F : PartIR.

Hypothesis contF : Continuous J F.

Variable x0 : IR.
Hypothesis Hx0 : J x0.

(* begin hide *)
Let G := ( [-S-]contF) x0 Hx0.
(* end hide *)

Lemma Continuous_prim : Continuous J G.
Proof.
 split.
  Included.
 intros a b Hab H. split.
 Included.
 intros e H0.
 simpl in |- *; simpl in H.
 exists (e[/] _[//] max_one_ap_zero (Norm_Funct (included_imp_Continuous _ _ contF _ _ _ H))).
  apply div_resp_pos.
   apply pos_max_one.
  assumption.
 intros x y H1 H2 Hx Hy H3.
 cut (included (Compact (Min_leEq_Max y x)) (Compact Hab)).
  intro Hinc.
  cut (Continuous_I (Min_leEq_Max y x) F). intro H4.
   apply leEq_wdl with (AbsIR (Integral H4)).
    eapply leEq_transitive.
     apply Integral_leEq_norm.
    apply leEq_transitive with (Max (Norm_Funct (included_imp_Continuous _ _ contF _ _ _ H)) [1][*]
      AbsIR (x[-]y)).
     apply mult_resp_leEq_rht.
      apply leEq_transitive with (Norm_Funct (included_imp_Continuous _ _ contF _ _ _ H)).
       apply leEq_Norm_Funct.
       intros.
       apply norm_bnd_AbsIR.
       apply Hinc; auto.
      apply lft_leEq_Max.
     apply AbsIR_nonneg.
    eapply shift_mult_leEq'.
     apply pos_max_one.
    apply H3.
   apply AbsIR_wd.
   rstepl (Integral (prim_lemma J F contF x0 Hx0 y Hy) [+]Integral H4[-]
     Integral (prim_lemma J F contF x0 Hx0 y Hy)).
   apply cg_minus_wd.
    apply eq_symmetric_unfolded; apply Integral_plus_Integral with (Min3_leEq_Max3 x0 x y).
    apply included_imp_Continuous with J; auto.
    apply included3_interval; auto.
   apply Integral_wd.
   apply Feq_reflexive.
   apply (included_trans _ (Compact (Min_leEq_Max x0 y)) J); Included.
  apply included_imp_Continuous with J; auto.
  Included.
 Included.
Qed.

(**
The derivative of [G] is simply [F].
*)

Hypothesis pJ : proper J.

Theorem FTC1 : Derivative J pJ G F.
Proof.
 split; Included.
 split; Included.
 intros; apply Derivative_I_char.
   Included.
  inversion_clear contF.
  Included.
 intros.
 red in contF.
 inversion_clear contF.
 elim (contin_prop _ _ _ _ (X2 _ _ _ X) e X0); intros d H3 H4.
 exists d.
  assumption.
 intros x y X3 X4 Hx Hy Hx' H.
 simpl in |- *.
 rename Hab into Hab'.
 set (Hab := less_leEq _ _ _ Hab') in *.
 cut (included (Compact (Min_leEq_Max x y)) (Compact Hab)).
  intro Hinc.
  cut (Continuous_I (Min_leEq_Max x y) F).
   2: apply included_imp_Continuous with J; auto.
   intro H8.
   apply leEq_wdl with (AbsIR (Integral H8[-]
     Integral (Continuous_I_const _ _ (Min_leEq_Max x y) (F x Hx')))).
    apply leEq_wdl with (AbsIR (Integral (Continuous_I_minus _ _ _ _ _ H8
      (Continuous_I_const _ _ _ (F x Hx'))))).
     eapply leEq_transitive.
      apply Integral_leEq_norm.
     apply mult_resp_leEq_rht.
      2: apply AbsIR_nonneg.
     apply leEq_Norm_Funct.
     intros z Hz Hz1.
     simpl in |- *.
     apply leEq_wdl with (AbsIR (F z (X1 z (X z (Hinc z Hz))) [-]F x Hx')).
      2: apply AbsIR_wd; algebra.
     apply H4; auto.
     eapply leEq_transitive.
      2: apply H.
     eapply leEq_wdr.
      2: apply eq_symmetric_unfolded; apply Abs_Max.
     eapply leEq_wdr.
      2: apply AbsIR_eq_x; apply shift_leEq_minus.
      2: astepl (Min x y); apply Min_leEq_Max.
     apply compact_elements with (Min_leEq_Max x y); auto.
     apply compact_Min_lft.
    apply AbsIR_wd; apply Integral_minus.
   apply AbsIR_wd; apply cg_minus_wd.
    rstepl (Integral (prim_lemma _ _ contF x0 Hx0 _ Hx) [+]Integral H8[-]
      Integral (prim_lemma _ _ contF x0 Hx0 _ Hx)).
    apply cg_minus_wd.
     apply eq_symmetric_unfolded; apply Integral_plus_Integral with (Min3_leEq_Max3 x0 y x).
     apply included_imp_Continuous with J; auto.
     apply included3_interval; auto.
    apply Integral_wd. apply Feq_reflexive.
    apply (included_trans _ (Compact (Min_leEq_Max x0 x)) J); try apply included_interval; auto.
   apply Integral_const.
  Included.
 Included.
Qed.

(**
Any other function [G0] with derivative [F] must differ from [G] by a constant.
*)

Variable G0 : PartIR.
Hypothesis derG0 : Derivative J pJ G0 F.

Theorem FTC2 : {c : IR | Feq J (G{-}G0) [-C-]c}.
Proof.
 apply FConst_prop with pJ.
 apply Derivative_wdr with (F{-}F).
  FEQ.
 apply Derivative_minus; auto.
 apply FTC1.
Qed.

(**
The following is another statement of the Fundamental Theorem of Calculus, also known as Barrow's rule.
*)

(* begin hide *)
Let G0_inc := Derivative_imp_inc _ _ _ _ derG0.
(* end hide *)

End FTC.

Theorem Barrow : forall J F (contF : Continuous J F)
 (pJ:proper J) G0 (derG0 : Derivative J pJ G0 F)
 a b (H : Continuous_I (Min_leEq_Max a b) F) Ha Hb,
 let Ha' := Derivative_imp_inc _ _ _ _ derG0 a Ha in let Hb' := Derivative_imp_inc _ _ _ _ derG0 b Hb in Integral H [=] G0 b Hb'[-]G0 a Ha'.
Proof.
 (* begin hide *)
 intros J F contF pJ G0 derG0 a b H1 Ha Hb; intros.
 pose (x0:=a).
 pose (Hx0:=Ha).
 set (G := ( [-S-]contF) x0 Hx0).
 elim (@FTC2 J F contF x0 Hx0 pJ G0 derG0); intros c Hc.
 elim Hc; intros H2 H.
 elim H; clear H Hc; intros H3 H0.
 (* Allow G0a to be G0 of a.
 Allow G0b to be G0 of b. *)
 set (G0a := G0 a Ha') in *.
 set (G0b := G0 b Hb') in *.
 rstepr (G0b[+]c[-] (G0a[+]c)).
 (* Allow Ga to be G of a.
 Allow Gb to be G of b.*)
 set (Ga := G a Ha) in *.
 set (Gb := G b Hb) in *.
 apply eq_transitive_unfolded with (Gb[-]Ga).
  unfold Ga, Gb, G in |- *; simpl in |- *.
  cut (forall x y z : IR, z [=] x[+]y -> y [=] z[-]x). intro H5.
   apply H5.
   apply Integral_plus_Integral with (Min3_leEq_Max3 x0 b a).
   apply included_imp_Continuous with J.
    auto.
   apply included3_interval; auto.
  intros; apply eq_symmetric_unfolded.
  rstepr (x[+]y[-]x); algebra.
 cut (forall x y z : IR, x[-]y [=] z -> x [=] y[+]z); intros.
  fold G in H0.
  apply cg_minus_wd; unfold Ga, Gb, G0a, G0b in |- *; apply H; auto.
   simpl in H0.
   apply eq_transitive_unfolded with ((G{-}G0) b (Hb, Hb')).
    2: apply H0 with (Hx := (Hb, Hb')).
     simpl.
     apply cg_minus_wd.
      apply Integral_wd.
      apply Feq_reflexive.
      destruct H1 as [H1 _].
      apply H1.
     algebra.
    auto.
   auto.
  change c with ([-C-]c a I).
  apply eq_transitive_unfolded with ((G{-}G0) a (Ha, Ha')).
   2: apply H0 with (Hx := (Ha, Ha')).
   simpl.
   apply cg_minus_wd.
    apply Integral_wd.
    apply Feq_reflexive.
    destruct H1 as [H1 _].
    intros y Hy.
    apply H1.
    apply (compact_wd _ _ (Min_leEq_Max a b) a).
     apply compact_Min_lft.
    unfold compact, x0 in Hy.
    destruct Hy.
    apply leEq_imp_eq.
     astepl (Min a a). assumption.
      apply Min_id.
    stepr(Max a a). assumption.
     apply Max_id.
   algebra.
  auto.
 rstepl (y[+] (x[-]y)).
 algebra.
Qed.
(* end hide *)

#[global]
Hint Resolve Continuous_prim: continuous.
#[global]
Hint Resolve FTC1: derivate.

Section Limit_of_Integral_Seq.

(**
** Corollaries

With these tools in our hand, we can prove several useful results.

%\begin{convention}% From this point onwards:
 - [J : interval];
 - [f : nat->PartIR] is a sequence of continuous functions (in [J]);
 - [F : PartIR] is continuous in [J].

%\end{convention}%

In the first place, if a sequence of continuous functions converges
then the sequence of their primitives also converges, and the limit
commutes with the indefinite integral.
*)

Variable J : interval.

Variable f : nat -> PartIR.
Variable F : PartIR.

Hypothesis contf : forall n : nat, Continuous J (f n).
Hypothesis contF : Continuous J F.

Section Compact.

(**
We need to prove this result first for compact intervals.

%\begin{convention}% Assume that [a, b, x0 : IR] with [(f n)] and [F]
continuous in [[a,b]], $x0\in[a,b]$#x0&isin;[a,b]#; denote by
[(g n)] and [G] the indefinite integrals respectively of [(f n)] and
[F] with origin [x0].
%\end{convention}%
*)

Variables a b : IR.
Hypothesis Hab : a [<=] b.
Hypothesis contIf : forall n : nat, Continuous_I Hab (f n).
Hypothesis contIF : Continuous_I Hab F.
(* begin show *)
Hypothesis convF : conv_fun_seq' a b Hab f F contIf contIF.
(* end show *)

Variable x0 : IR.
Hypothesis Hx0 : J x0.
Hypothesis Hx0' : Compact Hab x0.

(* begin hide *)
Let g (n : nat) := ( [-S-]contf n) x0 Hx0.
Let G := ( [-S-]contF) x0 Hx0.
(* end hide *)

(* begin show *)
Hypothesis contg : forall n : nat, Continuous_I Hab (g n).
Hypothesis contG : Continuous_I Hab G.
(* end show *)

Lemma fun_lim_seq_integral : conv_fun_seq' a b Hab g G contg contG.
Proof.
 assert (H : conv_norm_fun_seq _ _ _ _ _ contIf contIF).
  apply conv_fun_seq'_norm; assumption.
 intros e H0.
 elim (Archimedes (AbsIR (b[-]a) [/] _[//]pos_ap_zero _ _ H0)); intros k Hk.
 elim (H k); intros N HN.
 exists N; intros.
 assert (H2 : included (Compact (Min_leEq_Max x0 x)) (Compact Hab)).
  apply included2_compact; auto.
 simpl in |- *.
 apply leEq_wdl with (AbsIR (Integral (Continuous_I_minus _ _ _ _ _ (prim_lemma _ _ (contf n) x0 Hx0 _
   (contin_imp_inc _ _ _ _ (contg n) _ Hx)) (prim_lemma _ _ contF x0 Hx0 _
     (contin_imp_inc _ _ _ _ contG _ Hx))))).
  2: apply AbsIR_wd; apply Integral_minus.
 eapply leEq_transitive.
  apply Integral_leEq_norm.
 apply leEq_transitive with (one_div_succ k[*]AbsIR (b[-]a)).
  apply mult_resp_leEq_both.
     apply positive_norm.
    apply AbsIR_nonneg.
   eapply leEq_transitive.
    2: apply (HN n H1).
   apply leEq_Norm_Funct; intros.
   apply norm_bnd_AbsIR.
   apply H2; auto.
  apply compact_elements with Hab; auto.
 unfold one_div_succ, Snring in |- *.
 rstepl (AbsIR (b[-]a) [/] _[//]nring_ap_zero _ _ (sym_not_eq (O_S k))).
 apply shift_div_leEq.
  apply pos_nring_S.
 eapply shift_leEq_mult'.
  assumption.
 apply less_leEq; eapply leEq_less_trans.
  apply Hk.
 simpl in |- *.
 apply less_plusOne.
Qed.

End Compact.

(**
And now we can generalize it step by step.
*)

Lemma limit_of_integral : conv_fun_seq'_IR J f F contf contF -> forall x y Hxy,
 included (Compact Hxy) J -> forall Hf HF,
 Cauchy_Lim_prop2 (fun n => integral x y Hxy (f n) (Hf n)) (integral x y Hxy F HF).
Proof.
 intros H x y Hxy H0 Hf HF.
 assert (Hx : J x). apply H0; apply compact_inc_lft.
  assert (Hy : J y). apply H0; apply compact_inc_rht.
  set (g := fun n : nat => ( [-S-]contf n) x Hx) in *.
 set (G := ( [-S-]contF) x Hx) in *.
 set (Hxg := fun n : nat => Hy) in *.
 apply Lim_wd with (Part G y Hy).
  simpl in |- *; apply Integral_integral.
 apply Cauchy_Lim_prop2_wd with (fun n : nat => Part (g n) y (Hxg n)).
  2: intro; simpl in |- *; apply Integral_integral.
 cut (forall n : nat, Continuous_I Hxy (g n)). intro H1.
  cut (Continuous_I Hxy G). intro H2.
   apply fun_conv_imp_seq_conv with (contf := H1) (contF := H2).
    set (H4 := fun n : nat => included_imp_Continuous _ _ (contf n) _ _ _ H0) in *.
    set (H5 := included_imp_Continuous _ _ contF _ _ _ H0) in *.
    unfold g, G in |- *.
    apply fun_lim_seq_integral with H4 H5.
     unfold H4, H5 in |- *.
     apply H; auto.
    apply compact_inc_lft.
   apply compact_inc_rht.
  unfold G in |- *; apply included_imp_Continuous with J; Contin.
 intro; unfold g in |- *; apply included_imp_Continuous with J; Contin.
Qed.

Lemma limit_of_Integral : conv_fun_seq'_IR J f F contf contF -> forall x y,
 included (Compact (Min_leEq_Max x y)) J -> forall Hxy Hf HF,
 Cauchy_Lim_prop2 (fun n => Integral (a:=x) (b:=y) (Hab:=Hxy) (F:=f n) (Hf n))
   (Integral (Hab:=Hxy) (F:=F) HF).
Proof.
 intros convF x y H.
 set (x0 := Min x y) in *.
 intros.
 assert (Hx0 : J x0).
  apply H; apply compact_inc_lft.
 assert (Hx0' : Compact Hxy x0).
  apply compact_inc_lft.
 set (g := fun n : nat => ( [-S-]contf n) x0 Hx0) in *.
 set (G := ( [-S-]contF) x0 Hx0) in *.
 unfold Integral in |- *; fold x0 in |- *.
 apply (Cauchy_Lim_minus (fun n : nat => integral _ _ _ _ (Integral_inc2 _ _ _ _ (Hf n)))
   (fun n : nat => integral _ _ _ _ (Integral_inc1 _ _ _ _ (Hf n)))); fold x0 in |- *.
  apply limit_of_integral with (Hf := fun n : nat => Integral_inc2 _ _ Hxy _ (Hf n)); auto.
  apply included_trans with (Compact (Min_leEq_Max x y)); Included.
  apply included_compact.
   apply compact_inc_lft.
  apply compact_Min_rht.
 apply limit_of_integral with (Hf := fun n : nat => Integral_inc1 _ _ Hxy _ (Hf n)); auto.
 apply included_trans with (Compact (Min_leEq_Max x y)); auto.
 apply included_compact.
  apply compact_inc_lft.
 apply compact_Min_lft.
Qed.

Section General.

(**
Finally, with [x0, g, G] as before,
*)

(* begin show *)
Hypothesis convF : conv_fun_seq'_IR J f F contf contF.
(* end show *)

Variable x0 : IR.
Hypothesis Hx0 : J x0.

(* begin hide *)
Let g (n : nat) := ( [-S-]contf n) x0 Hx0.
Let G := ( [-S-]contF) x0 Hx0.
(* end hide *)

Hypothesis contg : forall n : nat, Continuous J (g n).
Hypothesis contG : Continuous J G.

Lemma fun_lim_seq_integral_IR : conv_fun_seq'_IR J g G contg contG.
Proof.
 red in |- *; intros.
 unfold g, G in |- *.
 cut (J a). intro H.
  set (h := fun n : nat => [-C-] (Integral (prim_lemma _ _ (contf n) x0 Hx0 a H))) in *.
  set (g' := fun n : nat => h n{+} ( [-S-]contf n) a H) in *.
  set (G' := [-C-] (Integral (prim_lemma _ _ contF x0 Hx0 a H)) {+} ( [-S-]contF) a H) in *.
  assert (H0 : forall n : nat, Continuous_I Hab (h n)).
   intro; unfold h in |- *; Contin.
  cut (forall n : nat, Continuous_I Hab (( [-S-]contf n) a H)). intro H1.
   assert (H2 : forall n : nat, Continuous_I Hab (g' n)).
    intro; unfold g' in |- *; Contin.
   cut (Continuous_I Hab (( [-S-]contF) a H)). intro H3.
    assert (H4 : Continuous_I Hab G').
     unfold G' in |- *; Contin.
    apply conv_fun_seq'_wdl with g' H2 (included_imp_Continuous _ _ contG _ _ _ Hinc).
     intro; FEQ.
     simpl in |- *.
     apply eq_symmetric_unfolded; apply Integral_plus_Integral with (Min3_leEq_Max3 x0 x a).
     apply included_imp_Continuous with J; Contin.
    apply conv_fun_seq'_wdr with H2 G' H4.
     FEQ.
     simpl in |- *.
     apply eq_symmetric_unfolded; apply Integral_plus_Integral with (Min3_leEq_Max3 x0 x a).
     apply included_imp_Continuous with J; Contin.
    unfold g', G' in |- *.
    apply conv_fun_seq'_wdl with (f := g')
      (contf := fun n : nat => Continuous_I_plus _ _ _ _ _ (H0 n) (H1 n)) (contF := H4).
     unfold g' in H2.
     intro; apply Feq_reflexive; Included.
    unfold g', G' in |- *.
    apply (fun_Lim_seq_plus' _ _ Hab h (fun n : nat => ( [-S-]contf n) a H) H0 H1 _ _
      (Continuous_I_const _ _ _ (Integral (prim_lemma _ _ contF x0 Hx0 a H))) H3).
     unfold h in |- *.
     apply seq_conv_imp_fun_conv
       with (x := fun n : nat => Integral (prim_lemma _ _ (contf n) x0 Hx0 a H)).
     apply limit_of_Integral with (Hf := fun n : nat => prim_lemma _ _ (contf n) x0 Hx0 a H); auto.
     Included.
    apply fun_lim_seq_integral with (fun n : nat => included_imp_Continuous _ _ (contf n) _ _ _ Hinc)
      (included_imp_Continuous _ _ contF _ _ _ Hinc).
     apply convF; auto.
    apply compact_inc_lft.
   apply included_imp_Continuous with J; Contin.
  intro; apply included_imp_Continuous with J; Contin.
 apply Hinc; apply compact_inc_lft.
Qed.

End General.

End Limit_of_Integral_Seq.

Section Limit_of_Derivative_Seq.

(**
Similar results hold for the sequence of derivatives of a converging sequence; this time the proof is easier, as we can do it directly for any kind of interval.

%\begin{convention}% Let [g] be the sequence of derivatives of [f] and [G] be the derivative of [F].
%\end{convention}%
*)

Variable J : interval.
Hypothesis pJ : proper J.

Variables f g : nat -> PartIR.
Variables F G : PartIR.

Hypothesis contf : forall n : nat, Continuous J (f n).
Hypothesis contF : Continuous J F.
Hypothesis convF : conv_fun_seq'_IR J f F contf contF.

Hypothesis contg : forall n : nat, Continuous J (g n).
Hypothesis contG : Continuous J G.
Hypothesis convG : conv_fun_seq'_IR J g G contg contG.

Hypothesis derf : forall n : nat, Derivative J pJ (f n) (g n).

Lemma fun_lim_seq_derivative : Derivative J pJ F G.
Proof.
 elim (nonvoid_point _ (proper_nonvoid _ pJ)); intros a Ha.
 set (h := fun n : nat => ( [-S-]contg n) a Ha) in *.
 set (H := ( [-S-]contG) a Ha) in *.
 assert (H0 : Derivative J pJ H G). unfold H in |- *; apply FTC1.
  assert (H1 : forall n : nat, Derivative J pJ (h n) (g n)). intro; unfold h in |- *; apply FTC1.
  assert (H2 : conv_fun_seq'_IR J _ _ (fun n : nat => Derivative_imp_Continuous _ _ _ _ (H1 n))
    (Derivative_imp_Continuous _ _ _ _ H0)).
  unfold h, H in |- *. eapply fun_lim_seq_integral_IR with (contf := contg); auto.
  cut {c : IR | Feq J (F{-}H) [-C-]c}.
  intro H3.
  elim H3; clear H3; intros c Hc.
  apply Derivative_wdl with (H{+} [-C-]c).
   apply Feq_transitive with (H{+} (F{-}H)).
    apply Feq_plus.
     apply Feq_reflexive; Included.
    apply Feq_symmetric; assumption.
   clear Hc H2 H1; clearbody H.
   FEQ.
  apply Derivative_wdr with (G{+} [-C-][0]).
   FEQ.
  apply Derivative_plus; auto.
  apply Derivative_const.
 assert (H3 : forall n : nat, {c : IR | Feq J (f n{-}h n) [-C-]c}).
  intro; apply FConst_prop with pJ.
  apply Derivative_wdr with (g n{-}g n). FEQ. apply Derivative_minus; auto.
   assert (contw : forall n : nat, Continuous J (f n{-}h n)). unfold h in |- *; Contin.
  assert (contW : Continuous J (F{-}H)). unfold H in |- *; Contin.
  apply fun_const_Lim with (fun n : nat => f n{-}h n) contw contW.
   auto.
  eapply fun_Lim_seq_minus'_IR.
   apply convF.
  apply H2.
 assumption.
Qed.

End Limit_of_Derivative_Seq.

Section Derivative_Series.

(**
As a very important case of this result, we get a rule for deriving series.
*)

Variable J : interval.
Hypothesis pJ : proper J.
Variables f g : nat -> PartIR.

(* begin show *)
Hypothesis convF : fun_series_convergent_IR J f.
Hypothesis convG : fun_series_convergent_IR J g.
(* end show *)
Hypothesis derF : forall n : nat, Derivative J pJ (f n) (g n).

Lemma Derivative_FSeries : Derivative J pJ (FSeries_Sum convF) (FSeries_Sum convG).
Proof.
 apply fun_lim_seq_derivative with (f := fun n : nat => FSum0 n f)
   (contf := Continuous_Sum0 _ _ (convergent_imp_Continuous _ _ convF))
     (contF := Continuous_FSeries_Sum _ _ convF) (g := fun n : nat => FSum0 n g)
       (contg := Continuous_Sum0 _ _ (convergent_imp_Continuous _ _ convG))
         (contG := Continuous_FSeries_Sum _ _ convG).
   3: Deriv.
  apply FSeries_conv.
 apply FSeries_conv.
Qed.

End Derivative_Series.
