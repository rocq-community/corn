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

Require Export CoRN.reals.CReals1.

Set Nested Proofs Allowed.

Section CMetric_Fields.

(**
* Metric Fields *)

Record is_CMetricField (F : CField) (abs : CSetoid_fun F IR) : Prop :=
  {ax_abs_gt_zero   : forall x : F, [0] [<=] abs x;
   ax_abs_resp_mult : forall x y : F, abs (x[*]y) [=] abs x[*]abs y;
   ax_abs_triangle  : forall x y : F, abs (x[+]y) [<=] abs x[+]abs y}.

Record CMetricField : Type :=
  {cmf_crr   :> CField;
   cmf_abs   :  CSetoid_fun cmf_crr IR;
   cmf_proof :  is_CMetricField cmf_crr cmf_abs}.

End CMetric_Fields.

Notation MAbs := (cmf_abs _).
Section basics.

Lemma MAbs_one : forall F : CMetricField,
 {MAbs ([1]:F) [=] [0]} + {MAbs ([1]:F) [=] [1]}.
Proof.
 intro F.
 apply square_id.
 astepl (cmf_abs F [1][*]cmf_abs F [1]).
 astepl (cmf_abs F ([1][*][1])).
  astepl (cmf_abs F [1]).
  apply eq_reflexive.
 apply ax_abs_resp_mult.
 apply cmf_proof.
Qed.

(* begin hide *)
Lemma Hulp : forall F : CMetricField,
    cmf_abs F [1] [=] [1] -> cmf_abs F [--][1] [=] [--] (cmf_abs F [1]) -> False.
  intros F G H.
  set (H0 := ax_abs_gt_zero) in *.
  generalize H0.
  intro H1.
  set (H2 := H1 F (cmf_abs F) (cmf_proof F) [--] ([1]:F)) in *.
  rewrite -> leEq_def in H2.
  apply H2.
  astepl ( [--] (cmf_abs F [1])).
  astepl ( [--]OneR).
  apply plus_cancel_less with OneR.
  astepl ZeroR.
  astepr OneR.
  apply pos_one.
Qed.
(* begin hide *)

Lemma MAbs_one_recip_one : forall F : CMetricField,
 MAbs ([1]:F) [=] MAbs ( [--][1]:F).
Proof.
 intro F.
 cut ({cmf_abs F ([1]:F) [=] [0]} + {cmf_abs F ([1]:F) [=] [1]}).
  intro H.
  elim H.
   intro H2.
   astepl ZeroR.
   astepr (cmf_abs F ( [--][1][*][1])).
   astepr (cmf_abs F [--][1][*]cmf_abs F [1]).
    astepr (cmf_abs F [--][1][*][0]).
    astepr ZeroR.
    apply eq_reflexive_unfolded.
   apply eq_symmetric_unfolded.
   apply ax_abs_resp_mult.
   apply cmf_proof.
  intro H1.
  cut (cmf_abs F [--][1] [=] cmf_abs F [1] or cmf_abs F [--][1] [=] [--] (cmf_abs F [1])).
   intro H2.
   elim H2.
    intro H3.
    apply eq_symmetric_unfolded.
    exact H3.
   intro H3.
simpl in |- *.
   set (H4 := Hulp F H1 H3) in *.
   intuition.
  apply cond_square_eq.
    apply ap_symmetric_unfolded.
    apply less_imp_ap.
    apply pos_two.
   astepl OneR.
   algebra.
  astepl (cmf_abs F [--][1][*]cmf_abs F [--][1]).
  astepl (cmf_abs F ( [--][1][*][--][1])).
   2: apply ax_abs_resp_mult.
   2: apply cmf_proof.
  astepl (cmf_abs F [1]).
   2: apply csf_wd.
   2: astepl ( [--] (([1]:F) [*][--][1])).
    2: astepl ( [--] ( [--] ([1]:F) [*][1])).
    2: astepl ( [--][--] (([1]:F) [*][1])).
    2: astepl (([1]:F) [*][1]).
    2: algebra.
   astepl (cmf_abs F ([1][*][1])).
   astepl (cmf_abs F [1][*]cmf_abs F [1]).
    2: apply eq_symmetric_unfolded.
    2: apply ax_abs_resp_mult.
    2: apply cmf_proof.
   astepr (cmf_abs F [1][*]cmf_abs F [1]).
   apply eq_reflexive_unfolded.
  rational.
 apply MAbs_one.
Qed.
(* end hide *)

End basics.
Section CMetric_Field_Cauchy.
Variable F : CMetricField.

(**
%\begin{convention}% Let [F:CMetricField].
%\end{convention}%
*)

Definition MCauchy_prop (g : nat -> F) : CProp := forall e : IR,
  [0] [<] e -> {N : nat | forall m, N <= m -> MAbs (g m[-]g N) [<=] e}.

Record MCauchySeq : Type :=
 {MCS_seq   :> nat -> F;
  MCS_proof :  MCauchy_prop MCS_seq}.

Definition MseqLimit (seq : nat -> F) (lim : F) : CProp := forall e : IR,
  [0] [<] e -> {N : nat | forall m, N <= m -> MAbs (seq m[-]lim) [<=] e}.

Definition is_MCauchyCompl (lim : MCauchySeq -> F) : CProp :=
  forall (s : MCauchySeq), MseqLimit s (lim s).

End CMetric_Field_Cauchy.

Arguments MseqLimit [F].
