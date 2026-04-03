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

(** printing _X_ %\ensuremath{x}% *)
(** printing _C_ %\ensuremath\diamond% *)
(** printing [+X*] %\ensuremath{+x\times}% #+x&times;# *)
(** printing RX %\ensuremath{R[x]}% #R[x]# *)
(** printing FX %\ensuremath{F[x]}% #F[x]# *)

Require Import CoRN.algebra.CRing_Homomorphisms.
Require Import CoRN.tactics.Rational.

(* Backwards compatibility for Hint Rewrite locality attributes *)
Set Warnings "-unsupported-attributes".

(**
* Polynomials
The first section only proves the polynomials form a ring.
Section%~\ref{section:poly-equality}% gives some basic properties of
equality and induction of polynomials.
** Definition of polynomials; they form a ring
%\label{section:poly-ring}%
*)

Section CPoly_CRing.
(**
%\begin{convention}% Let [CR] be a ring.
%\end{convention}%
*)

Variable CR : CRing.

(**
The intuition behind the type [cpoly] is the following
- [(cpoly CR)] is $CR[X]$ #CR[X]#;
- [cpoly_zero] is the `empty' polynomial with no coefficients;
- [(cpoly_linear c p)] is [c[+]X[*]p]

*)

Inductive cpoly : Type :=
  | cpoly_zero   : cpoly
  | cpoly_linear : CR -> cpoly -> cpoly.

Definition cpoly_constant (c : CR) : cpoly := cpoly_linear c cpoly_zero.

Definition cpoly_one : cpoly := cpoly_constant [1].

(**
Some useful induction lemmas for doubly quantified propositions.
*)

Lemma Ccpoly_double_ind0 : forall P : cpoly -> cpoly -> CProp,
 (forall p, P p cpoly_zero) -> (forall p, P cpoly_zero p) ->
 (forall p q c d, P p q -> P (cpoly_linear c p) (cpoly_linear d q)) -> forall p q, P p q.
Proof.
 simple induction p; auto.
 simple induction q; auto.
Qed.

Lemma Ccpoly_double_sym_ind0 : forall P : cpoly -> cpoly -> CProp,
 Csymmetric P -> (forall p, P p cpoly_zero) ->
(forall p q c d, P p q -> P (cpoly_linear c p) (cpoly_linear d q)) -> forall p q, P p q.
Proof.
 intros.
 apply Ccpoly_double_ind0; auto.
Qed.

Lemma Ccpoly_double_ind0' : forall P : cpoly -> cpoly -> CProp,
 (forall p, P cpoly_zero p) -> (forall p c, P (cpoly_linear c p) cpoly_zero) ->
 (forall p q c d, P p q -> P (cpoly_linear c p) (cpoly_linear d q)) -> forall p q, P p q.
Proof.
 simple induction p; auto.
 simple induction q; auto.
Qed.

Lemma cpoly_double_ind0 : forall P : cpoly -> cpoly -> Prop,
 (forall p, P p cpoly_zero) -> (forall p, P cpoly_zero p) ->
 (forall p q c d, P p q -> P (cpoly_linear c p) (cpoly_linear d q)) -> forall p q, P p q.
Proof.
 simple induction p; auto.
 simple induction q; auto.
Qed.

Lemma cpoly_double_sym_ind0 : forall P : cpoly -> cpoly -> Prop,
 Tsymmetric P -> (forall p, P p cpoly_zero) ->
 (forall p q c d, P p q -> P (cpoly_linear c p) (cpoly_linear d q)) -> forall p q, P p q.
Proof.
 intros.
 apply cpoly_double_ind0; auto.
Qed.

Lemma cpoly_double_ind0' : forall P : cpoly -> cpoly -> Prop,
 (forall p, P cpoly_zero p) -> (forall p c, P (cpoly_linear c p) cpoly_zero) ->
 (forall p q c d, P p q -> P (cpoly_linear c p) (cpoly_linear d q)) -> forall p q, P p q.
Proof.
 simple induction p; auto.
 simple induction q; auto.
Qed.

(**
*** The polynomials form a setoid
*)
Fixpoint cpoly_eq_zero (p : cpoly) : Prop :=
  match p with
  | cpoly_zero        => True
  | cpoly_linear c p1 => c [=] [0] /\ cpoly_eq_zero p1
  end.

Fixpoint cpoly_eq (p q : cpoly) {struct p} : Prop :=
  match p with
  | cpoly_zero        => cpoly_eq_zero q
  | cpoly_linear c p1 =>
      match q with
      | cpoly_zero        => cpoly_eq_zero p
      | cpoly_linear d q1 => c [=] d /\ cpoly_eq p1 q1
      end
  end.

Lemma cpoly_eq_p_zero : forall p, cpoly_eq p cpoly_zero = cpoly_eq_zero p.
Proof.
 simple induction p; auto.
Qed.

Fixpoint cpoly_ap_zero (p : cpoly) : CProp :=
  match p with
  | cpoly_zero        => False
  | cpoly_linear c p1 => c [#] [0] or cpoly_ap_zero p1
  end.

Fixpoint cpoly_ap (p q : cpoly) {struct p} : CProp :=
  match p with
  | cpoly_zero        => cpoly_ap_zero q
  | cpoly_linear c p1 =>
      match q with
      | cpoly_zero        => cpoly_ap_zero p
      | cpoly_linear d q1 => c [#] d or cpoly_ap p1 q1
      end
  end.

Lemma cpoly_ap_p_zero : forall p, cpoly_ap_zero p = cpoly_ap p cpoly_zero.
Proof.
 simple induction p; auto.
Qed.

Lemma irreflexive_cpoly_ap : irreflexive cpoly_ap.
Proof.
 red in |- *.
 intro p; induction  p as [| s p Hrecp].
  intro H; elim H.
 intro H.
 elim H.
  apply ap_irreflexive_unfolded.
 assumption.
Qed.

Lemma symmetric_cpoly_ap : Csymmetric cpoly_ap.
Proof.
 red in |- *.
 intros x y.
 pattern x, y in |- *.
 apply Ccpoly_double_ind0'.
   simpl in |- *; simple induction p; auto.
  simpl in |- *; auto.
 simpl in |- *.
 intros p q c d H H0.
 elim H0; intro H1.
  left.
  apply ap_symmetric_unfolded.
  assumption.
 auto.
Qed.

Lemma cotransitive_cpoly_ap : cotransitive cpoly_ap.
Proof.
 red in |- *.
 intros x y.
 pattern x, y in |- *.
 apply Ccpoly_double_sym_ind0.
   red in |- *; intros p q H H0 r.
   generalize (symmetric_cpoly_ap _ _ H0); intro H1.
   elim (H H1 r); intro H2; [ right | left ]; apply symmetric_cpoly_ap; assumption.
  simpl in |- *; intros p H z.
  generalize H.
  pattern p, z in |- *.
  apply Ccpoly_double_ind0'.
    simpl in |- *; intros q H0; elim H0.
   simpl in |- *; auto.
  simpl in |- *; intros r q c d H0 H1.
  elim H1; intro H2.
   generalize (ap_cotransitive_unfolded _ _ _ H2 d); intro H3.
   elim H3; auto.
  rewrite cpoly_ap_p_zero in H2.
  elim (H0 H2); auto.
  right; right; rewrite cpoly_ap_p_zero; assumption.
 intros p q c d H H0 r.
 simpl in H0.
 elim H0; intro H1.
  induction  r as [| s r Hrecr].
   simpl in |- *.
   generalize (ap_cotransitive_unfolded _ _ _ H1 [0]); intro H2.
   elim H2; auto.
   intro H3.
   right; left; apply ap_symmetric_unfolded; assumption.
  simpl in |- *.
  generalize (ap_cotransitive_unfolded _ _ _ H1 s); intro H2.
  elim H2; auto.
 induction  r as [| s r Hrecr].
  simpl in |- *.
  cut (cpoly_ap_zero p or cpoly_ap_zero q).
   intro H2; elim H2; auto.
  generalize H1; pattern p, q in |- *; apply Ccpoly_double_ind0.
    simpl in |- *.
    intros r H2.
    left; rewrite cpoly_ap_p_zero; assumption.
   auto.
  simpl in |- *.
  intros p0 q0 c0 d0 H2 H3.
  elim H3; intro H4.
   elim (ap_cotransitive_unfolded _ _ _ H4 [0]); intro H5.
    auto.
   right; left; apply ap_symmetric_unfolded; assumption.
  elim (H2 H4); auto.
 simpl in |- *.
 elim (H H1 r); auto.
Qed.

Lemma tight_apart_cpoly_ap : tight_apart cpoly_eq cpoly_ap.
Proof.
 red in |- *.
 intros x y.
 pattern x, y in |- *.
 apply cpoly_double_ind0'.
   simple induction p.
    simpl in |- *.
    unfold iff in |- *.
    unfold Not in |- *.
    split.
     auto.
    intros H H0; inversion H0.
   simpl in |- *.
   intros s c H.
   cut (Not (s [#] [0]) <-> s [=] [0]).
    unfold Not in |- *.
    intro H0.
    elim H0; intros H1 H2.
    split.
     intro H3.
     split; auto.
     elim H; intros H4 H5.
     apply H4.
     intro H6.
     auto.
    intros H3 H4.
    elim H3; intros H5 H6.
    elim H4; intros H7.
     auto.
    elim H; intros H8 H9.
    unfold Not in H8.
    elim H9; assumption.
   apply (ap_tight CR).
  simple induction p.
   simpl in |- *.
   intro c.
   cut (Not (c [#] [0]) <-> c [=] [0]).
    unfold Not in |- *.
    intro H.
    elim H; intros H0 H1.
    split.
     auto.
    intros H2 H3.
    elim H3; intro H4.
     tauto.
    elim H4.
   apply (ap_tight CR).
  simpl in |- *.
  intros s c H d.
  generalize (H d).
  generalize (ap_tight CR d [0]).
  generalize (ap_tight CR s [0]).
  unfold Not in |- *.
  intros H0 H1 H2.
  elim H0; clear H0; intros H3 H4.
  elim H1; clear H1; intros H0 H5.
  elim H2; clear H2; intros H1 H6.
  tauto.
 simpl in |- *.
 unfold Not in |- *.
 intros p q c d H.
 elim H; intros H0 H1.
 split.
  intro H2.
  split.
   generalize (ap_tight CR c d).
   unfold Not in |- *; tauto.
  tauto.
 intros H2 H3.
 elim H3.
  elim H2.
  intros H4 H5 H6.
  generalize (ap_tight CR c d).
  unfold Not in |- *.
  tauto.
 elim H2.
 auto.
Qed.

Lemma cpoly_is_CSetoid : is_CSetoid _ cpoly_eq cpoly_ap.
Proof.
 apply Build_is_CSetoid.
    exact irreflexive_cpoly_ap.
   exact symmetric_cpoly_ap.
  exact cotransitive_cpoly_ap.
 exact tight_apart_cpoly_ap.
Qed.

Definition cpoly_csetoid := Build_CSetoid _ _ _ cpoly_is_CSetoid.
Canonical Structure cpoly_csetoid.
Canonical Structure cpoly_setoid := cs_crr cpoly_csetoid.

(**
Now that we know that the polynomials form a setoid, we can use the
notation with [ [#] ] and [ [=] ]. In order to use this notation,
we introduce [cpoly_zero_cs] and [cpoly_linear_cs], so that Coq
recognizes we are talking about a setoid.
We formulate the induction properties and
the most basic properties of equality and apartness
in terms of these generators.
*)

Let cpoly_zero_cs : cpoly_csetoid := cpoly_zero.

Let cpoly_linear_cs c (p : cpoly_csetoid) : cpoly_csetoid := cpoly_linear c p.

Lemma Ccpoly_ind_cs : forall P : cpoly_csetoid -> CProp,
 P cpoly_zero_cs -> (forall p c, P p -> P (cpoly_linear_cs c p)) -> forall p, P p.
Proof.
 simple induction p; auto.
Qed.

Lemma Ccpoly_double_ind0_cs : forall P : cpoly_csetoid -> cpoly_csetoid -> CProp,
 (forall p, P p cpoly_zero_cs) -> (forall p, P cpoly_zero_cs p) ->
 (forall p q c d, P p q -> P (cpoly_linear_cs c p) (cpoly_linear_cs d q)) -> forall p q, P p q.
Proof.
 simple induction p.
  auto.
 simple induction q.
  auto.
 simpl in X1.
 unfold cpoly_linear_cs in X1.
 auto.
Qed.

Lemma Ccpoly_double_sym_ind0_cs : forall P : cpoly_csetoid -> cpoly_csetoid -> CProp,
 Csymmetric P -> (forall p, P p cpoly_zero_cs) ->
 (forall p q c d, P p q -> P (cpoly_linear_cs c p) (cpoly_linear_cs d q)) -> forall p q, P p q.
Proof.
 intros.
 apply Ccpoly_double_ind0; auto.
Qed.

Lemma cpoly_ind_cs : forall P : cpoly_csetoid -> Prop,
 P cpoly_zero_cs -> (forall p c, P p -> P (cpoly_linear_cs c p)) -> forall p, P p.
Proof.
 simple induction p; auto.
Qed.

Lemma cpoly_double_ind0_cs : forall P : cpoly_csetoid -> cpoly_csetoid -> Prop,
 (forall p, P p cpoly_zero_cs) -> (forall p, P cpoly_zero_cs p) ->
 (forall p q c d, P p q -> P (cpoly_linear_cs c p) (cpoly_linear_cs d q)) -> forall p q, P p q.
Proof.
 simple induction p.
  auto.
 simple induction q.
  auto.
 simpl in H1.
 unfold cpoly_linear_cs in H1.
 auto.
Qed.

Lemma cpoly_double_sym_ind0_cs : forall P : cpoly_csetoid -> cpoly_csetoid -> Prop,
 Tsymmetric P -> (forall p, P p cpoly_zero_cs) ->
 (forall p q c d, P p q -> P (cpoly_linear_cs c p) (cpoly_linear_cs d q)) -> forall p q, P p q.
Proof.
 intros.
 apply cpoly_double_ind0; auto.
Qed.

Lemma cpoly_lin_eq_zero_ : forall p c,
 cpoly_linear_cs c p [=] cpoly_zero_cs -> c [=] [0] /\ p [=] cpoly_zero_cs.
Proof.
 unfold cpoly_linear_cs in |- *.
 unfold cpoly_zero_cs in |- *.
 simpl in |- *.
 intros p c H.
 elim H; intros.
 split; auto.
 rewrite cpoly_eq_p_zero.
 assumption.
Qed.

Lemma _cpoly_lin_eq_zero : forall p c,
 c [=] [0] /\ p [=] cpoly_zero_cs -> cpoly_linear_cs c p [=] cpoly_zero_cs.
Proof.
 unfold cpoly_linear_cs in |- *.
 unfold cpoly_zero_cs in |- *.
 simpl in |- *.
 intros p c H.
 elim H; intros.
 split; auto.
 rewrite <- cpoly_eq_p_zero.
 assumption.
Qed.

Lemma cpoly_zero_eq_lin_ : forall p c,
 cpoly_zero_cs [=] cpoly_linear_cs c p -> c [=] [0] /\ cpoly_zero_cs [=] p.
Proof.
 auto.
Qed.

Lemma _cpoly_zero_eq_lin : forall p c,
 c [=] [0] /\ cpoly_zero_cs [=] p -> cpoly_zero_cs [=] cpoly_linear_cs c p.
Proof.
 auto.
Qed.

Lemma cpoly_lin_eq_lin_ : forall p q c d,
 cpoly_linear_cs c p [=] cpoly_linear_cs d q -> c [=] d /\ p [=] q.
Proof.
 auto.
Qed.


Lemma _cpoly_lin_eq_lin : forall p q c d,
 c [=] d /\ p [=] q -> cpoly_linear_cs c p [=] cpoly_linear_cs d q.
Proof.
 auto.
Qed.


Lemma cpoly_lin_ap_zero_ : forall p c,
 cpoly_linear_cs c p [#] cpoly_zero_cs -> c [#] [0] or p [#] cpoly_zero_cs.
Proof.
 unfold cpoly_zero_cs in |- *.
 intros p c H.
 cut (cpoly_ap (cpoly_linear c p) cpoly_zero); auto.
 intro H0.
 simpl in H0.
 elim H0; auto.
 right.
 rewrite <- cpoly_ap_p_zero.
 assumption.
Qed.

Lemma _cpoly_lin_ap_zero : forall p c,
 c [#] [0] or p [#] cpoly_zero_cs -> cpoly_linear_cs c p [#] cpoly_zero_cs.
Proof.
 unfold cpoly_zero_cs in |- *.
 intros.
 simpl in |- *.
 elim X; try auto.
 intros.
 right.
 rewrite cpoly_ap_p_zero.
 assumption.
Qed.

Lemma cpoly_lin_ap_zero : forall p c,
 (cpoly_linear_cs c p [#] cpoly_zero_cs) = (c [#] [0] or p [#] cpoly_zero_cs).
Proof.
 intros.
 simpl in |- *.
 unfold cpoly_zero_cs in |- *.
 rewrite cpoly_ap_p_zero.
 reflexivity.
Qed.

Lemma cpoly_zero_ap_lin_ : forall p c,
 cpoly_zero_cs [#] cpoly_linear_cs c p -> c [#] [0] or cpoly_zero_cs [#] p.
Proof.
 intros.
 simpl in |- *.
 assumption.
Qed.

Lemma _cpoly_zero_ap_lin : forall p c,
 c [#] [0] or cpoly_zero_cs [#] p -> cpoly_zero_cs [#] cpoly_linear_cs c p.
Proof.
 intros.
 simpl in |- *.
 assumption.
Qed.

Lemma cpoly_zero_ap_lin : forall p c,
 (cpoly_zero_cs [#] cpoly_linear_cs c p) = (c [#] [0] or cpoly_zero_cs [#] p).
Proof. reflexivity. Qed.

Lemma cpoly_lin_ap_lin_ : forall p q c d,
 cpoly_linear_cs c p [#] cpoly_linear_cs d q -> c [#] d or p [#] q.
Proof.  auto. Qed.

Lemma _cpoly_lin_ap_lin : forall p q c d,
 c [#] d or p [#] q -> cpoly_linear_cs c p [#] cpoly_linear_cs d q.
Proof. auto. Qed.

Lemma cpoly_lin_ap_lin : forall p q c d,
 (cpoly_linear_cs c p [#] cpoly_linear_cs d q) = (c [#] d or p [#] q).
Proof. reflexivity. Qed.

Lemma cpoly_linear_strext : bin_fun_strext _ _ _ cpoly_linear_cs.
Proof.
 unfold bin_fun_strext in |- *.
 intros until 1.
 apply cpoly_lin_ap_lin_;assumption.
Qed.

Lemma cpoly_linear_wd : bin_fun_wd _ _ _ cpoly_linear_cs.
Proof.
 apply bin_fun_strext_imp_wd. now repeat intro.
Qed.

Definition cpoly_linear_fun := Build_CSetoid_bin_fun _ _ _ _ cpoly_linear_strext.

Lemma Ccpoly_double_comp_ind : forall P : cpoly_csetoid -> cpoly_csetoid -> CProp,
 (forall p1 p2 q1 q2, p1 [=] p2 -> q1 [=] q2 -> P p1 q1 -> P p2 q2) ->
 P cpoly_zero_cs cpoly_zero_cs ->
 (forall p q c d, P p q -> P (cpoly_linear_cs c p) (cpoly_linear_cs d q)) -> forall p q, P p q.
Proof.
 intros.
 apply Ccpoly_double_ind0_cs.
   intro p0; pattern p0 in |- *; apply Ccpoly_ind_cs;[assumption|].
   intros p1 c. intros.
   apply X with (cpoly_linear_cs c p1) (cpoly_linear_cs [0] cpoly_zero_cs).
     algebra.
    apply _cpoly_lin_eq_zero.
    split; algebra.
   apply X1; assumption.
  intro p0; pattern p0 in |- *; apply Ccpoly_ind_cs.
   assumption.
  intros.
  apply X with (cpoly_linear_cs [0] cpoly_zero_cs) (cpoly_linear_cs c p1).
    apply _cpoly_lin_eq_zero;split; algebra.
   algebra.
  apply X1;  assumption.
 now apply X1.
Qed.

Lemma Ccpoly_triple_comp_ind :
 forall P : cpoly_csetoid -> cpoly_csetoid -> cpoly_csetoid -> CProp,
 (forall p1 p2 q1 q2 r1 r2,
  p1 [=] p2 -> q1 [=] q2 -> r1 [=] r2 -> P p1 q1 r1 -> P p2 q2 r2) ->
 P cpoly_zero_cs cpoly_zero_cs cpoly_zero_cs ->
 (forall p q r c d e,
  P p q r -> P (cpoly_linear_cs c p) (cpoly_linear_cs d q) (cpoly_linear_cs e r)) ->
 forall p q r, P p q r.
Proof.
 do 6 intro.
 pattern p, q in |- *.
 apply Ccpoly_double_comp_ind.
   intros.
   apply X with p1 q1 r.
      assumption.
     assumption.
    algebra.
   apply X2.
  intro r; pattern r in |- *; apply Ccpoly_ind_cs.
   assumption.
  intros.
  apply X with (cpoly_linear_cs [0] cpoly_zero_cs) (cpoly_linear_cs [0] cpoly_zero_cs)
    (cpoly_linear_cs c p0).
     apply _cpoly_lin_eq_zero; split; algebra.
    apply _cpoly_lin_eq_zero; split; algebra.
   algebra.
  apply X1.
  assumption.
 do 6 intro.
 pattern r in |- *; apply Ccpoly_ind_cs.
  apply X with (cpoly_linear_cs c p0) (cpoly_linear_cs d q0) (cpoly_linear_cs [0] cpoly_zero_cs).
     algebra.
    algebra.
   apply _cpoly_lin_eq_zero; split; algebra.
  apply X1.
  apply X2.
 intros.
 apply X1.
 apply X2.
Qed.

Lemma cpoly_double_comp_ind : forall P : cpoly_csetoid -> cpoly_csetoid -> Prop,
 (forall p1 p2 q1 q2, p1 [=] p2 -> q1 [=] q2 -> P p1 q1 -> P p2 q2) ->
 P cpoly_zero_cs cpoly_zero_cs ->
 (forall p q c d, P p q -> P (cpoly_linear_cs c p) (cpoly_linear_cs d q)) -> forall p q, P p q.
Proof.
 intros.
 apply cpoly_double_ind0_cs.
   intro p0; pattern p0 in |- *; apply cpoly_ind_cs.
    assumption.
   intros.
   apply H with (cpoly_linear_cs c p1) (cpoly_linear_cs [0] cpoly_zero_cs).
     algebra.
    apply _cpoly_lin_eq_zero.
    split; algebra.
   apply H1.
   assumption.
  intro p0; pattern p0 in |- *; apply cpoly_ind_cs.
   assumption.
  intros.
  apply H with (cpoly_linear_cs [0] cpoly_zero_cs) (cpoly_linear_cs c p1).
    apply _cpoly_lin_eq_zero.
    split; algebra.
   algebra.
  now apply H1.
 now apply H1.
Qed.

Lemma cpoly_triple_comp_ind :
 forall P : cpoly_csetoid -> cpoly_csetoid -> cpoly_csetoid -> Prop,
 (forall p1 p2 q1 q2 r1 r2,
  p1 [=] p2 -> q1 [=] q2 -> r1 [=] r2 -> P p1 q1 r1 -> P p2 q2 r2) ->
 P cpoly_zero_cs cpoly_zero_cs cpoly_zero_cs ->
 (forall p q r c d e,
  P p q r -> P (cpoly_linear_cs c p) (cpoly_linear_cs d q) (cpoly_linear_cs e r)) ->
 forall p q r, P p q r.
Proof.
 do 6 intro.
 pattern p, q in |- *.
 apply cpoly_double_comp_ind.
   intros.
   apply H with p1 q1 r.
      assumption.
     assumption.
    algebra.
   apply H4.
  intro r; pattern r in |- *; apply cpoly_ind_cs.
   assumption.
  intros.
  apply H with (cpoly_linear_cs [0] cpoly_zero_cs) (cpoly_linear_cs [0] cpoly_zero_cs)
    (cpoly_linear_cs c p0).
     apply _cpoly_lin_eq_zero; split; algebra.
    apply _cpoly_lin_eq_zero; split; algebra.
   algebra.
  apply H1.
  assumption.
 do 6 intro.
 pattern r in |- *; apply cpoly_ind_cs.
  apply H with (cpoly_linear_cs c p0) (cpoly_linear_cs d q0) (cpoly_linear_cs [0] cpoly_zero_cs).
     algebra.
    algebra.
   apply _cpoly_lin_eq_zero; split; algebra.
  apply H1.
  apply H2.
 intros.
 apply H1.
 apply H2.
Qed.

(**
*** The polynomials form a semi-group and a monoid
*)

Fixpoint cpoly_plus (p q : cpoly) {struct p} : cpoly :=
  match p with
  | cpoly_zero        => q
  | cpoly_linear c p1 =>
      match q with
      | cpoly_zero        => p
      | cpoly_linear d q1 => cpoly_linear (c[+]d) (cpoly_plus p1 q1)
      end
  end.

Definition cpoly_plus_cs (p q : cpoly_csetoid) : cpoly_csetoid := cpoly_plus p q.

Lemma cpoly_zero_plus : forall p, cpoly_plus_cs cpoly_zero_cs p = p.
Proof.
 auto.
Qed.

Lemma cpoly_plus_zero : forall p, cpoly_plus_cs p cpoly_zero_cs = p.
Proof.
 simple induction p.
  auto.
 auto.
Qed.

Lemma cpoly_lin_plus_lin : forall p q c d,
 cpoly_plus_cs (cpoly_linear_cs c p) (cpoly_linear_cs d q) =
  cpoly_linear_cs (c[+]d) (cpoly_plus_cs p q).
Proof.
 auto.
Qed.

Lemma cpoly_plus_commutative : forall p q, cpoly_plus_cs p q [=] cpoly_plus_cs q p.
Proof.
 intros.
 pattern p, q in |- *.
 apply cpoly_double_sym_ind0_cs.
   unfold Tsymmetric in |- *.
   intros.
   algebra.
  intro p0.
  rewrite cpoly_zero_plus.
  rewrite cpoly_plus_zero.
  algebra.
 intros.
 repeat rewrite cpoly_lin_plus_lin.
 apply _cpoly_lin_eq_lin.
 split.
  algebra.
 assumption.
Qed.

Lemma cpoly_plus_q_ap_q : forall p q, cpoly_plus_cs p q [#] q -> p [#] cpoly_zero_cs.
Proof.
 intro p; pattern p in |- *; apply Ccpoly_ind_cs.
  intro.
  rewrite cpoly_zero_plus.
  intro H.
  exfalso.
  apply (ap_irreflexive _ _ H).
 do 4 intro.
 pattern q in |- *; apply Ccpoly_ind_cs.
  rewrite cpoly_plus_zero.
  auto.
 do 3 intro.
 rewrite cpoly_lin_plus_lin.
 intros.
 cut (c[+]c0 [#] c0 or cpoly_plus_cs p0 p1 [#] p1).
  intros.
  2: apply cpoly_lin_ap_lin_.
  2: assumption.
 cut (c [#] [0] or p0 [#] cpoly_zero_cs).
  intro. apply _cpoly_lin_ap_zero. assumption.
  elim X1; intro.
  left.
  apply cg_ap_cancel_rht with c0.
  astepr c0. auto.
  right.
 generalize (X _ b); intro.
 assumption.
Qed.

Lemma cpoly_p_plus_ap_p : forall p q, cpoly_plus_cs p q [#] p -> q [#] cpoly_zero.
Proof.
 intros.
 apply cpoly_plus_q_ap_q with p.
 apply ap_wdl_unfolded with (cpoly_plus_cs p q).
  assumption.
 apply cpoly_plus_commutative.
Qed.


Lemma cpoly_ap_zero_plus : forall p q,
 cpoly_plus_cs p q [#] cpoly_zero_cs -> p [#] cpoly_zero_cs or q [#] cpoly_zero_cs.
Proof.
 intros p q; pattern p, q in |- *; apply Ccpoly_double_sym_ind0_cs.
   unfold Csymmetric in |- *.
   intros x y H H0.
   elim H.
     auto. auto.
    astepl (cpoly_plus_cs y x). auto.
    apply cpoly_plus_commutative.
  intros p0 H.
  left.
  rewrite cpoly_plus_zero in H.
  assumption.
 intros p0 q0 c d.
 rewrite cpoly_lin_plus_lin.
 intros.
 cut (c[+]d [#] [0] or cpoly_plus_cs p0 q0 [#] cpoly_zero_cs).
  2: apply cpoly_lin_ap_zero_.
  2: assumption.
 clear X0.
 intros H0.
 elim H0; intro H1.
  cut (c[+]d [#] [0][+][0]).
   intro H2.
   elim (cs_bin_op_strext _ _ _ _ _ _ H2); intro H3.
    left.
    simpl in |- *.
    left.
    assumption.
   right.
   cut (d [#] [0] or q0 [#] cpoly_zero_cs).
    intro H4.
    apply _cpoly_lin_ap_zero.
    auto.
   left.
   assumption.
  astepr ([0]:CR). auto.
  elim (X H1); intro.
  left.
  cut (c [#] [0] or p0 [#] cpoly_zero_cs).
   intro; apply _cpoly_lin_ap_zero.
   auto.
  right.
  assumption.
 right.
 cut (d [#] [0] or q0 [#] cpoly_zero_cs).
  intro.
  apply _cpoly_lin_ap_zero.
  auto.
 right.
 assumption.
Qed.

Lemma cpoly_plus_op_strext : bin_op_strext cpoly_csetoid cpoly_plus_cs.
Proof.
 unfold bin_op_strext in |- *.
 unfold bin_fun_strext in |- *.
 intros x1 x2.
 pattern x1, x2 in |- *.
 apply Ccpoly_double_sym_ind0_cs.
   unfold Csymmetric in |- *.
   intros.
   generalize (ap_symmetric_unfolded _ _ _ X0); intro H1.
   generalize (X _ _ H1); intro H2.
   elim H2; intro H3; generalize (ap_symmetric_unfolded _ _ _ H3); auto.
  intro p; pattern p in |- *; apply Ccpoly_ind_cs.
   intro; intro H.
   simpl in |- *; auto.
  intros s c H y1 y2.
  pattern y1, y2 in |- *.
  apply Ccpoly_double_ind0_cs.
    intros p0 H0.
    apply cpoly_ap_zero_plus.
    apply H0.
   intro p0.
   intro H0.
   elim (ap_cotransitive _ _ _ H0 cpoly_zero_cs); auto.
  do 4 intro.
  intros.
  cut (c[+]c0 [#] d or cpoly_plus_cs s p0 [#] q).
   2: apply cpoly_lin_ap_lin_; assumption.
  clear X0; intro H1.
  elim H1; intro H2.
   cut (c[+]c0 [#] [0][+]d).
    intro H3.
    elim (cs_bin_op_strext _ _ _ _ _ _ H3).
     intro H4.
     left.
     apply _cpoly_lin_ap_zero.
     auto.
    intro.
    right.
    apply _cpoly_lin_ap_lin.
    auto.
   astepr d. auto.
   elim (H _ _ H2); auto.
   intro.
   left.
   apply _cpoly_lin_ap_zero.
   auto.
  right.
  apply _cpoly_lin_ap_lin.
  auto.
 do 7 intro.
 pattern y1, y2 in |- *.
 apply Ccpoly_double_ind0_cs.
   intro p0; pattern p0 in |- *; apply Ccpoly_ind_cs.
    auto.
   intros.
   cut (c[+]c0 [#] d or cpoly_plus_cs p p1 [#] q).
    intro H2.
    2: apply cpoly_lin_ap_lin_.
    2: auto.
   elim H2; intro H3.
    cut (c[+]c0 [#] d[+][0]).
     intro H4.
     elim (cs_bin_op_strext _ _ _ _ _ _ H4).
      intro.
      left.
      apply _cpoly_lin_ap_lin.
      auto.
     intro.
     right.
     apply _cpoly_lin_ap_zero.
     auto.
    astepr d. auto.
    elim X with p1 cpoly_zero_cs.
     intro.
     left.
     apply _cpoly_lin_ap_lin.
     auto.
    right.
    apply _cpoly_lin_ap_zero.
    auto.
   rewrite cpoly_plus_zero.
   assumption.
  intro p0; pattern p0 in |- *; apply Ccpoly_ind_cs.
   auto.
  intros.
  cut (c [#] d[+]c0 or p [#] cpoly_plus_cs q p1).
   2: apply cpoly_lin_ap_lin_.
   2: assumption.
  clear X1; intro H1.
  elim H1; intro H2.
   cut (c[+][0] [#] d[+]c0).
    intro H3.
    elim (cs_bin_op_strext _ _ _ _ _ _ H3).
     intro.
     left.
     unfold cpoly_linear_cs in |- *; simpl in |- *; auto.
    intro.
    right.
    left.
    apply ap_symmetric_unfolded.
    assumption.
   astepl c. auto.
   elim X with cpoly_zero_cs p1.
    intro.
    left.
    unfold cpoly_linear_cs in |- *; simpl in |- *; auto.
   intro.
   right.
   right; auto.
  rewrite cpoly_plus_zero.
  assumption.
 intros.
 elim X1; intro H2.
  elim (cs_bin_op_strext _ _ _ _ _ _ H2); auto.
   intro.
   left.
   left; auto.
  intro. right.
  left; auto.
 simpl in H2.
 elim (X _ _ H2).
  intro.
  left; right; auto.
 right; right; auto.
Qed.

Lemma cpoly_plus_op_wd : bin_op_wd cpoly_csetoid cpoly_plus_cs.
Proof.
 unfold bin_op_wd in |- *.
 apply bin_fun_strext_imp_wd.
 exact cpoly_plus_op_strext.
Qed.

Definition cpoly_plus_op := Build_CSetoid_bin_op _ _ cpoly_plus_op_strext.

Lemma cpoly_plus_associative : associative cpoly_plus_op.
Proof.
 unfold associative in |- *.
 intros p q r.
 change (cpoly_plus_cs p (cpoly_plus_cs q r) [=] cpoly_plus_cs (cpoly_plus_cs p q) r) in |- *.
 pattern p, q, r in |- *; apply cpoly_triple_comp_ind.
   intros.
   apply eq_transitive_unfolded with (cpoly_plus_cs p1 (cpoly_plus_cs q1 r1)).
    apply eq_symmetric_unfolded.
    apply cpoly_plus_op_wd.
     assumption.
    apply cpoly_plus_op_wd.
     assumption.
    assumption.
   astepl (cpoly_plus_cs (cpoly_plus_cs p1 q1) r1).
   apply cpoly_plus_op_wd.
    apply cpoly_plus_op_wd.
     assumption.
    assumption.
   assumption.
  simpl in |- *.
  auto.
 intros.
 repeat rewrite cpoly_lin_plus_lin.
 apply _cpoly_lin_eq_lin.
 split.
  algebra.
 assumption.
Qed.

Definition cpoly_csemi_grp := Build_CSemiGroup _ _ cpoly_plus_associative.
Canonical Structure cpoly_csemi_grp.

Lemma cpoly_cm_proof : is_CMonoid cpoly_csemi_grp cpoly_zero.
Proof.
 apply Build_is_CMonoid.
  intro; rewrite -> cpoly_plus_zero;algebra.
 intro x.
 eapply eq_transitive_unfolded.
  apply cpoly_plus_commutative.
 rewrite cpoly_plus_zero;algebra.
Qed.

Definition cpoly_cmonoid := Build_CMonoid _ _ cpoly_cm_proof.
Canonical Structure cpoly_cmonoid.

(**
*** The polynomials form a group
*)

Fixpoint cpoly_inv (p : cpoly) : cpoly :=
  match p with
  | cpoly_zero        => cpoly_zero
  | cpoly_linear c p1 => cpoly_linear [--]c (cpoly_inv p1)
  end.

Definition cpoly_inv_cs (p : cpoly_csetoid) : cpoly_csetoid := cpoly_inv p.

Lemma cpoly_inv_zero : cpoly_inv_cs cpoly_zero_cs = cpoly_zero_cs.
Proof.
 auto.
Qed.

Lemma cpoly_inv_lin : forall p c,
 cpoly_inv_cs (cpoly_linear_cs c p) = cpoly_linear_cs [--]c (cpoly_inv_cs p).
Proof. simple induction p; auto. Qed.

Lemma cpoly_inv_op_strext : un_op_strext cpoly_csetoid cpoly_inv_cs.
Proof.
 unfold un_op_strext in |- *.
 unfold fun_strext in |- *.
 intros x y.
 pattern x, y in |- *.
 apply Ccpoly_double_sym_ind0_cs.
   unfold Csymmetric in |- *.
   intros.
   apply ap_symmetric_unfolded.
   apply X.
   apply ap_symmetric_unfolded.
   assumption.
  intro p; pattern p in |- *; apply Ccpoly_ind_cs.
   auto.
  intros.
  cut ( [--]c [#] [0] or cpoly_inv_cs p0 [#] cpoly_zero_cs).
   2: apply cpoly_lin_ap_zero_.
   2: auto.
  clear X0; intro H0.
  apply _cpoly_lin_ap_zero.
  auto.
  elim H0.
   left.
   astepl ( [--][--]c). algebra.
   right.
  apply X.
  assumption.
 intros.
 cut ( [--]c [#] [--]d or cpoly_inv_cs p [#] cpoly_inv_cs q).
  2: apply cpoly_lin_ap_lin_.
  2: auto.
 clear X0; intro H0.
 auto.
 elim H0; intro.
  left.
  astepl ( [--][--]c).
  astepr ( [--][--]d).
  apply inv_resp_ap.
  assumption.
 right.
 apply X.
 assumption.
Qed.

Lemma cpoly_inv_op_wd : un_op_wd cpoly_csetoid cpoly_inv_cs.
Proof.
 apply fun_strext_imp_wd.  exact cpoly_inv_op_strext.
Qed.

Definition cpoly_inv_op := Build_CSetoid_un_op _ _ cpoly_inv_op_strext.

Lemma cpoly_cg_proof : is_CGroup cpoly_cmonoid cpoly_inv_op.
Proof.
 intro x.
 unfold is_inverse in |- *.
 assert (x[+]cpoly_inv_cs x [=] [0]).
  pattern x in |- *; apply cpoly_ind_cs.
   rewrite cpoly_inv_zero.
   rewrite -> cpoly_plus_zero.
   simpl; auto.
  intros.
  rewrite cpoly_inv_lin.
  rewrite ->  cpoly_lin_plus_lin.
  apply _cpoly_lin_eq_zero.
  split;[algebra|assumption].
 split; auto.
 eapply eq_transitive_unfolded.
  apply cpoly_plus_commutative.
 auto.
Qed.

Definition cpoly_cgroup := Build_CGroup _ _ cpoly_cg_proof.
Canonical Structure cpoly_cgroup.

Lemma cpoly_cag_proof : is_CAbGroup cpoly_cgroup.
Proof. repeat intro. apply: cpoly_plus_commutative. Qed.

Definition cpoly_cabgroup := Build_CAbGroup _ cpoly_cag_proof.
Canonical Structure cpoly_cabgroup.

(**
*** The polynomials form a ring
*)

Fixpoint cpoly_mult_cr (q : cpoly) (c : CR) {struct q} : cpoly :=
  match q with
  | cpoly_zero        => cpoly_zero
  | cpoly_linear d q1 => cpoly_linear (c[*]d) (cpoly_mult_cr q1 c)
  end.

Fixpoint cpoly_mult (p q : cpoly) {struct p} : cpoly :=
  match p with
  | cpoly_zero        => cpoly_zero
  | cpoly_linear c p1 =>
      cpoly_plus (cpoly_mult_cr q c) (cpoly_linear [0] (cpoly_mult p1 q))
  end.

Definition cpoly_mult_cr_cs (p : cpoly_csetoid) c : cpoly_csetoid :=
  cpoly_mult_cr p c.

Lemma cpoly_zero_mult_cr : forall c,
 cpoly_mult_cr_cs cpoly_zero_cs c = cpoly_zero_cs.
Proof. auto. Qed.

Lemma cpoly_lin_mult_cr : forall c d q,
 cpoly_mult_cr_cs (cpoly_linear_cs d q) c =
  cpoly_linear_cs (c[*]d) (cpoly_mult_cr_cs q c).
Proof. auto. Qed.

Lemma cpoly_mult_cr_zero : forall p, cpoly_mult_cr_cs p [0] [=] cpoly_zero_cs.
Proof.
 intro; pattern p in |- *; apply cpoly_ind_cs.
  rewrite cpoly_zero_mult_cr.
  algebra.
 intros.
 rewrite cpoly_lin_mult_cr.
 apply _cpoly_lin_eq_zero.
 split.
  algebra.
 assumption.
Qed.

Lemma cpoly_mult_cr_strext : bin_fun_strext _ _ _ cpoly_mult_cr_cs.
Proof.
 unfold bin_fun_strext in |- *.
 do 4 intro.
 pattern x1, x2 in |- *.
 apply Ccpoly_double_ind0_cs.
   intro.
   rewrite cpoly_zero_mult_cr.
   intro H.
   left.
   generalize H.
   pattern p in |- *.
   apply Ccpoly_ind_cs.
    rewrite cpoly_zero_mult_cr.
    auto.
   do 2 intro.
   rewrite cpoly_lin_mult_cr.
   intros.
   cut (y1[*]c [#] [0] or cpoly_mult_cr_cs p0 y1 [#] cpoly_zero_cs).
    2: apply cpoly_lin_ap_zero_.
    2: auto.
   clear H0; intro H1.
   cut (c [#] [0] or p0 [#] cpoly_zero_cs).
    intro; apply _cpoly_lin_ap_zero.
    auto.
   elim H1; intro H2.
    generalize (cring_mult_ap_zero_op _ _ _ H2); intro.
    auto.
   right.
   auto.
  rewrite cpoly_zero_mult_cr.
  intros.
  left.
  generalize X.
  pattern p in |- *; apply Ccpoly_ind_cs.
   rewrite cpoly_zero_mult_cr.
   auto.
  do 2 intro.
  rewrite cpoly_lin_mult_cr.
  intros.
  cut (y2[*]c [#] [0] or cpoly_zero_cs [#] cpoly_mult_cr_cs p0 y2).
   2: apply cpoly_zero_ap_lin_.
   2: auto.
  clear X1; intro H1.
  cut (c [#] [0] or cpoly_zero_cs [#] p0).
   intro.
   apply _cpoly_zero_ap_lin. auto.
   elim H1; intro H2.
   generalize (cring_mult_ap_zero_op _ _ _ H2); auto.
  right.
  auto.
 do 4 intro.
 repeat rewrite cpoly_lin_mult_cr.
 intros.
 cut (y1[*]c [#] y2[*]d or cpoly_mult_cr_cs p y1 [#] cpoly_mult_cr_cs q y2).
  2: apply cpoly_lin_ap_lin_.
  2: auto.
 clear X0; intro H0.
 cut ((c [#] d or p [#] q) or y1 [#] y2).
  intro.
  elim X0; try auto.
 elim H0; intro H1.
  generalize (cs_bin_op_strext _ _ _ _ _ _ H1); tauto.
 elim X; auto.
Qed.

Lemma cpoly_mult_cr_wd : bin_fun_wd _ _ _ cpoly_mult_cr_cs.
Proof.
 apply bin_fun_strext_imp_wd.
 exact cpoly_mult_cr_strext.
Qed.

Definition cpoly_mult_cs (p q : cpoly_csetoid) : cpoly_csetoid := cpoly_mult p q.

Lemma cpoly_zero_mult : forall q, cpoly_mult_cs cpoly_zero_cs q = cpoly_zero_cs.
Proof. auto. Qed.

Lemma cpoly_lin_mult : forall c p q,
 cpoly_mult_cs (cpoly_linear_cs c p) q =
  cpoly_plus_cs (cpoly_mult_cr_cs q c) (cpoly_linear_cs [0] (cpoly_mult_cs p q)).
Proof. auto. Qed.

Lemma cpoly_mult_op_strext : bin_op_strext cpoly_csetoid cpoly_mult_cs.
Proof.
 do 4 intro.
 pattern x1, x2 in |- *.
 apply Ccpoly_double_ind0_cs.
   rewrite cpoly_zero_mult.
   intro; pattern p in |- *; apply Ccpoly_ind_cs.
    rewrite cpoly_zero_mult.
    auto.
   do 2 intro.
   rewrite cpoly_lin_mult.
   intros.
   cut ((c [#] [0] or p0 [#] cpoly_zero_cs) or y1 [#] y2).
    intro H1. elim H1.  intro; left; apply _cpoly_lin_ap_zero; assumption.
    auto.
   cut (cpoly_plus_cs (cpoly_mult_cr_cs y1 c) (cpoly_linear_cs [0] (cpoly_mult_cs p0 y1)) [#]
     cpoly_plus_cs (cpoly_mult_cr_cs y2 [0]) (cpoly_linear_cs [0] (cpoly_mult_cs cpoly_zero_cs y2))).
    intro H1.
    elim (cpoly_plus_op_strext _ _ _ _ H1); intro H2.
     elim (cpoly_mult_cr_strext _ _ _ _ H2); auto.
    elim H2; intro H3.
     elim (ap_irreflexive _ _ H3).
    rewrite cpoly_zero_mult in H3.
    elim X; auto.
   rewrite cpoly_zero_mult.
   apply ap_wdr_unfolded with cpoly_zero_cs.
    assumption.
   astepl (cpoly_plus_cs cpoly_zero_cs cpoly_zero_cs).
   apply cpoly_plus_op_wd.
    apply eq_symmetric_unfolded.
    apply cpoly_mult_cr_zero.
   apply _cpoly_zero_eq_lin.
   split; algebra.
  intro; pattern p in |- *; apply Ccpoly_ind_cs.
   auto.
  intros.
  cut ((c [#] [0] or cpoly_zero_cs [#] p0) or y1 [#] y2).
   intro.
   elim X1; try auto.
  cut (cpoly_plus_cs (cpoly_mult_cr_cs y1 [0])
    (cpoly_linear_cs [0] (cpoly_mult_cs cpoly_zero_cs y1)) [#] cpoly_plus_cs (cpoly_mult_cr_cs y2 c)
      (cpoly_linear_cs [0] (cpoly_mult_cs p0 y2))).
   intro H1.
   elim (cpoly_plus_op_strext _ _ _ _ H1); intro H2.
    elim (cpoly_mult_cr_strext _ _ _ _ H2); auto.
    intro.
    left. left.
    apply ap_symmetric_unfolded.
    assumption.
   cut (([0]:CR) [#] [0] or cpoly_mult_cs cpoly_zero_cs y1 [#] cpoly_mult_cs p0 y2).
    2: apply cpoly_lin_ap_lin_; auto.
   clear H2; intro H2.
   elim H2; intro H3.
    elim (ap_irreflexive _ _ H3).
   rewrite cpoly_zero_mult in H3.
   elim X; auto.
  rewrite cpoly_zero_mult.
  apply ap_wdl_unfolded with cpoly_zero_cs.
   assumption.
  astepl (cpoly_plus_cs cpoly_zero_cs cpoly_zero_cs).
  apply cpoly_plus_op_wd.
   apply eq_symmetric_unfolded.
   apply cpoly_mult_cr_zero.
  apply _cpoly_zero_eq_lin.
  split; algebra.
 intros.
 cut ((c [#] d or p [#] q) or y1 [#] y2).
  intro.
  auto.
 elim (cpoly_plus_op_strext _ _ _ _ X0); intro H1.
  elim (cpoly_mult_cr_strext _ _ _ _ H1); auto.
 elim H1; intro H2.
  elim (ap_irreflexive _ _ H2).
 elim X; auto.
Qed.

Lemma cpoly_mult_op_wd : bin_op_wd cpoly_csetoid cpoly_mult.
Proof.
 apply bin_fun_strext_imp_wd. exact cpoly_mult_op_strext.
Qed.

Definition cpoly_mult_op := Build_CSetoid_bin_op _ _ cpoly_mult_op_strext.

Lemma cpoly_mult_cr_dist : forall p q c,
 cpoly_mult_cr_cs (cpoly_plus_cs p q) c [=]
  cpoly_plus_cs (cpoly_mult_cr_cs p c) (cpoly_mult_cr_cs q c).
Proof.
 intros.
 pattern p, q in |- *.
 apply cpoly_double_comp_ind.
   intros.
   apply eq_transitive_unfolded with (cpoly_mult_cr_cs (cpoly_plus_cs p1 q1) c).
    apply eq_symmetric_unfolded.
    apply cpoly_mult_cr_wd.
     apply cpoly_plus_op_wd.
      assumption.
     assumption.
    algebra.
   astepl (cpoly_plus_cs (cpoly_mult_cr_cs p1 c) (cpoly_mult_cr_cs q1 c)).
   apply cpoly_plus_op_wd.
    apply cpoly_mult_cr_wd; algebra.
   apply cpoly_mult_cr_wd; algebra.
  repeat rewrite cpoly_zero_plus.
  algebra.
 intros.
 repeat rewrite cpoly_lin_mult_cr.
 repeat rewrite cpoly_lin_plus_lin.
 apply: _cpoly_lin_eq_lin.
 split; algebra.
Qed.

Lemma cpoly_cr_dist : distributive cpoly_mult_op cpoly_plus_op.
Proof.
 unfold distributive in |- *.
 intros p q r.
 change (cpoly_mult_cs p (cpoly_plus_cs q r) [=]
   cpoly_plus_cs (cpoly_mult_cs p q) (cpoly_mult_cs p r)) in |- *.
 pattern p in |- *. apply cpoly_ind_cs.
 repeat rewrite cpoly_zero_mult.
  rewrite cpoly_zero_plus.
  algebra.
 intros.
 repeat rewrite cpoly_lin_mult.
 apply eq_transitive_unfolded with (cpoly_plus_cs
   (cpoly_plus_cs (cpoly_mult_cr_cs q c) (cpoly_mult_cr_cs r c))
     (cpoly_plus_cs (cpoly_linear_cs [0] (cpoly_mult_cs p0 q))
       (cpoly_linear_cs [0] (cpoly_mult_cs p0 r)))).
  apply cpoly_plus_op_wd.
   apply cpoly_mult_cr_dist.
  rewrite cpoly_lin_plus_lin.
  apply _cpoly_lin_eq_lin.
  split.
   algebra.
  assumption.
 clear H.
 apply eq_transitive_unfolded with (cpoly_plus_cs (cpoly_mult_cr_cs q c)
   (cpoly_plus_cs (cpoly_mult_cr_cs r c) (cpoly_plus_cs (cpoly_linear_cs [0] (cpoly_mult_cs p0 q))
     (cpoly_linear_cs [0] (cpoly_mult_cs p0 r))))).
  apply eq_symmetric_unfolded.
  apply cpoly_plus_associative.
 apply eq_transitive_unfolded with (cpoly_plus_cs (cpoly_mult_cr_cs q c)
   (cpoly_plus_cs (cpoly_linear_cs [0] (cpoly_mult_cs p0 q)) (cpoly_plus_cs (cpoly_mult_cr_cs r c)
     (cpoly_linear_cs [0] (cpoly_mult_cs p0 r))))).
  apply cpoly_plus_op_wd.
   algebra.
  apply eq_transitive_unfolded with (cpoly_plus_cs (cpoly_plus_cs (cpoly_mult_cr_cs r c)
    (cpoly_linear_cs [0] (cpoly_mult_cs p0 q))) (cpoly_linear_cs [0] (cpoly_mult_cs p0 r))).
   apply cpoly_plus_associative.
  apply eq_transitive_unfolded with (cpoly_plus_cs
    (cpoly_plus_cs (cpoly_linear_cs [0] (cpoly_mult_cs p0 q))
      (cpoly_mult_cr_cs r c)) (cpoly_linear_cs [0] (cpoly_mult_cs p0 r))).
   apply cpoly_plus_op_wd.
    apply cpoly_plus_commutative.
   algebra.
  apply eq_symmetric_unfolded.
  apply cpoly_plus_associative.
 apply cpoly_plus_associative.
Qed.

Lemma cpoly_mult_cr_assoc_mult_cr : forall p c d,
 cpoly_mult_cr_cs (cpoly_mult_cr_cs p c) d [=] cpoly_mult_cr_cs p (d[*]c).
Proof.
 intros.
 pattern p in |- *; apply cpoly_ind_cs.
  repeat rewrite cpoly_zero_mult_cr.
  algebra.
 intros.
 repeat rewrite cpoly_lin_mult_cr.
 apply _cpoly_lin_eq_lin.
 split.
  algebra.
 assumption.
Qed.

Lemma cpoly_mult_cr_assoc_mult : forall p q c,
 cpoly_mult_cr_cs (cpoly_mult_cs p q) c [=] cpoly_mult_cs (cpoly_mult_cr_cs p c) q.
Proof.
 intros.
 pattern p in |- *; apply cpoly_ind_cs.
  rewrite cpoly_zero_mult.
  rewrite -> cpoly_zero_mult_cr; reflexivity.
 intros.
 rewrite cpoly_lin_mult.
 repeat rewrite cpoly_lin_mult_cr.
 rewrite cpoly_lin_mult.
 apply eq_transitive_unfolded with (cpoly_plus_cs (cpoly_mult_cr_cs (cpoly_mult_cr_cs q c0) c)
   (cpoly_mult_cr_cs (cpoly_linear_cs [0] (cpoly_mult_cs p0 q)) c)).
  apply cpoly_mult_cr_dist.
 apply cpoly_plus_op_wd.
  apply cpoly_mult_cr_assoc_mult_cr.
 rewrite cpoly_lin_mult_cr.
 apply _cpoly_lin_eq_lin.
 split;algebra.
Qed.

Lemma cpoly_mult_zero : forall p, cpoly_mult_cs p cpoly_zero_cs [=] cpoly_zero_cs.
Proof.
 intros.
 pattern p in |- *; apply cpoly_ind_cs.
  algebra.
 intros.
 rewrite cpoly_lin_mult.
 rewrite cpoly_zero_mult_cr.
 rewrite cpoly_zero_plus.
 apply _cpoly_lin_eq_zero.
 split;algebra.
Qed.

Lemma cpoly_mult_lin : forall c p q,
 cpoly_mult_cs p (cpoly_linear_cs c q) [=]
  cpoly_plus_cs (cpoly_mult_cr_cs p c) (cpoly_linear_cs [0] (cpoly_mult_cs p q)).
Proof.
 intros.
 pattern p in |- *; apply cpoly_ind_cs.
  repeat rewrite cpoly_zero_mult.
  rewrite cpoly_zero_mult_cr.
  rewrite cpoly_zero_plus.
  apply _cpoly_zero_eq_lin.
  algebra.
 intros.
 repeat rewrite cpoly_lin_mult.
 repeat rewrite cpoly_lin_mult_cr.
 repeat rewrite cpoly_lin_plus_lin.
 apply _cpoly_lin_eq_lin. split.
 algebra.
 apply eq_transitive_unfolded with (cpoly_plus_cs
   (cpoly_plus_cs (cpoly_mult_cr_cs p0 c) (cpoly_mult_cr_cs q c0))
     (cpoly_linear_cs [0] (cpoly_mult_cs p0 q))).
  2: apply eq_symmetric_unfolded.
  2: apply cpoly_plus_associative.
 apply eq_transitive_unfolded with (cpoly_plus_cs
   (cpoly_plus_cs (cpoly_mult_cr_cs q c0) (cpoly_mult_cr_cs p0 c))
     (cpoly_linear_cs [0] (cpoly_mult_cs p0 q))).
  2: apply cpoly_plus_op_wd.
   3: algebra.
  2: apply cpoly_plus_commutative.
 apply eq_transitive_unfolded with (cpoly_plus_cs (cpoly_mult_cr_cs q c0)
   (cpoly_plus_cs (cpoly_mult_cr_cs p0 c) (cpoly_linear_cs [0] (cpoly_mult_cs p0 q)))).
  2: apply cpoly_plus_associative.
 apply cpoly_plus_op_wd.
  algebra.
 assumption.
Qed.

Lemma cpoly_mult_commutative :
 forall p q : cpoly_csetoid, cpoly_mult_cs p q [=] cpoly_mult_cs q p.
Proof.
 intros.
 pattern p in |- *.
 apply cpoly_ind_cs.
  rewrite cpoly_zero_mult.
  apply eq_symmetric_unfolded.
  apply cpoly_mult_zero.
 intros.
 rewrite cpoly_lin_mult.
 apply eq_transitive_unfolded with (cpoly_plus_cs (cpoly_mult_cr_cs q c)
   (cpoly_linear_cs [0] (cpoly_mult_cs q p0))).
  2: apply eq_symmetric_unfolded; apply cpoly_mult_lin.
 apply cpoly_plus_op_wd.
  algebra.
 apply cpoly_linear_wd.
  algebra.
 assumption.
Qed.

Lemma cpoly_mult_dist_rht : forall p q r,
 cpoly_mult_cs (cpoly_plus_cs p q) r [=]
  cpoly_plus_cs (cpoly_mult_cs p r) (cpoly_mult_cs q r).
Proof.
 intros.
 apply eq_transitive_unfolded with (cpoly_mult_cs r (cpoly_plus_cs p q)).
  apply cpoly_mult_commutative.
 apply eq_transitive_unfolded with (cpoly_plus_cs (cpoly_mult_cs r p) (cpoly_mult_cs r q)).
  generalize cpoly_cr_dist; intro.
  unfold distributive in H.
  simpl in H.
  simpl in |- *.
  apply H.
 apply cpoly_plus_op_wd.
  apply cpoly_mult_commutative.
 apply cpoly_mult_commutative.
Qed.

Lemma cpoly_mult_assoc : associative cpoly_mult_op.
Proof.
 unfold associative in |- *.
 intros p q r.
 change (cpoly_mult_cs p (cpoly_mult_cs q r) [=] cpoly_mult_cs (cpoly_mult_cs p q) r) in |- *.
 pattern p in |- *; apply cpoly_ind_cs.
  repeat rewrite cpoly_zero_mult.
  algebra.
 intros.
 repeat rewrite cpoly_lin_mult.
 apply eq_transitive_unfolded with (cpoly_plus_cs (cpoly_mult_cs (cpoly_mult_cr_cs q c) r)
   (cpoly_mult_cs (cpoly_linear_cs [0] (cpoly_mult_cs p0 q)) r)).
  apply cpoly_plus_op_wd.
   apply cpoly_mult_cr_assoc_mult.
  rewrite cpoly_lin_mult.
  apply eq_transitive_unfolded with (cpoly_plus_cs cpoly_zero_cs
    (cpoly_linear_cs [0] (cpoly_mult_cs (cpoly_mult_cs p0 q) r))).
   rewrite cpoly_zero_plus.
   apply _cpoly_lin_eq_lin.
   split.
    algebra.
   assumption.
  apply cpoly_plus_op_wd.
   apply eq_symmetric_unfolded.
   apply cpoly_mult_cr_zero.
  apply _cpoly_lin_eq_lin.
  split.
   algebra.
  algebra.
 apply eq_symmetric_unfolded.
 apply cpoly_mult_dist_rht.
Qed.

Lemma cpoly_mult_cr_one : forall p, cpoly_mult_cr_cs p [1] [=] p.
Proof.
 intro.
 pattern p in |- *; apply cpoly_ind_cs.
  algebra.
 intros.
 rewrite cpoly_lin_mult_cr.
 apply _cpoly_lin_eq_lin.
 algebra.
Qed.

Lemma cpoly_one_mult : forall p, cpoly_mult_cs cpoly_one p [=] p.
Proof.
 intro.
 unfold cpoly_one in |- *.
 unfold cpoly_constant in |- *.
 replace (cpoly_linear [1] cpoly_zero) with (cpoly_linear_cs [1] cpoly_zero).
  2: reflexivity.
 rewrite cpoly_lin_mult.
 rewrite cpoly_zero_mult.
 apply eq_transitive_unfolded with (cpoly_plus_cs p cpoly_zero_cs).
  apply cpoly_plus_op_wd.
   apply cpoly_mult_cr_one.
  apply _cpoly_lin_eq_zero; algebra.
 rewrite cpoly_plus_zero; algebra.
Qed.

Lemma cpoly_mult_one : forall p, cpoly_mult_cs p cpoly_one [=] p.
Proof.
 intro.
 apply eq_transitive_unfolded with (cpoly_mult_cs cpoly_one p).
  apply cpoly_mult_commutative.
 apply cpoly_one_mult.
Qed.

Lemma cpoly_mult_monoid :
 is_CMonoid (Build_CSemiGroup _ _ cpoly_mult_assoc) cpoly_one.
Proof.
 apply Build_is_CMonoid.
  exact cpoly_mult_one.
 exact cpoly_one_mult.
Qed.

Lemma cpoly_cr_non_triv : cpoly_ap cpoly_one cpoly_zero.
Proof.
 change (cpoly_linear_cs [1] cpoly_zero_cs [#] cpoly_zero_cs) in |- *.
 cut (([1]:CR) [#] [0] or cpoly_zero_cs [#] cpoly_zero_cs).
  auto.
 left.
 algebra.
Qed.

(**
cring_old uses the original definition of polynomial multiplication
*)

Lemma cpoly_is_CRing_old : is_CRing cpoly_cabgroup cpoly_one cpoly_mult_op.
Proof.
 apply Build_is_CRing with cpoly_mult_assoc.
    exact cpoly_mult_monoid.
   exact cpoly_mult_commutative.
  exact cpoly_cr_dist.
 exact cpoly_cr_non_triv.
Qed.

Definition cpoly_cring_old : CRing := Build_CRing _ _ _ cpoly_is_CRing_old.

(**
[cpoly_mult_fast] produces smaller lengthed polynomials when multiplying by zero.
For example [Eval simpl in cpoly_mult_cs _ _X_ ([0]:cpoly_cring Q_as_CRing)]
returns
[cpoly_linear Q_as_CRing QZERO (cpoly_linear Q_as_CRing QZERO (cpoly_zero Q_as_CRing))]
while
[Eval simpl in cpoly_mult_fast_cs _ _X_ ([0]:cpoly_cring Q_as_CRing)]
returns
[cpoly_zero Q_as_CRing].

Smaller lengthed polynomials means faster operations, and better estimates of the
degree of a polynomial.
*)

Definition cpoly_mult_fast (p q : cpoly) : cpoly :=
  match q with
  | cpoly_zero        => cpoly_zero
  | _ => cpoly_mult p q
  end.

Definition cpoly_mult_fast_cs (p q : cpoly_csetoid) : cpoly_csetoid := cpoly_mult_fast p q.

(** cpoly_mult_fast is proven correct with respect the the original multiplication
in cpoly_cring_old *)

Lemma cpoly_mult_fast_ap_equiv : forall p1 p2 q1 q2,
(cpoly_mult_fast_cs p1 q1)[#](cpoly_mult_cs p2 q2) -> p1[#]p2 or q1[#]q2.
Proof.
 destruct q1 as [|c q1]; destruct q2 as [|c0 q2]; intros X; simpl in X.
    rewrite cpoly_ap_p_zero in X.
    elim (ap_irreflexive cpoly_csetoid cpoly_zero).
    stepl (cpoly_mult_cs p2 cpoly_zero).
     assumption.
    apply cpoly_mult_zero.
   rewrite cpoly_ap_p_zero in X.
   right.
   apply ap_symmetric.
   eapply cring_mult_ap_zero_op with (R:=cpoly_cring_old).
   apply X.
  right.
  eapply cring_mult_ap_zero_op with (R:=cpoly_cring_old).
  change (cpoly_mult p1 (cpoly_linear c q1)) with (cpoly_mult_cs p1 (cpoly_linear c q1)) in X.
  stepr (cpoly_mult_cs p2 cpoly_zero).
   apply X.
  apply cpoly_mult_zero.
 apply cpoly_mult_op_strext.
 apply X.
Qed.

Lemma cpoly_mult_fast_equiv : forall p q,
(cpoly_mult_fast_cs p q)[=](cpoly_mult_cs p q).
Proof.
 intros p q.
 apply not_ap_imp_eq.
 intro H.
 assert (p[#]p or q[#]q).
  apply cpoly_mult_fast_ap_equiv.
  assumption.
 destruct X as [X|X]; apply (ap_irreflexive _ _ X).
Qed.

Lemma cpoly_mult_fast_op_strext : bin_op_strext cpoly_csetoid cpoly_mult_fast_cs.
Proof.
 intros x1 x2 y1 y2 H.
 apply cpoly_mult_op_strext.
 stepl (cpoly_mult_fast_cs x1 y1).
  stepr (cpoly_mult_fast_cs x2 y2).
   assumption.
  apply cpoly_mult_fast_equiv.
 apply cpoly_mult_fast_equiv.
Qed.

Definition cpoly_mult_fast_op := Build_CSetoid_bin_op _ _ cpoly_mult_fast_op_strext.

Lemma cpoly_is_CRing : is_CRing cpoly_cabgroup cpoly_one cpoly_mult_fast_op.
Proof.
 assert (mult_assoc:(associative cpoly_mult_fast_op)).
  intros p q r.
  stepl (cpoly_mult_op p (cpoly_mult_op q r)).
   stepr (cpoly_mult_op (cpoly_mult_op p q) r).
    apply cpoly_mult_assoc.
   stepl (cpoly_mult_op (cpoly_mult_fast_op p q) r).
    apply eq_symmetric; apply cpoly_mult_fast_equiv.
   apply bin_op_wd_unfolded.
    apply cpoly_mult_fast_equiv.
   apply eq_reflexive.
  stepl (cpoly_mult_op p (cpoly_mult_fast_op q r)).
   apply eq_symmetric; apply cpoly_mult_fast_equiv.
  apply bin_op_wd_unfolded.
   apply eq_reflexive.
  apply cpoly_mult_fast_equiv.
 eapply Build_is_CRing with mult_assoc.
    split.
     intro p.
     stepl (cpoly_mult_op p cpoly_one).
      apply cpoly_mult_one.
     apply eq_symmetric; apply cpoly_mult_fast_equiv.
    intro p.
    stepl (cpoly_mult_op cpoly_one p).
     apply cpoly_one_mult.
    apply eq_symmetric; apply cpoly_mult_fast_equiv.
   intros p q.
   stepl (cpoly_mult_op p q).
    stepr (cpoly_mult_op q p).
     apply cpoly_mult_commutative.
    apply eq_symmetric; apply cpoly_mult_fast_equiv.
   apply eq_symmetric; apply cpoly_mult_fast_equiv.
  intros p q r.
  stepl (cpoly_mult_op p (q[+]r)).
   stepr (cpoly_plus_op (cpoly_mult_op p q) (cpoly_mult_op p r)).
    apply cpoly_cr_dist.
   apply bin_op_wd_unfolded; apply eq_symmetric; apply cpoly_mult_fast_equiv.
  apply eq_symmetric; apply cpoly_mult_fast_equiv.
 exact cpoly_cr_non_triv.
Qed.

Definition cpoly_cring : CRing := Build_CRing _ _ _ cpoly_is_CRing.
Canonical Structure cpoly_cring.

Lemma cpoly_constant_strext :
 fun_strext (S1:=CR) (S2:=cpoly_cring) cpoly_constant.
Proof.
 unfold fun_strext in |- *.
 unfold cpoly_constant in |- *.
 simpl in |- *.
 intros x y H.
 elim H.
  auto.
 intro.
 elim b.
Qed.

Lemma cpoly_constant_wd : fun_wd (S1:=CR) (S2:=cpoly_cring) cpoly_constant.
Proof.
 apply fun_strext_imp_wd.
 exact cpoly_constant_strext.
Qed.

Definition cpoly_constant_fun := Build_CSetoid_fun _ _ _ cpoly_constant_strext.

Definition cpoly_var : cpoly_cring := cpoly_linear_cs [0] ([1]:cpoly_cring).
Notation "'_X_'" := cpoly_var.

Definition cpoly_x_minus_c c : cpoly_cring :=
 cpoly_linear_cs [--]c ([1]:cpoly_cring).

Lemma cpoly_x_minus_c_strext :
 fun_strext (S1:=CR) (S2:=cpoly_cring) cpoly_x_minus_c.
Proof.
 unfold fun_strext in |- *.
 unfold cpoly_x_minus_c in |- *.
 simpl in |- *.
 intros x y H.
 elim H; intro H0.
  apply (cs_un_op_strext _ _ _ _ H0).
 elim H0; intro H1.
  elim (ap_irreflexive_unfolded _ _ H1).
 elim H1.
Qed.

Lemma cpoly_x_minus_c_wd : fun_wd (S1:=CR) (S2:=cpoly_cring) cpoly_x_minus_c.
Proof.
 apply fun_strext_imp_wd.
 exact cpoly_x_minus_c_strext.
Qed.

Definition cpoly_ring_th:= (CRing_Ring cpoly_cring).
End CPoly_CRing.


Canonical Structure cpoly_cring.
Notation "'_X_'" := (@cpoly_var _).

Definition cpoly_linear_fun' (CR : CRing) :
 CSetoid_bin_fun CR (cpoly_cring CR) (cpoly_cring CR) := cpoly_linear_fun CR.

Arguments cpoly_linear_fun' {CR}.
Infix "[+X*]" := cpoly_linear_fun' (at level 50, left associativity).


(**
** Apartness, equality, and induction
%\label{section:poly-equality}%
*)

Section CPoly_CRing_ctd.

(**
%\begin{convention}%
Let [CR] be a ring, [p] and [q] polynomials over that ring, and [c] and [d]
elements of the ring.
%\end{convention}%
*)
Variable CR : CRing.
Add Ring cpolycring_th : (CRing_Ring (cpoly_cring CR)).

Notation RX := (cpoly_cring CR).

Section helpful_section.

Variables p q : RX.
Variables c d : CR.
(** It should be possible to merge most of this section using the new apply *)
Lemma linear_eq_zero_ : c[+X*]p [=] [0] -> c [=] [0] /\ p [=] [0].
Proof cpoly_lin_eq_zero_ CR p c.

Lemma _linear_eq_zero : c [=] [0] /\ p [=] [0] -> c[+X*]p [=] [0].
Proof _cpoly_lin_eq_zero CR p c.

Lemma zero_eq_linear_ : [0] [=] c[+X*]p -> c [=] [0] /\ [0] [=] p.
Proof cpoly_zero_eq_lin_ CR p c.

Lemma _zero_eq_linear : c [=] [0] /\ [0] [=] p -> [0] [=] c[+X*]p.
Proof _cpoly_zero_eq_lin CR p c.

Lemma linear_eq_linear_ : c[+X*]p [=] d[+X*]q -> c [=] d /\ p [=] q.
Proof cpoly_lin_eq_lin_ CR p q c d.

Lemma _linear_eq_linear : c [=] d /\ p [=] q -> c[+X*]p [=] d[+X*]q.
Proof _cpoly_lin_eq_lin CR p q c d.

Lemma linear_ap_zero_ : c[+X*]p [#] [0] -> c [#] [0] or p [#] [0].
Proof cpoly_lin_ap_zero_ CR p c.

Lemma _linear_ap_zero : c [#] [0] or p [#] [0] -> c[+X*]p [#] [0].
Proof _cpoly_lin_ap_zero CR p c.

Lemma linear_ap_zero : (c[+X*]p [#] [0]) = (c [#] [0] or p [#] [0]).
Proof cpoly_lin_ap_zero CR p c.

Lemma zero_ap_linear_ : [0] [#] c[+X*]p -> c [#] [0] or [0] [#] p.
Proof cpoly_zero_ap_lin_ CR p c.

Lemma _zero_ap_linear : c [#] [0] or [0] [#] p -> [0] [#] c[+X*]p.
Proof _cpoly_zero_ap_lin CR p c.

Lemma zero_ap_linear : ([0] [#] c[+X*]p) = (c [#] [0] or [0] [#] p).
Proof cpoly_zero_ap_lin CR p c.

Lemma linear_ap_linear_ : c[+X*]p [#] d[+X*]q -> c [#] d or p [#] q.
Proof cpoly_lin_ap_lin_ CR p q c d.

Lemma _linear_ap_linear : c [#] d or p [#] q -> c[+X*]p [#] d[+X*]q.
Proof _cpoly_lin_ap_lin CR p q c d.

Lemma linear_ap_linear : (c[+X*]p [#] d[+X*]q) = (c [#] d or p [#] q).
Proof cpoly_lin_ap_lin CR p q c d.

End helpful_section.

Lemma Ccpoly_induc : forall P : RX -> CProp, P [0] ->
 (forall p c, P p -> P (c[+X*]p)) -> forall p, P p.
Proof (Ccpoly_ind_cs CR).

Lemma Ccpoly_double_sym_ind : forall P : RX -> RX -> CProp,
 Csymmetric P -> (forall p, P p [0]) ->
 (forall p q c d, P p q -> P (c[+X*]p) (d[+X*]q)) -> forall p q, P p q.
Proof (Ccpoly_double_sym_ind0_cs CR).

Lemma Cpoly_double_comp_ind : forall P : RX -> RX -> CProp,
 (forall p1 p2 q1 q2, p1 [=] p2 -> q1 [=] q2 -> P p1 q1 -> P p2 q2) -> P [0] [0] ->
 (forall p q c d, P p q -> P (c[+X*]p) (d[+X*]q)) -> forall p q, P p q.
Proof (Ccpoly_double_comp_ind CR).

Lemma Cpoly_triple_comp_ind : forall P : RX -> RX -> RX -> CProp,
 (forall p1 p2 q1 q2 r1 r2,
  p1 [=] p2 -> q1 [=] q2 -> r1 [=] r2 -> P p1 q1 r1 -> P p2 q2 r2) ->
 P [0] [0] [0] -> (forall p q r c d e, P p q r -> P (c[+X*]p) (d[+X*]q) (e[+X*]r)) ->
 forall p q r, P p q r.
Proof (Ccpoly_triple_comp_ind CR).

Lemma cpoly_induc : forall P : RX -> Prop,
 P [0] -> (forall p c, P p -> P (c[+X*]p)) -> forall p, P p.
Proof (cpoly_ind_cs CR).

Lemma cpoly_double_sym_ind : forall P : RX -> RX -> Prop,
 Tsymmetric P -> (forall p, P p [0]) ->
 (forall p q c d, P p q -> P (c[+X*]p) (d[+X*]q)) -> forall p q, P p q.
Proof (cpoly_double_sym_ind0_cs CR).

Lemma poly_double_comp_ind : forall P : RX -> RX -> Prop,
 (forall p1 p2 q1 q2, p1 [=] p2 -> q1 [=] q2 -> P p1 q1 -> P p2 q2) -> P [0] [0] ->
 (forall p q c d, P p q -> P (c[+X*]p) (d[+X*]q)) -> forall p q, P p q.
Proof (cpoly_double_comp_ind CR).

Lemma poly_triple_comp_ind : forall P : RX -> RX -> RX -> Prop,
 (forall p1 p2 q1 q2 r1 r2,
  p1 [=] p2 -> q1 [=] q2 -> r1 [=] r2 -> P p1 q1 r1 -> P p2 q2 r2) ->
 P [0] [0] [0] ->
 (forall p q r c d e, P p q r -> P (c[+X*]p) (d[+X*]q) (e[+X*]r)) -> forall p q r, P p q r.
Proof (cpoly_triple_comp_ind CR).

Transparent cpoly_cring.
Transparent cpoly_cgroup.
Transparent cpoly_csetoid.

Fixpoint cpoly_apply (p : RX) (x : CR) {struct p} : CR :=
  match p with
  | cpoly_zero _ => [0]
  | cpoly_linear _ c p1 => c[+]x[*]cpoly_apply p1 x
  end.

Lemma cpoly_apply_strext : bin_fun_strext _ _ _ cpoly_apply.
Proof.
 unfold bin_fun_strext in |- *.
 do 2 intro.
 pattern x1, x2 in |- *.
 apply Ccpoly_double_sym_ind.
   unfold Csymmetric in |- *.
   intros.
   generalize (ap_symmetric _ _ _ X0); intro.
   elim (X _ _ X1); intro.
    left.
    apply ap_symmetric_unfolded.
    assumption.
   right.
   apply ap_symmetric_unfolded.
   assumption.
  do 3 intro.
  pattern p in |- *.
  apply Ccpoly_induc.
   simpl in |- *.
   intro H.
   elim (ap_irreflexive _ _ H).
  intros.
  simpl in X0.
  simpl in X.
  cut (c[+]y1[*]cpoly_apply p0 y1 [#] [0][+]y1[*][0]).
   intro.
   elim (cs_bin_op_strext _ _ _ _ _ _ X1); intro H2.
    left.
    cut (c [#] [0] or p0 [#] [0]).
     intro.
     apply _linear_ap_zero.
     auto.
    left.
    assumption.
   elim (cs_bin_op_strext _ _ _ _ _ _ H2); intro H3.
    elim (ap_irreflexive _ _ H3).
   elim (X H3); intro H4.
    left.
    cut (c [#] [0] or p0 [#] [0]).
     intro; apply _linear_ap_zero.
     auto.
    right.
    exact H4.
   auto.
  astepr ([0][+]([0]:CR)).
  astepr ([0]:CR). auto.
  simpl in |- *.
 intros.
 elim (cs_bin_op_strext _ _ _ _ _ _ X0); intro H1.
  auto.
 elim (cs_bin_op_strext _ _ _ _ _ _ H1); intro H2.
  auto.
 elim (X _ _ H2); auto.
Qed.

Lemma cpoly_apply_wd : bin_fun_wd _ _ _ cpoly_apply.
Proof.
 apply bin_fun_strext_imp_wd.
 exact cpoly_apply_strext.
Qed.

Definition cpoly_apply_fun := Build_CSetoid_bin_fun _ _ _ _ cpoly_apply_strext.

End CPoly_CRing_ctd.

(**
%\begin{convention}%
[cpoly_apply_fun] is denoted infix by [!]
The first argument is left implicit, so the application of
polynomial [f] (seen as a function) to argument [x] can be written as [f!x].
In the names of lemmas, we write [apply].
%\end{convention}%
*)

Arguments cpoly_apply_fun {CR}.
Infix "!" := cpoly_apply_fun (at level 1, no associativity).

(**
** Basic properties of polynomials
%\begin{convention}%
Let [R] be a ring and write [RX] for the ring of polynomials over [R].
%\end{convention}%
*)

Section Poly_properties.
Variable R : CRing.
Add Ring cpolycring_thR : (cpoly_ring_th R).
Notation RX := (cpoly_cring R).

Lemma cpoly_const_one : [1] [=] cpoly_constant_fun _ ([1]:R).
Proof. 
 simpl in |- *; split; algebra.
Qed.

Lemma cpoly_const_plus : forall a b : R, cpoly_constant_fun _ (a[+]b) [=] cpoly_constant_fun _ a[+]cpoly_constant_fun _ b.
Proof.
 simpl in |- *; split; algebra.
Qed.

Lemma cpoly_const_mult : forall a b : R, cpoly_constant_fun _ (a[*]b) [=] cpoly_constant_fun _ a[*] cpoly_constant_fun _ b.
Proof.
 simpl in |- *; split; algebra.
Qed.

Definition polyconst : RingHom R RX := Build_RingHom _ _ _ cpoly_const_plus cpoly_const_mult cpoly_const_one.
Notation "'_C_'" := polyconst.

Lemma c_one : [1] [=] _C_ ([1]:R).
Proof.
 simpl in |- *; split; algebra.
Qed.

Lemma c_plus : forall a b : R, _C_ (a[+]b) [=] _C_ a[+] _C_ b.
Proof.
 simpl in |- *; split; algebra.
Qed.

Lemma c_mult : forall a b : R, _C_ (a[*]b) [=] _C_ a[*] _C_ b.
Proof.
 simpl in |- *; split; algebra.
Qed.

Lemma c_zero : [0] [=] _C_ ([0]:R).
Proof.
 simpl in |- *; split; algebra.
Qed.

(**
*** Constant and identity
*)

Lemma cpoly_X_ : _X_ [=] ([0]:RX) [+X*][1].
Proof.
 algebra.
Qed.

Lemma cpoly_C_ : forall c : R, _C_ c [=] c[+X*][0].
Proof.
 algebra.
Qed.

Hint Resolve cpoly_X_ cpoly_C_: algebra.

Lemma cpoly_const_eq : forall c d : R, c [=] d -> _C_ c [=] _C_ d.
Proof.
 algebra.
Qed.

Lemma cpoly_lin : forall (p : RX) (c : R), c[+X*]p [=] _C_ c[+]_X_[*]p.
Proof.
 intros.
 astepr (c[+X*][0][+] ((cpoly_mult_cr_cs _ p [0]:RX) [+] (cpoly_linear _ ([0]:R)
   (cpoly_mult_cs _ (cpoly_one R) (p:cpoly_csetoid R)) :cpoly_csetoid R))).
  cut (cpoly_mult_cr_cs R p [0] [=] ([0]:RX)).
   intro.
   astepr (c[+X*][0][+] (([0]:RX) [+] (cpoly_linear _ ([0]:R)
     (cpoly_mult_cs _ (cpoly_one R) (p:cpoly_csetoid R)) :cpoly_csetoid R))).
   2: apply (cpoly_mult_cr_zero R p).
  cut ((cpoly_mult_cs _ (cpoly_one R) (p:cpoly_csetoid R):cpoly_csetoid R) [=] p).
   intro.
   apply eq_transitive_unfolded with
     (c[+X*][0][+](([0]:RX) [+]cpoly_linear _ ([0]:R) (p:cpoly_csetoid R))).
    2: apply bin_op_wd_unfolded.
     2: algebra.
    2: apply bin_op_wd_unfolded.
     2: algebra.
    2: apply (cpoly_linear_wd R).
     2: algebra.
    2: apply eq_symmetric_unfolded.
    2: apply cpoly_one_mult.
   astepr (c[+X*][0][+]cpoly_linear _ ([0]:R) (p:cpoly_csetoid R)).
   astepr (c[+][0][+X*]([0][+]p)).
   astepr (c[+X*]p).
   algebra.
  apply cpoly_one_mult.
 destruct p.
  simpl.
  algebra.
 simpl.
 split.
  auto with *.
 apply eq_reflexive with (S:=cpoly_cring R).
Qed.

Hint Resolve cpoly_lin: algebra.

(* SUPERFLUOUS *)
Lemma poly_linear : forall c f, (cpoly_linear _ c f:RX) [=] _X_[*]f[+]_C_ c.
Proof.
 intros.
 astepr (_C_ c[+]_X_[*]f).
 exact (cpoly_lin f c).
Qed.

Lemma poly_c_apzero : forall a : R, _C_ a [#] [0] -> a [#] [0].
Proof.
 intros.
 cut (_C_ a [#] _C_ [0]).
  intro H0.
  generalize (csf_strext _ _ _ _ _ H0); auto.
 Hint Resolve c_zero: algebra.
 astepr ([0]:RX). auto.
Qed.

Lemma c_mult_lin : forall (p : RX) c d, _C_ c[*] (d[+X*]p) [=] c[*]d[+X*]_C_ c[*]p.
Proof.
 intros.
 pattern p in |- *.
 apply cpoly_induc.
  simpl in |- *.
  repeat split; algebra.
 intros. simpl in |- *.
 repeat split; algebra.
 change ((cpoly_mult_cr R p0 c:RX) [=] (cpoly_mult_cr R p0 c:RX)[+][0]) in |- *.
 algebra.
Qed.


(* SUPERFLUOUS ? *)
Lemma lin_mult : forall (p q : RX) c, (c[+X*]p) [*]q [=] _C_ c[*]q[+]_X_[*] (p[*]q).
Proof.
 intros.
 astepl ((_C_ c[+]_X_[*]p)[*]q).
 astepl (_C_ c[*]q[+]_X_[*]p[*]q).
 algebra.
Qed.

Hint Resolve lin_mult: algebra.

(**
*** Application of polynomials
*)

Lemma poly_eq_zero : forall p : RX, p [=] cpoly_zero R -> forall x, p ! x [=] [0].
Proof.
 intros.
 astepl (cpoly_zero R) ! x.
 change ([0] ! x [=] [0]) in |- *.
 algebra.
Qed.

Lemma apply_wd : forall (p p' : RX) x x', p [=] p' -> x [=] x' -> p ! x [=] p' ! x'.
Proof.
 algebra.
Qed.

Lemma cpolyap_pres_eq : forall (f : RX) x y, x [=] y -> f ! x [=] f ! y.
Proof.
 algebra.
Qed.

Lemma cpolyap_strext : forall (f : RX) x y, f ! x [#] f ! y -> x [#] y.
Proof.
 intros f x y H.
 elim (csbf_strext _ _ _ _ _ _ _ _ H); intro H0.
  elim (ap_irreflexive_unfolded _ _ H0).
 assumption.
Qed.

Definition cpoly_csetoid_op (f : RX) : CSetoid_un_op R :=
 Build_CSetoid_fun _ _ (fun x => f ! x) (cpolyap_strext f).

Definition FPoly p := total_eq_part _ (cpoly_csetoid_op p).

Lemma c_apply : forall c x : R, (_C_ c) ! x [=] c.
Proof.
 intros.
 simpl in |- *.
 astepl (c[+][0]).
 algebra.
Qed.

Lemma x_apply : forall x : R, _X_ ! x [=] x.
Proof.
 intros.
 simpl in |- *.
 astepl (x[*]([1][+]x[*][0])).
 astepl (x[*]([1][+][0])).
 astepl (x[*][1]).
 algebra.
Qed.

Lemma plus_apply : forall (p q : RX) x, (p[+]q) ! x [=] p ! x[+]q ! x.
Proof.
 intros.
 pattern p, q in |- *; apply poly_double_comp_ind.
   intros.
   astepl (p1[+]q1) ! x.
   astepr (p1 ! x[+]q1 ! x).
   algebra.
  simpl in |- *.
  algebra.
 intros.
 astepl (c[+]d[+]x[*](p0[+]q0) ! x).
 astepr (c[+]x[*]p0 ! x[+](d[+]x[*]q0 ! x)).
 astepl (c[+]d[+]x[*](p0 ! x[+]q0 ! x)).
 astepl (c[+]d[+](x[*]p0 ! x[+]x[*]q0 ! x)).
 astepl (c[+](d[+](x[*]p0 ! x[+]x[*]q0 ! x))).
 astepr (c[+](x[*]p0 ! x[+](d[+]x[*]q0 ! x))).
 astepl (c[+](d[+]x[*]p0 ! x[+]x[*]q0 ! x)).
 astepr (c[+](x[*]p0 ! x[+]d[+]x[*]q0 ! x)).
 algebra.
Qed.

Lemma inv_apply : forall (p : RX) x, ( [--]p) ! x [=] [--]p ! x.
Proof.
 intros.
 pattern p in |- *.
 apply cpoly_induc.
  simpl in |- *.
  algebra.
 intros.
 astepl ( [--]c[+]x[*]( [--]p0) ! x).
 astepr ( [--](c[+]x[*]p0 ! x)).
 astepr ( [--]c[+][--](x[*]p0 ! x)).
 astepr ( [--]c[+]x[*][--]p0 ! x).
 algebra.
Qed.

Hint Resolve plus_apply inv_apply: algebra.

Lemma minus_apply : forall (p q : RX) x, (p[-]q) ! x [=] p ! x[-]q ! x.
Proof.
 intros.
 astepl (p[+][--]q) ! x.
 astepr (p ! x[+][--]q ! x).
 astepl (p ! x[+]( [--]q) ! x).
 algebra.
Qed.

Lemma c_mult_apply : forall (q : RX) c x, (_C_ c[*]q) ! x [=] c[*]q ! x.
Proof.
 intros.
 astepl ((cpoly_mult_cr R q c:RX)[+]([0][+X*][0])) ! x.
  astepl ((cpoly_mult_cr R q c) ! x[+]([0][+X*][0]) ! x).
  astepl ((cpoly_mult_cr R q c) ! x[+]([0][+]x[*][0])).
  astepl ((cpoly_mult_cr R q c) ! x[+]([0][+][0])).
  astepl ((cpoly_mult_cr R q c) ! x[+][0]).
  astepl (cpoly_mult_cr R q c) ! x.
  pattern q in |- *.
  apply cpoly_induc.
   simpl in |- *.
   algebra.
  intros.
  astepl (c[*]c0[+X*]cpoly_mult_cr R p c) ! x.
  astepl (c[*]c0[+]x[*](cpoly_mult_cr R p c) ! x).
  astepl (c[*]c0[+]x[*](c[*]p ! x)).
  astepr (c[*](c0[+]x[*]p ! x)).
  astepr (c[*]c0[+]c[*](x[*]p ! x)).
  apply bin_op_wd_unfolded.
   algebra.
  astepl (x[*]c[*]p ! x).
  astepr (c[*]x[*]p ! x).
  algebra.
 stepr ((cpoly_mult _ (_C_ c) q)!x).
  apply eq_reflexive.
 apply apply_wd.
  apply eq_symmetric.
  apply (cpoly_mult_fast_equiv _ (_C_ c) q).
 apply eq_reflexive.
Qed.

Hint Resolve c_mult_apply: algebra.

Lemma mult_apply : forall (p q : RX) x, (p[*]q) ! x [=] p ! x[*]q ! x.
Proof.
 intros.
 pattern p in |- *.
 apply cpoly_induc.
  astepl ([0] ! x).
  simpl in |- *.
  algebra.
 intros.
 astepl (_C_ c[*]q[+]_X_[*](p0[*]q)) ! x.
 astepl ((_C_ c[*]q) ! x[+](_X_[*](p0[*]q)) ! x).
 astepl ((_C_ c[*]q) ! x[+]([0][+]_X_[*](p0[*]q)) ! x).
 astepl ((_C_ c[*]q) ! x[+](_C_ [0][+]_X_[*](p0[*]q)) ! x).
 astepl ((_C_ c[*]q) ! x[+]([0][+X*]p0[*]q) ! x).
 astepl ((_C_ c[*]q) ! x[+]([0][+]x[*](p0[*]q) ! x)).
 astepl (c[*]q ! x[+]x[*](p0[*]q) ! x).
 astepl (c[*]q ! x[+]x[*](p0 ! x[*]q ! x)).
 astepr ((c[+]x[*]p0 ! x)[*]q ! x).
 astepr (c[*]q ! x[+]x[*]p0 ! x[*]q ! x).
 algebra.
Qed.

Hint Resolve mult_apply: algebra.

Lemma one_apply : forall x : R, [1] ! x [=] [1].
Proof.
 intro.
 astepl (_C_ [1]) ! x.
 apply c_apply.
Qed.

Hint Resolve one_apply: algebra.

Lemma nexp_apply : forall (p : RX) n x, (p[^]n) ! x [=] p ! x[^]n.
Proof.
 intros.
 induction  n as [| n Hrecn].
  astepl ([1]:RX) ! x.
  astepl ([1]:R).
  algebra.
 astepl (p[*]p[^]n) ! x.
 astepl (p ! x[*](p[^]n) ! x).
 astepl (p ! x[*]p ! x[^]n).
 algebra.
Qed.

(* SUPERFLUOUS *)
Lemma poly_inv_apply : forall (p : RX) x, (cpoly_inv _ p) ! x [=] [--]p ! x.
Proof inv_apply.

Lemma Sum0_cpoly_ap : forall (f : nat -> RX) a k, (Sum0 k f) ! a [=] Sum0 k (fun i => (f i) ! a).
Proof.
 intros.
 induction  k as [| k Hreck].
  simpl in |- *.
  algebra.
 astepl (Sum0 k f[+]f k) ! a.
 astepl ((Sum0 k f) ! a[+](f k) ! a).
 astepl (Sum0 k (fun i : nat => (f i) ! a)[+](f k) ! a).
 simpl in |- *.
 algebra.
Qed.

Lemma Sum_cpoly_ap : forall (f : nat -> RX) a k l,
 (Sum k l f) ! a [=] Sum k l (fun i => (f i) ! a).
Proof.
 unfold Sum in |- *.
 unfold Sum1 in |- *.
 intros.
 unfold cg_minus in |- *.
 astepl ((Sum0 (S l) f) ! a[+]( [--](Sum0 k f)) ! a).
 astepl ((Sum0 (S l) f) ! a[+][--](Sum0 k f) ! a).
 apply bin_op_wd_unfolded.
  apply Sum0_cpoly_ap.
 apply un_op_wd_unfolded.
 apply Sum0_cpoly_ap.
Qed.

Lemma cm_Sum_apply (l: list (cpoly_cring R)) (x: R):
 (cm_Sum l) ! x [=] cm_Sum (map (fun e => e ! x) l).
Proof.
 induction l.
  reflexivity.
 change ((a [+] cm_Sum l) ! x[=]cm_Sum (map (fun e : cpoly_cring R => e ! x) (a :: l))).
 rewrite plus_apply, IHl.
 reflexivity.
Qed.

Hint Rewrite cm_Sum_apply: apply.

Lemma cr_Product_apply (l: list (cpoly_cring R)) (x: R):
 (cr_Product l) ! x [=] cr_Product (map (fun e => e ! x) l).
Proof.
 induction l.
  simpl.
  rewrite cring_mult_zero.
  apply cm_rht_unit_unfolded.
 change ((a [*] cr_Product l) ! x[=]cr_Product (map (fun e : cpoly_cring R => e ! x) (a :: l))).
 rewrite mult_apply, IHl.
 reflexivity.
Qed.

Hint Rewrite cr_Product_apply: apply.

End Poly_properties.

(* Implicit Arguments _C_ [R].*)
Notation "'_C_'" := (@polyconst _).

(**
** Induction properties of polynomials for [Prop]
*)
Section Poly_Prop_Induction.

Variable CR : CRing.
Add Ring cpolycring_thCR : (cpoly_ring_th CR).
Notation Cpoly := (cpoly CR).

Notation Cpoly_zero := (cpoly_zero CR).

Notation Cpoly_linear := (cpoly_linear CR).

Notation Cpoly_cring := (cpoly_cring CR).

Lemma cpoly_double_ind : forall P : Cpoly_cring -> Cpoly_cring -> Prop,
 (forall p, P p [0]) -> (forall p, P [0] p) ->
 (forall p q c d, P p q -> P (c[+X*]p) (d[+X*]q)) -> forall p q, P p q.
Proof (cpoly_double_ind0_cs CR).

End Poly_Prop_Induction.

#[global]
Hint Resolve poly_linear cpoly_lin: algebra.
#[global]
Hint Resolve apply_wd cpoly_const_eq: algebra_c.
#[global]
Hint Resolve c_apply x_apply inv_apply plus_apply minus_apply mult_apply
  nexp_apply: algebra.
#[global]
Hint Resolve one_apply c_zero c_one c_mult: algebra.
#[global]
Hint Resolve poly_inv_apply: algebra.
#[global]
Hint Resolve c_mult_lin: algebra.

#[global]
Hint Rewrite one_apply c_apply x_apply mult_apply plus_apply minus_apply : apply.
#[global]
Hint Rewrite inv_apply nexp_apply c_mult_apply poly_inv_apply : apply.
Ltac poly_apply:= autorewrite with apply; simpl.
(** The tactic [poly_apply] applies polynomials to arguments *)
 
Section Derivative.

Variable R:CRing.
Add Ring cpolycring_thR1 : (cpoly_ring_th R).
Notation RX:= (cpoly_cring R).

Fixpoint cpoly_diff (p : RX) : RX :=
match p with
| cpoly_zero _ => [0]
| cpoly_linear _ c p1 => p1[+]([0][+X*](cpoly_diff p1))
end.

Lemma cpoly_diff_strext : un_op_strext _ cpoly_diff.
Proof.
 intros x.
 induction x.
  induction y.
   auto with *.
  intros Hxy.
  right.
  abstract ( destruct (cpoly_ap_zero_plus _ _ _ (ap_symmetric _ _ _ Hxy)) as [c|[c|c]];
    [apply (ap_symmetric _ _ _ c) |elim (ap_irreflexive _ _ c) |apply IHy;apply c]).
 intros [|a y] Hxy.
  simpl in Hxy.
  right.
  abstract ( destruct (cpoly_ap_zero_plus _ _ _ Hxy) as [c|[c|c]]; [apply (ap_symmetric _ _ _ c)
    |elim (ap_irreflexive _ _ c)
      |change ([0][#]x); apply ap_symmetric; apply IHx; apply ap_symmetric; apply c]).
 right.
 destruct (cpoly_plus_op_strext _ _ _ _ _ Hxy) as [c|[c|c]].
   assumption.
  elim (ap_irreflexive _ _ c).
 apply IHx; apply c.
Defined.

Lemma cpoly_diff_wd : un_op_wd _ cpoly_diff.
Proof.
 apply fun_strext_imp_wd.
 apply cpoly_diff_strext.
Qed.

Definition cpolyder := Build_CSetoid_un_op _ _ cpoly_diff_strext.
Notation "'_D_'" := cpolyder.

Lemma diff_zero : _D_ [0][=][0].
Proof.
 reflexivity.
Qed.

Lemma diff_one : _D_ [1][=][0].
Proof.
 simpl; split; auto with *; reflexivity.
Qed.

Lemma diff_const : forall c, _D_ (_C_ c)[=][0].
Proof.
 simpl; split; auto with *.
Qed.

Lemma diff_x : _D_ _X_[=][1].
Proof.
 simpl; split; auto with *.
Qed.

Lemma diff_linear : forall a (p:RX), _D_ (a[+X*]p)[=]p[+]_X_[*]_D_ p.
Proof.
 intros a p.
 change (p[+]([0][+X*]_D_ p)[=]p[+]_X_[*]_D_ p).
 rewrite -> cpoly_lin.
 rewrite <- c_zero. 
 ring.
Qed.

Lemma diff_plus : forall (p q:RX), _D_ (p[+]q)[=]_D_ p[+]_D_ q.
Proof.
 induction p.
  reflexivity.
 intros [|a q].
  rewrite -> cm_rht_unit_unfolded.
  change (cpoly_zero R) with ([0]:cpoly_cring R); algebra.
 change ((p[+]q)[+]cpoly_linear _ [0] (_D_ (p[+]q))[=]
   (p[+]cpoly_linear _ [0] (_D_ p))[+](q[+]cpoly_linear _ [0] (_D_ q))).
 do 3 rewrite -> poly_linear.
 change (st_car RX) in p, q.
 change (p[+]q[+](_X_[*]_D_ (p[+]q)[+]_C_ [0])[=]
   p[+](_X_[*]_D_ p[+]_C_ [0])[+](q[+](_X_[*]_D_ q[+]_C_ [0]))).
 rewrite -> (IHp q).
 rewrite <- c_zero.
 ring.
Qed.

Lemma diff_c_mult : forall c (p:RX), _D_ (_C_ c[*]p)[=]_C_ c[*]_D_ p.
Proof.
 intros c p.
 induction p.
  auto with *.
 change (_D_ (cpoly_linear R s p)) with (p[+]([0][+X*](_D_ p))).
 change (cpoly_linear R s p) with (s[+X*]p).
 rewrite -> c_mult_lin.
 change (_D_ (c[*]s[+X*]_C_ c[*]p)) with (_C_ c[*]p [+] ([0][+X*](_D_ (_C_ c[*]p)))).
 rewrite -> IHp.
 do 2 rewrite -> cpoly_lin.
 rewrite <- c_zero.
(* An attempt to avoid the following "change" 
Bind Scope ring_scope with CRing.
Notation "a '====' b":=(a [=] b)(at level 80, right associativity): ring_scope.
set (LHS:=_C_ c[*]p[+]([0][+]_X_[*](_C_ c[*]_D_ p))).
set (RHS:=(_C_ c[*](p[+]([0][+]_X_[*]_D_ p)))).
change  (LHS ==== RHS).

Or even:
Ltac preRing :=
match goal with
| |-(@st_eq ?s ?l ?r) => change (l ==== r) end.
preRing.*) 

 (* (cpoly_csemi_grp R) should be folded to RX *)
 change
 (@st_eq RX
  (@csg_op RX (@cr_mult RX (polyconst R c) p)
     (@csg_op RX (cm_unit RX)
        (@cr_mult RX (cpoly_var R) (@cr_mult RX (polyconst R c) (cpolyder p)))))
  (@cr_mult RX (polyconst R c)
     (@csg_op RX p
        (@csg_op RX (cm_unit RX) (@cr_mult RX (cpoly_var R) (cpolyder p)))))).
 ring.
Qed.

Lemma diff_mult : forall (p q:RX), _D_ (p[*]q)[=]_D_ p[*]q [+] p[*]_D_ q.
Proof.
 induction p.
  intros q.
  change (_D_([0][*]q)[=][0][*]q[+][0][*]_D_ q).
  stepl (_D_([0]:RX)). 2: now destruct q.
  rewrite -> diff_zero.
  ring.
 intros q.
 change (st_car RX) in p.
 change (_D_((s[+X*]p)[*]q)[=]_D_(s[+X*]p)[*]q[+](s[+X*]p)[*]_D_ q).
 do 2 rewrite -> lin_mult.
 rewrite -> diff_linear.
 rewrite -> diff_plus.
 setoid_replace (_D_ ((_C_ s:RX)[*]q)) with (_C_ s[*]_D_ q) by apply diff_c_mult.
 setoid_replace (((_X_:RX)[*](p[*]q)):RX)
   with ((((_X_:RX)[*](p[*]q)))[+][0]) by (symmetry;apply cm_rht_unit_unfolded).
 setoid_replace ([0]:RX) with (_C_ [0]:RX) by apply c_zero.
 rewrite <- poly_linear.
 change (_D_ (cpoly_linear R [0] (p[*]q))) with (p[*]q [+] ([0][+X*]_D_ (p[*]q))).
 rewrite -> cpoly_lin.
 rewrite <- c_zero.
 rewrite -> IHp.
 ring.
Qed.

End Derivative.
Notation "'_D_'" := (@cpolyder _).

#[global]
Hint Rewrite diff_zero diff_one diff_const diff_x diff_plus diff_c_mult diff_mult diff_linear : poly_diff.
Section Map.

Variable R S : CRing.
Add Ring cpolycring_thRR : (cpoly_ring_th R).
Add Ring cpolycring_thSS : (cpoly_ring_th S).
Variable f : RingHom R S.
Notation RX := (cpoly_cring R).
Notation SX := (cpoly_cring S).

Fixpoint cpoly_map_fun (p:RX) : SX :=
match p with
| cpoly_zero _ => cpoly_zero _
| cpoly_linear _ c p1 => cpoly_linear _ (f c) (cpoly_map_fun p1)
end.

Lemma cpoly_map_strext : fun_strext cpoly_map_fun.
Proof.
 intros x.
 induction x; intros y H.
  induction y.
   elim H.
  destruct H as [H|H].
   left.
   eapply rh_apzero; apply H.
  right.
  apply IHy.
  apply H.
 destruct y as [|c y].
  destruct H as [H|H].
   left.
   eapply rh_apzero; apply H.
  right.
  change ([0][#]x).
  apply ap_symmetric.
  apply IHx.
  apply ap_symmetric.
  apply H.
 destruct H as [H|H].
  left.
  eapply rh_strext; apply H.
 right.
 apply IHx.
 apply H.
Defined.

Definition cpoly_map_csf : CSetoid_fun RX SX := Build_CSetoid_fun _ _ _ cpoly_map_strext.

Lemma cpoly_map_pres_plus : fun_pres_plus _ _ cpoly_map_csf.
Proof.
 unfold fun_pres_plus.
 apply (cpoly_double_ind0 R).
   intros p.
   change (cpoly_map_csf(p[+][0])[=]cpoly_map_csf p[+][0]).
   stepr (cpoly_map_csf p). 2: ring.
   apply csf_wd.
   cut (forall p: cpoly_cring R, csg_op p [0] [=] p). easy.
   intros. ring.
  reflexivity.
 intros p q c d H.
 split.
  apply rh_pres_plus.
 apply H.
Qed.

Lemma cpoly_map_pres_mult : fun_pres_mult _ _ cpoly_map_csf.
Proof.
 unfold fun_pres_mult.
 assert (X:forall x y, cpoly_map_csf (cpoly_mult_cr _ x y)[=]cpoly_mult_cr _ (cpoly_map_csf x) (f y)).
  induction x; intros y.
   apply eq_reflexive.
  split.
   apply rh_pres_mult.
  apply IHx.
 apply (cpoly_double_ind0 R).
   intros p.
   apply eq_reflexive.
  intros p.
  change (st_car RX) in p.
  change (cpoly_zero R) with ([0]:RX).
  stepl (cpoly_map_csf ([0]:RX)).
   change (cpoly_map_csf [0]) with ([0]:SX).
   ring.
  apply csf_wd; ring. 
 intros p q c d H.
 split.
  autorewrite with ringHomPush.
  reflexivity.
 change (st_car RX) in p,q.
 change (cpoly_map_csf ((cpoly_mult_cr _ q c)[+](p[*](cpoly_linear _ d q)))
   [=](cpoly_mult_cr _ (cpoly_map_csf q) (f c))[+](cpoly_map_csf p)[*](cpoly_map_csf (cpoly_linear _ d q))).
 stepl ((cpoly_map_csf (cpoly_mult_cr R q c))[+](cpoly_map_csf (p[*]cpoly_linear R d q)));
  [| apply eq_symmetric; apply cpoly_map_pres_plus].
 apply csbf_wd.
  apply X.
 stepl (cpoly_map_csf ((cpoly_linear R d q:RX)[*]p)); [| apply csf_wd;ring].
 stepr (cpoly_map_csf (cpoly_linear R d q)[*]cpoly_map_csf p).
  2:apply (mult_commut_unfolded SX).
 change ((cpoly_linear R d q:RX)[*]p) with (cpoly_mult_fast_cs _ (cpoly_linear R d q) p).
 rewrite -> cpoly_mult_fast_equiv.
 rewrite cpoly_lin_mult.
 change (cpoly_map_csf (cpoly_linear R d q:RX)[*]cpoly_map_csf p)
   with (cpoly_mult_fast_cs _ (cpoly_linear S (f d) (cpoly_map_csf q)) (cpoly_map_csf p)).
 rewrite -> cpoly_mult_fast_equiv.
 rewrite cpoly_lin_mult.
 stepl (cpoly_map_csf (cpoly_mult_cr_cs R p d)[+]cpoly_map_csf (cpoly_linear R [0] (cpoly_mult_cs R q p)));
  [| apply eq_symmetric; apply cpoly_map_pres_plus].
 change (cpoly_map_fun (cpoly_mult_cr_cs R p d)[+] cpoly_map_fun ([0][+X*] (cpoly_mult_cs R q p))[=]
   (cpoly_mult_cr_cs S (cpoly_map_fun p) (f d))[+]
     ([0][+X*](cpoly_mult_cs S (cpoly_map_fun q) (cpoly_map_fun p)))).
 apply csbf_wd.
  apply X.
 split.
  auto with *.
 change ((cpoly_map_csf (cpoly_mult_cs R q p))[=](cpoly_mult_cs S (cpoly_map_csf q) (cpoly_map_csf p))).
 repeat setoid_rewrite <- cpoly_mult_fast_equiv.
 change (cpoly_map_csf (q[*]p)[=]cpoly_map_csf q[*]cpoly_map_csf p).
 stepr (cpoly_map_csf p[*]cpoly_map_csf q). 2: ring.
 rewrite <- H.
 apply csf_wd;ring.
Qed.

Lemma cpoly_map_pres_unit : fun_pres_unit _ _ cpoly_map_csf.
Proof.
 split.
  apply rh_pres_unit.
 constructor.
Qed.

Definition cpoly_map := Build_RingHom _ _ _ cpoly_map_pres_plus cpoly_map_pres_mult cpoly_map_pres_unit.

Lemma cpoly_map_X : cpoly_map _X_[=]_X_.
Proof.
 repeat split.
  apply rh_pres_zero.
 apply rh_pres_unit.
Qed.

Lemma cpoly_map_C : forall c, cpoly_map (_C_ c)[=]_C_ (f c).
Proof. reflexivity. Qed.

Lemma cpoly_map_diff : forall p, cpoly_map (_D_ p) [=] _D_ (cpoly_map p).
Proof.
 induction p.
  reflexivity.
 change (cpoly_map (_D_ (s[+X*]p))[=]_D_ (f s[+X*](cpoly_map p))).
 do 2 rewrite -> diff_linear.
 autorewrite with ringHomPush.
 rewrite -> IHp.
 rewrite -> cpoly_map_X.
 reflexivity.
Qed.

Lemma cpoly_map_apply : forall p x, f (p ! x)[=] (cpoly_map p) ! (f x).
Proof.
 induction p.
  intros x.
  apply rh_pres_zero.
 intros x.
 simpl in *.
 rewrite -> rh_pres_plus.
 rewrite -> rh_pres_mult.
 rewrite -> IHp.
 reflexivity.
Qed.

End Map.
Arguments cpoly_map [R S].

Lemma cpoly_map_compose : forall R S T (g:RingHom S T) (f:RingHom R S) p,
 (cpoly_map (RHcompose _ _ _ g f) p)[=]cpoly_map g (cpoly_map f p).
Proof.
 induction p.
  constructor.
 split.
  reflexivity.
 apply IHp.
Qed.

(* TODO: prove that the polynomials form a module over the ring*)
