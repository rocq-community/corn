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

(** printing Not %\ensuremath\neg% #~# *)
(** printing CNot %\ensuremath\neg% #~# *)
(** printing Iff %\ensuremath\Leftrightarrow% #&hArr;# *)
(** printing CFalse %\ensuremath\bot% #&perp;# *)
(** printing False %\ensuremath\bot% #&perp;# *)
(** printing CTrue %\ensuremath\top% *)
(** printing True %\ensuremath\top% *)
(** printing or %\ensuremath{\mathrel\vee}% *)
(** printing and %\ensuremath{\mathrel\wedge}% *)

From Coq Require Export Compare_dec.
Require Export CoRN.logic.CornBasics.
From Coq Require Export ZArith.
From Coq Require Export ZArithRing.
From Coq Require Export Wf_nat.
From Coq Require Import Lia.


(**
* Extending the Coq Logic
Because notions of apartness and order have computational meaning, we
will have to define logical connectives in [Type].  In order to
keep a syntactic distinction between types of terms, we define [CProp]
as an alias for [Type], to be used as type of (computationally meaningful)
propositions.

Falsehood and negation will typically not be needed in [CProp], as
they are used to refer to negative statements, which carry no
computational meaning.  Therefore, we will simply define a negation
operator from [Type] to [Prop] .

Conjunction, disjunction and existential quantification will have to come in
multiple varieties.  For conjunction, we will need four operators of type
[s1->s2->s3], where [s3] is [Prop] if both [s1] and [s2]
are [Prop] and [CProp] otherwise.
We here take advantage of the inclusion of [Prop] in [Type].

Disjunction is slightly different, as it will always return a value in [CProp] even
if both arguments are propositions.  This is because in general
it may be computationally important to know which of the two branches of the
disjunction actually holds.

Existential quantification will similarly always return a value in [CProp].

- [CProp]-valued conjuction will be denoted as [and];
- [Crop]-valued conjuction will be denoted as [or];
- Existential quantification will be written as [{x:A & B}] or [{x:A | B}],
according to whether [B] is respectively of type [CProp] or [Prop].

In a few specific situations we do need truth, false and negation in [CProp],
so we will also introduce them; this should be a temporary option.

Finally, for other formulae that might occur in our [CProp]-valued
propositions, such as [(le m n)], we have to introduce a [CProp]-valued
version.
*)

Notation "'CProp'":= Type.

Section Basics.
(**
** Basics
Here we treat conversion from [Prop] to [CProp] and vice versa,
and some basic connectives in [CProp].
*)

Definition True_constr := I.
  (* The name I is occasionally used for other things, hiding True's constructor. *)

Definition Not (P : CProp) := P -> False.

Definition Iff (A B : CProp) : CProp := prod (A -> B) (B -> A).

Definition proj1_sigT (A : Type) (P : A -> CProp) (e : sigT P) :=
  match e with
  | existT _ a b => a
  end.

Definition proj2_sigT (A : Type) (P : A -> CProp) (e : sigT P) :=
  match e return (P (proj1_sigT A P e)) with
  | existT _ a b => b
  end.

Inductive sig2T (A : Type) (P Q : A -> CProp) : CProp :=
    exist2T : forall x : A, P x -> Q x -> sig2T A P Q.

Definition proj1_sig2T (A : Type) (P Q : A -> CProp) (e : sig2T A P Q) :=
  match e with
  | exist2T _ _ _ a b c => a
  end.

Definition proj2a_sig2T (A : Type) (P Q : A -> CProp) (e : sig2T A P Q) :=
  match e return (P (proj1_sig2T A P Q e)) with
  | exist2T _ _ _ a b c => b
  end.

Definition proj2b_sig2T (A : Type) (P Q : A -> CProp) (e : sig2T A P Q) :=
  match e return (Q (proj1_sig2T A P Q e)) with
  | exist2T _ _ _ a b c => c
  end.

End Basics.


(* begin hide *)
Infix "or" := sum (at level 85, right associativity).

Infix "and" := prod (at level 80, right associativity).

Notation "A 'IFF' B" := (Iff A B) (at level 95, no associativity).

Notation ProjT1 := (proj1_sigT _ _).

Notation ProjT2 := (proj2_sigT _ _).
(* end hide *)

(**
Some lemmas to make it possible to use [Step]
when reasoning with bi-implications. *)

Lemma Iff_left :
  forall (A B C : CProp),
  (A IFF B) -> (A IFF C) -> (C IFF B).
Proof.
 unfold Iff.
 intuition.
Qed.

Lemma Iff_right:
  forall (A B C : CProp),
  (A IFF B) -> (A IFF C) -> (B IFF C).
Proof.
 unfold Iff.
 intuition.
Qed.

Lemma Iff_refl : forall (A : CProp), (A IFF A).
Proof.
 unfold Iff.
 intuition.
Qed.

Lemma Iff_sym :
  forall (A B : CProp),(A IFF B) -> (B IFF A).
Proof.
 unfold Iff.
 intuition.
Qed.

Lemma Iff_trans :
  forall (A B C : CProp),
  (prod (A IFF B) (B IFF C)) -> (A IFF C).
Proof.
 unfold Iff.
 intuition.
Qed.

Lemma Iff_imp_imp :
  forall (A B : CProp),
  (A IFF B) -> (prod (A->B) (B->A)).
Proof.
 unfold Iff.
 intuition.
Qed.

Declare Right Step Iff_right.
Declare Left Step Iff_left.
#[global]
Hint Resolve Iff_trans Iff_sym Iff_refl Iff_right Iff_left Iff_imp_imp : algebra.



Lemma not_r_cor_rect :
  forall (A B : CProp) (S : Type) (l r : S),
  Not B ->
  forall H : A or B,
  @sum_rect A B (fun _ : A or B => S) (fun x : A => l) (fun x : B => r) H = l.
Proof.
 intros. elim H0.
 intros. reflexivity.
  intro. elim H. assumption.
Qed.

Lemma not_l_cor_rect :
  forall (A B : CProp) (S : Type) (l r : S),
  Not A ->
  forall H : A or B,
  @sum_rect A B (fun _ : A or B => S) (fun x : A => l) (fun x : B => r) H = r.
Proof.
 intros. elim H0.
 intro. elim H. assumption.
  intros. reflexivity.
Qed.

(* begin hide *)
(** This notation is incompatible with [Program]. It should be avoided *)
Notation "{ x : A  |  P }" := (sigT (fun x : A => P):CProp)
  (at level 0, x at level 99) : type_scope.
Notation "{ x : A  |  P  |  Q }" :=
  (sig2T A (fun x : A => P) (fun x : A => Q)) (at level 0, x at level 99) :
  type_scope.

(* end hide *)

#[global]
Hint Resolve pair inl inr existT exist2T : core.

Section Choice.
(* **Choice
Let [P] be a predicate on $\NN^2$#N times N#.
*)

Variable P : nat -> nat -> Prop.

Lemma choice :
  (forall n : nat, {m : nat | P n m}) ->
  {d : nat -> nat | forall n : nat, P n (d n)}.
Proof.
 intro H.
 exists (fun i : nat => proj1_sigT _ _ (H i)).
 apply (fun i : nat => proj2_sigT _ _ (H i)).
Qed.

End Choice.

Section Logical_Remarks.

(** We prove a few logical results which are helpful to have as lemmas
when [A], [B] and [C] are non trivial.
*)

Lemma CNot_Not_or : forall A B C : CProp,
 (A -> Not C) -> (B -> Not C) -> ~ Not (A or B) -> Not C.
Proof.
 intros A B C H H0 H1.
 intro H2.
 apply H1.
 intro H3.
 elim H3.
  intro; apply H; auto.
 intro; apply H0; auto.
Qed.

Lemma CdeMorgan_ex_all : forall (A : Type) (P : A -> CProp) (X : Type),
 (sigT P -> X) -> forall a : A, P a -> X.
Proof.
 intros A P X H a H0.
 eauto.
Qed.

End Logical_Remarks.

Section CRelation_Definition.

(**
** [CProp]-valued Relations
Similar to Relations.v in Coq's standard library.

%\begin{convention}% Let [A:Type] and [R:Crelation].
%\end{convention}%
*)

Variable A : Type.

Definition Crelation := A -> A -> CProp.

Variable R : Crelation.

Definition Creflexive : CProp :=
  forall x : A, R x x.

Definition Ctransitive : CProp :=
  forall x y z : A, R x y -> R y z -> R x z.

Definition Csymmetric : CProp :=
  forall x y : A, R x y -> R y x.

Record Cequivalence : CProp :=
  {Cequiv_refl  : Creflexive;
   Cequiv_symm  : Csymmetric;
   Cequiv_trans : Ctransitive}.

Definition Cdecidable (P:CProp):= P or Not P.

End CRelation_Definition.

Fixpoint member (A : Type) (n : A) (l : list A) {struct l} : CProp :=
  match l with
  | nil => False
  | cons y m => member A n m or y = n
  end.

Arguments member [A].

Section TRelation_Definition.
(**
** [Prop]-valued Relations
Analogous.

%\begin{convention}% Let [A:Type] and [R:Trelation].
%\end{convention}%
*)

Variable A : Type.

Definition Trelation := A -> A -> Prop.

Variable R : Trelation.

Definition Treflexive : CProp := forall x : A, R x x.

Definition Ttransitive : CProp := forall x y z : A, R x y -> R y z -> R x z.

Definition Tsymmetric : CProp := forall x y : A, R x y -> R y x.

Definition Tequiv : CProp := Treflexive and Ttransitive and Tsymmetric.

End TRelation_Definition.

Section le_odd.

(**
** The relation [le], [lt], [odd] and [even] in [CProp]
*)

Inductive Cle (n : nat) : nat -> CProp :=
  | Cle_n : Cle n n
  | Cle_S : forall m : nat, Cle n m -> Cle n (S m).

Theorem Cnat_double_ind : forall R : nat -> nat -> CProp,
 (forall n : nat, R 0 n) -> (forall n : nat, R (S n) 0) ->
 (forall n m : nat, R n m -> R (S n) (S m)) -> forall n m : nat, R n m.
Proof.
 simple induction n; auto.
 simple induction m; auto.
Qed.

Theorem my_Cle_ind : forall (n : nat) (P : nat -> CProp),
 P n -> (forall m : nat, Cle n m -> P m -> P (S m)) ->
 forall n0 : nat, Cle n n0 -> P n0.
Proof.
 intros n P.
 generalize (Cle_rect n (fun (n0 : nat) (H : Cle n n0) => P n0)); intro.
 assumption.
Qed.

Theorem Cle_n_S : forall n m : nat, Cle n m -> Cle (S n) (S m).
Proof.
 intros n m H.
 pattern m in |- *.
 apply (my_Cle_ind n).
   apply Cle_n.
  intros.
  apply Cle_S.
  assumption.
 assumption.
Qed.

Lemma toCle : forall m n : nat, m <= n -> Cle m n.
Proof.
 intros m.
 induction  m as [| m Hrecm].
  simple induction n.
   intro H.
   apply Cle_n.
  intros n0 H H0.
  apply Cle_S.
  apply H.
  apply Nat.le_0_l.
 simple induction n.
  intro.
  exfalso.
  inversion H.
 intros n0 H H0.
 generalize (le_S_n _ _ H0); intro H1.
 generalize (Hrecm _ H1); intro H2.
 apply Cle_n_S.
 assumption.
Qed.

Hint Resolve toCle.

Lemma Cle_to : forall m n : nat, Cle m n -> m <= n.
Proof.
 intros m n H.
 elim H.
  apply le_n.
 intros m0 s H0.
 apply le_S.
 assumption.
Qed.

Definition Clt (m n : nat) : CProp := Cle (S m) n.

Lemma toCProp_lt : forall m n : nat, m < n -> Clt m n.
Proof.
 unfold lt in |- *.
 unfold Clt in |- *.
 intros m n H.
 apply toCle.
 assumption.
Qed.

Lemma Clt_to : forall m n : nat, Clt m n -> m < n.
Proof.
 unfold lt in |- *.
 unfold Clt in |- *.
 intros m n H.
 apply Cle_to.
 assumption.
Qed.

Lemma Cle_le_S_eq : forall p q : nat, p <= q -> {S p <= q} + {p = q}.
Proof.
 intros p q H.
 elim (gt_eq_gt_dec p q); intro H0.
  elim H0; auto.
 exfalso.
 apply Nat.lt_nge with q p; auto.
Qed.

Lemma Cnat_total_order : forall m n : nat, m <> n -> {m < n} + {n < m}.
Proof.
 intros m n H.
 elim (gt_eq_gt_dec m n).
  intro H0.
  elim H0; intros.
   left; auto.
  exfalso.
  auto.
 auto.
Qed.


(** For compatibility with Coq.8.14 and Coq.8.15: this can be removed and
    changed with Nat.Even_Odd_dec when the minimal version is bumped to 8.16 *)
Lemma Even_Odd_dec (n : nat) : {Nat.Even n} + {Nat.Odd n}.
Proof.
  destruct (Nat.even n) eqn:E.
  - left; apply Nat.even_spec; exact E.
  - right; apply Bool.negb_true_iff in E; rewrite Nat.negb_even in E.
    apply Nat.odd_spec; exact E.
Qed.

Inductive Codd : nat -> CProp :=
    Codd_S : forall n : nat, Ceven n -> Codd (S n)
with Ceven : nat -> CProp :=
  | Ceven_O : Ceven 0
  | Ceven_S : forall n : nat, Codd n -> Ceven (S n).

Lemma Codd_even_to : forall n : nat, (Codd n -> Nat.Odd n) /\ (Ceven n -> Nat.Even n).
Proof.
 simple induction n.
  split.
   intro H.
   inversion H.
  intro.
  now exists 0.
 intros n0 H.
 elim H; intros H0 H1.
 split.
  intro H2.
  inversion H2.
  apply Nat.Odd_succ.
  apply H1.
  assumption.
 intro H2.
 inversion H2.
 apply Nat.Even_succ.
 apply H0.
 assumption.
Qed.

Lemma Codd_to : forall n : nat, Codd n -> Nat.Odd n.
Proof.
 intros n H.
 elim (Codd_even_to n); auto.
Qed.

Lemma Ceven_to : forall n : nat, Ceven n -> Nat.Even n.
Proof.
 intros n H.
 elim (Codd_even_to n); auto.
Qed.

Lemma to_Codd_even : forall n : nat, (Nat.Odd n -> Codd n) and (Nat.Even n -> Ceven n).
Proof.
 induction n as [| n IH]; split.
 - intros H%Nat.odd_spec; discriminate H.
 - intros _; exact Ceven_O.
 - now intros H%Nat.Odd_succ; apply IH in H; apply Codd_S.
 - now intros H%Nat.Even_succ; apply IH in H; apply Ceven_S.
Qed.

Lemma to_Codd : forall n : nat, Nat.Odd n -> Codd n.
Proof.
 intros.
 elim (to_Codd_even n); auto.
Qed.

Lemma to_Ceven : forall n : nat, Nat.Even n -> Ceven n.
Proof.
 intros.
 elim (to_Codd_even n); auto.
Qed.

End le_odd.

Section Misc.

(**
** Miscellaneous
*)

Lemma CZ_exh : forall z : Z, {n : nat | z = n} or {n : nat | z = (- n)%Z}.
Proof.
 intro z.
 elim z.
   left.
   exists 0.
   auto.
  intro p.
  left.
  exists (nat_of_P p).
  rewrite convert_is_POS.
  reflexivity.
 intro p.
 right.
 exists (nat_of_P p).
 rewrite min_convert_is_NEG.
 reflexivity.
Qed.

Lemma Cnats_Z_ind : forall P : Z -> CProp,
 (forall n : nat, P n) -> (forall n : nat, P (- n)%Z) -> forall z : Z, P z.
Proof.
 intros P H H0 z.
 elim (CZ_exh z); intros H1.
  elim H1; intros n H2.
  rewrite H2.
  apply H.
 elim H1; intros n H2.
 rewrite H2.
 apply H0.
Qed.

Lemma Cdiff_Z_ind : forall P : Z -> CProp,
 (forall m n : nat, P (m - n)%Z) -> forall z : Z, P z.
Proof.
 intros P H z.
 apply Cnats_Z_ind.
  intro n.
  replace (Z_of_nat n) with (n - 0%nat)%Z.
   apply H.
  simpl in |- *.
  auto with zarith.
 intro n.
 replace (- n)%Z with (0%nat - n)%Z.
  apply H.
 simpl in |- *.
 reflexivity.
Qed.

Lemma Cpred_succ_Z_ind : forall P : Z -> CProp,
 P 0%Z -> (forall n : Z, P n -> P (n + 1)%Z) ->
 (forall n : Z, P n -> P (n - 1)%Z) -> forall z : Z, P z.
Proof.
 intros P H H0 H1 z.
 apply Cnats_Z_ind.
  intro n.
  elim n.
   exact H.
  intros n0 H2.
  replace (S n0:Z) with (n0 + 1)%Z.
   apply H0.
   assumption.
  rewrite Znat.inj_S.
  reflexivity.
 intro n.
 elim n.
  exact H.
 intros n0 H2.
 replace (- S n0)%Z with (- n0 - 1)%Z.
  apply H1.
  assumption.
 rewrite Znat.inj_S.
 unfold Z.succ in |- *.
 rewrite Zopp_plus_distr.
 reflexivity.
Qed.

Lemma not_r_sum_rec : forall (A B S : Set) (l r : S), Not B -> forall H : A + B,
 sum_rec (fun _ : A + B => S) (fun x : A => l) (fun x : B => r) H = l.
Proof.
 intros A B S l r H H0. elim H0.
 intro a. reflexivity.
  intro b. elim H. assumption.
Qed.

Lemma not_l_sum_rec : forall (A B S : Set) (l r : S), Not A -> forall H : A + B,
 sum_rec (fun _ : A + B => S) (fun x : A => l) (fun x : B => r) H = r.
Proof.
 intros A B S l r H H0. elim H0.
 intro a. elim H. assumption.
  intros. reflexivity.
Qed.

(**
%\begin{convention}%
Let [M:Type].
%\end{convention}%
*)

Variable M : Type.

Lemma member_app :
  forall (x : M) (l k : (list M)),
  (Iff (member x (app k l))
       ((member x k) or (member x l))).
Proof.
 induction k; firstorder.
Qed.

End Misc.

(**
** Results about the natural numbers

We now define a class of predicates on a finite subset of natural
numbers that will be important throughout all our work.  Essentially,
these are simply setoid predicates, but for clarity we will never
write them in that form but we will single out the preservation of the
setoid equality.
*)

Definition nat_less_n_pred (n : nat) (P : forall i : nat, i < n -> CProp) :=
  forall i j : nat, i = j -> forall (H : i < n) (H' : j < n), P i H -> P j H'.

Definition nat_less_n_pred' (n : nat) (P : forall i : nat, i <= n -> CProp) :=
  forall i j : nat, i = j -> forall (H : i <= n) (H' : j <= n), P i H -> P j H'.

Arguments nat_less_n_pred [n].
Arguments nat_less_n_pred' [n].

Section Odd_and_Even.

(**
For our work we will many times need to distinguish cases between even or odd numbers.
We begin by proving that this case distinction is decidable.
Next, we prove the usual results about sums of even and odd numbers:
*)

Lemma even_plus_n_n : forall n : nat, Nat.Even (n + n).
Proof.
 intros n; replace (n + n) with (Nat.double n) by reflexivity.
 now rewrite Nat.double_twice; exists n.
Qed.

Lemma even_or_odd_plus : forall k : nat, {j : nat &  {k = j + j} + {k = S (j + j)}}.
Proof.
 induction k as [| k IH].
 - exists 0; left; reflexivity.
 - destruct IH as [j [H | H]].
   + now exists j; right; rewrite H.
   + now exists (S j); left; rewrite H, Nat.add_succ_r.
Qed.

(** Finally, we prove that an arbitrary natural number can be written in some canonical way.
*)

Lemma even_or_odd_plus_gt : forall i j : nat,
 i <= j -> {k : nat &  {j = i + (k + k)} + {j = i + S (k + k)}}.
Proof.
 intros i j H.
 destruct (even_or_odd_plus (j - i)) as [k [Hk | Hk]]; exists k.
 destruct (Nat.eq_dec k 0) as [-> | I].
 - left; rewrite Nat.add_0_r; rewrite Nat.add_0_r in Hk.
   now apply Nat.sub_0_le in Hk; apply Nat.le_antisymm.
 - left; apply Nat.add_sub_eq_nz in Hk; [| now intros [C _]%Nat.eq_add_0].
   exact (eq_sym Hk).
 - right; apply Nat.add_sub_eq_nz in Hk; [| now intros C].
   exact (eq_sym Hk).
Qed.

End Odd_and_Even.

#[global]
Hint Resolve even_plus_n_n: arith.
#[global]
Hint Resolve toCle: core.

Section Natural_Numbers.

(**
** Algebraic Properties

We now present a series of trivial things proved with [Lia] that are
stated as lemmas to make proofs shorter and to aid in auxiliary
definitions.  Giving a name to these results allows us to use them in
definitions keeping conciseness.
*)

Lemma Clt_le_weak : forall i j : nat, Clt i j -> Cle i j.
Proof.
 intros.
 apply toCle; apply Nat.lt_le_incl; apply Clt_to; assumption.
Qed.

Lemma lt_5 : forall i n : nat, i < n -> pred i < n.
Proof.
 intros; apply Nat.le_lt_trans with (pred n).
  apply Nat.pred_le_mono; auto with arith.
 apply Nat.lt_pred_l; apply Nat.neq_0_lt_0. apply Nat.le_lt_trans with i; auto with arith.
Qed.

Lemma lt_8 : forall m n : nat, m < pred n -> m < n.
Proof.
 intros; apply Nat.lt_le_trans with (pred n); auto with arith.
Qed.

Lemma pred_lt : forall m n : nat, m < pred n -> S m < n.
Proof.
 intros; apply Nat.le_lt_trans with (pred n); auto with arith.
 apply Nat.lt_pred_l; apply Nat.neq_0_lt_0. apply Nat.le_lt_trans with m.
  auto with arith.
 apply Nat.lt_le_trans with (pred n); auto with arith.
Qed.

Lemma lt_10 : forall i m n : nat,
 0 < i -> i < pred (m + n) -> pred i < pred m + pred n.
Proof.
 intros; lia.
Qed.

Lemma lt_pred' : forall m n : nat, 0 < m -> m < n -> pred m < pred n.
Proof.
 intros m n H H0; red in |- *.
 destruct n.
  inversion H0.
 rewrite (Nat.lt_succ_pred 0 m); auto.
 simpl in |- *.
 auto with arith.
Qed.

Lemma le_1 : forall m n : nat, Cle m n -> pred m <= n.
Proof.
 intros.
 cut (m <= n); [ intro | apply Cle_to; assumption ].
 apply Nat.le_trans with (pred n); auto with arith.
 apply Nat.pred_le_mono; auto.
Qed.

Lemma le_2 : forall i j : nat, i < j -> i <= pred j.
Proof.
 intros; lia.
Qed.

Lemma plus_eq_one_imp_eq_zero : forall m n : nat,
 m + n <= 1 -> {m = 0} + {n = 0}.
Proof.
 intros m n H.
 elim (le_lt_dec m 0); intro.
  left; auto with arith.
 right; lia.
Qed.

Lemma not_not_lt : forall i j : nat, ~ ~ i < j -> i < j.
Proof.
 intros; lia.
Qed.

Lemma plus_pred_pred_plus :
  forall i j k,
  k <= pred i + pred j ->
  k <= pred (i + j).
Proof.
 intros; lia.
Qed.

(** We now prove some properties of functions on the natural numbers.

%\begin{convention}% Let [H:nat->nat].
%\end{convention}%
*)

Variable h : nat -> nat.

(**
First we characterize monotonicity by a local condition: if [h(n) < h(n+1)]
for every natural number [n] then [h] is monotonous.  An analogous result
holds for weak monotonicity.
*)

Lemma nat_local_mon_imp_mon :
  (forall i : nat, h i < h (S i)) ->
  forall i j : nat, i < j -> h i < h j.
Proof.
 intros H i j H0.
 induction  j as [| j Hrecj].
  exfalso; lia.
 cut (i <= j); [ intro H1 | auto with arith ].
 elim (le_lt_eq_dec _ _ H1); intro H2.
  cut (h i < h j); [ intro | apply Hrecj; assumption ].
  cut (h j < h (S j)); [ intro | apply H ].
  apply Nat.lt_trans with (h j); auto.
 rewrite H2; apply H.
Qed.

Lemma nat_local_mon_imp_mon_le :
  (forall i : nat, h i <= h (S i)) ->
  forall i j : nat, i <= j -> h i <= h j.
Proof.
 intros H i j H0.
 induction  j as [| j Hrecj].
  cut (i = 0); [ intro H1 | auto with arith ].
  rewrite H1; apply le_n.
 elim (le_lt_eq_dec _ _ H0); intro H1.
  cut (h i <= h j); [ intro | apply Hrecj; auto with arith ].
  cut (h j <= h (S j)); [ intro | apply H ].
  apply Nat.le_trans with (h j); auto.
 rewrite H1; apply le_n.
Qed.

(** A strictly increasing function is injective: *)

Lemma nat_mon_imp_inj : (forall i j : nat, i < j -> h i < h j) ->
 forall i j : nat, h i = h j -> i = j.
Proof.
 intros H i j H0.
 cut (~ i <> j); [ lia | intro H1 ].
 cut (i < j \/ j < i); [ intro H2 | lia ].
 inversion_clear H2.
  cut (h i < h j); [ rewrite H0; apply Nat.lt_irrefl | apply H; assumption ].
 cut (h j < h i); [ rewrite H0; apply Nat.lt_irrefl | apply H; assumption ].
Qed.

(** And (not completely trivial) a function that preserves [lt] also preserves [le]. *)

Lemma nat_mon_imp_mon' : (forall i j : nat, i < j -> h i < h j) ->
 forall i j : nat, i <= j -> h i <= h j.
Proof.
 intros H i j H0.
 elim (le_lt_eq_dec _ _ H0); intro H1.
  apply Nat.lt_le_incl; apply H; assumption.
 rewrite H1; apply le_n.
Qed.

(**
The last lemmas in this section state that a monotonous function in the
 natural numbers completely covers the natural numbers, that is, for every
natural number [n] there is an [i] such that [h(i) <= n<(n+1) <= h(i+1)].
These are useful for integration.
*)

Lemma mon_fun_covers : (forall i j, i < j -> h i < h j) -> h 0 = 0 ->
 forall n, {k : nat | S n <= h k} -> {i : nat | h i <= n | S n <= h (S i)}.
Proof.
 intros H H0 n H1.
 elim H1; intros k Hk.
 induction  k as [| k Hreck].
  exists 0.
   rewrite H0; auto with arith.
  cut (h 0 < h 1); [ intro; apply Nat.le_trans with (h 0); auto with arith | apply H; apply Nat.lt_succ_diag_r ].
 cut (h k < h (S k)); [ intro H2 | apply H; apply Nat.lt_succ_diag_r ].
 elim (le_lt_dec (S n) (h k)); intro H3.
  elim (Hreck H3); intros i Hi.
  exists i; assumption.
 exists k; auto with arith.
Qed.

Lemma weird_mon_covers : forall n (f : nat -> nat), (forall i, f i < n -> f i < f (S i)) ->
 {m : nat | n <= f m | forall i, i < m -> f i < n}.
Proof.
 intros; induction  n as [| n Hrecn].
  exists 0.
   auto with arith.
  intros; inversion H0.
 elim Hrecn.
  2: auto.
 intros m Hm Hm'.
 elim (le_lt_eq_dec _ _ Hm); intro.
  exists m.
   assumption.
  auto with arith.
 exists (S m).
  apply Nat.le_lt_trans with (f m).
   rewrite b; auto with arith.
  apply H.
  rewrite b; apply Nat.lt_succ_diag_r.
 intros.
 elim (le_lt_eq_dec _ _ H0); intro.
  auto with arith.
 cut (i = m); [ intro | auto ].
 rewrite b; rewrite <- H1.
 apply Nat.lt_succ_diag_r.
Qed.

End Natural_Numbers.

(**
Useful for the Fundamental Theorem of Algebra.
*)

Lemma kseq_prop :
  forall (k : nat -> nat) (n : nat),
  (forall i : nat, 1 <= k i /\ k i <= n) ->
  (forall i : nat, k (S i) <= k i) ->
  {j : nat | S j < 2 * n /\ k j = k (S j) /\ k (S j) = k (S (S j))}.
Proof.
 intros k n.
 generalize k; clear k.
 induction  n as [| n Hrecn]; intros k H H0.
  elim (H 0); intros H1 H2.
  generalize (Nat.le_trans _ _ _ H1 H2); intro H3.
  exfalso.
  inversion H3.
 elim (eq_nat_dec (k 0) (k 2)).
  intro H1.
  exists 0.
  cut (k 0 = k 1).
   intro H2.
   repeat split.
     lia.
    assumption.
   rewrite <- H1.
   auto.
  apply Nat.le_antisymm.
   rewrite H1.
   apply H0.
  apply H0.
 intro H1.
 elim (Hrecn (fun m : nat => k (S (S m)))).
   3: intro; apply H0.
  intros m Hm.
  exists (S (S m)); lia.
 intro i.
 split.
  elim (H (S (S i))); auto.
 elim (lt_eq_lt_dec (k 0) (k 2)); intro H2.
  elim H2; intro H3.
   generalize (H0 0); intro H4.
   generalize (H0 1); intro H5.
   lia.
  tauto.
 generalize (H 0); intro H3.
 elim H3; intros H4 H5.
 generalize (Nat.lt_le_trans _ _ _ H2 H5); intro H6.
 cut (k 2 <= n).
  2: lia.
 intro H7.
 induction  i as [| i Hreci].
  assumption.
 apply Nat.le_trans with (k (S (S i))); auto.
Qed.

Section Predicates_to_CProp.

(**
** Logical Properties

This section contains lemmas that aid in logical reasoning with
natural numbers.  First, we present some principles of induction, both
for [CProp]- and [Prop]-valued predicates.  We begin by presenting the
results for [CProp]-valued predicates:
*)

Lemma even_induction :
  forall P : nat -> CProp,
  P 0 ->
  (forall n, Nat.Even n -> P n -> P (S (S n))) ->
  forall n, Nat.Even n -> P n.
Proof.
 intros P H0 H n; induction n as [n IH] using Wf_nat.lt_wf_rect.
 destruct n as [| n].
 - intros _; exact H0.
 - destruct n as [| n].
   + intros C%Nat.even_spec; discriminate C.
   + intros Hn; apply ->Nat.Even_succ_succ in Hn.
     apply H; [exact Hn |].
     apply IH; [| exact Hn].
     apply Nat.lt_trans with (1 := Nat.lt_succ_diag_r n).
     exact (Nat.lt_succ_diag_r _).
Qed.

Lemma odd_induction :
  forall P : nat -> CProp,
  P 1 ->
  (forall n, Nat.Odd n -> P n -> P (S (S n))) ->
  forall n, Nat.Odd n -> P n.
Proof.
 intros P H1 H [| n] Hn.
 - apply Nat.odd_spec in Hn; discriminate Hn.
 - apply (even_induction (fun n => P (S n))).
   + exact H1.
   + now intros k Hk; apply H, Nat.Odd_succ.
   + now apply Nat.Odd_succ.
Qed.

Lemma four_induction :
  forall P : nat -> CProp,
  P 0 -> P 1 -> P 2 -> P 3 ->
  (forall n, P n -> P (S (S (S (S n))))) ->
  forall n, P n.
Proof.
 intros.
 apply lt_wf_rect.
 intro m.
 case m; auto.
 clear m; intro m.
 case m; auto.
 clear m; intro m.
 case m; auto.
 clear m; intro m.
 case m; auto with arith.
Qed.

Lemma nat_complete_double_induction : forall P : nat -> nat -> CProp,
 (forall m n, (forall m' n', m' < m -> n' < n -> P m' n') -> P m n) -> forall m n, P m n.
Proof.
 intros P H m.
 pattern m in |- *; apply lt_wf_rect; auto with arith.
Qed.

Lemma odd_double_ind : forall P : nat -> CProp, (forall n, Nat.Odd n -> P n) ->
 (forall n, 0 < n -> P n -> P (Nat.double n)) -> forall n, 0 < n -> P n.
Proof.
 assert (forall n : nat, 0 < Nat.double n -> 0 < n) as H. {
  unfold Nat.double; intros [| n]; simpl; [intros []%Nat.lt_irrefl |].
  intros _; exact (Nat.lt_0_succ _).
 }
 intro. intro H0. intro H1. intro n.
 pattern n in |- *.
 apply lt_wf_rect. intros n0 H2 H3.
 pose proof (even_or_odd_plus n0) as [k [Hk | Hk]].
 - assert (0 < k) as I. {
    apply H; unfold Nat.double; rewrite <-Hk; exact H3.
   }
   rewrite Hk; apply H1; [exact I |].
   apply H2. lia. exact I.
 - apply H0. exists k. lia.
Qed.

(** For subsetoid predicates in the natural numbers we can eliminate
disjunction (and existential quantification) as follows.
*)

Lemma finite_or_elim :
  forall (n : nat) (P Q : forall i, i <= n -> CProp),
  nat_less_n_pred' P ->
  nat_less_n_pred' Q ->
  (forall i H, P i H or Q i H) ->
  {m : nat | {Hm : m <= n | P m Hm}} or (forall i H, Q i H).
Proof.
 intro n; induction  n as [| n Hrecn].
  intros P Q HP HQ H.
  elim (H _ (le_n 0)); intro H0.
   left; exists 0; exists (le_n 0); assumption.
  right; intros i H1.
  apply HQ with (H := le_n 0); auto with arith.
 intros P Q H H0 H1.
 elim (H1 _ (le_n (S n))); intro H2.
  left; exists (S n); exists (le_n (S n)); assumption.
 set (P' := fun (i : nat) (H : i <= n) => P i (le_S _ _ H)) in *.
 set (Q' := fun (i : nat) (H : i <= n) => Q i (le_S _ _ H)) in *.
 cut ({m : nat | {Hm : m <= n | P' m Hm}} or (forall (i : nat) (H : i <= n), Q' i H)).
  intro H3; elim H3; intro H4.
   left.
   elim H4; intros m Hm; elim Hm; clear H4 Hm; intros Hm Hm'.
   exists m.
   unfold P' in Hm'.
   exists (le_S _ _ Hm).
   eapply H with (i := m); [ lia | apply Hm' ].
  right.
  intros i H5.
  unfold Q' in H4.
  elim (le_lt_eq_dec _ _ H5); intro H6.
   cut (i <= n); [ intro | auto with arith ].
   eapply H0 with (i := i); [ auto with arith | apply (H4 i H7) ].
  eapply H0 with (i := S n); [ auto with arith | apply H2 ].
 apply Hrecn.
   intro i; intros j H3 H4 H5 H6.
   unfold P' in |- *.
   exact (H _ _ H3 _ _ H6).
  intro i; intros j H3 H4 H5 H6.
  unfold Q' in |- *.
  exact (H0 _ _ H3 _ _ H6).
 intros i H3.
 unfold P', Q' in |- *; apply H1.
Qed.

Lemma str_finite_or_elim :
  forall (n : nat) (P Q : forall i, i <= n -> CProp),
  nat_less_n_pred' P ->
  nat_less_n_pred' Q ->
  (forall i H, P i H or Q i H) ->
  {j : nat | {Hj : j <= n | P j Hj and (forall j' Hj', j' < j -> Q j' Hj')}}
  or (forall i H, Q i H).
Proof.
 intro n; induction  n as [| n Hrecn].
  intros P Q H H0 H1.
  elim (H1 0 (le_n 0)); intro HPQ.
   left.
   exists 0; exists (le_n 0).
   split.
    apply H with (H := le_n 0); auto.
   intros; exfalso; inversion H2.
  right; intros.
  apply H0 with (H := le_n 0); auto with arith.
 intros P Q H H0 H1.
 set (P' := fun (i : nat) (H : i <= n) => P i (le_S _ _ H)) in *.
 set (Q' := fun (i : nat) (H : i <= n) => Q i (le_S _ _ H)) in *.
 elim (Hrecn P' Q').
     intro H2.
     left.
     elim H2; intros m Hm; elim Hm; clear H2 Hm; intros Hm Hm'.
     exists m.
     unfold P' in Hm'.
     exists (le_S _ _ Hm).
     elim Hm'; clear Hm'; intros Hm' Hj.
     split.
      eapply H with (i := m); [ auto with arith | apply Hm' ].
     unfold Q' in Hj; intros j' Hj' H2.
     cut (j' <= n); [ intro H4 | apply Nat.le_trans with m; auto with arith ].
     apply H0 with (H := le_S _ _ H4); [ auto | apply Hj; assumption ].
    elim (H1 (S n) (le_n (S n))); intro H1'.
     intro H2.
     left; exists (S n); exists (le_n (S n)); split.
      assumption.
     intros j' Hj' H3; unfold Q' in H1'.
     cut (j' <= n); [ intro H4 | auto with arith ].
     unfold Q' in H2.
     apply H0 with (H := le_S _ _ H4); auto.
    intro H2.
    right; intros i H3.
    unfold Q' in H1'.
    elim (le_lt_eq_dec _ _ H3); intro H4.
     cut (i <= n); [ intro H5 | auto with arith ].
     unfold Q' in H2.
     apply H0 with (H := le_S _ _ H5); auto.
    apply H0 with (H := le_n (S n)); auto.
   intro i; intros j H2 H3 H4 H5.
   unfold P' in |- *.
   exact (H _ _ H2 _ _ H5).
  intro i; intros j H2 H3 H4 H5.
  unfold Q' in |- *.
  exact (H0 _ _ H2 _ _ H5).
 intros i H2.
 unfold P', Q' in |- *.
 apply H1.
Qed.

End Predicates_to_CProp.

Section Predicates_to_Prop.

(** Finally, analogous results for [Prop]-valued predicates are presented for
completeness's sake.
*)

Lemma even_ind : forall P : nat -> Prop,
 P 0 -> (forall n, Nat.Even n -> P n -> P (S (S n))) -> forall n, Nat.Even n -> P n.
Proof. now intros P; apply even_induction. Qed.

(* NOTE: this statement is not consistent with odd_induction, is it intended? *)
Lemma odd_ind : forall P : nat -> Prop,
 P 1 -> (forall n, P n -> P (S (S n))) -> forall n, Nat.Odd n -> P n.
Proof.
  intros P H1 H n Hn; apply odd_induction; [exact H1 | |].
  - now intros k _; apply H.
  - exact Hn.
Qed.

Lemma nat_complete_double_ind :
  forall P : nat -> nat -> Prop,
  (forall m n, (forall m' n', m' < m -> n' < n -> P m' n') -> P m n) ->
  forall m n, P m n.
Proof.
 intros P H m.
 pattern m in |- *; apply lt_wf_ind; auto.
Qed.

Lemma four_ind :
  forall P : nat -> Prop,
  P 0 -> P 1 -> P 2 -> P 3 ->
  (forall n, P n -> P (S (S (S (S n))))) -> forall n, P n.
Proof.
 intros.
 apply lt_wf_ind.
 intro m.
 case m; auto.
 clear m; intro m.
 case m; auto.
 clear m; intro m.
 case m; auto.
 clear m; intro m.
 case m; auto with arith.
Qed.

End Predicates_to_Prop.

(**
** Integers

Similar results for integers.
*)

(* begin hide *)
Tactic Notation "ElimCompare" constr(c) constr(d) :=  elim_compare c d.
(* end hide *)

Definition Zlts (x y : Z) := eq (A:=Datatypes.comparison) (x ?= y)%Z Datatypes.Lt.

Lemma toCProp_Zlt : forall x y : Z, (x < y)%Z -> Zlts x y.
Proof.
 intros x y H.
 unfold Zlts in |- *.
 unfold Z.lt in H.
 auto.
Qed.

Lemma CZlt_to : forall x y : Z, Zlts x y -> (x < y)%Z.
Proof.
 intros x y H.
 unfold Z.lt in |- *.
 inversion H.
 auto.
Qed.

Lemma Zsgn_1 : forall x : Z, {Z.sgn x = 0%Z} + {Z.sgn x = 1%Z} + {Z.sgn x = (-1)%Z}.
Proof.
 intro x.
 case x.
   left.
   left.
   unfold Z.sgn in |- *.
   reflexivity.
  intro p.
  simpl in |- *.
  left.
  right.
  reflexivity.
 intro p.
 right.
 simpl in |- *.
 reflexivity.
Qed.

Lemma Zsgn_2 : forall x : Z, Z.sgn x = 0%Z -> x = 0%Z.
Proof.
 intro x.
 case x.
   intro H.
   reflexivity.
  intros p H.
  inversion H.
 intros p H.
 inversion H.
Qed.

Lemma Zsgn_3 : forall x : Z, x <> 0%Z -> Z.sgn x <> 0%Z.
Proof.
 intro x.
 case x.
   intro H.
   elim H.
   reflexivity.
  intros p H.
  simpl in |- *.
  discriminate.
 intros p H.
 simpl in |- *.
 discriminate.
Qed.

(** The following have unusual names, in line with the series of lemmata in
fast_integers.v.
*)

Lemma ZL4' : forall y : positive, {h : nat | nat_of_P y = S h}.
Proof.
 simple induction y; [ intros p H; elim H; intros x H1; exists (S x + S x);
   unfold nat_of_P in |- *; simpl in |- *; rewrite ZL0;
     rewrite Pmult_nat_r_plus_morphism; unfold nat_of_P in H1; rewrite H1; auto with arith
       | intros p H1; elim H1; intros x H2; exists (x + S x);
         unfold nat_of_P in |- *; simpl in |- *; rewrite ZL0;
           rewrite Pmult_nat_r_plus_morphism; unfold nat_of_P in H2; rewrite H2; auto with arith
             | exists 0; auto with arith ].
Qed.

Lemma ZL9 : forall p : positive, Z_of_nat (nat_of_P p) = Zpos p.
Proof.
 intro p.
 elim (ZL4 p).
 intros x H0.
 rewrite H0.
 unfold Z_of_nat in |- *.
 apply f_equal with (A := positive) (B := Z) (f := Zpos).
 cut (P_of_succ_nat (nat_of_P p) = P_of_succ_nat (S x)).
  intro H1.
  rewrite P_of_succ_nat_o_nat_of_P_eq_succ in H1.
  cut (Pos.pred (Pos.succ p) = Pos.pred (P_of_succ_nat (S x))).
   intro H2.
   rewrite Pos.pred_succ in H2.
   simpl in H2.
   rewrite Pos.pred_succ in H2.
   auto.
  apply f_equal with (A := positive) (B := positive) (f := Pos.pred).
  assumption.
 apply f_equal with (f := P_of_succ_nat).
 assumption.
Qed.

Theorem Zsgn_4 : forall a : Z, a = (Z.sgn a * Z.abs_nat a)%Z.
Proof.
 intro a.
 case a.
   simpl in |- *.
   reflexivity.
  intro p.
  unfold Z.sgn in |- *.
  unfold Z.abs_nat in |- *.
  rewrite Zmult_1_l.
  symmetry  in |- *.
  apply ZL9.
 intro p.
 unfold Z.sgn in |- *.
 unfold Z.abs_nat in |- *.
 rewrite ZL9.
 constructor.
Qed.

Theorem Zsgn_5 : forall a b x y : Z, x <> 0%Z -> y <> 0%Z ->
 (Z.sgn a * x)%Z = (Z.sgn b * y)%Z -> (Z.sgn a * y)%Z = (Z.sgn b * x)%Z.
Proof.
 intros a b x y H H0.
 case a.
   case b.
     simpl in |- *.
     trivial.
    intro p.
    unfold Z.sgn in |- *.
    intro H1.
    rewrite Zmult_1_l in H1.
    simpl in H1.
    elim H0.
    auto.
   intro p.
   unfold Z.sgn in |- *.
   intro H1.
   elim H0.
   apply Z.opp_inj.
   simpl in |- *.
   transitivity (-1 * y)%Z; auto.
  intro p.
  unfold Z.sgn at 1 in |- *.
  unfold Z.sgn at 2 in |- *.
  intro H1.
  transitivity y.
   rewrite Zmult_1_l.
   reflexivity.
  transitivity (Z.sgn b * (Z.sgn b * y))%Z.
   case (Zsgn_1 b).
    intro H2.
    case H2.
     intro H3.
     elim H.
     rewrite H3 in H1.
     change ((1 * x)%Z = 0%Z) in H1.
     rewrite Zmult_1_l in H1.
     assumption.
    intro H3.
    rewrite H3.
    rewrite Zmult_1_l.
    rewrite Zmult_1_l.
    reflexivity.
   intro H2.
   rewrite H2.
   ring.
  rewrite Zmult_1_l in H1.
  rewrite H1.
  reflexivity.
 intro p.
 unfold Z.sgn at 1 in |- *.
 unfold Z.sgn at 2 in |- *.
 intro H1.
 transitivity (Z.sgn b * (-1 * (Z.sgn b * y)))%Z.
  case (Zsgn_1 b).
   intro H2.
   case H2.
    intro H3.
    elim H.
    apply Z.opp_inj.
    transitivity (-1 * x)%Z.
     ring.
    unfold Z.opp in |- *.
    rewrite H3 in H1.
    transitivity (0 * y)%Z; auto.
   intro H3.
   rewrite H3.
   ring.
  intro H2.
  rewrite H2.
  ring.
 rewrite <- H1.
 ring.
Qed.


Lemma nat_nat_pos : forall m n : nat, ((m + 1) * (n + 1) > 0)%Z.
Proof.
 intros m n.
 apply Z.lt_gt.
 cut (Z_of_nat m + 1 > 0)%Z.
  intro H.
  cut (0 < Z_of_nat n + 1)%Z.
   intro H0.
   cut ((Z_of_nat m + 1) * 0 < (Z_of_nat m + 1) * (Z_of_nat n + 1))%Z.
    rewrite Zmult_0_r.
    auto.
   apply Zlt_reg_mult_l; auto.
  change (0 < Z.succ (Z_of_nat n))%Z in |- *.
  apply Zle_lt_succ.
  change (Z_of_nat 0 <= Z_of_nat n)%Z in |- *.
  apply Znat.inj_le.
  apply Nat.le_0_l.
 apply Z.lt_gt.
 change (0 < Z.succ (Z_of_nat m))%Z in |- *.
 apply Zle_lt_succ.
 change (Z_of_nat 0 <= Z_of_nat m)%Z in |- *.
 apply Znat.inj_le.
 apply Nat.le_0_l.
Qed.

Theorem S_predn : forall m : nat, m <> 0 -> S (pred m) = m.
Proof.
 intros m H.
 symmetry  in |- *.
 symmetry; apply Nat.lt_succ_pred with 0.
 lia.
Qed.

Lemma absolu_1 : forall x : Z, Z.abs_nat x = 0 -> x = 0%Z.
Proof.
 intros x H.
 case (dec_eq x 0).
  auto.
 intro H0.
 apply False_ind.
 ElimCompare x 0%Z.
   intro H2.
   apply H0.
   elim (Zcompare_Eq_iff_eq x 0%nat).
   intros H3 H4.
   auto.
  intro H2.
  cut (exists h : nat, Z.abs_nat x = S h).
   intro H3.
   case H3.
   rewrite H.
   exact O_S.
  change (x < 0)%Z in H2.
  set (H3 := Z.lt_gt _ _ H2) in *.
  elim (Zcompare_Gt_spec _ _ H3).
  intros x0 H5.
  cut (exists q : positive, x = Zneg q).
   intro H6.
   case H6.
   intros x1 H7.
   rewrite H7.
   unfold Z.abs_nat in |- *.
   generalize x1.
   exact ZL4.
  cut (x = (- Zpos x0)%Z).
   simpl in |- *.
   intro H6.
   exists x0.
   assumption.
  rewrite <- (Z.opp_involutive x).
  exact (f_equal Z.opp H5).
 intro H2.
 cut (exists h : nat, Z.abs_nat x = S h).
  intro H3.
  case H3.
  rewrite H.
  exact O_S.
 elim (Zcompare_Gt_spec _ _ H2).
 simpl in |- *.
 rewrite Zplus_0_r.
 intros x0 H4.
 rewrite H4.
 unfold Z.abs_nat in |- *.
 generalize x0.
 exact ZL4.
Qed.

Lemma absolu_2 : forall x : Z, x <> 0%Z -> Z.abs_nat x <> 0.
Proof.
 intros x H.
 intro H0.
 apply H.
 apply absolu_1.
 assumption.
Qed.

Lemma Zgt_mult_conv_absorb_l : forall a x y : Z,
 (a < 0)%Z -> (a * x > a * y)%Z -> (x < y)%Z.
Proof.
 intros a x y H H0.
 case (dec_eq x y).
  intro H1.
  apply False_ind.
  rewrite H1 in H0.
  cut ((a * y)%Z = (a * y)%Z).
   change ((a * y)%Z <> (a * y)%Z) in |- *.
   apply Zgt_not_eq.
   assumption.
  trivial.
 intro H1.
 case (not_Zeq x y H1).
  trivial.
 intro H2.
 apply False_ind.
 cut (a * y > a * x)%Z.
  apply Zgt_asym with (m := (a * y)%Z) (n := (a * x)%Z).
  assumption.
 apply Zlt_conv_mult_l.
  assumption.
 assumption.
Qed.

Lemma Zgt_mult_reg_absorb_l : forall a x y : Z,
 (a > 0)%Z -> (a * x > a * y)%Z -> (x > y)%Z.
Proof.
 intros a x y H H0.
 cut (- a < - (0))%Z.
  rewrite <- (Z.opp_involutive a) in H.
  rewrite <- (Z.opp_involutive 0) in H.
  simpl in |- *.
  intro H1.
  rewrite <- (Z.opp_involutive x).
  rewrite <- (Z.opp_involutive y).
  apply Zlt_opp.
  apply Zgt_mult_conv_absorb_l with (a := (- a)%Z) (x := (- x)%Z).
   assumption.
  rewrite Zopp_mult_distr_l_reverse.
  rewrite Zopp_mult_distr_l_reverse.
  apply Zlt_opp.
  rewrite <- Zopp_mult_distr_r.
  rewrite <- Zopp_mult_distr_r.
  apply Z.gt_lt.
  apply Zlt_opp.
  apply Z.gt_lt.
  assumption.
 lia.
Qed.

Lemma Zmult_Sm_Sn : forall m n : Z,
 ((m + 1) * (n + 1))%Z = (m * n + (m + n) + 1)%Z.
Proof.
 intros.
 ring.
Qed.


Definition CForall {A: Type} (P: A -> Type): list A -> Type :=
  fold_right (fun x => prod (P x)) True.

Definition CForall_prop {A: Type} (P: A -> Prop) (l: list A):
 (forall x, In x l -> P x)  IFF  CForall P l.
Proof with firstorder. induction l... subst... Qed.

Lemma CForall_indexed {A} (P: A -> Type) (l: list A): CForall P l ->
  forall i (d: A), (i < length l)%nat -> P (nth i l d).
Proof.
 intros X i.
 revert l X.
 induction i; destruct l; simpl in *; intuition; auto with *; exfalso; inversion H.
Qed.

Lemma CForall_map {A B} (P: B -> Type) (f: A -> B) (l: list A):
  CForall P (map f l)  IFF  CForall (fun x => P (f x)) l.
Proof. induction l; firstorder. Qed.

Lemma CForall_weak {A} (P Q: A -> Type):
  (forall x, P x -> Q x) ->
  (forall l, CForall P l -> CForall Q l).
Proof. induction l; firstorder. Qed.

Fixpoint CNoDup {T: Type} (R: T -> T -> Type) (l: list T): Type :=
  match l with
  | nil => True
  | h :: t => prod (CNoDup R t) (CForall (R h) t)
  end.

Lemma CNoDup_weak {A: Type} (Ra Rb: A -> A -> Type) (l: list A):
  (forall x y, Ra x y -> Rb x y) ->
  CNoDup Ra l -> CNoDup Rb l.
Proof with auto.
 induction l... firstorder.
 apply CForall_weak with (Ra a)...
Qed.


Lemma CNoDup_indexed {T} (R: T -> T -> Type) (Rsym: Csymmetric _ R) (l: list T) (d: T): CNoDup R l ->
  forall i j, (i < length l)%nat -> (j < length l)%nat -> i <> j -> R (nth i l d) (nth j l d).
Proof.
 induction l; simpl; intuition.
  exfalso; auto with *.
 destruct i.
  destruct j; intuition.
  apply (CForall_indexed (R a) l); auto with *.
 destruct j; auto with *.
 apply Rsym.
 apply (CForall_indexed (R a) l); auto with *.
Qed.

Lemma CNoDup_map {A B: Type} (R: B -> B -> Type) (f: A -> B):
  forall l, CNoDup (fun x y => R (f x) (f y)) l  IFF  CNoDup R (map f l).
Proof.
 induction l; simpl; auto; intuition; auto with *.
 split; intro; split.
    apply IHl, X.
   apply CForall_map; auto; intuition.
  apply IHl, X.
 apply CForall_map; auto; intuition.
Qed.
