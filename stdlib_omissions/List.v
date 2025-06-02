Require Export Coq.Lists.List.

Require Import
  Coq.Arith.Arith Coq.Unicode.Utf8 Coq.Setoids.Setoid Coq.Sorting.Permutation Coq.Setoids.Setoid Coq.Classes.Morphisms CoRN.stdlib_omissions.Pair.

Fixpoint zip {A B} (a: list A) (b: list B): list (A * B) :=
  match a, b with
  | ah :: au, bh :: bt => (ah, bh) :: zip au bt
  | _, _ => nil
  end.

Lemma zip_map_snd {A B C} (a: list A) (b: list B) (f: B → C):
  zip a (map f b) = map (second f) (zip a b).
Proof with auto.
 revert b. induction a; destruct b...
 simpl in *. intros. rewrite IHa...
Qed.

Lemma move_to_front {A} (x: A) (l: list A): In x l →
  exists l', Permutation (x :: l') l.
Proof with eauto.
 induction l; simpl.
  intuition.
 intros [[] | D]...
 destruct (IHl D) as [y ?].
 exists (a :: y).
 rewrite perm_swap...
Qed.

#[global]
Hint Resolve nth_In.

Lemma NoDup_indexed {A} (l: list A) (N: NoDup l) (d: A):
  forall i j: nat, i < length l → j < length l -> i <> j -> nth i l d <> nth j l d.
Proof with auto with arith.
 intro i. revert l N.
 induction i; intros.
  destruct l; simpl.
   inversion H.
  destruct j. intuition.
  inversion_clear N.
  intro. subst...
 destruct l.
  inversion H0.
 inversion_clear N.
 simpl.
 destruct j...
 intro. subst a...
Qed.

#[global]
Instance: forall A, Proper (@Permutation A ==> iff) (@NoDup A).
Proof with auto.
 intro.
 cut (forall x y: list A, Permutation x y → NoDup x → NoDup y).
  intros ??? B.
  split. apply H...
  symmetry in B.
  apply H...
 intros x y P.
 induction P; intros...
  inversion_clear H.
  apply NoDup_cons...
  intro.
  apply H0.
  apply Permutation_in with l'...
  symmetry...
 inversion_clear H.
 inversion_clear H1.
 apply NoDup_cons.
  intros [?|?]...
  subst y.
  intuition.
 apply NoDup_cons...
 intuition.
Qed.

#[global]
Instance: forall A, Proper (@Permutation A ==> eq) (@length A).
Proof Permutation_length.

Section list_eq.

  Context {A} (R: relation A).

  Fixpoint list_eq (x y: list A): Prop :=
    match x, y with
    | nil, nil => True
    | a :: x', b :: y' => R a b ∧ list_eq x' y'
    | _, _ => False
    end.

  Lemma list_eq_rect (P: list A → list A → Type)
   (Pnil: P nil nil)
   (Pcons: forall a b, R a b → forall x y, list_eq x y → P x y → P (a :: x) (b :: y)):
     forall x y, list_eq x y → P x y.
  Proof. induction x; destruct y; simpl; intuition. Qed.

  Global Instance list_eq_refl: Reflexive R → Reflexive list_eq.
  Proof. intros H x. induction x; simpl; intuition; eauto. Qed.
  
  Global Instance list_eq_sym: Symmetric R → Symmetric list_eq.
  Proof. intros H x y E. apply (list_eq_rect (fun x y => list_eq y x)); simpl; intuition; eauto. Qed.

  Global Instance list_eq_trans: Transitive R → Transitive list_eq.
  Proof. intros H x. induction x; destruct y; destruct z; simpl; intuition; eauto. Qed.

  Global Instance: Equivalence R → Equivalence list_eq := {}.

  Lemma Perm_list_eq_commute (x y y': list A): Permutation x y → list_eq y y' → exists x', list_eq x x' ∧ Permutation x' y'.
  Proof with simpl; intuition.
   intro P. revert y'.
   induction P.
      destruct y'...
      exists nil...
     destruct y'; simpl. intuition.
     intros [? Rxa].
     destruct (IHP y' Rxa) as [x0[??]].
     exists (a :: x0). intuition.
    destruct y'...
    destruct y'...
    exists (a0 :: a :: y').
    intuition.
    apply perm_swap.
   intros.
   destruct (IHP2 y' H) as [?[??]].
   destruct (IHP1 x H0) as [?[??]].
   exists x0...
   transitivity x...
  Qed.

End list_eq.

Lemma list_eq_eq {A} (x y: list A): list_eq eq x y <-> x = y.
Proof with auto.
 split; intro.
  apply (@list_eq_rect A eq)...
  intros.
  subst.
  reflexivity.
 subst.
 reflexivity.
Qed.

#[global]
Instance: forall A (x: A), Proper (@Permutation A ==> iff) (@In A x).
Proof. pose proof Permutation_in. firstorder auto with crelations. Qed.

Lemma tl_map {A B} (l: list A) (f: A → B): tl (map f l) = map f (tl l).
Proof. destruct l; reflexivity. Qed.

#[global]
Hint Resolve in_cons.
#[global]
Hint Immediate in_eq.
