Require Import
  Coq.Unicode.Utf8 Coq.Setoids.Setoid CoRN.stdlib_omissions.List Coq.Sorting.Permutation Coq.Setoids.Setoid Coq.Classes.Morphisms.

(** The standard Permutation property is not setoid-aware, so we
 introduce a variant that is. *)

Section def.

  Context {A: Type} (e: relation A) `{!Equivalence e}.

  Inductive SetoidPermutation: list A → list A → Prop :=
    | s_perm_nil : SetoidPermutation nil nil
    | s_perm_skip x y: e x y -> ∀ l l', SetoidPermutation l l' → SetoidPermutation (x :: l) (y :: l')
    | s_perm_swap x y l: SetoidPermutation (y :: x :: l) (x :: y :: l)
    | s_perm_trans l l' l'':  SetoidPermutation l l' → SetoidPermutation l' l'' → SetoidPermutation l l''.

  Hint Constructors SetoidPermutation.

  Global Instance: Equivalence SetoidPermutation.
  Proof with eauto; intuition.
   constructor...
    intro l.
    induction l; eauto; intuition; auto with *.
   intros x y H.
   induction H; eauto; intuition; auto with *.
  Qed.

  Global Instance: Proper (list_eq e ==> list_eq e ==> iff) SetoidPermutation.
  Proof with eauto.
   assert (forall a b, list_eq e a b → SetoidPermutation a b).
    intros ?? E. apply (@list_eq_rect _ e SetoidPermutation); auto.
   intros ?? E ?? F.
   split; intro.
    symmetry in E...
   symmetry in F...
  Qed.

End def.

#[global]
Hint Constructors SetoidPermutation Permutation.

Lemma SetoidPermutation_stronger {A} (R U: relation A):
  (forall x y: A, R x y → U x y) →
  forall a b, SetoidPermutation R a b → SetoidPermutation U a b.
Proof. intros ??? P. induction P; eauto. Qed.

(** With eq for the element relation, SetoidPermutation is directly equivalent to Permutation: *)

Lemma SetoidPermutation_eq {A} (a b: list A): SetoidPermutation eq a b ↔ Permutation a b.
Proof. split; intro; induction H; eauto. subst; eauto. Qed.

(** And since eq is stronger than any other equivalence, SetoidPermutation always follows from Permutation: *)

Lemma SetoidPermutation_from_Permutation {A} (e: relation A) `{!Reflexive e} (a b: list A):
  Permutation a b → SetoidPermutation e a b.
Proof.
 intro.
 apply SetoidPermutation_stronger with eq.
  intros. subst. reflexivity.
 apply SetoidPermutation_eq.
 assumption.
Qed.

(** In general, SetoidPermutation is equivalent to Permutation modulo setoid list equivalence: *)

Lemma SetoidPermutation_meaning {A} (R: relation A) `{!Equivalence R} (x y: list A):
  SetoidPermutation R x y ↔ ∃ y', list_eq R x y' ∧ Permutation y y'.
Proof with auto.
 split.
  intro H. induction H.
     exists nil. intuition; auto with *.
    destruct IHSetoidPermutation as [?[??]].
    exists (y :: x0).
    repeat split...
   exists (y :: x :: l).
   split... reflexivity.
  destruct IHSetoidPermutation1 as [x [H1 H3]].
  destruct IHSetoidPermutation2 as [x0 [H2 H4]].
  symmetry in H3.
  destruct (Perm_list_eq_commute R x l' x0 H3 H2).
  exists x1.
  split.
   transitivity x; intuition.
  transitivity x0; intuition; auto with *.
 intros [?[E?]]. rewrite E.
 symmetry. apply SetoidPermutation_from_Permutation...
 apply _.
Qed.

#[global]
Instance map_perm_proper {A B} (Ra: relation A) (Rb: relation B):
  Equivalence Ra →
  Equivalence Rb →
  Proper ((Ra ==> Rb) ==> SetoidPermutation Ra ==> SetoidPermutation Rb) (@map A B).
Proof with simpl; auto; try reflexivity.
 intros ??????? X.
 induction X; simpl...
  apply s_perm_trans with (x y0 :: x x0 :: map y l).
   apply s_perm_skip...
   apply s_perm_skip...
   induction l... intuition; auto with *.
  apply s_perm_trans with (y y0 :: y x0 :: map y l)...
  unfold respectful in *.
  apply s_perm_skip. intuition; auto with *.
  apply s_perm_skip... intuition; auto with *.
 apply s_perm_trans with (map y l')...
 apply s_perm_trans with (map x l')...
 clear IHX1 IHX2 X1 X2.
 induction l'... constructor. now symmetry; apply H1. easy.
Qed.
