Require Import CoRN.algebra.RSetoid.
Require Import
  Unicode.Utf8 Setoid List Permutation Setoid Morphisms SetoidPermutation
  stdlib_omissions.Pair.

Fixpoint separates {A} (l: list A): list (A * list A) :=
  match l with
  | nil => nil
  | x :: xs => (x, xs) :: map (fun pq => (fst pq, x :: snd pq)) (separates xs)
  end.

(** 
separates (0::1::2::nil)= (0, 1 :: 2 :: nil) :: (1, 0 :: 2 :: nil) :: (2, 0 :: 1 :: nil) :: nil
*)

Lemma separates_length {A} (l: list A): length (separates l) = length l.
Proof.
 induction l. intuition.
 simpl. rewrite map_length.
 congruence.
Qed.

Lemma separates_elem_lengths {A} (l x: list A): In x (map (@snd _ _) (separates l)) →
  length l = S (length x).
Proof with auto.
 revert x.
 induction l; simpl. intuition.
 intros x [[] | C]...
 rewrite map_map in C.
 simpl in C.
 destruct (proj1 (in_map_iff _ _ _) C) as [x0 [[]?]].
 rewrite (IHl (snd x0)). reflexivity.
 apply in_map_iff. eauto.
Qed.

#[global]
Instance separates_Proper {A}:
  Proper (@Permutation _ ==> SetoidPermutation (pair_rel eq (@Permutation _))) (@separates A).
Proof with simpl; auto; intuition; auto with *.
 intros ?? P.
 induction P...
     3:eauto.
   apply s_perm_skip. split...
   apply (map_perm_proper (pair_rel eq (@Permutation A)))...
   intros ?? [??]. split...
  rewrite s_perm_swap.
  repeat apply s_perm_skip...
  do 2 rewrite map_map.
  apply (map_perm_proper (pair_rel eq (SetoidPermutation eq)))...
  intros ?? [C D]. split...
  apply perm_trans with (l':=(x :: y :: snd x0))...
  do 2 apply perm_skip...
  apply SetoidPermutation_eq...
Qed.
