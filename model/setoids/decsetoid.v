(* Standard Coq Setoids with decidable equality yield CSetoids with
 apartness defined as negation of equivalence. Also, morphisms on these
 setoids yield fun_strext/bin_fun_strext/Crel_strext. *)

Set Implicit Arguments.

Require Import CoRN.algebra.CSetoids.
From Coq Require Import SetoidDec Morphisms SetoidClass.


Class Apartness `{SetoidClass.Setoid} (ap: Crelation A): Type :=
  { ap_irreflexive: irreflexive ap
  ; ap_symmetric: Csymmetric ap
  ; ap_cotransitive: cotransitive ap
  ; ap_tight: tight_apart equiv ap
  }.

Class CSetoid_class `(Setoid): Type :=
  { apart: Crelation A
  ; csetoid_apart :: Apartness apart
  }.

Definition is_CSetoid_from_class `{Apartness}: is_CSetoid _ equiv ap0.
 destruct H0.
 apply Build_is_CSetoid; assumption.
Defined.

Definition CSetoid_from_class `{CSetoid_class}: CSetoid.
Proof.
 intros.
 apply (Build_CSetoid A equiv apart is_CSetoid_from_class).
Defined.

Section contents.

  Context {T: Type} {S: Setoid T} {eq_dec: EqDec S}.

  Let ap (a b: T): Prop := ~ (a == b).

  Instance ap_apart: Apartness ap.
  Proof with auto.
   apply Build_Apartness.
      do 2 intro. intuition; auto with *.
     do 4 intro. intuition; auto with *.
    intros x y H z.
    destruct (eq_dec x z)...
    destruct (eq_dec z y)...
    exfalso.
    apply H.
    transitivity z...
   red. unfold ap, Not. split...
   destruct (eq_dec x y)...
   intuition.
  Qed.

  Global Instance dec_CSetoid: CSetoid_class S := { apart := ap; csetoid_apart := ap_apart }.

  Definition is_CSetoid: is_CSetoid T equiv ap := is_CSetoid_from_class.
  Definition CSetoid: CSetoid := CSetoid_from_class.

  Lemma fun_strext (S': CSetoids.CSetoid) (f: T -> S'):
    Proper (equiv ==> @st_eq _) f -> @fun_strext CSetoid S' f.
  Proof with auto.
   red. simpl.
   repeat intro.
   apply <- (ax_ap_tight _ _ _ (cs_proof S') (f x) (f y))...
  Qed.

  Lemma Crel_strext (R: relation T): Proper (equiv ==> equiv ==> iff) R -> Crel_strext CSetoid R.
  Proof with auto.
   red. simpl. intros.
   destruct (eq_dec x1 x2)...
   destruct (eq_dec y1 y2)...
   left.
   rewrite <- e, <- e0...
  Qed.

End contents.

Module test.

  (* If we now have an equality-decidable setoid, we can immediately refer to apartness without any
   explicit invocation. *)
  Definition test `{eq_dec: EqDec} := fun x y =>apart x y.

End test.

Section binary.

  Context {T T': Type} {S: Setoid T} {S': Setoid T'} {eq_dec: EqDec S} {eq_dec': EqDec S'}.

  Lemma bin_fun_strext (S'': CSetoids.CSetoid) (f: T -> T' -> S''):
    Proper (equiv ==> equiv ==> @st_eq _) f -> bin_fun_strext CSetoid CSetoid S'' f.
  Proof with auto.
   red. simpl.
   intros.
   destruct (eq_dec x1 x2)...
   destruct (eq_dec' y1 y2)...
   exfalso.
   apply <- (ax_ap_tight _ _ _ (cs_proof S'') (f x1 y1) (f x2 y2))...
   rewrite -> e, e0.
   reflexivity.
  Qed.

End binary.
