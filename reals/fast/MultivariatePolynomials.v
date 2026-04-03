Require Import CoRN.algebra.RSetoid.
Require Import CoRN.metric2.Metric.
Require Import CoRN.metric2.UniformContinuity.
Require Import CoRN.algebra.Bernstein.
Require Import CoRN.algebra.CRing_Homomorphisms.
Require Import CoRN.algebra.COrdFields2.
Require Export CoRN.model.ordfields.Qordfield.
Require Import CoRN.model.totalorder.QMinMax.
Require Import CoRN.tactics.CornTac.
Require Import CoRN.tactics.Qauto.
Require Import CoRN.model.metric2.Qmetric.
From Coq Require Import Qabs.
Require Import CoRN.reals.fast.CRabs.
Require Import CoRN.reals.fast.ModulusDerivative.
Require Import CoRN.reals.fast.CRArith.
Require Import CoRN.reals.fast.CRArith_alg.

Set Implicit Arguments.

Opaque cpoly_cring.
Opaque cpoly_apply_fun.
Opaque polyconst.

Section MultivariatePolynomial.

(**
** Multivariable polynomails

Here we prove that multivariable polynomials over the rationals are uniformly continuous
on the unit hyperinterval.  Hence they can be lifted to apply to real numbers.
This allows real numbers to be used in polynomial expressions so that each variable
is only approximated once.
*)

Variable F : CRing.

(** Define the type of multivariable polynomials with [n] variables *)
Fixpoint MultivariatePolynomial (n:nat) : CRing :=
match n with
| O => F
| S n' => cpoly_cring (MultivariatePolynomial n')
end.

(** The constant multivariable polynomial *)
Fixpoint MVP_C_ (n:nat) : RingHom F (MultivariatePolynomial n) :=
match n return RingHom F (MultivariatePolynomial n) with
| O => RHid _
| S n' =>  RHcompose _ _ _ _C_ (MVP_C_ n')
end.

(** Apply a multivariable polynomial to a vector of input values *)
Fixpoint MVP_apply (n:nat) : MultivariatePolynomial n -> (Vector.t F n) -> F :=
match n return MultivariatePolynomial n -> Vector.t F n -> F with
| O => fun x _ => x
| (S n') => fun p v => (MVP_apply (p ! (MVP_C_ _ (Vector.hd v))) (Vector.tl v))
end.

End MultivariatePolynomial.

(* begin hide *)
Add Parametric Morphism F n : (@MVP_apply F n) with signature (@st_eq (MultivariatePolynomial F n)) ==> (@eq _) ==> (@st_eq _) as MVP_apply_wd.
Proof.
 induction n; intros x y Hxy z.
  assumption.
 simpl.
 apply IHn.
 rewrite -> Hxy.
 reflexivity.
Qed.
(* end hide *)

(* Multivariable polynomial application by a constant set of inputs is a ring homomorphism. *)

Lemma zero_MVP_apply : forall F n v, MVP_apply F ([0]:MultivariatePolynomial F n) v[=][0].
Proof.
 induction v.
  reflexivity.
 simpl.
 rewrite <- IHv.
 reflexivity.
Qed.

Lemma one_MVP_apply : forall F n v, MVP_apply F ([1]:MultivariatePolynomial F n) v[=][1].
Proof.
 induction v.
  reflexivity.
 simpl.
 rewrite <- IHv.
 rewrite -> one_apply.
 reflexivity.
Qed.

Lemma C_MVP_apply : forall F n q v, MVP_apply F (MVP_C_ F n q) v[=]q.
Proof.
 induction v.
  reflexivity.
 simpl.
 rewrite -> c_apply.
 assumption.
Qed.

Lemma MVP_plus_apply: forall F n (p q : MultivariatePolynomial F n) v,
  MVP_apply F (p[+]q) v [=] MVP_apply F p v[+]MVP_apply F q v.
Proof.
 induction v.
  reflexivity.
 simpl.
 rewrite -> plus_apply.
 apply IHv.
Qed.

Lemma MVP_mult_apply: forall F n (p q : MultivariatePolynomial F n) v,
  MVP_apply F (p[*]q) v [=] MVP_apply F p v[*]MVP_apply F q v.
Proof.
 induction v.
  reflexivity.
 simpl.
 rewrite -> mult_apply.
 apply IHv.
Qed.

Lemma MVP_c_mult_apply: forall F n (p : MultivariatePolynomial F n) c v,
  MVP_apply F (MVP_C_ _ _ c[*]p) v[=]c[*]MVP_apply F p v.
Proof.
 induction v.
  reflexivity.
 simpl.
 rewrite <- IHv.
 rewrite -> c_mult_apply.
 reflexivity.
Qed.

Lemma MVP_apply_hom_strext : forall (F:CRing) n (v:Vector.t F n), fun_strext (fun (p:MultivariatePolynomial F n) => MVP_apply _ p v).
Proof.
 induction n.
  intros v x y.
  simpl.
  auto with *.
 intros v x y H.
 simpl in H.
 destruct (csbf_strext _ _ _ _ _ _ _ _ (IHn _ _ _ H)) as [H0 | H0].
  assumption.
 elim (ap_irreflexive _ _ H0).
Defined.

Definition MVP_apply_hom_csf (F:CRing) n (v:Vector.t F n) :=
Build_CSetoid_fun _ _ _ (MVP_apply_hom_strext F v).

Definition MVP_apply_hom (F:CRing) n (v:Vector.t F n) : RingHom (MultivariatePolynomial F n) F.
Proof.
 exists (MVP_apply_hom_csf F v).
   intros x y; apply: MVP_plus_apply.
  intros x y; apply: MVP_mult_apply.
 apply: one_MVP_apply.
Defined.

(** [MVP_map] applies a ring homomorphism to the coefficents of a multivariable polynomial *)
Fixpoint MVP_map R S (f:RingHom R S) (n:nat) : RingHom (MultivariatePolynomial R n) (MultivariatePolynomial S n) :=
match n return RingHom (MultivariatePolynomial R n) (MultivariatePolynomial S n) with
| O => f
| (S n') => cpoly_map (MVP_map f n')
end.

Lemma MVP_map_C_ : forall R S (f:RingHom R S) n c,
 MVP_map f n (MVP_C_ _ _ c)[=]MVP_C_ _ _ (f c).
Proof.
 induction n.
  intros c; reflexivity.
 intros c.
 simpl.
 change (cpoly_map (MVP_map f n) (_C_ (MVP_C_ R n c))[=]_C_ (MVP_C_ S n (f c))).
 rewrite -> cpoly_map_C.
 rewrite -> IHn.
 reflexivity.
Qed.

(* In practice we use the Bernstein coeffecients to bound the polynomials *)
(** Some upper bound on the polynomial on [0,1] *)
Fixpoint MVP_upperBound (n:nat) : MultivariatePolynomial Q_as_CRing n -> Q :=
match n return MultivariatePolynomial Q_as_CRing n -> Q with
| O => fun x => x
| (S n') => fun p => let (m,b) := BernsteinCoefficents (MVP_C_ Q_as_CRing n') p
                      in Vector.t_rec _ (fun _ _ => Q) 0%Q
                         (fun c _ _ rec => Qmax (MVP_upperBound n' c) rec) m b
end.

(** Some lower bound on the polynomial on [0,1] *)
Fixpoint MVP_lowerBound (n:nat) : MultivariatePolynomial Q_as_CRing n -> Q :=
match n return MultivariatePolynomial Q_as_CRing n -> Q with
| O => fun x => x
| (S n') => fun p => let (m,b) := BernsteinCoefficents (MVP_C_ Q_as_CRing n') p
                      in Vector.t_rec _ (fun _ _ => Q) 0%Q
                         (fun c _ _ rec => Qmin (MVP_lowerBound n' c) rec) m b
end.

Local Open Scope Q_scope.

(** Definition of the unit hyperinterval of n dimensions *)
Fixpoint UnitHyperInterval (n:nat) (v:Vector.t Q n) : Prop :=
match v with
| Vector.nil _ => True
| Vector.cons _ a _ v' => 0 <= a <= 1 /\ UnitHyperInterval v'
end.

(* begin hide *)
Lemma BernsteinApplyRingHom : forall R F (eta: RingHom R F) n i (H:(i <= n)%nat) a,
 (Bernstein F H) ! (eta a)[=](eta (Bernstein R H) ! a).
Proof.
 induction n.
  simpl.
  intros _ _ a.
  do 2 rewrite -> one_apply.
  auto with *.
 intros [|i] H a; simpl;[|destruct (le_lt_eq_dec (S i) (S n) H)]; autorewrite with apply ringHomPush;
   repeat rewrite -> IHn; reflexivity.
Qed.

Lemma MVP_BernsteinNonNeg : forall m n i (H:(i <= n)%nat) v (a:Q), 0 <= a -> a <= 1 ->
 0 <= @MVP_apply Q_as_CRing m ((Bernstein _ H)!(MVP_C_ _ _ a)) v.
Proof.
 intros m n i H v a Ha0 Ha1.
 induction v.
  apply: BernsteinNonNeg; auto.
 simpl.
 replace RHS with (MVP_apply Q_as_CRing (Bernstein _ H) ! (MVP_C_ Q_as_CRing n0 a) v).
  apply IHv.
 apply: MVP_apply_wd; try reflexivity.
 rewrite -> BernsteinApplyRingHom.
 auto with *.
Qed.
(* end hide *)

(** Return the ith entry of a vector *)
Fixpoint Vector_ix A (n i:nat) (H:(i < n)%nat) (v:Vector.t A n) : A :=
match v in Vector.t _ m return (i < m)%nat -> A with
| Vector.nil _ => fun p => False_rect _ (Nat.nlt_0_r _ p)
| Vector.cons _ c n' v' => fun _ => match lt_le_dec i n' with
                            | left p => Vector_ix p v'
                            | right _ => c
                            end
end H.

(** The upper and lower bounds are correct. *)
Lemma MVP_upperBound_correct : forall n p v, UnitHyperInterval v -> MVP_apply _ p v[<=]MVP_upperBound n p.
Proof.
 induction n; intros p v H.
  apply Qle_refl.
 revert p H.
 dependent inversion v as [|a n0 v0].
 clear H.
 intros p [[Ha0 Ha1] Hv].
 stepl (@MVP_apply Q_as_CRing (S n) (let (n0, b) := BernsteinCoefficents (MVP_C_ Q_as_CRing n) p in
   evalBernsteinBasis (MultivariatePolynomial Q_as_CRing n) b) (@Vector.cons Q a n v0));
     [|apply MVP_apply_wd;[apply evalBernsteinCoefficents|reflexivity]].
 simpl (MVP_upperBound (S n) p).
 destruct (BernsteinCoefficents (MVP_C_ Q_as_CRing n) p) as [m b].
 apply Qle_trans with (Vector.t_rec (MultivariatePolynomial Q_as_CRing n)
   (fun (n1 : nat) (_ : Vector.t (MultivariatePolynomial Q_as_CRing n) n1) => Q) 0
     (fun (c : MultivariatePolynomial Q_as_CRing n) (n1 : nat)
       (_ : Vector.t (MultivariatePolynomial Q_as_CRing n) n1) (rec : Q) =>
         Qmax (MVP_apply _ c v0) rec) m b).
  clear IHn Hv.
  destruct m as [|m].
   rewrite (V0_eq b).
   unfold evalBernsteinBasis.
   simpl.
   rewrite -> zero_MVP_apply.
   apply Qle_refl.
  unfold evalBernsteinBasis.
  match goal with |- (?A <= ?B) => set (L:=A); set (R:=B) end.
  change (L[<=]R).
  rstepr (R[*][1]).
  rewrite <- (@one_MVP_apply Q_as_CRing _ (Vector.cons _ a _ v0)).
  stepr (R[*](@MVP_apply Q_as_CRing (S n) (@Sumx (cpoly_cring _) _ (fun i H => Bernstein _ (proj1 (Nat.lt_succ_r i m) (Nat.lt_le_trans _ _ _ H (Nat.le_refl _))))) (Vector.cons _ a _ v0))).
   fold (MultivariatePolynomial Q_as_CRing n).
   unfold L, R; clear L R.
   generalize (Nat.le_refl (S m)).
   revert b.
   generalize (S m) at 1 2 5 6 7 8 11.
   induction b as [| a0]; intros l.
    simpl.
    rewrite -> zero_MVP_apply.
    apply Qle_refl.
   simpl (Vector.t_rec (MultivariatePolynomial Q_as_CRing n)
     (fun (n2 : nat) (_ : Vector.t (MultivariatePolynomial Q_as_CRing n) n2) => Q) 0
       (fun (c : MultivariatePolynomial Q_as_CRing n) (n2 : nat)
         (_ : Vector.t (MultivariatePolynomial Q_as_CRing n) n2) (rec : Q) =>
           Qmax (MVP_apply Q_as_CRing c v0) rec) (S n1)
             (Vector.cons _ a0 _ b)).
   simpl (evalBernsteinBasisH (MultivariatePolynomial Q_as_CRing n)
     (Vector.cons (MultivariatePolynomial Q_as_CRing n) a0 n1 b) l).
   simpl (Sumx (fun (i : nat) (H : (i < S n1)%nat) => Bernstein (MultivariatePolynomial Q_as_CRing n)
     (proj1 (Nat.lt_succ_r i m) (Nat.lt_le_trans i (S n1) (S m) H l)))).
   do 2 rewrite -> MVP_plus_apply.
   rewrite ->  (Qplus_comm (@MVP_apply Q_as_CRing (S n) (Sumx (fun (i : nat) (l0 : (i < n1)%nat) =>
     Bernstein (MultivariatePolynomial Q_as_CRing n)
       (proj1 (Nat.lt_succ_r i m) (Nat.lt_le_trans i (S n1) (S m) (Nat.lt_lt_succ_r i n1 l0) l)))) (Vector.cons Q a n v0))).
   rewrite -> Qmult_comm.
   rewrite -> Qmult_plus_distr_l.
   apply Qplus_le_compat; rewrite -> Qmult_comm; rewrite -> Qmax_mult_pos_distr_l.
      replace LHS with (MVP_apply Q_as_CRing a0 v0 * @MVP_apply Q_as_CRing (S n)
        (Bernstein (MultivariatePolynomial Q_as_CRing n)
          (proj1 (Nat.lt_succ_r n1 m) (Nat.lt_le_trans n1 (S n1) (S m) (Nat.lt_succ_diag_r n1) l))) (Vector.cons _ a _ v0)).
       apply Qmax_ub_l.
      simpl.
      rewrite <- (MVP_mult_apply Q_as_CRing).
      apply: MVP_apply_wd; try reflexivity.
      replace (proj1 (Nat.lt_succ_r n1 m) (Nat.lt_le_trans n1 (S n1) (S m) (Nat.lt_succ_diag_r n1) l))
        with (proj2 (Nat.succ_le_mono n1 m) l) by apply le_irrelevent.
      replace (le_S_n n1 m l) with (proj2 (Nat.succ_le_mono n1 m) l) by apply le_irrelevent.
      apply c_mult_apply. 
     apply MVP_BernsteinNonNeg; auto.
    eapply Qle_trans;[|apply Qmax_ub_r].
    set (R:=Vector.t_rec (MultivariatePolynomial Q_as_CRing n)
      (fun (n2 : nat) (_ : Vector.t (MultivariatePolynomial Q_as_CRing n) n2) => Q) 0
        (fun (c : MultivariatePolynomial Q_as_CRing n) (n2 : nat)
          (_ : Vector.t (MultivariatePolynomial Q_as_CRing n) n2) (rec : Q) =>
            Qmax (MVP_apply Q_as_CRing c v0) rec) n1 b) in *.
    replace RHS with (R*@MVP_apply Q_as_CRing (S n) (Sumx (fun (i : nat) (l0 : (i < n1)%nat) =>
      Bernstein (MultivariatePolynomial Q_as_CRing n)
        (proj1 (Nat.lt_succ_r i m) (Nat.lt_le_trans i n1 (S m) l0 (Nat.lt_le_incl _ _ l))))) (Vector.cons _ a _ v0)).
     apply IHb.
    apply: mult_wdr.
    apply MVP_apply_wd; try reflexivity.
    apply Sumx_wd.
    intros i H.
    replace (proj1 (Nat.lt_succ_r i m) (Nat.lt_le_trans i (S n1) (S m) (Nat.lt_lt_succ_r i n1 H) l))
      with (proj1 (Nat.lt_succ_r i m) (Nat.lt_le_trans i n1 (S m) H (Nat.lt_le_incl n1 (S m) l))) by apply le_irrelevent.
    reflexivity.
   clear - Ha0 Ha1.
   induction n1.
    rewrite -> zero_MVP_apply.
    auto with *.
   simpl (Sumx (fun (i : nat) (l0 : (i < S n1)%nat) => Bernstein (MultivariatePolynomial Q_as_CRing n)
     (proj1 (Nat.lt_succ_r i m) (Nat.lt_le_trans i (S (S n1)) (S m) (Nat.lt_lt_succ_r i (S n1) l0) l)))).
   rewrite -> MVP_plus_apply.
   apply: plus_resp_nonneg.
    stepr (@MVP_apply Q_as_CRing (S n) (Sumx (fun (i : nat) (l0 : (i < n1)%nat) =>
      Bernstein (MultivariatePolynomial Q_as_CRing n)
        (proj1 (Nat.lt_succ_r i m) (Nat.lt_le_trans i (S n1) (S m) (Nat.lt_lt_succ_r i n1 l0) (Nat.lt_le_incl _ _ l))))) (Vector.cons _ a _ v0)).
     apply IHn1.
    apply MVP_apply_wd; try reflexivity.
    apply Sumx_wd.
    intros i H.
    replace (proj1 (Nat.lt_succ_r i m) (Nat.lt_le_trans i (S n1) (S m) (Nat.lt_lt_succ_r i n1 H) (Nat.lt_le_incl (S n1) (S m) l)))
      with (proj1 (Nat.lt_succ_r i m) (Nat.lt_le_trans i (S (S n1)) (S m) (Nat.lt_lt_succ_r i (S n1) (Nat.lt_lt_succ_r i n1 H)) l))
        by apply le_irrelevent.
    reflexivity.
   apply MVP_BernsteinNonNeg; auto with *.
  apply mult_wdr.
  apply MVP_apply_wd; try reflexivity.
  simpl (MultivariatePolynomial Q_as_CRing (S n)).
  rewrite <- (fun X => partitionOfUnity X m).
  apply Sumx_wd.
  intros i H.
  replace (proj1 (Nat.lt_succ_r i m) (Nat.lt_le_trans i (S m) (S m) H (Nat.le_refl (S m))))
    with (proj1 (Nat.lt_succ_r i m) H) by apply le_irrelevent.
  reflexivity.
 clear - IHn Hv.
 induction b.
  auto with *.
 apply Qmax_le_compat.
  apply IHn; apply Hv.
 auto.
Qed.

Lemma MVP_lowerBound_correct : forall n p v, UnitHyperInterval v -> MVP_lowerBound n p[<=]MVP_apply _ p v.
Proof.
 induction n; intros p v H.
  apply Qle_refl.
 revert p H.
 dependent inversion v as [| a n0 v0 ].
 clear H.
 intros p [[Ha0 Ha1] Hv].
 stepr (@MVP_apply Q_as_CRing (S n) (let (n0, b) := BernsteinCoefficents (MVP_C_ Q_as_CRing n) p in
   evalBernsteinBasis (MultivariatePolynomial Q_as_CRing n) b) (Vector.cons _ a _ v0));
     [|apply MVP_apply_wd;[apply evalBernsteinCoefficents|reflexivity]].
 simpl (MVP_lowerBound (S n) p).
 destruct (BernsteinCoefficents (MVP_C_ Q_as_CRing n) p) as [m b].
 apply Qle_trans with (Vector.t_rec (MultivariatePolynomial Q_as_CRing n)
   (fun (n1 : nat) (_ : Vector.t (MultivariatePolynomial Q_as_CRing n) n1) => Q) 0
     (fun (c : MultivariatePolynomial Q_as_CRing n) (n1 : nat)
       (_ : Vector.t (MultivariatePolynomial Q_as_CRing n) n1) (rec : Q) =>
         Qmin (MVP_apply _ c v0) rec) m b).
  clear - IHn Hv.
  induction b.
   auto with *.
  apply Qmin_le_compat.
   apply IHn; apply Hv.
  auto.
 clear IHn Hv.
 destruct m as [|m].
  rewrite (V0_eq b).
  unfold evalBernsteinBasis.
  simpl.
  rewrite -> zero_MVP_apply.
  apply Qle_refl.
 unfold evalBernsteinBasis.
 match goal with |- (?A <= ?B) => set (R:=A); set (L:=B) end.
 change (R[<=]L).
 rstepl (R[*][1]).
 rewrite <- (@one_MVP_apply Q_as_CRing _ (Vector.cons _ a _ v0)).
 stepl (R[*](@MVP_apply Q_as_CRing (S n) (@Sumx (cpoly_cring _) _ (fun i H => Bernstein _ (proj1 (Nat.lt_succ_r i m) (Nat.lt_le_trans _ _ _ H (Nat.le_refl _))))) (Vector.cons _ a _ v0))).
  fold (MultivariatePolynomial Q_as_CRing n).
  unfold L, R; clear L R.
  generalize (Nat.le_refl (S m)).
  revert b.
  generalize (S m) at 1 2 4 5 6 9 12.
  induction b as [| a0]; intros l.
   simpl.
   rewrite -> zero_MVP_apply.
   apply Qle_refl.
  simpl (Vector.t_rec (MultivariatePolynomial Q_as_CRing n)
    (fun (n2 : nat) (_ : Vector.t (MultivariatePolynomial Q_as_CRing n) n2) => Q) 0
      (fun (c : MultivariatePolynomial Q_as_CRing n) (n2 : nat)
        (_ : Vector.t (MultivariatePolynomial Q_as_CRing n) n2) (rec : Q) =>
          Qmin (MVP_apply Q_as_CRing c v0) rec) (S n1)
            (Vector.cons _ a0 _ b)).
  simpl (evalBernsteinBasisH (MultivariatePolynomial Q_as_CRing n)
    (Vector.cons _ a0 _ b) l).
  simpl (Sumx (fun (i : nat) (H : (i < S n1)%nat) => Bernstein (MultivariatePolynomial Q_as_CRing n)
    (proj1 (Nat.lt_succ_r i m) (Nat.lt_le_trans i (S n1) (S m) H l)))).
  do 2 rewrite -> MVP_plus_apply.
  rewrite ->  (Qplus_comm (@MVP_apply Q_as_CRing (S n) (Sumx (fun (i : nat) (l0 : (i < n1)%nat) =>
    Bernstein (MultivariatePolynomial Q_as_CRing n)
      (proj1 (Nat.lt_succ_r i m) (Nat.lt_le_trans i (S n1) (S m) (Nat.lt_lt_succ_r i n1 l0) l)))) (Vector.cons _ a _ v0))).
  rewrite ->  Qmult_comm.
  rewrite -> Qmult_plus_distr_l.
  apply Qplus_le_compat; rewrite -> Qmult_comm; rewrite -> Qmin_mult_pos_distr_l.
     replace RHS with (MVP_apply Q_as_CRing a0 v0 * @MVP_apply Q_as_CRing (S n)
       (Bernstein (MultivariatePolynomial Q_as_CRing n)
         (proj1 (Nat.lt_succ_r n1 m) (Nat.lt_le_trans n1 (S n1) (S m) (Nat.lt_succ_diag_r n1) l))) (Vector.cons _ a _ v0)).
      apply Qmin_lb_l.
     simpl.
     rewrite <- (MVP_mult_apply Q_as_CRing).
     apply: MVP_apply_wd; try reflexivity.
     replace (proj1 (Nat.lt_succ_r n1 m) (Nat.lt_le_trans n1 (S n1) (S m) (Nat.lt_succ_diag_r n1) l))
       with (proj2 (Nat.succ_le_mono n1 m) l) by apply le_irrelevent.
     replace (le_S_n n1 m l) with (proj2 (Nat.succ_le_mono n1 m) l) by apply le_irrelevent.
     apply c_mult_apply.
    apply MVP_BernsteinNonNeg; auto.
   eapply Qle_trans;[apply Qmin_lb_r|].
   set (R:=Vector.t_rec (MultivariatePolynomial Q_as_CRing n)
     (fun (n2 : nat) (_ : Vector.t (MultivariatePolynomial Q_as_CRing n) n2) => Q) 0
       (fun (c : MultivariatePolynomial Q_as_CRing n) (n2 : nat)
         (_ : Vector.t (MultivariatePolynomial Q_as_CRing n) n2) (rec : Q) =>
           Qmin (MVP_apply Q_as_CRing c v0) rec) n1 b) in *.
   replace LHS with (R*@MVP_apply Q_as_CRing (S n) (Sumx (fun (i : nat) (l0 : (i < n1)%nat) =>
     Bernstein (MultivariatePolynomial Q_as_CRing n)
       (proj1 (Nat.lt_succ_r i m) (Nat.lt_le_trans i n1 (S m) l0 (Nat.lt_le_incl _ _ l))))) (Vector.cons _ a _ v0)).
    apply IHb.
   apply: mult_wdr.
   apply MVP_apply_wd; try reflexivity.
   apply Sumx_wd.
   intros i H.
   replace (proj1 (Nat.lt_succ_r i m) (Nat.lt_le_trans i (S n1) (S m) (Nat.lt_lt_succ_r i n1 H) l))
     with (proj1 (Nat.lt_succ_r i m) (Nat.lt_le_trans i n1 (S m) H (Nat.lt_le_incl n1 (S m) l))) by apply le_irrelevent.
   reflexivity.
  clear - Ha0 Ha1.
  induction n1.
   rewrite -> zero_MVP_apply.
   auto with *.
  simpl (Sumx (fun (i : nat) (l0 : (i < S n1)%nat) => Bernstein (MultivariatePolynomial Q_as_CRing n)
    (proj1 (Nat.lt_succ_r i m) (Nat.lt_le_trans i (S (S n1)) (S m) (Nat.lt_lt_succ_r i (S n1) l0) l)))).
  rewrite -> MVP_plus_apply.
  apply: plus_resp_nonneg.
   stepr (@MVP_apply Q_as_CRing (S n) (Sumx (fun (i : nat) (l0 : (i < n1)%nat) =>
     Bernstein (MultivariatePolynomial Q_as_CRing n)
       (proj1 (Nat.lt_succ_r i m) (Nat.lt_le_trans i (S n1) (S m) (Nat.lt_lt_succ_r i n1 l0) (Nat.lt_le_incl _ _ l))))) (Vector.cons _ a _ v0)).
    apply IHn1.
   apply MVP_apply_wd; try reflexivity.
   apply Sumx_wd.
   intros i H.
   replace (proj1 (Nat.lt_succ_r i m) (Nat.lt_le_trans i (S n1) (S m) (Nat.lt_lt_succ_r i n1 H) (Nat.lt_le_incl (S n1) (S m) l)))
     with (proj1 (Nat.lt_succ_r i m) (Nat.lt_le_trans i (S (S n1)) (S m) (Nat.lt_lt_succ_r i (S n1) (Nat.lt_lt_succ_r i n1 H)) l))
       by apply le_irrelevent.
   reflexivity.
  apply MVP_BernsteinNonNeg; auto with *.
 apply mult_wdr.
 apply MVP_apply_wd; try reflexivity.
 simpl (MultivariatePolynomial Q_as_CRing (S n)).
 rewrite <- (fun X => partitionOfUnity X m).
 apply Sumx_wd.
 intros i H.
 replace (proj1 (Nat.lt_succ_r i m) (Nat.lt_le_trans i (S m) (S m) H (Nat.le_refl (S m))))
   with (proj1 (Nat.lt_succ_r i m) H) by apply le_irrelevent.
 reflexivity.
Qed.

Local Open Scope Q_scope.

(** Use the upper and lower bounds of the derivative of a polynomial to
define its modulus of continuity. *)
Definition MVP_apply_modulus n (p:MultivariatePolynomial Q_as_CRing (S n)) :=
let p' := (_D_ p) in
Qscale_modulus (Qmax (MVP_upperBound (S n) p') (-(MVP_lowerBound (S n) p'))).

Lemma MVP_apply_modulus_correct
  : forall n (p:MultivariatePolynomial Q_as_CRing (S n)) x y e,
 (0 <= x) -> (x <= 1) -> (0 <= y) -> (y <= 1) ->
 @ball_ex Q_as_MetricSpace (MVP_apply_modulus p e) x y ->
 forall (v:Vector.t Q n), UnitHyperInterval v ->
                     @ball Q_as_MetricSpace (proj1_sig e) (MVP_apply _ p (Vector.cons _ x _ v):Q) (MVP_apply _ p (Vector.cons _ y _ v)).
Proof.
 intros n p x y e Hx0 Hx1 Hy0 Hy1 Hxy v Hv.
 assert (Hx : (Qmax 0 (Qmin 1 x))==x).
  rewrite ->  Qle_min_r in Hx1.
  rewrite -> Hx1.
  rewrite ->  Qle_max_r in Hx0.
  rewrite -> Hx0.
  reflexivity.
 assert (Hy : (Qmax 0 (Qmin 1 y))==y).
  rewrite -> Qle_min_r in Hy1.
  rewrite -> Hy1.
  rewrite ->  Qle_max_r in Hy0.
  rewrite -> Hy0.
  reflexivity.
 simpl.
 rewrite <- Hx.
 rewrite <- Hy.
 unfold MVP_apply_modulus in Hxy.
 set (c:=(Qmax (MVP_upperBound (S n) (_D_ p)) (- MVP_lowerBound (S n) (_D_ p)))) in *.
 set (fp:=cpoly_map (RHcompose _ _ _ (inj_Q_hom IR) (MVP_apply_hom _ v)) p).
 apply (fun A B e => is_UniformlyContinuousD_Q (Some 0) (Some 1) refl_equal (FPoly _ fp) (FPoly _ (_D_ fp)) (Derivative_poly _ _ _)
   (fun x => (MVP_apply _ p (Vector.cons _ x _ v))) A c B e x y); try assumption.
  unfold fp.
  simpl.
  intros q _ _.
  clear - p.
  change (inj_Q_hom IR (MVP_apply_hom Q_as_CRing v p ! (MVP_C_ Q_as_CRing n q))[=]
    (cpoly_map (RHcompose (MultivariatePolynomial Q_as_CRing n) Q_as_CRing IR
      (inj_Q_hom IR) (MVP_apply_hom Q_as_CRing v)) p) ! (inj_Q_hom IR q)).
  rewrite -> cpoly_map_compose.
  rewrite <- cpoly_map_apply.
  apply inj_Q_wd.
  rewrite -> cpoly_map_apply.
  apply csbf_wd; try reflexivity.
  apply: C_MVP_apply.
 simpl.
 clear - c Hv.
 intros x _ [H0x Hx1].
 change (AbsIR (_D_ (cpoly_map (RHcompose (MultivariatePolynomial Q_as_CRing n) Q_as_CRing IR
   (inj_Q_hom IR) (MVP_apply_hom Q_as_CRing v)) p)) ! (inj_Q_hom IR x)[<=] inj_Q IR c).
 rewrite <- cpoly_map_diff.
 rewrite -> cpoly_map_compose.
 rewrite <- cpoly_map_apply.
 change (AbsIR (inj_Q IR (cpoly_map (MVP_apply_hom Q_as_CRing v) (_D_ p)) ! x)[<=]inj_Q IR c).
 rewrite -> AbsIR_Qabs.
 apply inj_Q_leEq.
 assert (Hx: 0 <= x <= 1).
  split; apply (leEq_inj_Q IR).
   rewrite -> inj_Q_Zero.
   rstepl ([0][/][0][+][1][//]den_is_nonzero IR 0); auto.
  rewrite -> inj_Q_One.
  rstepr ([1][/][0][+][1][//]den_is_nonzero IR 1); auto.
 setoid_replace ((cpoly_map (MVP_apply_hom Q_as_CRing v) (_D_ p)) ! x)
   with (@MVP_apply Q_as_CRing (S n) (_D_ p) (Vector.cons _ x _ v)).
  apply Qabs_case; intros H.
   eapply Qle_trans;[|apply Qmax_ub_l].
   apply MVP_upperBound_correct.
   split; auto.
  eapply Qle_trans;[|apply Qmax_ub_r].
  apply Qopp_le_compat.
  apply MVP_lowerBound_correct.
  split; auto.
 generalize (_D_ p).
 intros s; clear -s.
 simpl.
 change ((cpoly_map_fun (MultivariatePolynomial Q_as_CRing n) Q_as_CRing
   (MVP_apply_hom Q_as_CRing v) s) ! x == MVP_apply_hom Q_as_CRing v (s ! (MVP_C_ Q_as_CRing n x))).
 rewrite -> cpoly_map_apply.
 simpl.
 rewrite -> C_MVP_apply.
 reflexivity.
Qed.

Local Open Scope uc_scope.

(** Clamp a value to the unit interval *)
Definition Qclamp01 := QboundBelow_uc (0) ∘ QboundAbove_uc 1.

Lemma Qclamp01_clamped : forall x, 0 <= Qclamp01 x <= 1.
Proof.
 intros x.
 unfold Qclamp01.
 split; simpl.
  apply Qmax_ub_l.
 rewrite -> Qmax_min_distr_r.
 apply Qmin_lb_l.
Qed.

Lemma Qclamp01_le : forall x y, x <= y -> Qclamp01 x <= Qclamp01 y.
Proof.
 intros x y H.
 simpl.
 apply Qmax_le_compat; auto with *.
 apply Qmin_le_compat; auto with *.
Qed.

Lemma Qclamp01_close : forall e x y, Qabs (x-y) <= e -> Qabs (Qclamp01 x - Qclamp01 y) <= e.
Proof.
 intros e.
 cut (forall x y : Q, y <= x -> x - y <= e -> Qclamp01 x - Qclamp01 y <= e).
  intros H x y.
  destruct (Qle_total x y).
   rewrite -> Qabs_neg.
    intros He.
    rewrite -> Qabs_neg.
     replace LHS with (Qclamp01 y - Qclamp01 x) by simpl; ring.
     apply H; auto.
     replace LHS with (- (x-y)) by simpl; ring.
     auto.
    apply (shift_minus_leEq Q_as_COrdField).
    stepr (Qclamp01 y); [| now (simpl; ring)].
    apply Qclamp01_le.
    auto.
   apply (shift_minus_leEq Q_as_COrdField).
   stepr y; [| now (simpl; ring)].
   auto.
  rewrite -> Qabs_pos.
   intros He.
   rewrite -> Qabs_pos.
    apply H; auto.
   apply: shift_zero_leEq_minus.
   apply Qclamp01_le.
   auto.
  apply: shift_zero_leEq_minus.
  auto.
 intros x y Hxy He.
 simpl.
 apply (Qmin_case 1 y).
  intros Hy.
  assert (Hx:=Qle_trans _ _ _ Hy Hxy).
  rewrite ->  Qle_min_l in Hx.
  rewrite -> Hx.
  replace LHS with  0 by simpl; ring.
  eapply Qle_trans;[|apply He].
  apply: shift_zero_leEq_minus; auto.
 apply (Qmin_case 1 x).
  intros Hx Hy.
  eapply Qle_trans;[|apply He].
  apply Qplus_le_compat; auto.
  apply Qopp_le_compat.
  apply Qmax_ub_r.
 intros _ _.
 apply (Qmax_case 0 x); intros Hx.
  assert (Hy:=Qle_trans _ _ _ Hxy Hx).
  rewrite ->  Qle_max_l in Hy.
  rewrite -> Hy.
  eapply Qle_trans;[|apply He].
  apply: shift_zero_leEq_minus; auto.
 apply (Qmax_case 0 y); intros Hy.
  eapply Qle_trans;[|apply He].
  apply Qplus_le_compat; auto with *.
 auto.
Qed.

Require Import CoRN.algebra.RSetoid.

(** Definition of a setoid function type of n parameters *)
Fixpoint n_Function X Y (n:nat) :=
match n with
|O => Y
|S n' => extSetoid X (n_Function X Y n')
end.

(** Definition of a uniformly continuous function type of n parameters *)
Fixpoint n_UniformlyContinuousFunction (X Y:MetricSpace) (n:nat) :=
match n with
|O => Y
|S n' => X --> (n_UniformlyContinuousFunction X Y n')
end.

(** [MVP_uc_sig] is a recursive type definition that is needed for part of the definition of
 of a multivariable polynomial as a uniformly continuous function. *)
Fixpoint MVP_uc_sig (n:nat) :MultivariatePolynomial Q_as_CRing n -> n_UniformlyContinuousFunction Q_as_MetricSpace Q_as_MetricSpace n -> Type :=
match n return MultivariatePolynomial Q_as_CRing n -> n_UniformlyContinuousFunction Q_as_MetricSpace Q_as_MetricSpace n -> Type with
| O => fun p x => p==x
| (S n') => fun p f => forall v, MVP_uc_sig n' (p ! (MVP_C_ Q_as_CRing _ (Qclamp01 v))) (f v)
end.

Lemma MVP_uc_rec (n : nat)
  (IHn : forall p : MultivariatePolynomial Q_as_CRing n,
        {f : n_UniformlyContinuousFunction Q_as_MetricSpace Q_as_MetricSpace n &
        MVP_uc_sig n p f})
  (p : MultivariatePolynomial Q_as_CRing (S n))
  : @is_UniformlyContinuousFunction
           Q_as_MetricSpace (n_UniformlyContinuousFunction Q_as_MetricSpace Q_as_MetricSpace n)
           (fun (x:Q_as_CRing) => ProjT1 (IHn (p ! (MVP_C_ Q_as_CRing _ (Qclamp01 x))))) (MVP_apply_modulus p).
Proof.
  intros e x y Hxy.
  assert (Hxy' : ball_ex (MVP_apply_modulus p e) (Qclamp01 x) (Qclamp01 y)) by
     (destruct (MVP_apply_modulus p e); auto; simpl; rewrite -> Qball_Qabs; apply: Qclamp01_close;
      rewrite <- Qball_Qabs; auto).
  destruct (Qclamp01_clamped x) as [Hx0 Hx1].
  destruct (Qclamp01_clamped y) as [Hy0 Hy1].
  assert (X:=@MVP_apply_modulus_correct _ p (Qclamp01 x) (Qclamp01 y) e Hx0 Hx1 Hy0 Hy1 Hxy').
  clear Hxy Hxy'; generalize (proj2_sigT _  _ (IHn p ! (MVP_C_ Q_as_CRing n (Qclamp01 x))))
                             (proj2_sigT _  _ (IHn p ! (MVP_C_ Q_as_CRing n (Qclamp01 y)))).
  set (x':=Qclamp01 x) in *; set (y':=Qclamp01 y) in *; simpl in X; revert X.
  generalize (ProjT1 (IHn p ! (MVP_C_ Q_as_CRing n x')))
             (ProjT1 (IHn p ! (MVP_C_ Q_as_CRing n y'))).
  change (Q_as_CSetoid) with (csg_crr Q_as_CRing).
  generalize (p ! (MVP_C_ Q_as_CRing n x')) (p ! (MVP_C_ Q_as_CRing n y')).
  clear - e.
  induction n.
  - simpl; intros p q s t H Hs Ht;
      rewrite <- Hs, <- Ht; apply (H (Vector.nil _)); constructor.
  - simpl.
    intros p q s t H Hs Ht. split.
    apply Qpos_nonneg.
    intro v; apply (fun H => IHn _ _ _ _ H (Hs v) (Ht v));
      intros v0 Hv0; apply (H (Vector.cons _ (Qclamp01 v) _ v0)); split; auto;
          apply Qclamp01_clamped. 
Qed.

(** Multivariable polynomials are uniformly continuous on the unit hyper interval *)
Definition MVP_uc : forall n (p:MultivariatePolynomial Q_as_CRing n),
 {f:n_UniformlyContinuousFunction Q_as_MetricSpace Q_as_MetricSpace n
 |MVP_uc_sig _ p f}.
Proof.
 induction n.
  intros x.
  exists x.
  simpl.
  reflexivity.
 intros p.
 exists (Build_UniformlyContinuousFunction (MVP_uc_rec IHn p)).
 simpl.
 intros v.
 exact (ProjT2 (IHn p ! (MVP_C_ Q_as_CRing n (Qclamp01 v)))).
Defined.

Definition MVP_uc_Q := (fun n p => ProjT1 (MVP_uc n p)).

Add Parametric Morphism n : (@MVP_uc_Q n)
    with signature (@st_eq _) ==> (@msp_eq _) as MVP_uc_Q_wd.
Proof.
 induction n.
  simpl.
  unfold MVP_uc_Q.
  simpl.
  intros. apply Qball_0,H.
 intros x y Hxy.
 apply ucEq_equiv. intro a.
 apply IHn.
 rewrite -> Hxy.
 reflexivity.
Qed.

Fixpoint n_Cap X Y (plX : PrelengthSpace X) n : Complete (n_UniformlyContinuousFunction X Y n) -->
 n_UniformlyContinuousFunction (Complete X) (Complete Y) n :=
match n return Complete (n_UniformlyContinuousFunction X Y n) -->
 n_UniformlyContinuousFunction (Complete X) (Complete Y) n with
| O => uc_id _
| (S n') => (uc_compose_uc _ _ _ (@n_Cap X Y plX n')) ∘ (@Cap X _ plX)
end.

(** A [Cmap] for an n parameter function. *)
Definition n_Cmap X Y (plX : PrelengthSpace X) n : n_UniformlyContinuousFunction X Y n -->
 n_UniformlyContinuousFunction (Complete X) (Complete Y) n :=
(@n_Cap X Y plX n) ∘ (@Cunit _).

Add Parametric Morphism X Y plX n : (@n_Cap X Y plX n)
 with signature (@msp_eq _) ==> (@msp_eq _) as n_Cap_wd.
Proof.
 induction n.
  simpl.
  auto.
 intros x y Hxy.
 apply ucEq_equiv. intro z.
 apply IHn.
 apply Cap_wd; auto.
 reflexivity.
Qed.

Add Parametric Morphism X Y plX n : (@n_Cmap X Y plX n)
 with signature (@msp_eq _) ==> (@msp_eq _) as n_Cmap_wd.
Proof.
 intros x y Hxy.
 unfold n_Cmap.
 simpl.
 rewrite -> Hxy.
 reflexivity.
Qed.

(** Multivariable polynomials on the unit hyper interval can be applied to real numbers *)
Definition MVP_uc_fun n (p:MultivariatePolynomial _ n) :
 n_UniformlyContinuousFunction CR CR n :=
n_Cmap _ QPrelengthSpace n (MVP_uc_Q n p).

Add Parametric Morphism n : (@MVP_uc_fun n)
 with signature (@st_eq _) ==> (@msp_eq _) as MVP_uc_fun_wd.
Proof.
 intros x y Hxy.
 unfold MVP_uc_fun.
 rewrite -> Hxy.
 reflexivity.
Qed.

Section MVP_correct.

(** Correctness lemmas for [MVP_uc_fun]. *)
Lemma MVP_uc_fun_sub_Q : forall n (p:MultivariatePolynomial _ (S n)) x,
 0 <= x -> x <= 1 ->
 msp_eq (MVP_uc_fun (S n) p ('x)%CR) (MVP_uc_fun n (p!(MVP_C_ _ _ x))).
Proof.
 intros n p x Hx0 Hx1.
 unfold MVP_uc_fun.
 apply: n_Cap_wd.
 intros e1 e2.
 simpl.
 unfold Cap_raw.
 simpl.
 rewrite Qplus_0_r.
 change (ball (proj1_sig e1 + proj1_sig e2) (MVP_uc_Q n p ! (MVP_C_ Q_as_CRing n (Qmax 0 (Qmin 1 x))))
   (MVP_uc_Q n p ! (MVP_C_ Q_as_CRing n x))).
 rewrite ->  Qle_min_r in Hx1.
 rewrite -> Hx1.
 rewrite ->  Qle_max_r in Hx0.
 rewrite -> Hx0.
 apply ball_refl.
 apply (Qpos_nonneg (e1+e2)).
Qed.

Lemma MVP_CR_apply_prf
  : forall n (morph : MultivariatePolynomial CRasCRing n ->
                 n_Function (msp_as_RSetoid CR) (msp_as_RSetoid CR) n)
      (morph_prf : forall x1 x2 : MultivariatePolynomial CRasCRing n,
          x1 [=] x2 -> morph x1 [=] morph x2)
      p (x y : CR),
    msp_eq x y -> st_eq (morph (p!(MVP_C_ CRasCRing n x)))
                       (morph (p!(MVP_C_ CRasCRing n y))).
Proof.
  intros.
  apply morph_prf.
  apply cpoly_apply_wd. reflexivity.
  apply csf_wd. apply H.
Qed.

Lemma MVP_CR_apply_prf_2 :
  forall n (morph : MultivariatePolynomial CRasCRing n ->
          n_Function (msp_as_RSetoid CR) (msp_as_RSetoid CR) n)
    (morph_prf : forall x1 x2 : MultivariatePolynomial CRasCRing n,
        x1 [=] x2 -> morph x1 [=] morph x2)
    (p1 p2 : cpoly_cring (MultivariatePolynomial CRasCRing n)),
  p1 [=] p2 ->
  extEq (n_Function (msp_as_RSetoid CR) (msp_as_RSetoid CR) n)
    (fun x : RegularFunction Qball => morph p1 ! (MVP_C_ CRasCRing n x))
    (fun x : RegularFunction Qball => morph p2 ! (MVP_C_ CRasCRing n x)).
Proof.
  intros. intro x.
  simpl.
  apply morph_prf, cpoly_apply_wd.
  exact H.
  apply csf_wd. reflexivity.
Qed. 

(* The induction couples both the apply function
   and the proof that it is a morphism. *)
Fixpoint MVP_CR_apply (n : nat)
  : extSetoid (MultivariatePolynomial CRasCRing n)
              (n_Function (msp_as_RSetoid CR) (msp_as_RSetoid CR) n).
Proof.
  destruct n as [|n'].
  - exact id.
  - exact (Build_Morphism
              (MultivariatePolynomial CRasCRing (S n'))
              (n_Function (msp_as_RSetoid CR) (msp_as_RSetoid CR) (S n'))
              (fun p => Build_Morphism
                       _ _ (fun x => (MVP_CR_apply n') (p!(MVP_C_ CRasCRing n' x)))
                       (MVP_CR_apply_prf n' (MVP_CR_apply n') (Morphism_prf (MVP_CR_apply n')) p))
              (fun p1 p2 H => MVP_CR_apply_prf_2 n' (MVP_CR_apply n') (Morphism_prf (MVP_CR_apply n')) p1 p2 H)).
Defined.

Fixpoint MVP_uc_fun_correct_sig_Q n
  : n_UniformlyContinuousFunction CR CR n
    -> n_Function (msp_as_RSetoid CR) (msp_as_RSetoid CR) n -> Prop :=
  match n return n_UniformlyContinuousFunction CR CR n
                 -> n_Function (msp_as_RSetoid CR) (msp_as_RSetoid CR) n -> Prop with
| O => fun a b => msp_eq a b
| S n' => fun f g => forall x, (0 <= x)%Q -> (x <= 1)%Q -> MVP_uc_fun_correct_sig_Q n' (f ('x)%CR) (g ('x)%CR)
end.

Add Parametric Morphism n :
  (@MVP_uc_fun_correct_sig_Q n)
    with signature (@msp_eq _) ==> (@st_eq _) ==> iff as MVP_uc_fun_correct_sig_Q_wd.
Proof.
 induction n; intros x y Hxy a b Hab.
  change (x==a <-> y==b)%CR.
  rewrite -> Hxy, Hab.
  reflexivity.
 simpl.
 split; intros H c.
 apply ucEq_equiv in Hxy.
  rewrite <- (IHn _ _ (Hxy (' c)%CR) _ _ (Hab ('c)%CR)).
  auto.
 apply ucEq_equiv in Hxy.
 rewrite -> (IHn _ _ (Hxy ('c)%CR) _ _ (Hab ('c)%CR)).
 auto.
Qed.

Lemma MVP_uc_fun_correct_Q : forall n (p:MultivariatePolynomial Q_as_CRing n),
 MVP_uc_fun_correct_sig_Q n (MVP_uc_fun n p) (MVP_CR_apply n (MVP_map inject_Q_hom n p)).
Proof.
 induction n; intros p.
  change ('p=='p)%CR.
  reflexivity.
 intros x Hx0 Hx1.
 change (MVP_uc_fun_correct_sig_Q
           n (MVP_uc_fun (S n) p ('x)%CR)
           (MVP_CR_apply n ((MVP_map inject_Q_hom (S n) p)!(MVP_C_ CRasCRing _ ('x)%CR)))).
 eapply MVP_uc_fun_correct_sig_Q_wd;[apply MVP_uc_fun_sub_Q; auto| |apply IHn].
 apply Morphism_prf.
 simpl.
 setoid_replace (MVP_C_ CRasCRing n (' x)%CR) with ((MVP_map inject_Q_hom n) (MVP_C_ Q_as_CRing n x)).
  symmetry.
  apply cpoly_map_apply.
 clear - n.
 induction n.
 reflexivity.
 simpl.
 refine (csf_wd _ _ _ _ _ _).
 apply IHn.
Qed.

Fixpoint MVP_uc_fun_close_sig n e
  : n_UniformlyContinuousFunction CR CR n
    -> n_Function (msp_as_RSetoid CR) (msp_as_RSetoid CR) n -> Prop :=
match n return n_UniformlyContinuousFunction CR CR n -> n_Function (msp_as_RSetoid CR) (msp_as_RSetoid CR) n -> Prop with
| O => fun a b => ball e a b
| S n' => fun f g => forall x, (0 <= x)%CR -> (x <= 1)%CR -> MVP_uc_fun_close_sig n' e (f x) (g x)
end.

Add Parametric Morphism n :
  (@MVP_uc_fun_close_sig n)
    with signature Qeq ==> (@msp_eq _) ==> (@st_eq _) ==> iff as MVP_uc_fun_close_sig_wd.
Proof.
 induction n; intros e1 e2 He x y Hxy a b Hab.
  change (ball e1 x a <-> ball e2 y b).
  rewrite -> He, Hxy, Hab.
  reflexivity.
 simpl.
 split; intros H c.
 apply ucEq_equiv in Hxy.
  rewrite <- (IHn _ _ He _ _ (Hxy c) _ _ (Hab c)).
  auto.
  apply ucEq_equiv in Hxy.
 rewrite -> (IHn _ _ He _ _ (Hxy c) _ _ (Hab c)).
 auto.
Qed.

Lemma MVP_uc_fun_close_weaken : forall n (e1 e2:Qpos) f g, (proj1_sig e1 <= proj1_sig e2) ->
 MVP_uc_fun_close_sig n (proj1_sig e1) f g ->
 MVP_uc_fun_close_sig n (proj1_sig e2) f g.
Proof.
 induction n; intros e1 e2 f g He H.
  eapply ball_weak_le.
   apply He.
  apply H.
 intros x Hx0 Hx1.
 eapply IHn.
  apply He.
 apply H; auto.
Qed.

Fixpoint n_Function_ball01 n e : n_Function (msp_as_RSetoid CR) (msp_as_RSetoid CR) n
                                 -> n_Function (msp_as_RSetoid CR) (msp_as_RSetoid CR) n -> Prop :=
  match n return n_Function (msp_as_RSetoid CR) (msp_as_RSetoid CR) n
                 -> n_Function (msp_as_RSetoid CR) (msp_as_RSetoid CR) n -> Prop with
| O => ball e
| S n' => fun f g => forall x, (0 <= x)%CR -> (x <= 1)%CR -> n_Function_ball01 n' e (f x) (g x)
end.

Add Parametric Morphism n :
 (@n_Function_ball01 n) with signature Qeq ==> (@st_eq _) ==> (@st_eq _) ==> iff as n_Function_ball01_wd.
Proof.
 induction n; intros e1 e2 He x y Hxy a b Hab.
  change (ball e1 x a <-> ball e2 y b).
  rewrite -> He, Hxy, Hab.
  reflexivity.
 simpl.
 split; intros H c.
  rewrite <- (IHn _ _ He _ _ (Hxy c) _ _ (Hab c)).
  auto.
 rewrite -> (IHn _ _ He _ _ (Hxy c) _ _ (Hab c)).
 auto.
Qed.


Lemma MVP_uc_fun_close_left : forall n (e1 e2:Qpos) f1 f2 g,
 ball (proj1_sig e1) f1 f2 ->
 MVP_uc_fun_close_sig n (proj1_sig e2) f2 g ->
 MVP_uc_fun_close_sig n (proj1_sig e1+proj1_sig e2) f1 g.
Proof.
 induction n; intros e1 e2 f g1 g2 H0 H1.
  eapply ball_triangle.
   apply H0.
  apply H1.
 intros x Hx0 Hx1.
 eapply IHn.
  apply H0; auto.
 apply H1; auto.
Qed.

Lemma MVP_uc_fun_close_right : forall n (e1 e2:Qpos) f g1 g2,
 MVP_uc_fun_close_sig n (proj1_sig e1) f g1 ->
 n_Function_ball01 n (proj1_sig e2) g1 g2 ->
 MVP_uc_fun_close_sig n (proj1_sig e1+proj1_sig e2) f g2.
Proof.
 induction n; intros e1 e2 f g1 g2 H0 H1.
  eapply ball_triangle.
   apply H0.
  apply H1.
 intros x Hx0 Hx1.
 eapply IHn.
  apply H0; auto.
 apply H1; auto.
Qed.

Lemma n_Function_ball01_sym : forall n e f g,
(n_Function_ball01 n e f g) ->
(n_Function_ball01 n e g f).
Proof.
 induction n.
  apply ball_sym.
 intros e f g H x Hx0 Hx1.
 apply IHn.
 apply H; auto.
Qed.

Lemma n_Function_ball01_triangle : forall n e1 e2 f g h,
(n_Function_ball01 n e1 f g) ->
(n_Function_ball01 n e2 g h) ->
(n_Function_ball01 n (e1+e2)%Q f h).
Proof.
 induction n.
  apply ball_triangle.
 intros e1 e2 f g h H0 H1 x Hx0 Hx1.
 eapply IHn.
  apply H0; auto.
 apply H1; auto.
Qed.

Lemma n_Function_ball01_plus : forall n e p1 p2 p3,
(n_Function_ball01 n e (MVP_CR_apply n p2) (MVP_CR_apply n p3)) ->
(n_Function_ball01 n e (MVP_CR_apply n (p1[+]p2)) (MVP_CR_apply n (p1[+]p3))).
Proof.
 induction n; intros e p1 p2 p3 H.
  intros d1 d2.
  simpl.
  unfold Qball.
  unfold Cap_raw.
  simpl.
  replace RHS with ((approximate p1 ((1 # 2) * d1)%Qpos - approximate p1 ((1 # 2) * d2)%Qpos)
                    +(approximate p2 ((1 # 2) * d1)%Qpos - approximate p3 ((1 # 2) * d2)%Qpos))
    by simpl; ring.
  replace LHS with (((1 # 2) * proj1_sig d1 + (1 # 2) * proj1_sig d2)%Q
                    +(proj1_sig ((1 # 2) * d1)%Qpos + e
                      + proj1_sig ((1 # 2) * d2)%Qpos))%Q
    by simpl; ring.
(*
  replace LHS with (proj1_sig ((1 # 2) * d1 + (1 # 2) * d2)%Qpos
                    +proj1_sig ((1 # 2) * d1 + e + (1 # 2) * d2)%Qpos)
    by simpl; ring. *)
  apply AbsSmall_plus.
  change (ball (proj1_sig ((1 # 2) * d1 + (1 # 2) * d2)%Qpos)
               (approximate p1 ((1 # 2) * d1)%Qpos) (approximate p1 ((1 # 2) * d2)%Qpos)).
   generalize ((1#2)*d1)%Qpos ((1#2)*d2)%Qpos.
   change (regFunEq p1 p1).
   apply regFunEq_equiv. reflexivity.
  generalize ((1#2)*d1)%Qpos ((1#2)*d2)%Qpos.
  apply H.
 intros x Hx0 Hx1.
 change (n_Function_ball01 n e (MVP_CR_apply _ (p1[+]p2) ! (MVP_C_ CRasCRing _ x))
   (MVP_CR_apply _ (p1[+]p3) ! (MVP_C_ CRasCRing _ x))).
 eapply n_Function_ball01_wd;[| | |apply IHn].
    reflexivity.
   apply Morphism_prf.
   apply plus_apply.
  apply Morphism_prf.
  apply plus_apply.
 apply: H; auto.
Qed.

Lemma n_Function_ball01_mult_C : forall n (e:Qpos) c q1 q2,
(0 <= c)%CR -> (c <= 1)%CR ->
(n_Function_ball01 n (proj1_sig e) (MVP_CR_apply n q1) (MVP_CR_apply n q2)) ->
(n_Function_ball01 n (proj1_sig e) (MVP_CR_apply n ((MVP_C_ CRasCRing _ c)[*]q1))
                       (MVP_CR_apply n ((MVP_C_ CRasCRing _ c)[*]q2))).
Proof.
 induction n; intros e c q1 q2 Hc0 Hc1 H.
  change (ball (proj1_sig e) (c * q1)%CR (c * q2)%CR).
  rewrite <- CRAbsSmall_ball.
  (* change (AbsSmall (' proj1_sig e)%CR (c[*]q1[-]c[*]q2)). *)
  change (@cg_minus CRasCOrdField (c * q1)%CR (c * q2)%CR)
    with (c*q1 - c*q2)%CR.
  setoid_replace (c*q1 - c*q2)%CR
    with (c * (q1 - q2))%CR by ring.
  (* rstepr (c[*](q1[-]q2)). *)
  apply AbsSmall_leEq_trans with (c * 'proj1_sig e)%CR.
  rewrite <- (CRmult_1_l ('proj1_sig e)%CR) at 2.
   apply mult_resp_leEq_rht; auto.
   simpl. apply CRle_Qle, Qpos_nonneg.
  apply mult_resp_AbsSmall; auto.
  apply (CRAbsSmall_ball q1 q2).
  exact H.
 intros x Hx0 Hx1.
 change (n_Function_ball01 n (proj1_sig e) (MVP_CR_apply _ (MVP_C_ CRasCRing _ c[*]q1) ! (MVP_C_ CRasCRing _ x))
   (MVP_CR_apply _ (MVP_C_ CRasCRing _ c[*]q2) ! (MVP_C_ CRasCRing _ x))).
 eapply n_Function_ball01_wd.
    reflexivity.
   apply Morphism_prf.
   eapply eq_transitive.
    apply mult_apply.
   apply mult_wdl.
   simpl.
   apply c_apply.
  apply Morphism_prf.
  eapply eq_transitive.
   apply mult_apply.
  apply mult_wdl.
  simpl.
  apply c_apply.
 apply IHn; auto.
 apply: H; auto.
Qed.

Fixpoint MVP_is_Bound01 n (M:CR) : MultivariatePolynomial CRasCRing n -> Prop :=
match n return MultivariatePolynomial CRasCRing n -> Prop with
| O => fun a => @AbsSmall CRasCOrdField M a
| S n' => fun p => forall x, (0 <= x)%CR -> (x <= 1)%CR ->
  MVP_is_Bound01 n' M (p ! (MVP_C_ CRasCRing _ x))
end.

Add Parametric Morphism n :
  (@MVP_is_Bound01 n)
    with signature (@msp_eq _) ==> (@st_eq _) ==> iff as MVP_is_Bound01_wd.
Proof.
 induction n; intros x y Hxy a b Hab.
  simpl.
  rewrite -> Hxy.
  rewrite -> Hab.
  reflexivity.
 split; intros H c Hc0 Hc1.
  change (MVP_is_Bound01 n y b ! (MVP_C_ CRasCRing n c)).
  rewrite <- (IHn _ _ Hxy (a!(MVP_C_ CRasCRing n c)) (b!(MVP_C_ CRasCRing n c))).
   apply H; auto.
  rewrite -> Hab.
  reflexivity.
 change (MVP_is_Bound01 n x a ! (MVP_C_ CRasCRing n c)).
 rewrite <- (fun A => IHn y x A (b!(MVP_C_ CRasCRing n c)) (a!(MVP_C_ CRasCRing n c))).
   apply H; auto.
  symmetry; auto.
 rewrite -> Hab.
 reflexivity.
Qed.

Lemma MVP_is_Bound01_plus : forall n M N p q,
 MVP_is_Bound01 n M p -> MVP_is_Bound01 n N q ->
 MVP_is_Bound01 n (M+N)%CR (p[+]q).
Proof.
 induction n; intros M N p q Hp Hq.
  apply: AbsSmall_plus; auto.
 simpl.
 intros x Hx0 Hx1.
 rewrite -> plus_apply.
 auto.
Qed.

Lemma MVP_is_Bound01_mult01 : forall n M p x,
 (0 <= x)%CR -> (x <= 1)%CR ->
 MVP_is_Bound01 n M p ->
 MVP_is_Bound01 n M (MVP_C_ CRasCRing n x[*]p).
Proof.
 induction n; intros M p x Hx0 Hx1 H.
  simpl.
  change (msp_car CR) in p.
  eapply AbsSmall_leEq_trans;[|apply mult_resp_AbsSmall;[|apply H]]; auto.
  rewrite <- (CRmult_1_l M) at 2.
  apply mult_resp_leEq_rht; auto.
  simpl in H. unfold AbsSmall in H.
  rewrite <- CRabs_AbsSmall in H.
  eapply leEq_transitive;[|apply H].
  apply CRabs_nonneg.
 simpl.
 intros y Hy0 Hy1.
 rewrite -> mult_apply.
 rewrite -> c_apply.
 apply IHn; auto.
Qed.

Lemma n_Function_ball01_mult : forall n e x y p M,
MVP_is_Bound01 n ('M)%CR p ->
ball_ex (Qscale_modulus M e) x y ->
n_Function_ball01 n (proj1_sig e)
  (MVP_CR_apply n (MVP_C_ CRasCRing n x[*]p))
  (MVP_CR_apply n (MVP_C_ CRasCRing n y[*]p)).
Proof.
 induction n; intros e x y p b Hb Hxy.
  change (ball (proj1_sig e) (x*p) (y*p))%CR.
  rewrite <- CRAbsSmall_ball.
  change (@cg_minus CRasCOrdField (x * p)%CR (y * p)%CR)
    with (x*p-y*p)%CR.
  setoid_replace (x*p-y*p)%CR with (p*(x-y))%CR by ring.
  simpl in Hb.
  case_eq (Qscale_modulus b e).
   intros q Hq.
   apply AbsSmall_leEq_trans with (CRabs p * 'proj1_sig q)%CR.
    destruct b as [[|nb|nb] db].
      discriminate Hq.
     simpl in Hq.
     injection Hq; clear Hq; intros Hq; rewrite <- Hq.
     assert (' proj1_sig ((db # nb) * e)%Qpos >< 0)%CR as Z.
     { apply Qap_CRap, Qpos_nonzero. }
     apply shift_mult_leEq with Z.
      apply: CRlt_Qlt; auto with *.
      unfold AbsSmall in Hb.
     rewrite <- CRabs_AbsSmall in Hb.
     stepr ('(nb#db))%CR; auto.
     change ((' (nb # db)) == (' proj1_sig e)%CR * CRinvT (' proj1_sig ((db # nb) * e)%Qpos) Z)%CR.
     rewrite -> CRinv_Qinv.
     rewrite -> CRmult_Qmult.
     rewrite -> CReq_Qeq.
     simpl.
     rewrite -> Qinv_mult_distr.
     replace RHS with ((/(db#nb) * proj1_sig e) * /proj1_sig e) by simpl; ring.
     change (nb#db == ((nb#db)*proj1_sig e/proj1_sig e)).
     rewrite -> Qdiv_mult_l.
      reflexivity.
     apply Qpos_nonzero.
    elim (Qle_not_lt 0 (Zneg nb # db)); auto with *.
    rewrite <- CRle_Qle.
    eapply AbsSmall_nonneg.
    apply Hb.
   cut (Not (Not (@AbsSmall CRasCOrdField (CRabs p * (' proj1_sig q))%CR (p * (x - y))%CR))).
   { unfold Not, AbsSmall.
    repeat rewrite -> leEq_def.
    unfold Not; tauto. }
   generalize (leEq_or_leEq CRasCOrdField [0] p).
   unfold Not.
   intros H abs.
   contradict H; intro H. contradict abs.
   destruct H as [Hp|Hp].
 - rewrite -> CRabs_pos; auto.
    apply mult_resp_AbsSmall;auto.
    rewrite Hq in Hxy.
    apply (CRAbsSmall_ball x y).
    auto.
 - rewrite -> CRabs_neg; auto.
   setoid_replace (p * (x - y))%CR with (-p * (y - x))%CR by ring.
   apply mult_resp_AbsSmall.
   rewrite <- CRopp_0.
    apply inv_resp_leEq.
    auto.
   rewrite Hq in Hxy.
   apply (CRAbsSmall_ball y x).
   apply ball_sym.
   apply Hxy.
 - intros Hq.
  destruct b as [[|nb|nb] db]; try discriminate Hq.
  setoid_replace p with 0%CR.
  rewrite CRmult_comm, CRmult_0_r.
   apply zero_AbsSmall.
   simpl.
   rewrite -> CRle_Qle; auto with *.
  destruct Hb as [Hb0 Hb1].
  apply CRle_antisym. split.
  stepr ((' (0 # db)))%CR; auto.
  change ('(0#db)==0)%CR.
  rewrite -> CReq_Qeq.
  unfold Qeq; reflexivity. 
   stepl (-(' (0 # db)))%CR; auto.
   rewrite -> CRopp_Qopp.
   change ('(0#db)==0)%CR.
   rewrite -> CReq_Qeq.
   unfold Qeq; reflexivity.
 - simpl.
 intros a Ha0 Ha1.
 eapply n_Function_ball01_wd.
    reflexivity.
   apply Morphism_prf.
   eapply eq_transitive.
    apply mult_apply.
   apply csbf_wd.
    apply c_apply.
   reflexivity.
  apply Morphism_prf.
  eapply eq_transitive.
   apply mult_apply.
  apply csbf_wd.
   apply c_apply.
  reflexivity.
 apply: IHn; auto.
Qed.

Fixpoint MVP_poor_Bound01 n : MultivariatePolynomial Q_as_CRing n -> Q :=
match n return MultivariatePolynomial Q_as_CRing n -> Q with
| O => Qabs
| S n' => fix MVP_poor_Bound01_H p : Q :=
          match p with
          | cpoly_zero _ => 0
          | cpoly_linear _ s p' => MVP_poor_Bound01 n' s + MVP_poor_Bound01_H p'
          end
end.

Lemma MVP_poor_Bound01_zero : forall n, MVP_poor_Bound01 n ([0])==0.
Proof.
 induction n.
  reflexivity.
 reflexivity.
Qed.

Add Parametric Morphism n :
 (@MVP_poor_Bound01 n) with signature (@st_eq _) ==> Qeq as MVP_poor_Bound01_wd.
Proof.
 induction n.
  intros x y Hxy.
  simpl in *.
  rewrite -> Hxy.
  reflexivity.
 induction x.
  induction y.
   reflexivity.
  intros [H0 H1].
  simpl in *.
  change 0 with (0+0).
  apply Qplus_comp.
   rewrite <- (MVP_poor_Bound01_zero n).
   apply IHn.
   symmetry; auto.
  apply IHy.
  apply H1.
 intros [|t y] [H0 H1].
  simpl.
  change 0 with (0+0).
  apply Qplus_comp.
   rewrite <- (MVP_poor_Bound01_zero n).
   apply IHn.
   auto.
  change (MVP_poor_Bound01 (S n) x==0).
  rewrite <- (MVP_poor_Bound01_zero (S n)).
  apply IHx.
  apply eq_symmetric.
  apply H1.
 simpl.
 apply Qplus_comp.
  apply IHn.
  auto.
 apply IHx.
 auto.
Qed.

Lemma MVP_poor_is_Bound01 : forall n p,
MVP_is_Bound01 n ('(MVP_poor_Bound01 n p))%CR (MVP_map inject_Q_hom n p).
Proof.
 induction n.
  split.
   change (-('Qabs p)<='p)%CR.
   rewrite -> CRopp_Qopp.
   rewrite -> CRle_Qle.
   simpl in p.
   replace RHS with (- (- p)) by simpl; ring.
   apply Qopp_le_compat.
   rewrite <- Qabs_opp.
   apply Qle_Qabs.
  change ('p<=('Qabs p))%CR.
  rewrite -> CRle_Qle.
  apply Qle_Qabs.
 simpl.
 induction p; intros x Hx0 Hx1.
  change (MVP_is_Bound01 n 0%CR ([0])).
  clear - n.
  induction n.
   apply AbsSmall_reflexive.
   apply leEq_reflexive.
  intros y _ _.
  apply IHn.
 change (MVP_is_Bound01 n (' (MVP_poor_Bound01 n s + (fix MVP_poor_Bound01_H (p0 : cpoly
   (MultivariatePolynomial Q_as_CRing n)) : Q := match p0 with | cpoly_zero _ => 0
     | cpoly_linear _ s0 p' => (MVP_poor_Bound01 n s0 + MVP_poor_Bound01_H p')%Q end) p)%Q)%CR
       (MVP_map inject_Q_hom n s[+]MVP_C_ CRasCRing n x[*](cpoly_map (MVP_map inject_Q_hom n) p) ! (MVP_C_ CRasCRing n x))).
 rewrite <- CRplus_Qplus.
 apply MVP_is_Bound01_plus.
  apply IHn.
 apply MVP_is_Bound01_mult01; auto.
Qed.

Lemma MVP_CR_apply_cont : forall n (e : Qpos) (p:MultivariatePolynomial Q_as_CRing (S n)),
 {d | forall x y,
 (0 <= x)%CR -> (x <= 1)%CR ->
 (0 <= 'y)%CR -> ('y <= 1)%CR ->
 ball_ex d x ('y)%CR ->
 n_Function_ball01 n (proj1_sig e) (MVP_CR_apply _ (MVP_map inject_Q_hom _ p) x)
                       (MVP_CR_apply _ (MVP_map inject_Q_hom _ p) ('y)%CR)}.
Proof.
 intros n e p.
 revert e.
 induction p; intros e.
  exists QposInfinity.
  intros x y _ _ _ _ _.
  change (n_Function_ball01 n (proj1_sig e) (MVP_CR_apply n [0]) (MVP_CR_apply n [0])).
  generalize (MVP_CR_apply n [0]).
  induction n.
   intros. apply ball_refl, Qpos_nonneg.
  intros s a _ _.
  apply IHn.
 simpl.
 destruct (IHp ((1#2)*e)%Qpos) as [d0 Hd0].
 set (b:=MVP_poor_Bound01 (S n) p).
 set (d1:=(Qscale_modulus b ((1 # 2) * e))).
 exists (QposInf_min d0 d1).
 intros x y Hx0 Hx1 Hy0 Hy1 Hxy.
 change (n_Function_ball01 n (proj1_sig e) (MVP_CR_apply n
   ((MVP_map inject_Q_hom n s)[+](MVP_C_ CRasCRing n x)[*]((cpoly_map (MVP_map inject_Q_hom n) p))
     ! (MVP_C_ CRasCRing n x))) (MVP_CR_apply n
       ((MVP_map inject_Q_hom n s)[+](MVP_C_ CRasCRing n ('y)%CR)[*]((cpoly_map (MVP_map inject_Q_hom n) p))
         ! (MVP_C_ CRasCRing n (inject_Q_hom y)%CR)))).
 apply n_Function_ball01_plus.
 setoid_replace (proj1_sig e)
   with (proj1_sig ((1#2)*e + (1#2)*e)%Qpos) by (simpl; ring).
 apply n_Function_ball01_triangle with (MVP_CR_apply n (MVP_C_ CRasCRing n x[*]
   (cpoly_map (MVP_map inject_Q_hom n) p) ! (MVP_C_ CRasCRing n (inject_Q_hom y)%CR))).
  apply n_Function_ball01_mult_C; auto.
  change (n_Function_ball01 n ((1 # 2) * proj1_sig e) (MVP_CR_apply (S n) (MVP_map inject_Q_hom (S n) p) x)
    (MVP_CR_apply (S n) (MVP_map inject_Q_hom (S n) p) ('y)%CR)).
  apply Hd0; auto with *.
  eapply ball_ex_weak_le;[|apply Hxy].
  apply QposInf_min_lb_l.
 eapply n_Function_ball01_wd.
    reflexivity.
   apply Morphism_prf.
   apply mult_wdr.
   eapply eq_transitive.
    apply csbf_wd;[apply eq_reflexive|].
    symmetry.
    apply MVP_map_C_.
   symmetry.
   apply cpoly_map_apply.
  apply Morphism_prf.
  apply mult_wdr.
  eapply eq_transitive.
   apply csbf_wd;[apply eq_reflexive|].
   symmetry.
   apply MVP_map_C_.
  symmetry.
  apply cpoly_map_apply.
 apply n_Function_ball01_mult with b.
  assert (Z:=MVP_poor_is_Bound01 (S n) p _ Hy0 Hy1).
  unfold b.
  change (MVP_is_Bound01 n (' MVP_poor_Bound01 (S n) p)%CR
    (MVP_map inject_Q_hom (S n) p) ! (MVP_C_ CRasCRing n (' y)%CR)) in Z.
  eapply MVP_is_Bound01_wd;[| |apply Z].
   reflexivity.
  simpl.
  change (MVP_map inject_Q_hom n p ! (MVP_C_ Q_as_CRing n y)[=] (cpoly_map (MVP_map inject_Q_hom n) p)
    ! (MVP_C_ CRasCRing n (inject_Q_hom y)%CR)).
  rewrite <- MVP_map_C_.
  apply cpoly_map_apply.
 eapply ball_ex_weak_le;[|apply Hxy].
 apply QposInf_min_lb_r.
Qed.

Lemma MVP_uc_fun_close : forall n (e:Qpos) (p:MultivariatePolynomial Q_as_CRing n),
 MVP_uc_fun_close_sig n (proj1_sig e) (MVP_uc_fun n p) (MVP_CR_apply n (MVP_map inject_Q_hom n p)).
Proof.
 induction n; intros e p.
  apply ball_refl, Qpos_nonneg.
 intros x Hx0 Hx1.
 change (MVP_uc_fun_close_sig n (proj1_sig e) (MVP_uc_fun (S n) p x)
   (MVP_CR_apply (S n) (MVP_map inject_Q_hom (S n) p) x)).
 setoid_replace (proj1_sig e)
   with (proj1_sig ((((1#3)*e)+(1#3)*e)+(1#3)*e)%Qpos) by (simpl; ring).
 set (e3:=((1#3)*e)%Qpos).
 destruct (MVP_CR_apply_cont e3 p) as [d0 Hd].
 set (d1:=mu (MVP_uc_fun (S n) p) e3).
 set (d:=QposInf_min d0 d1).
 set (y:=Qclamp01 (approximate x d)).
 destruct (Qclamp01_clamped (approximate x d)) as [Hy0 Hy1].
 rewrite <- CRle_Qle in Hy0.
 rewrite <- CRle_Qle in Hy1.
 pose proof (Hd _ _ Hx0 Hx1 Hy0 Hy1) as Hd0.
 assert (ball_ex d x (' Qclamp01 (approximate x d))%CR) as Z.
 { clear - Hx0 Hx1.
  destruct d as [d|];[|constructor].
  change (ball (proj1_sig d) x (' Qclamp01 (approximate x d))%CR).
  rewrite <- CRAbsSmall_ball.
  pose proof (ball_approx_r x d) as Z.
  rewrite <- CRAbsSmall_ball in Z.
  revert Z.
  generalize (approximate x d).
  clear - Hx0 Hx1.
  intros s [Z0 Z1].
  simpl.
  split.
   apply Qmax_case.
    intros _.
    apply leEq_transitive with 0%CR.
    rewrite <- CRopp_0.
     apply inv_resp_leEq.
     change (0<='proj1_sig d)%CR.
     rewrite -> CRle_Qle.
     apply Qpos_nonneg.
     change (@cg_minus CRasCGroup x (inject_Q_CR 0)) with (x-0)%CR.
     rewrite CRopp_0, CRplus_0_r.
     exact Hx0.
   intros H.
   apply (CRle_trans Z0).
   apply (minus_resp_leEq_rht CRasCOrdField (Cunit s) (' Qmin 1 s)%CR x).
   rewrite ->  CRle_Qle.
   apply Qmin_lb_r.
  rewrite -> Qmax_min_distr_r.
  apply Qmin_case.
   intros _.
   apply (@CRle_trans _ (1-1)%CR).
   apply (CRplus_le_r x 1%CR (CRopp 1%CR)).
    assumption.
    rewrite CRplus_opp.
   rewrite -> CRle_Qle.
   exact (Qpos_nonneg d).
  intros H.
  refine (CRle_trans _ Z1).
  apply (minus_resp_leEq_rht CRasCOrdField _ _ x).
  rewrite ->  CRle_Qle.
  apply Qmax_ub_r. }
 eapply MVP_uc_fun_close_right; [|apply n_Function_ball01_sym;apply Hd0].
  eapply MVP_uc_fun_close_left.
   apply uc_prf.
   eapply ball_ex_weak_le;[|apply Z].
   apply QposInf_min_lb_r.
  rewrite ->  CRle_Qle in Hy0.
  rewrite ->  CRle_Qle in Hy1.
  rewrite -> MVP_uc_fun_sub_Q;auto.
  eapply MVP_uc_fun_close_sig_wd.
     reflexivity.
    reflexivity.
   simpl.
   apply Morphism_prf.
   eapply eq_transitive.
    apply csbf_wd.
     reflexivity.
    symmetry.
    apply (MVP_map_C_ inject_Q_hom).
   symmetry.
   change (cpoly_map_fun (MultivariatePolynomial Q_as_CRing n)
     (MultivariatePolynomial CRasCRing n) (MVP_map inject_Q_hom n) p)
       with (cpoly_map (MVP_map inject_Q_hom n) p).
   apply cpoly_map_apply.
  apply IHn.
 eapply ball_ex_weak_le;[|apply Z].
 apply QposInf_min_lb_l.
Qed.

Fixpoint MVP_uc_fun_correct_sig n
  : n_UniformlyContinuousFunction CR CR n -> n_Function (msp_as_RSetoid CR) (msp_as_RSetoid CR) n -> Prop :=
match n return n_UniformlyContinuousFunction CR CR n -> n_Function (msp_as_RSetoid CR) (msp_as_RSetoid CR) n -> Prop with
| O => fun a b => msp_eq a b
| S n' => fun f g => forall x, (0 <= x)%CR -> (x <= 1)%CR -> MVP_uc_fun_correct_sig n' (f x) (g x)
end.

(** Finally, the correctness lemma. *)
Lemma MVP_uc_fun_correct : forall n (p:MultivariatePolynomial Q_as_CRing n),
 MVP_uc_fun_correct_sig n (MVP_uc_fun n p) (MVP_CR_apply n (MVP_map inject_Q_hom n p)).
Proof.
 intros n p.
 generalize (fun e => MVP_uc_fun_close n e p).
 generalize (MVP_uc_fun n p) (MVP_CR_apply n (MVP_map inject_Q_hom n p)).
 clear p.
 induction n; intros a b H.
  apply ball_eq.
  intros. apply (H (exist _ _ H0)).
 intros x Hx0 Hx1.
 apply IHn.
 intros e.
 apply H; auto.
Qed.

End MVP_correct.
