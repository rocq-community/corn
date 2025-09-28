
(** MathClasses-style operational & structural classes for a Russell-style metric space (i.e. MetricSpace). 
  We don't put this in MathClasses because for reasons of interoperability with the existing MetricSpace 
  it is still bound to stdlib Q rather than an abstract Rationals implementation. *)

Require Import CoRN.algebra.RSetoid.
Require Import
 Arith List
 CoRN.model.totalorder.QposMinMax
 CSetoids Qmetric Qring Qinf QnnInf QnonNeg
 ProductMetric QposInf Qposclasses (* defines Equiv on Qpos *)
 UniformContinuity MathClasses.implementations.stdlib_rationals
 stdlib_omissions.Pair stdlib_omissions.Q PointFree
 MathClasses.interfaces.abstract_algebra
 MathClasses.theory.setoids MathClasses.theory.products.

Import Qinf.notations QnonNeg.coercions.

Require Vector.

Section MetricSpaceClass.

  Variable X: Type.

  Class MetricSpaceBall: Type := mspc_ball: Qinf → relation X.
Hint Unfold relation : type_classes.
  (** We used to have mspc_ball take a Qpos instead of a Qinf. Because it is sometimes convenient
   to speak in terms of a generalized notion of balls that can have infinite or negative radius, we used
   a separate derived definition for that (which return False for negative radii, True for an infinite radius,
   and reduced to setoid equality for a radius equal to 0). This kinda worked, but had a big downside.
   The derived generalized ball relation (let's call it "gball") was defined using case distinctions on the
   finiteness and sign of the radius. These case distinctions routinely got in the way, because it
   meant that e.g. gball for the product metric space did not reduce to the composition of gballs derived
   for the constituent metrics spaces. Consequently, both the basic ball and the generalized ball
   relation were used side-by-side, and converting between the two was a constant annoyance.

   Because of this, we now use the generalized type for the "basic" ball. Now the product metric space's
   (generalized) ball relation is defined directly in terms of the constituent metric spaces' balls, and
   so reduces nicely. It also means that there is now a _single_ ball relation that is used everywhere.

   Of course, when defining the ball relation for a concrete metric space, the generalization to a Qinf
   parameter implies "more work". Fortunately, the additional work can be factored out into a smart
   constructor (defined later in this module) that takes the version with a Qpos parameter and extends
   it to Qinf in the way described above. All the ball's properties can be lifted along with this extension. *)

  Context `{!MetricSpaceBall}.

  Class MetricSpaceClass: Prop :=
    { mspc_ball_proper:: forall (e1 e2 : Qinf) (x y : X),
          equiv e1 e2 -> (mspc_ball e1 x y <-> mspc_ball e2 x y)
    ; mspc_ball_inf: ∀ x y, mspc_ball Qinf.infinite x y
    ; mspc_ball_negative: ∀ (e: Q), (e < 0)%Q → ∀ x y, ~ mspc_ball e x y
    ; mspc_refl:: ∀ e, (0 <= e)%Qinf → Reflexive (mspc_ball e)
    ; mspc_sym:: ∀ e, Symmetric (mspc_ball e)
    ; mspc_triangle: ∀ (e1 e2: Qinf) (a b c: X),
         mspc_ball e1 a b → mspc_ball e2 b c → mspc_ball (e1 + e2) a c
    ; mspc_closed: ∀ (e: Qinf) (a b: X),
         (∀ d: Qpos, mspc_ball (e + d) a b) → mspc_ball e a b
    ; mspc_stable: ∀ (e: Q) (a b: X),
         (~~mspc_ball e a b) → mspc_ball e a b }.

  Context `{MetricSpaceClass}.

  Local Instance mspc_equiv : Equiv X :=
    fun x y => mspc_ball 0 x y.

  (** Two simple derived properties: *)
  Lemma mspc_eq a b: (∀ e: Qpos, mspc_ball e a b) → a = b.
  Proof with auto.
   intros.
   apply mspc_closed.
   intros.
   rewrite (mspc_ball_proper (0+d)%Qinf d).
   apply H1.
   change (0 + d == d). ring.
  Qed.

  Lemma mspc_ball_weak_le (q q': Qinf): (q <= q')%Qinf → ∀ x y: X, mspc_ball q x y → mspc_ball q' x y.
  Proof with auto.
   destruct q, q'; simpl; intros...
     assert (q0 == q + (q0 - q))%Q as E by ring.
     rewrite (mspc_ball_proper q0 (q+(q0-q)) x y E).
     change (mspc_ball (Qinf.finite q + Qinf.finite (q0 - q)%Q) x y).
     apply mspc_triangle with y...
     apply mspc_refl.
     simpl.
     apply QArith_base.Qplus_le_r with q.
     ring_simplify...
    apply mspc_ball_inf.
   intuition.
  Qed.

  Lemma mspc_ball_e_wd : ∀ (e d : Q) (x y : X),
      e == d → mspc_ball e x y ↔ mspc_ball d x y.
  Proof.
    intros. apply mspc_ball_proper, H1.
  Qed. 

  Lemma mspc_ball_wd : forall (e d : Qinf) x1 x2 y1 y2,
      e = d -> x1 = x2 -> y1 = y2
      -> (mspc_ball e x1 y1 <-> mspc_ball d x2 y2).
  Proof.
    unfold equiv, mspc_equiv. split.
    - intros.
      destruct d as [d|]. 2: apply mspc_ball_inf.
      destruct e as [e|]. 2: inversion H1. simpl in H1.
    assert (0+(e+0) == d).
    { rewrite Qplus_0_r, Qplus_0_l. exact H1. }
    apply (mspc_ball_e_wd _ _ x2 y2 H5).
    clear H5 H1 d.
    pose proof (mspc_triangle 0 (e+0) x2 x1 y2).
    apply H1. clear H1.
    apply mspc_sym, H2.
    pose proof (mspc_triangle e 0 x1 y1 y2).
    apply H5. exact H4. exact H3.
  - intros.
    destruct e as [e|]. 2: apply mspc_ball_inf.
    destruct d as [d|]. 2: inversion H1. simpl in H1. 
    assert (0+(d+0) == e).
    { rewrite Qplus_0_r, Qplus_0_l. rewrite H1. reflexivity. }
    apply (mspc_ball_e_wd _ _ x1 y1 H5).
    clear H5 H1 e.
    pose proof (mspc_triangle 0 (d+0) x1 x2 y1).
    apply H1. exact H2. clear H1.
    pose proof (mspc_triangle d 0 x2 y2 y1).
    apply H1. exact H4.
    apply mspc_sym, H3.
  Qed.


  (** Instances can be bundled to yield MetricSpaces: *)
  Program Definition bundle_MetricSpace: MetricSpace :=
    Build_MetricSpace mspc_ball_e_wd _.

  Next Obligation. Proof with auto.
   constructor.
   - intros e epos. apply mspc_refl, epos.
   - intros. apply mspc_sym.
   - intros. apply (mspc_triangle e1 e2 a b c)...
   - intros. apply mspc_closed...
     intros. apply H1. apply Qpos_ispos.
   - intros. apply Qnot_lt_le. intro abs.
     destruct H0. exact (mspc_ball_negative0 e abs a b H1).
   - intros. apply mspc_stable, H1.
  Qed.

  (** .. which obviously have the same carrier: *)

  Goal X ≡ bundle_MetricSpace.
  Proof. reflexivity. Qed.

End MetricSpaceClass.

#[global]
Instance: Params (@mspc_ball) 2 := {}.

#[global]
Hint Resolve Qlt_le_weak Qplus_lt_le_0_compat.
  (* Todo: Move. *)

(** We now define the smart constructor that builds a MetricSpace from a ball relation with positive radius. *)

Section genball.

  Context
    `{Setoid X}
    (R: Qpos → relation X) `{!Proper (QposEq ==> (=)) R}  `{∀ e, Reflexive (R e)} `{∀ e, Symmetric (R e)}
    (Rtriangle: ∀ (e1 e2: Qpos) (a b c: X), R e1 a b → R e2 b c → R (e1 + e2)%Qpos a c)
    (Req: ∀ (a b: X), (∀ d: Qpos, R d a b) → a = b)
    (Rclosed: ∀ (e: Qpos) (a b: X), (∀ d: Qpos, R (e + d)%Qpos a b) → R e a b)
    (Rstable: ∀ (e: Qpos) (a b: X), (~~R e a b) → R e a b).

  Definition genball: MetricSpaceBall X := λ (oe: Qinf),
    match oe with
    | Qinf.infinite => λ _ _, True
    | Qinf.finite e =>
      match Qdec_sign e with
      | inl (inl _) => λ _ _ , False
      | inl (inr p) => R (exist (Qlt 0) e p)
      | inr _ => equiv
      end
    end.

  Definition ball_genball (q: Qpos) (a b: X): genball q a b ↔ R q a b.
  Proof.
   unfold genball; simpl.
   destruct Qdec_sign as [[|]|U].
     exfalso.
     destruct q.
     apply (Qlt_is_antisymmetric_unfolded 0 x); assumption.
    apply Proper0; reflexivity.
   exfalso.
   destruct q.
   simpl in U.
   revert q.
   rewrite U.
   apply Qlt_irrefl.
  Qed.

  Lemma genball_alt (q: Q) (x y: X):
    genball q x y <-> 
        match Qdec_sign q with
        | inl (inl _) => False
        | inl (inr p) => genball q x y
        | inr _ => x=y
        end.
  Proof.
   unfold genball. simpl.
   split; destruct Qdec_sign as [[|]|]; auto.
  Qed.

  Instance genball_Proper: Proper ((=) ==> (=) ==> (=) ==> iff) genball.
  Proof with auto; intuition; auto with *.
   unfold genball.
   intros u e' E.
   destruct u, e'.
      change (q = q0) in E.
      destruct Qdec_sign as [[|]|]; destruct Qdec_sign as [[|]|].
              repeat intro...
             exfalso. revert q1. apply Qlt_is_antisymmetric_unfolded. rewrite E...
            exfalso. revert q1. rewrite E. rewrite q2. apply Qlt_irrefl.
           exfalso. revert q1. rewrite E. apply Qlt_is_antisymmetric_unfolded...
          apply Proper0...
         exfalso. revert q1. rewrite E, q2. apply Qlt_irrefl.
        exfalso. revert q2. rewrite <- E, q1. apply Qlt_irrefl.
       exfalso. revert q2. rewrite <- E, q1. apply Qlt_irrefl.
      intros ?? A ?? B. rewrite A, B...
     repeat intro...
    intuition; auto with *.
   repeat intro.
   reflexivity.
  Qed.

Instance: ∀ e, Proper ((=) ==> (=) ==> iff) (genball e).
Proof. intros; now apply genball_Proper. Qed.

  Lemma genball_negative (q: Q): (q < 0)%Q → ∀ x y: X, ~ genball q x y.
  Proof with auto.
   unfold genball.
   intros E ??.
   destruct Qdec_sign as [[|]|U]; intro...
    apply (Qlt_is_antisymmetric_unfolded 0 q)...
   revert E.
   rewrite U.
   apply Qlt_irrefl.
  Qed.

  Lemma genball_Reflexive (q: Qinf): (0 <= q)%Qinf → Reflexive (genball q).
  Proof with auto.
   repeat intro.
   unfold genball.
   destruct q...
   destruct Qdec_sign as [[|]|]; intuition; auto with *.
   apply (Qlt_not_le q 0)...
  Qed.

  Global Instance genball_Symmetric: ∀ e, Symmetric (genball e).
  Proof with auto.
   intros [q|]... simpl. destruct Qdec_sign as [[|]|]; try apply _...
  Qed.

  Lemma genball_triangle (e1 e2: Qinf) (a b c: X): genball e1 a b → genball e2 b c → genball (e1 + e2) a c.
  Proof with auto.
   intros U V.
   destruct e1 as [e1|]...
   destruct e2 as [e2|]...
   apply genball_alt.
   apply genball_alt in U.
   apply genball_alt in V.
   destruct (Qdec_sign (e1 + e2)) as [[G | I] | J];
   destruct (Qdec_sign e1) as [[A | B] | C];
   destruct (Qdec_sign e2) as [[D | E] | F]; intuition.
   revert G. apply (Qlt_is_antisymmetric_unfolded _ _)...
   revert G. rewrite F, Qplus_0_r. apply (Qlt_is_antisymmetric_unfolded _ _ B)...
   revert G. rewrite C, Qplus_0_l. apply (Qlt_is_antisymmetric_unfolded _ _ E)...
   revert G. rewrite C, F. apply Qlt_irrefl.
   change (genball (exist _ e1 B + exist _ e2 E )%Qpos a c).
   apply ball_genball.
   apply Rtriangle with b; apply ball_genball...
   rewrite <- V.
   assert (e1 + e2 == e1) by (rewrite F, Qplus_0_r; reflexivity).
   apply (genball_Proper (e1+e2) e1 H2 a a (reflexivity _) b b (reflexivity _)), U.
   rewrite U.
   assert (e1 + e2 == e2) by (rewrite C, Qplus_0_l; reflexivity).
   apply (genball_Proper (e1+e2) e2 H2 b b (reflexivity _) c c (reflexivity _)), V.
   rewrite U, V.
   apply genball_Reflexive.
   apply Qlt_le_weak, I.
   exfalso.
   apply Qlt_le_weak in E.
   apply (Qplus_lt_le_compat _ _ _ _ B) in E.
   rewrite J in E. apply (Qlt_irrefl 0 E).
   exfalso. rewrite F, Qplus_0_r in J.
   rewrite J in B. exact (Qlt_irrefl 0 B).
   exfalso. rewrite C, Qplus_0_l in J.
   rewrite J in E. exact (Qlt_irrefl 0 E).
  Qed.

  Lemma genball_closed :
    (∀ (e: Qinf) (a b: X), (∀ d: Qpos, genball (e + d) a b) → genball e a b).
  Proof with auto with *.
   intros.
   unfold genball.
   destruct e...
   destruct Qdec_sign as [[|]|].
     assert (0 < (1#2) * -q)%Q.
      apply Qmult_lt_0_compat...
      apply Qopp_Qlt_0_l...
     pose proof (H2 (exist _ _ H3)).
     refine (genball_negative _ _ _ _ H4).
     simpl.
     ring_simplify.
     apply Qopp_Qlt_0_l...
     setoid_replace (- ((1 # 2) * q))%Q with (-q * (1#2))%Q by (simpl; ring).
     apply Qmult_lt_0_compat...
     apply Qopp_Qlt_0_l...
    apply Rclosed.
    intros.
    apply ball_genball.
    apply (H2 d).
   apply Req.
   intros.
   apply ball_genball.
   assert (d == q + d) by (rewrite q0, Qplus_0_l; reflexivity).
   apply (genball_Proper d (q+d) H3 a a (reflexivity _) b b (reflexivity _)), H2.
  Qed.

  Lemma genball_stable :
    (∀ (e: Q) (a b: X), (~~genball e a b) → genball e a b).
  Proof.
    intros. unfold genball.
    unfold genball in H2.
    destruct (Qdec_sign e). destruct s.
    - contradict H2. intro H2. contradiction.
    - apply Rstable, H2.
    - apply Req. unfold equiv in H2.
      intro d. apply Rstable.
      intro abs. contradict H2; intro H2.
      contradict abs.
      rewrite H2.
      apply H0.
  Qed.

  Instance genball_MetricSpace: @MetricSpaceClass X genball.
  Proof.
   constructor; try apply _.
   - unfold mspc_ball. intros. rewrite H2. reflexivity.
   - reflexivity.
   - apply genball_negative.
   - apply genball_Reflexive.
   - apply genball_triangle.
   - apply genball_closed.
   - apply genball_stable.
  Qed.

End genball.

(** Bundled MetricSpaces immediately yield instances of the classes: *)

#[global]
Instance: ∀ X: MetricSpace, MetricSpaceBall X := λ X, @genball X _ (@ball X).

#[global]
Instance class_from_MetricSpace (X: MetricSpace): MetricSpaceClass X.
Proof.
 apply genball_MetricSpace.
 - intros q r H x y H0 z t H1.
   apply ball_wd; assumption.
 - intros e. apply msp_refl. exact (msp X).
   apply Qpos_nonneg.
 - intro e. apply msp_sym, (msp X).
 - intros e1 e2. apply msp_triangle, X.
 - intros x y H.
   apply ball_closed. 
   intros. rewrite Qplus_0_l. apply (H (exist _ _ H0)).
 - intros e x y H. apply msp_closed.
   exact (msp X). intros. apply (H (exist _ _ H0)).
 - intros. apply (msp_stable (msp X)), H.
Qed.

Section products.

  Context `{MetricSpaceClass X} `{MetricSpaceClass Y}.

  Global Instance: MetricSpaceBall (X * Y)
    := λ e a b, mspc_ball X e (fst a) (fst b) ∧ mspc_ball Y e (snd a) (snd b).

  (* We do not reuse ProductMS here because to do so we'd need to go through genball,
   resulting in the problems described earlier. *)

  Global Instance: MetricSpaceClass (X * Y).
  Proof with auto.
   constructor.
   - intros. split. intros. destruct H4. split.
     rewrite <- (mspc_ball_proper X e1 e2 (fst x) (fst y) H3). exact H4.
     rewrite <- (mspc_ball_proper Y e1 e2 (snd x) (snd y) H3). exact H5.
     intros. destruct H4. split.
     rewrite (mspc_ball_proper X e1 e2 (fst x) (fst y) H3). exact H4.
     rewrite (mspc_ball_proper Y e1 e2 (snd x) (snd y) H3). exact H5.
   - split. apply (mspc_ball_inf X).
     apply (mspc_ball_inf Y).
   - repeat intro.
        destruct H4.
        apply (mspc_ball_negative X _ H3 _ _ H4).
   - intros e H3 x. split; apply mspc_refl.
     exact H0. exact H3. exact H2. exact H3.
   - split; apply (@symmetry _ _ ); try apply _; apply H3. (* just using [symmetry] here causes evar anomalies.. *)
   - split.
     apply (mspc_triangle X) with (fst b).
      apply H3.
     apply H4.
    apply (mspc_triangle Y) with (snd b).
     apply H3.
    apply H4.
   - split.
    apply (mspc_closed X). apply H3.
   apply (mspc_closed Y). apply H3.
   - split.
   apply (mspc_stable X).
   intro abs. contradict H3; intro H3.
   destruct H3. contradiction.
   apply (mspc_stable Y).
   intro abs. contradict H3; intro H3.
   destruct H3. contradiction.
  Qed.

End products.

(* Workaround Vector.Forall2, which is hard to destruct. *)
Fixpoint Vector_Forall2 {X : Type} {n : nat} (P : X -> X -> Prop)
         (x y : Vector.t X n) { struct x } : Prop.
Proof.
  destruct x as [|xh n xt].
  - exact True.
  - exact (P xh (Vector.hd y) /\ Vector_Forall2 X n P xt (Vector.tl y)).
Defined.

Section vector_setoid.

  Context `{Setoid X} (n: nat).

  Global Instance: Equiv (Vector.t X n) := Vector_Forall2 equiv.

  Global Instance vector_setoid: Setoid (Vector.t X n).
  Proof.
   constructor.
   - intro x.
     unfold equiv, Equiv_instance_0.
     induction x; simpl; constructor.
     reflexivity. exact IHx.
   - intros x y H0.
     unfold equiv, Equiv_instance_0, equiv.
     unfold equiv, Equiv_instance_0, equiv in H0.
     induction x.
     + apply (Vector.case0 (fun y => Vector_Forall2 Ae y (Vector.nil X))).
       simpl. trivial.
     + simpl in H0.
       revert H0.
       apply (Vector.caseS' y). clear y.
       intros. destruct H0.
       split. simpl. symmetry. exact H0.
       apply IHx, H1.
   - intros x y z H1 H2.
     unfold Transitive, equiv, Equiv_instance_0, equiv.
     unfold Transitive, equiv, Equiv_instance_0, equiv in H1.
     unfold Transitive, equiv, Equiv_instance_0, equiv in H2.
     induction x.
     + simpl. trivial.
     + revert H2.
       apply (Vector.caseS' z).
       clear z. intros zh zt. 
       revert H1.
       apply (Vector.caseS' y).
       clear y. intros yh yt H0 H1.
       simpl in H0. simpl in H1.
       destruct H0, H1.
       split. simpl.
       transitivity yh; assumption.
       simpl. apply (IHx yt); assumption.
  Qed.

End vector_setoid. (* Todo: Move. *)

Section vectors.

  Context `{MetricSpaceClass X} (n: nat).

  Global Instance: MetricSpaceBall (Vector.t X n) :=
    λ e, Vector_Forall2 (mspc_ball X e).

End vectors.

(** I decided to experiment with a class used strictly to declare a metric space's
 components in a section using [Context] without also declaring the metric space structure
 itself, and risking accidental parameterization of the section context on the proof of that
 metric space structure if such parametrization is unneeded (for instance because there is
 already a UniformContinuous constraint which incorporates the metric space proof. *)

Class MetricSpaceComponents X `{MetricSpaceBall X}: Prop.

(** Next, we introduce classes for uniform continuity (which is what we're really after, since
 we will use these to automatically derive uniform continuity for various forms of function
 composition). *)

Arguments mspc_ball {X MetricSpaceBall}.

Class Canonical (T: Type): Type := canonical: T.
  (* Todo: Move. *)

#[global]
Instance: ∀ {T: Type}, Canonical (T → T) := @Datatypes.id.

#[global]
Instance: Canonical (Qpos → Qinf) := Qinf.finite ∘ QposAsQ.

#[global]
Instance composed_Proper `{Equiv A} `{Equiv B} `{Equiv C} (f: B → C) (g: A → B):
  Proper (=) f → Proper (=) g → Proper (=) (f ∘ g).
Proof with auto.
 repeat intro.
 unfold Basics.compose.
 apply H2.
 apply H3.
 assumption.
Qed.

#[global]
Instance: Proper (QposEq ==> (=)) QposAsQ.
Proof. repeat intro. assumption. Qed.

Require Import util.Container.

Definition Ball X R := prod X R.
#[global]
Hint Extern 0 (Equiv (Ball _ _)) => eapply @prod_equiv : typeclass_instances.

Section Ball.
  Context X `{MetricSpaceBall X} (R: Type) `{Canonical (R → Qinf)}.

  Global Instance ball_contains: Container X (Ball X R) := fun b => mspc_ball (canonical (snd b)) (fst b).

  Context `{Equiv R} `{!MetricSpaceClass X} `{!Proper (=) (canonical: R → Qinf)}.

  Local Instance : Equiv X :=
    fun x y => mspc_ball 0 x y.

  Global Instance ball_contains_Proper: Proper (=) (In: Ball X R → X → Prop).
  Proof with auto.
   repeat intro.
   unfold In, ball_contains.
   unfold canonical. unfold canonical in Proper0.
   apply mspc_ball_wd...
    apply Proper0.
    apply H2.
    apply H2.
  Qed. (* Todo: Clean up. *)

End Ball.


(*Instance: Params (@contains) 4.

Implicit Arguments contains [[X] [H] [H0] [R]].*)


Section sig_metricspace.

  Context `{MetricSpaceClass X} (P: X → Prop).

  Global Instance sig_mspc_ball: MetricSpaceBall (sig P) := λ e x y, mspc_ball e (` x) (` y).

  Global Instance sig_mspc: MetricSpaceClass (sig P).
  Proof with auto.
   constructor.
   - intros. destruct x, y. 
     unfold mspc_ball, sig_mspc_ball. simpl.
     apply mspc_ball_wd. exact H0. exact H1.
     apply mspc_refl. exact H0. apply Qle_refl.
     apply mspc_refl. exact H0. apply Qle_refl.
   - intros.
     change (mspc_ball Qinf.infinite (` x) (` y)).
     apply (mspc_ball_inf X).
   - intros. destruct x, y. 
     unfold mspc_ball, sig_mspc_ball. simpl.
     apply mspc_ball_negative. exact H0. exact H1.
   - intros d H1 x. destruct x.
     unfold mspc_ball, sig_mspc_ball. simpl.
     apply mspc_refl. exact H0. exact H1.
   - repeat intro.
     change (mspc_ball e (` y) (` x)).
     symmetry...
   - repeat intro.
    apply (mspc_triangle X e1 e2 (` a) (` b))...
   - intros.
   apply (mspc_closed X e (` a) (` b))...
   - intros. apply (mspc_stable X e (` a) (` b))...
  Qed.

End sig_metricspace.

#[global]
Instance Qpos_mspc_ball: MetricSpaceBall Qpos
  := @sig_mspc_ball Q_as_MetricSpace _ (Qlt 0).
#[global]
Instance Qpos_mspc: MetricSpaceClass Qpos
  := @sig_mspc Q_as_MetricSpace _ _ (Qlt 0).

#[global]
Instance: Cast QnnInf.T Qinf :=
  λ x, match x with
    | QnnInf.Infinite => Qinf.infinite
    | QnnInf.Finite q => Qinf.finite (proj1_sig q)
    end.

Section uniform_continuity.

  Context `{MetricSpaceComponents X} `{MetricSpaceComponents Y}.

  Class UniformlyContinuous_mu (f: X → Y): Type := { uc_mu: Qpos → QposInf }.
    (* Note: If we omit the {} around the uc_mu field and let the class become a definitional class,
     instance resolution will often find the wrong instance because the type of uc_mu is the same for
     different instantiations of X and Y. This solution is not ideal. *)

  Context (f: X → Y) `{!UniformlyContinuous_mu f}.

  Class UniformlyContinuous: Prop :=
    { uc_from: MetricSpaceClass X
    ; uc_to: MetricSpaceClass Y
    ; uniformlyContinuous: ∀ (e: Qpos) (a b: X), mspc_ball (uc_mu e) a b → mspc_ball e (f a) (f b) }.

  (** If we have a function with this constraint, then we can bundle it into a UniformlyContinuousFunction: *)

  Context `{uc: UniformlyContinuous}.

  Let hint := uc_from.
  Let hint' := uc_to.

(*  Program Definition wrap_uc_fun
    : UniformlyContinuousFunction (bundle_MetricSpace X) (bundle_MetricSpace Y)
    := @Build_UniformlyContinuousFunction (bundle_MetricSpace X) (bundle_MetricSpace Y) f uc_mu _.

  Next Obligation. Proof with auto.
   repeat intro.
   unfold ball. simpl.
   apply uniformlyContinuous.
   destruct uc_mu...
   apply (mspc_ball_inf X).
  Qed.*)

  (** Note that wrap_uc_fun _also_ bundles the source and target metric spaces, because
   UniformlyContinuousFunction is expressed in terms of the bundled data type for metric spaces. *)

End uniform_continuity.

Arguments uc_mu {X Y} f {UniformlyContinuous_mu}.

(** Local uniform continuity just means that the function restricted to any finite balls
 is uniformly continuous: *)

Section local_uniform_continuity.

  Context `{MetricSpaceComponents X} `{MetricSpaceComponents Y}.

  Definition restrict (b: Ball X Qpos) (f: X → Y): sig ((∈ b)) → Y
    := f ∘ @proj1_sig _ _.

  Class LocallyUniformlyContinuous_mu (f: X → Y): Type :=
    luc_mu (b: Ball X Qpos):: UniformlyContinuous_mu (restrict b f).

  Context (f: X → Y) {mu: LocallyUniformlyContinuous_mu f}.

  Class LocallyUniformlyContinuous: Prop :=
    { luc_from: MetricSpaceClass X
    ; luc_to: MetricSpaceClass Y
    ; luc_uc (b: Ball X Qpos): UniformlyContinuous (restrict b f) }.

  Context `{LocallyUniformlyContinuous}.

  Local Instance : Equiv (X -> Y) :=
    fun x y => forall a : X, mspc_ball 0 (x a) (y a).

  Instance luc_Proper: Proper (=) f.
  Proof with simpl; intuition.
   repeat intro.
   pose proof luc_to.
   apply (mspc_eq Y).
   intros. apply mspc_refl.
   exact H4.
   apply Qpos_nonneg.
  Qed.

End local_uniform_continuity.


Section local_from_global_continuity.

  Context `{MetricSpaceComponents X} `{MetricSpaceComponents Y}.

  Context (f: X → Y) {mu: UniformlyContinuous_mu f} {uc: UniformlyContinuous f}.

  Instance local_from_global_uc_mu: LocallyUniformlyContinuous_mu f
    := λ _, Build_UniformlyContinuous_mu _ (uc_mu f).

  Instance local_from_global_uc: LocallyUniformlyContinuous f.
  Proof with auto.
   constructor.
     apply uc.
    apply uc.
   intro.
   pose proof (uc_from f).
   pose proof (uc_to f).
   constructor; try apply _.
   intros.
   apply (uniformlyContinuous f).
   assumption.
  Qed.

End local_from_global_continuity.


(** Normally, we would like to use the type class constraints whenever we need uniform continuity of
 functions, including in the types for higher order functions. For instance, we would like to assign
 an integration function for uniformly continuous functions a type along the lines of:
   ∀ (f: sig (∈ r) → CR) `{!UniformlyContinuous f}, CR
 However, dependent types like these get in the way when we subsequently want to express continuity
 of this higher order function itself. Hence, a modicum of bundling is hard to avoid. However, we
 only need to bundle the components of the uniformly continuous function itself---there is no need to
 also start bundling source and target metric spaces the way UniformlyContinuousFunction and
 wrap_uc_fun do. Hence, we now introduce a record for uniformly continuous functions that does not
 needlessly bundle the source and target metric spaces. *)

Section shallowly_wrapped_ucfuns.

  Context `{@MetricSpaceComponents X Xb} `{@MetricSpaceComponents Y Yb}.
    (* We must name Xe/Xb/Ye/Yb here so that we can repeat them in the implicit argument
     specification later on. This could have been avoided if Coq offered more flexible
     commands for implicit argument specification that would let one reset implicit-ness for
     individual parameters without restating the whole list. *)

  Record UCFunction: Type := ucFunction
    { ucFun_itself:> X → Y
    ; ucFun_mu: UniformlyContinuous_mu ucFun_itself
    ; ucFun_uc: UniformlyContinuous ucFun_itself }.

  Local Instance : Equiv (X -> Y) :=
    fun x y => forall a : X, mspc_ball 0 (x a) (y a).

  Global Instance: ∀ (f: UCFunction), Proper (=) (f: X → Y).
  Proof. intros. destruct f. 
   simpl.
   set (local_from_global_uc_mu ucFun_itself0).
   apply (@luc_Proper X _ Y _ ucFun_itself0 l).
   apply (local_from_global_uc _).
  Qed.

End shallowly_wrapped_ucfuns.


#[global]
Existing Instance ucFun_mu.
#[global]
Existing Instance ucFun_uc.

Arguments UCFunction X {Xb} Y {Yb}.
Arguments ucFunction {X Xb Y Yb} _ {ucFun_mu ucFun_uc}.

Section proper_functions.

  (* Todo: This is bad. Make instances for (@sig (A → B) (Proper equiv)) instead and delegate to it for UCFunction. *)

  Context `{Setoid A} `{MetricSpaceClass B}.

  Local Instance : Equiv (A -> B) :=
    fun x y => forall a : A, mspc_ball 0 (x a) (y a). 

  Let T := (@sig (A → B) (Proper equiv)).

  (* The equivalence on functions is ext_equiv, ie equivalence of images
     for each equivalent arguments. *)
  Global Instance: Equiv T := λ x y, proj1_sig x = proj1_sig y.

  Global Instance: Setoid T.
  Proof.
   constructor.
   - intros [f fproper] x. simpl.
     apply mspc_refl. exact H1. apply Qle_refl.
   - intros [f fproper] [g gproper] fgeq x. simpl.
     apply mspc_sym. exact H1. apply fgeq.
   - intros [f fproper] [g gproper] [h hproper]
            fgeq gheq x.
     simpl. 
     rewrite (mspc_ball_e_wd B 0 (0+0) (f x) (h x) eq_refl).
     pose proof (@mspc_triangle B H0 H1 0 0 (f x) (g x) (h x)).
     apply H2. apply fgeq. apply gheq.
  Qed.

  Global Instance: MetricSpaceBall T := λ e f g, Qinf.le 0 e ∧ ∀ a, mspc_ball e (` f a) (` g a).
    (* The 0<=e condition is needed because otherwise if A is empty, we cannot deduce
     False from a premise of two functions being inside a negative ball of eachother.
     If this turns out to be annoying, we can make a separate higher-priority metric space instance
     for functions from a known-nonempty type (registered with a NonEmpty type class). *)

End proper_functions.


Section uc_functions.

  (* Todo: Just delegate to proper_functions. *)

  Context `{MetricSpaceClass A} `{MetricSpaceClass B}.

  Local Instance : Equiv (A -> B) :=
    fun x y => forall a : A, mspc_ball 0 (x a) (y a). 

  Global Instance: Equiv (UCFunction A B) := equiv: relation (A→B).

  Global Instance: Setoid (UCFunction A B).
  Proof.
   constructor.
   - intros f x. apply mspc_refl. exact H2. apply Qle_refl.
   - intros f g H3 x. apply mspc_sym. exact H2. apply H3.
   - intros f g h fgeq gheq x.
     rewrite (mspc_ball_e_wd B 0 (0+0) (f x) (h x) eq_refl).
     pose proof (@mspc_triangle B H1 H2 0 0 (f x) (g x) (h x)).
     apply H3. apply fgeq. apply gheq.
  Qed.

  Global Instance: MetricSpaceBall (UCFunction A B) := λ e f g, Qinf.le 0 e ∧ ∀ a, mspc_ball e (f a) (g a).
    (* The 0<=e condition is needed because otherwise if A is empty, we cannot deduce
     False from a premise of two functions being inside a negative ball of eachother.
     If this turns out to be annoying, we can make a separate higher-priority metric space instance
     for functions from a known-nonempty type (registered with a NonEmpty type class). *)

  Lemma Proper_uc_ball : Proper equiv mspc_ball.
  Proof.
    intros d e deeq f g fgeq h k hkeq.
    split.
    - intros [dpos H3].
      split. rewrite <- deeq. exact dpos.
      intro x. specialize (H3 x).
      specialize (fgeq x).
      specialize (hkeq x).
      rewrite <- (@mspc_ball_wd B _ H2 d e (f x) (g x) (h x) (k x)
                               deeq fgeq hkeq).
      exact H3.
    - intros [dpos H3].
      split. rewrite deeq. exact dpos.
      intro x. specialize (H3 x).
      specialize (fgeq x).
      specialize (hkeq x).
      symmetry in deeq.
      apply mspc_sym in fgeq.
      apply mspc_sym in hkeq.
      rewrite <- (@mspc_ball_wd B _ H2 e d (g x) (f x) (k x) (h x)
                               deeq fgeq hkeq).
      exact H3. exact H2. exact H2.
  Qed.

  Global Instance UCFunction_MetricSpace: MetricSpaceClass (UCFunction A B).
  Proof.
   constructor.
   - split. 
     + intros. destruct H4. split.
       rewrite <- H3. exact H4. intro a.
       destruct e2 as [e2|]. 2: apply mspc_ball_inf, H2.
       destruct e1 as [e1|].
       rewrite (@mspc_ball_e_wd B _ H2 e2 e1). apply H5.
       symmetry. exact H3. inversion H3.
     + intros. destruct H4. split.
       rewrite H3. exact H4. intro a.
       destruct e1 as [e1|]. 2: apply mspc_ball_inf, H2.
       destruct e2 as [e2|].
       rewrite (@mspc_ball_e_wd B _ H2 e1 e2). apply H5.
       exact H3. inversion H3.
   - intros f g. split. simpl. trivial.
     intro x. apply (mspc_ball_inf B).
   - intros. intros [H4 _].
     exact (Qlt_not_le _ _ H3 H4).
   - intros e epos f. split. exact epos.
     intros x. apply (mspc_refl B _ epos).
   - intros e f g [epos H3].
     split. exact epos. intro x.
     apply (mspc_sym B), (H3 x).
   - intros. destruct H3, H4. split.
     apply Qinf.le_0_plus_compat; assumption.
     intros x. specialize (H5 x). specialize (H6 x).
     apply (mspc_triangle B) with (b x); assumption.
   - intros. split.
     + destruct e as [e|]. 2: simpl; auto.
       simpl. destruct (Qlt_le_dec e 0). 2: exact q.
       exfalso.
       assert (0 < (1#2) * -e)%Q.
       apply Qmult_lt_0_compat. reflexivity.
       apply Qopp_Qlt_0_l, q.
       destruct (H3 (exist _ _ H4)) as [H5 _].
       simpl in H5. clear q.
       apply (Qlt_not_le _ _ H4). clear H4.
       apply (Qplus_le_l ((1#2)*e)).
       ring_simplify.
       ring_simplify in H5.
       setoid_replace (0#4) with 0%Q by reflexivity.
       exact H5.
     + intros x.
       apply (mspc_closed B).
       intros. apply H3.
   - intros e f g H3. split.
     + apply Qnot_lt_le. intro H4.
       contradict H3; intro H3.
       destruct H3 as [H3 _].
       exact (Qlt_not_le _ _ H4 H3).
     + intro x.
       apply (mspc_stable B). intro abs.
       contradict H3; intro H3.
       destruct H3 as [epos H3].
       exact (abs (H3 x)).
  Qed.

End uc_functions.

(** If source and target are /already/ bundled, then we don't need to rebundle them when bundling
 a uniformly continuous function: *)

Program Definition wrap_uc_fun' {X Y: MetricSpace} (f: X → Y)
  `{!UniformlyContinuous_mu f}
  `{@UniformlyContinuous X _ Y _ f _}:
    UniformlyContinuousFunction X Y :=
  @Build_UniformlyContinuousFunction X Y f (uc_mu f) _.

Next Obligation. Proof with auto.
 intros ????.
 assert (mspc_ball (uc_mu f e) a b).
  revert H0.
  set (uc_mu f e).
  intros.
  destruct q...
  apply <- (ball_genball (@ball X) q)...
 pose proof (uniformlyContinuous f e a b H1).
 apply (@ball_genball Y (@msp_eq Y) _
                      (fun q => ball (proj1_sig q))).
 2: auto.
 intros x y H4 z t H5 u v H6.
 unfold QposEq in H4. rewrite H4. 
 rewrite H5, H6. reflexivity.
Qed.

(** Conversely, if we have a UniformlyContinuousFunction (between bundled metric spaces) and project
 the real function out of it, instances of the classes can easily be derived. *)

Open Scope uc_scope.

Section unwrap_uc.

  Context {X Y: MetricSpace} (f: X --> Y).

  Global Instance unwrap_mu: UniformlyContinuous_mu f := { uc_mu := mu f }.

  Global Instance unwrap_uc_fun: UniformlyContinuous f.
  Proof with auto.
   constructor; try apply _.
   unfold uc_mu, unwrap_mu.
   destruct f.
   simpl. intros.
   unfold mspc_ball.
   unfold MetricSpaceBall_instance_0.
   apply ball_genball.
    apply _.
   apply uc_prf.
   set (mu e) in *.
   destruct q...
   simpl.
   apply (@ball_genball X (@msp_eq X) _
                      (fun q => ball (proj1_sig q))).
   2: auto.
   intros x y H4 z t H5 u v H6.
   unfold QposEq in H4. rewrite H4. 
   rewrite H5, H6. reflexivity.
  Qed.

End unwrap_uc.

(** Extentionally equal functions are obviously equally uniformly continuous (with extensionally equal mu's): *)

Lemma UniformlyContinuous_proper `{MetricSpaceClass X} `{MetricSpaceClass Y} (f g: X → Y)
  `{!UniformlyContinuous_mu f} `{!UniformlyContinuous_mu g}:
  (∀ x, mspc_equiv Y (f x) (g x)) → (∀ e, uc_mu f e ≡ uc_mu g e) →
    UniformlyContinuous f → UniformlyContinuous g.
      (* Todo: Stronger versions of this statement can be proved with a little effort. *)
Proof.
 constructor; try apply _.
 intros ????.
 pose proof (mspc_ball_proper Y) as H7.
 rewrite <- (mspc_ball_wd Y e e (f a) (g a) (f b) (g b)).
 apply (uniformlyContinuous f).
 rewrite H4. auto.
 reflexivity. apply H3. apply H3.
Qed.


(** We now show that a couple of basic functions are continuous: *)

(** The identity function is uniformly continuous: *)

Section id_uc. Context `{MetricSpaceClass X}.
  Global Instance: UniformlyContinuous_mu (@Datatypes.id X) := { uc_mu := Qpos2QposInf }.
  Global Instance: UniformlyContinuous (@Datatypes.id X).
  Proof. constructor; try apply _. intros. assumption. Qed.
End id_uc.
  (* Note: We don't need a separate instance for the [id] constant. If such an instance
   is needed, we can use [Hint Unfold id: typeclass_instances.] *)

(** Constant functions are uniformly continuous: *)

Section const_uc. Context `{MetricSpaceClass X} `{MetricSpaceClass Y} (y: Y).
  Global Instance: UniformlyContinuous_mu (@Basics.const Y X y) := { uc_mu := λ _, QposInfinity }.
  Global Instance: UniformlyContinuous (@Basics.const Y X y).
  Proof. repeat intro. constructor; try apply _. intros. apply (mspc_refl Y e). simpl. auto. Qed.
End const_uc.

(** Mapping both of a pair's components by uniformly continuous functions
 is uniformly continuous: *)

Section exist_uc.
  Context `{MetricSpaceComponents X} `{MetricSpaceComponents Y} (P: Y → Prop)
    (f: X → Y) (g: ∀ x, P (f x)) `{!UniformlyContinuous_mu f} `{!UniformlyContinuous f}.

  Global Instance exist_mu: UniformlyContinuous_mu (λ x: X, exist P (f x) (g x)) := { uc_mu := uc_mu f }.

  Global Instance exist_uc: UniformlyContinuous (λ x: X, exist P (f x) (g x)).
  Proof with auto.
   constructor.
     apply (uc_from f).
    pose proof (uc_to f).
    apply _.
   intros.
   apply (uniformlyContinuous f).
   assumption.
  Qed.
End exist_uc.

Section map_pair_uc.
  Context `{MetricSpaceComponents X} `{MetricSpaceComponents Y}
    `{MetricSpaceComponents A} `{MetricSpaceComponents B}
    (f: X → Y) `{!UniformlyContinuous_mu f} `{!UniformlyContinuous f}
    (g: A → B) `{!UniformlyContinuous_mu g} `{!UniformlyContinuous g}.

  Global Instance: UniformlyContinuous_mu (map_pair f g) :=
    { uc_mu := λ x, QposInf_min (uc_mu f x) (uc_mu g x) }.

  Let hint := uc_from g.
  Let hint' := uc_to g.
  Let hint'' := uc_from f.
  Let hint''' := uc_to f.

End map_pair_uc.

(** The diagonal function is uniformly continuous: *)

Section diagonal_uc.
  Context `{MetricSpaceClass X}.

  Global Instance: UniformlyContinuous_mu (@diagonal X) := { uc_mu := Qpos2QposInf }.

  Global Instance: UniformlyContinuous (@diagonal X).
  Proof. constructor; try apply _. intros ??? E. split; auto. Qed.
End diagonal_uc.

(** fst/snd/pair are uniformly continuous: *)

Section pairops_uc.
  Context `{MetricSpaceClass A} `{MetricSpaceClass B}.

  Global Instance: UniformlyContinuous_mu (@fst A B) := { uc_mu := Qpos2QposInf }.
  Global Instance: UniformlyContinuous_mu (@snd A B) := { uc_mu := Qpos2QposInf }.
  Global Instance: UniformlyContinuous_mu (uncurry (@pair A B)) := { uc_mu := Qpos2QposInf }.
  Global Instance: ∀ a, UniformlyContinuous_mu (@pair A B a) := { uc_mu := Qpos2QposInf }.

  Global Instance: UniformlyContinuous (@fst A B).
  Proof. constructor; try apply _. intros ??? P. apply P. Qed. 
  Global Instance: UniformlyContinuous (@snd A B).
  Proof. constructor; try apply _. intros ??? P. apply P. Qed. 
  Global Instance: UniformlyContinuous (uncurry (@pair A B)).
  Proof. constructor; try apply _. intros ??? P. apply P. Qed.
  Global Instance: ∀ a, UniformlyContinuous (@pair A B a).
  Proof. constructor; try apply _. intros ??? P.  split. apply (mspc_refl A). simpl. auto. apply P. Qed.
End pairops_uc.

Section compose_uc.
  Context `{MetricSpaceComponents X}  `{MetricSpaceComponents Y} `{MetricSpaceComponents Z'}
   (f: Y → Z') `{!UniformlyContinuous_mu f} `{!UniformlyContinuous f}
   (g: X → Y) `{!UniformlyContinuous_mu g} `{!UniformlyContinuous g}.

  Global Instance compose_mu: UniformlyContinuous_mu (f ∘ g)%prg :=
    { uc_mu := λ e, QposInf_bind (uc_mu g) (uc_mu f e) }.

  Let hint := uc_from g.
  Let hint' := uc_to g.
  Let hint'' := uc_to f.

End compose_uc.

Section curried_uc.
  Context `{MetricSpaceClass X} `{MetricSpaceClass Y} `{MetricSpaceClass Z'} (f: X → Y → Z')
   `{fmu1: ∀ x: X, UniformlyContinuous_mu (f x)}
   `{fuc1: ∀ x: X, UniformlyContinuous (f x)}
   `{fmu: !UniformlyContinuous_mu (λ p, f (fst p) (snd p))}
   `{fuc: !UniformlyContinuous (λ p, f (fst p) (snd p))}.

  Local Notation F := (λ x: X, {| ucFun_itself := λ y: Y, f x y; ucFun_mu := fmu1 x; ucFun_uc := fuc1 x |}).

  Global Instance curried_mu: UniformlyContinuous_mu F := { uc_mu := uc_mu (λ p, f (fst p) (snd p)) }.

  Global Instance curried_uc: UniformlyContinuous F.
  Proof with simpl; auto.
   constructor; try apply _.
   split...
   simpl in *.
   destruct fuc.
   intros.
   apply (@uniformlyContinuous0 e (a, a0) (b, a0)).
   simpl.
   set (q := uc_mu (λ p, f (fst p) (snd p)) e) in *.
   destruct q...
    split...
    apply (mspc_refl Y)...
   apply (mspc_ball_inf _).
  Qed.
End curried_uc.

Class HasLambda `{X: Type} (x: X): Prop.

#[global]
Instance lambda_has_lambda `(f: A → B): HasLambda (λ x, f x) := {}.
#[global]
Instance application_has_lambda_left: ∀ `(f: A → B) (x: A), HasLambda f → HasLambda (f x) := {}.
#[global]
Instance application_has_lambda_right: ∀ `(f: A → B) (x: A), HasLambda x → HasLambda (f x) := {}.


Section lambda_uc.

  Context `{MetricSpaceComponents A} `{MetricSpaceComponents B}  (f: A → B).

  Global Instance lambda_mu `{!HasLambda f} {free_f: A → B} `{!PointFree f free_f} `{!UniformlyContinuous_mu free_f}: UniformlyContinuous_mu f.
    (* Note: The HasLambda and PointFree constraints cannot be added to the Context declaration
     above because the definition of this mu needs to depend on them /despite/ not using them.
     Without the dependency, lambda_mu would be allowed to find a random free_f of the right signature
     for which it happens to have a mu already, and use that one.
     We do not factor out the mu constraint either, because for (dubious) efficiency reasons it is critical
     that it appear /after/ the PointFree constraint.*)
  Proof. constructor. apply UniformlyContinuous_mu0. Defined.

  Context `{!HasLambda f} {free_f: A → B} `{!PointFree f free_f} `{!UniformlyContinuous_mu free_f} `{!UniformlyContinuous free_f}.

  Global Instance lambda_uc: UniformlyContinuous f.
  Proof.
   destruct UniformlyContinuous0.
   constructor.
     apply _.
    apply _.
   destruct uc_from0.
   destruct uc_to0.
   intros.
   unfold PointFree in PointFree0.
   rewrite PointFree0.
   apply uniformlyContinuous0.
   unfold uc_mu in H3.
   simpl in H3.
   assumption.
  Qed. (* Todo: Clean up. *)

End lambda_uc.

(*
Module test.
Section test.

  Context
    `{MetricSpaceClass A}
    (f: A → A → A)
    `{!UniformlyContinuous_mu (uncurry f)} `{!UniformlyContinuous (uncurry f)}
    `{!Proper (=) f}.

  Definition t0: UniformlyContinuous_mu (λ (x: A), f (f x x) (f x (f x x))) := _.

End test.
End test.
*)
