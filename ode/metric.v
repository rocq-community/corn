Require Import CoRN.algebra.RSetoid.
Require Import CoRN.metric2.Metric.
Require Import CoRN.metric2.UniformContinuity.
From Coq Require Import QArith.
Require Import MathClasses.theory.setoids (* Equiv Prop *) MathClasses.theory.products
  MathClasses.implementations.stdlib_rationals (*Qinf*) (*Qpossec QposInf QnonNeg*) MathClasses.interfaces.abstract_algebra MathClasses.implementations.QType_rationals MathClasses.interfaces.additional_operations.
Require CoRN.model.structures.Qinf.
(*Import (*QnonNeg.notations*) QArith.*)
Require Import CoRN.tactics.Qauto.
From Coq Require Import QOrderedType.
(*Require Import orders.*)
Require Import MathClasses.theory.rings MathClasses.theory.dec_fields MathClasses.orders.rings MathClasses.orders.dec_fields MathClasses.theory.nat_pow.
Require Import MathClasses.interfaces.naturals MathClasses.interfaces.orders.
Import peano_naturals.

Require Import CoRN.reals.fast.CRGeometricSum.
Import Qround Qpower Qinf.notations Qinf.coercions.

(* Set Printing Coercions.*)

Definition ext_plus {A} `{Plus B} : Plus (A -> B) := λ f g x, f x + g x.
#[global]
Hint Extern 10 (Plus (_ -> _)) => apply @ext_plus : typeclass_instances.

Definition ext_negate {A} `{Negate B} : Negate (A -> B) := λ f x, - (f x).
#[global]
Hint Extern 10 (Negate (_ -> _)) => apply @ext_negate : typeclass_instances.

(* The definitions above replace the following.
Notation "f +1 g" := (λ x, f x + g x) (at level 50, left associativity).*)

Definition comp_inf {X Z : Type} (g : Q -> Z) (f : X -> Qinf) (inf : Z) (x : X) :=
match (f x) with
| Qinf.finite y => g y
| Qinf.infinite => inf
end.

(* [po_proper'] is useful for proving [a2 ≤ b2] from [H : a1 ≤ b1] when
[a1 = a2] and [b1 = b2]. Then [apply (po_proper' H)] generates [a1 = a2]
and [b1 = b2]. Should it be moved to MathClasses? *)
Lemma po_proper' `{PartialOrder A} {x1 x2 y1 y2 : A} :
  x1 ≤ y1 -> x1 = x2 -> y1 = y2 -> x2 ≤ y2.
Proof. intros A1 A2 A3; now apply (po_proper _ _ A2 _ _ A3). Qed.

(* This is a special case of lt_ne_flip. Do we need it? *)
(*Instance pos_ne_0 : forall `{StrictSetoidOrder A} `{Zero A} (x : A),
  PropHolds (0 < x) -> PropHolds (x ≠ 0).
Proof. intros; now apply lt_ne_flip. Qed.*)

Definition ext_equiv' `{Equiv A} `{Equiv B} : Equiv (A → B) :=
  λ f g, ∀ x : A, f x = g x.

Infix "=1" := ext_equiv' (at level 70, no associativity) : type_scope.

Lemma ext_equiv_l `{Setoid A, Setoid B} (f g : A -> B) :
  Proper ((=) ==> (=)) f -> f =1 g -> f = g.
Proof. intros P eq1_f_g x y eq_x_y; rewrite eq_x_y; apply eq1_f_g. Qed.

Lemma ext_equiv_r `{Setoid A, Setoid B} (f g : A -> B) :
  Proper ((=) ==> (=)) g -> f =1 g -> f = g.
Proof. intros P eq1_f_g x y eq_x_y; rewrite <- eq_x_y; apply eq1_f_g. Qed.

(*Ltac MCQconst t :=
match t with
(*| @zero Q _ _ => constr:(Qmake Z0 xH)
| @one Q _ _ => constr:(Qmake (Zpos xH) xH)*)
| _ => Qcst t
end.

Add Field Q : (stdlib_field_theory Q)
  (decidable Qeq_bool_eq,
   completeness Qeq_eq_bool,
   constants [MCQconst]).

Goal forall x y : Q, (1#1)%Q * x = x.
intros x y. ring.*)

(*
Local Notation Qnn := QnonNeg.T.

Instance Qnn_eq : Equiv Qnn := eq.
Instance Qnn_zero : Zero Qnn := QnonNeg.zero.
Instance Qnn_one : One Qnn := QnonNeg.one.
Instance Qnn_plus : Plus Qnn := QnonNeg.plus.
Instance Qnn_mult : Mult Qnn := QnonNeg.mult.
Instance Qnn_inv : DecRecip Qnn := QnonNeg.inv.

Instance Qpos_eq : Equiv Qpos := Qpossec.QposEq.
Instance Qpos_one : One Qpos := Qpossec.Qpos_one.
Instance Qpos_plus : Plus Qpos := Qpossec.Qpos_plus.
Instance Qpos_mult : Mult Qpos := Qpossec.Qpos_mult.
Instance Qpos_inv : DecRecip Qpos := Qpossec.Qpos_inv.

Instance Qinf_one : One Qinf := 1%Q.
*)

#[global]
Instance Qinf_le : Le Qinf := Qinf.le.
#[global]
Instance Qinf_lt : Lt Qinf := Qinf.lt.

(*
Ltac mc_simpl := unfold
  equiv, zero, one, plus, negate, mult, dec_recip, le, lt.

Ltac Qsimpl' := unfold
  Qnn_eq, Qnn_zero, Qnn_one, Qnn_plus, Qnn_mult, Qnn_inv,
  QnonNeg.eq, QnonNeg.zero, QnonNeg.one, QnonNeg.plus, QnonNeg.mult, QnonNeg.inv,
  Qpos_eq, Qpos_one, Qpos_plus, Qpos_mult, Qpos_inv,
  Qpossec.QposEq, Qpossec.Qpos_one, Qpossec.Qpos_plus, Qpossec.Qpos_mult, Qpossec.Qpos_inv,
  Qinf.eq, Qinf.lt, Qinf_lt, Qinf_one, Zero_instance_0 (* Zero Qinf *),
  Q_eq, Q_lt, Q_le, Q_0, Q_1, Q_opp, Q_plus, Q_mult, Q_recip;
  mc_simpl;
  unfold to_Q, QposAsQ;
  simpl.

Ltac nat_simpl := unfold
  nat_equiv, nat_0, nat_1, nat_plus, nat_plus, nat_mult, nat_le, nat_lt;
  mc_simpl;
  simpl.

Tactic Notation "Qsimpl" hyp_list(A) := revert A; Qsimpl'; intros A.
*)

Bind Scope mc_scope with Q.

(*Section QField.*)

Add Field Q : (stdlib_field_theory Q).

Class MetricSpaceBall (X : Type) : Type := mspc_ball: Qinf → relation X.
#[global] Instance: Params (@mspc_ball) 2 := {}.

Local Notation ball := mspc_ball.

(* In the proof of Banach fixpoint theorem we have to use arithmetic
expressions such as q^n / (1 - q) when 0 <= q < 1 as the ball radius. If
the radius is in Qnn (ie., QnonNeg.T), then we have to prove that 1 - q :
Qnn. It seems more convenient to have the radius live in Q and have the
axiom that no points are separated by a negative distance. *)

Class ExtMetricSpaceClass (X : Type) `{MetricSpaceBall X} : Prop := {
  mspc_radius_proper : Proper ((=) ==> (≡) ==> (≡) ==> iff) ball;
  mspc_inf: ∀ x y, ball Qinf.infinite x y;
  mspc_negative: ∀ (e: Q), e < 0 → ∀ x y, ~ ball e x y;
  mspc_refl:: ∀ e : Q, 0 ≤ e → Reflexive (ball e);
  mspc_symm:: ∀ e, Symmetric (ball e);
  mspc_triangle: ∀ (e1 e2: Q) (a b c: X),
     ball e1 a b → ball e2 b c → ball (e1 + e2) a c;
  mspc_closed: ∀ (e: Q) (a b: X),
     (∀ d: Q, 0 < d -> ball (e + d) a b) → ball e a b
}.

Class MetricSpaceDistance (X : Type) := msd : X -> X -> Q.
#[global] Instance: Params (@msd) 2 := {}.

Class MetricSpaceClass (X : Type) `{ExtMetricSpaceClass X} `{MetricSpaceDistance X} : Prop :=
  mspc_distance : forall x1 x2 : X, ball (msd x1 x2) x1 x2.

Section ExtMetricSpace.

Context `{ExtMetricSpaceClass X}.

Global Instance mspc_equiv : Equiv X := λ x1 x2, ball 0%Q x1 x2.

Global Instance mspc_setoid : Setoid X.
Proof.
constructor.
+ now apply mspc_refl.
+ apply mspc_symm.
+ intros x1 x2 x3 eq12 eq23.
  unfold mspc_equiv, equiv; change 0%Q with (0%Q + 0%Q); now apply mspc_triangle with (b := x2).
Qed.

Global Instance mspc_proper : Proper ((=) ==> (=) ==> (=) ==> iff) ball.
Proof.
assert (A := @mspc_radius_proper X _ _).
intros e1 e2 Ee1e2 x1 x2 Ex1x2 y1 y2 Ey1y2;
destruct e1 as [e1 |]; destruct e2 as [e2 |]; split; intro B; try apply mspc_inf;
try (unfold Qinf.eq, equiv in *; contradiction).
+ mc_setoid_replace e2 with (0 + (e2 + 0)) by ring.
  apply mspc_triangle with (b := x1); [apply mspc_symm, Ex1x2 |].
  now apply mspc_triangle with (b := y1); [rewrite <- Ee1e2 |].
+ mc_setoid_replace e1 with (0 + (e1 + 0)) by ring.
  apply mspc_triangle with (b := x2); [apply Ex1x2 |].
  now apply mspc_triangle with (b := y2); [rewrite Ee1e2 | apply mspc_symm].
Qed.

Lemma mspc_refl' (e : Qinf) : 0 ≤ e → Reflexive (ball e).
Proof.
intros E. destruct e as [e |].
+ apply mspc_refl, E.
+ intro x; apply mspc_inf.
Qed.

Lemma mspc_triangle' :
  ∀ (q1 q2 : Q) (x2 x1 x3 : X) (q : Q),
    q1 + q2 = q → ball q1 x1 x2 → ball q2 x2 x3 → ball q x1 x3.
Proof.
intros q1 q2 x2 x1 x3 q A1 A2 A3. rewrite <- A1. eapply mspc_triangle; eauto.
Qed.

Lemma mspc_monotone :
  ∀ q1 q2 : Q, q1 ≤ q2 -> ∀ x y : X, ball q1 x y → ball q2 x y.
Proof.
intros q1 q2 A1 x y A2.
apply (mspc_triangle' q1 (q2 - q1) y); [ring | trivial |]. apply mspc_refl.
apply (order_preserving (+ (-q1))) in A1. now rewrite plus_negate_r in A1.
Qed.

Lemma mspc_monotone' :
  ∀ q1 q2 : Qinf, q1 ≤ q2 -> ∀ x y : X, ball q1 x y → ball q2 x y.
Proof.
intros [q1 |] [q2 |] A1 x y A2; try apply mspc_inf.
+ apply (mspc_monotone q1); trivial.
+ elim A1.
Qed.

Lemma mspc_eq : ∀ x y : X, (∀ e : Q, 0 < e -> ball e x y) ↔ x = y.
Proof.
intros x y; split; intro A.
+ apply mspc_closed; intro d. change 0%Q with (@zero Q _); rewrite plus_0_l; apply A.
+ intros e e_pos. apply (mspc_monotone 0); trivial; solve_propholds.
Qed.

Lemma radius_nonneg (x y : X) (e : Q) : ball e x y -> 0 ≤ e.
Proof.
intro A. destruct (le_or_lt 0 e) as [A1 | A1]; [trivial |].
contradict A; now apply mspc_negative.
Qed.

End ExtMetricSpace.

Section MetricSpace.

Context `{MetricSpaceClass X}.

Lemma msd_nonneg (x1 x2 : X) : 0 ≤ msd x1 x2.
Proof. apply (radius_nonneg x1 x2), mspc_distance. Qed.

End MetricSpace.

Section SubMetricSpace.

Context `{ExtMetricSpaceClass X} (P : X -> Prop).

Global Instance sig_mspc_ball : MetricSpaceBall (sig P) := λ e x y, ball e (`x) (`y).

Global Instance sig_mspc : ExtMetricSpaceClass (sig P).
Proof.
constructor.
+ repeat intro; rapply mspc_radius_proper; congruence.
+ repeat intro; rapply mspc_inf.
+ intros; now rapply mspc_negative.
+ repeat intro; now rapply mspc_refl.
+ repeat intro; now rapply mspc_symm.
+ repeat intro; rapply mspc_triangle; eauto.
+ repeat intro; now rapply mspc_closed.
Qed.

Context {d : MetricSpaceDistance X} {MSC : MetricSpaceClass X}.

Global Instance sig_msd : MetricSpaceDistance (sig P) := λ x y, msd (`x) (`y).

Global Instance sig_mspc_distance : MetricSpaceClass (sig P).
Proof. intros x1 x2; apply: mspc_distance. Qed.

End SubMetricSpace.

Section ProductMetricSpace.

Context `{ExtMetricSpaceClass X, ExtMetricSpaceClass Y}.

Global Instance Linf_product_metric_space_ball : MetricSpaceBall (X * Y) :=
  λ e a b, ball e (fst a) (fst b) /\ ball e (snd a) (snd b).

Lemma product_ball_proper : Proper ((=) ==> (≡) ==> (≡) ==> iff) ball.
Proof.
intros e1 e2 A1 a1 a2 A2 b1 b2 A3.
unfold mspc_ball, Linf_product_metric_space_ball.
rewrite A1, A2, A3; reflexivity.
Qed.

Global Instance Linf_product_metric_space_class : ExtMetricSpaceClass (X * Y).
Proof.
constructor.
+ apply product_ball_proper.
+ intros x y; split; apply mspc_inf.
+ intros e e_neg x y [A _]. eapply (@mspc_negative X); eauto.
+ intros e e_nonneg x; split; apply mspc_refl; trivial.
+ intros e a b [A1 A2]; split; apply mspc_symm; trivial.
+ intros e1 e2 a b c [A1 A2] [B1 B2]; split; eapply mspc_triangle; eauto.
+ intros e a b A; split; apply mspc_closed; firstorder.
Qed.

Context {dx : MetricSpaceDistance X} {dy : MetricSpaceDistance Y}
  {MSCx : MetricSpaceClass X} {MSCy : MetricSpaceClass Y}.

(* Need consistent names of instances for sig, product and func *)

Global Instance Linf_product_msd : MetricSpaceDistance (X * Y) :=
  λ a b, join (msd (fst a) (fst b)) (msd (snd a) (snd b)).

Global Instance Linf_product_mspc_distance : MetricSpaceClass (X * Y).
Proof.
intros z1 z2; split.
(* Without unfolding Linf_product_msd, the following [apply join_ub_l] fails *)
+ apply (mspc_monotone (msd (fst z1) (fst z2)));
  [unfold msd, Linf_product_msd; apply join_ub_l | apply mspc_distance].
+ apply (mspc_monotone (msd (snd z1) (snd z2)));
  [unfold msd, Linf_product_msd; apply join_ub_r | apply mspc_distance].
Qed.

End ProductMetricSpace.

(** We define [Func T X Y] if there is a coercion func from T to (X -> Y),
i.e., T is a type of functions. It can be instatiated with (locally)
uniformly continuous function, (locally) Lipschitz functions, contractions
and so on. For instances T of [Func] we can define supremum metric ball
(i.e., L∞ metric) and prove that T is a metric space. [Func T X Y] is
similar to [Cast T (X -> Y)], but [cast] has types as explicit arguments,
so for [f : T] one would have to write [cast _ _ f x] instead of [func f x]. *)

Class Func (T X Y : Type) := func : T -> X -> Y.

Section FunctionMetricSpace.

Context {X Y T : Type} `{Func T X Y, NonEmpty X, ExtMetricSpaceClass Y}.

(* For any type that is convertible to functions we want to define the
supremum metric. This would give rise to an equality and a setoid
([mspc_equiv] and [mspc_setoid]). Thus, when Coq needs equality on any type
T at all, it may try to prove that T is a metric space by showing that T is
convertible to functions, i.e., there is an in instance of [Func T X Y] for
some types X, Y. This is why we make [Func T X Y] the first assumption
above. This way, if there is no instance of this class, the search for
[MetricSpaceBall T] fails quickly and Coq starts looking for an equality on
T using other means. If we make, for example, [ExtMetricSpaceClass Y] the
first assumption, Coq may eneter in an infinite loop: To find
[MetricSpaceBall T] it will look for [ExtMetricSpaceClass Y] for some
uninstantiated Y, for this in needs [MetricSpaceBall Y] and so on. This is
all because Coq proves assumptions (i.e., searches instances of classes) in
the order of the assumptions. *)

Global Instance Linf_func_metric_space_ball : MetricSpaceBall T :=
  λ e f g, forall x, ball e (func f x) (func g x).

Lemma func_ball_proper : Proper ((=) ==> (≡) ==> (≡) ==> iff) (ball (X := T)).
Proof.
intros q1 q2 A1 f1 f2 A2 g1 g2 A3; rewrite A2, A3.
split; intros A4 x; [rewrite <- A1 | rewrite A1]; apply A4.
Qed.

Lemma Linf_func_metric_space_class : ExtMetricSpaceClass T.
Proof.
match goal with | H : NonEmpty X |- _ => destruct H as [x0] end.
constructor.
+ apply func_ball_proper.
+ intros f g x; apply mspc_inf.
+ intros e e_neg f g A. specialize (A x0). eapply mspc_negative; eauto.
+ intros e e_nonneg f x; now apply mspc_refl.
+ intros e f g A x; now apply mspc_symm.
+ intros e1 e2 f g h A1 A2 x. now apply mspc_triangle with (b := func g x).
+ intros e f g A x. apply mspc_closed; intros d A1. now apply A.
Qed.

End FunctionMetricSpace.

Section UniformContinuity.

Context `{MetricSpaceBall X, MetricSpaceBall Y}.

Class IsUniformlyContinuous (f : X -> Y) (mu : Q -> Qinf) := {
  uc_pos : forall e : Q, 0 < e -> (0 < mu e);
  uc_prf : ∀ (e : Q) (x1 x2: X), 0 < e -> ball (mu e) x1 x2 → ball e (f x1) (f x2)
}.

Global Arguments uc_pos f mu {_} e _.
Global Arguments uc_prf f mu {_} e x1 x2 _ _.

Record UniformlyContinuous := {
  uc_func :> X -> Y;
  uc_mu : Q -> Qinf;
  uc_proof : IsUniformlyContinuous uc_func uc_mu
}.

(* We will prove next that IsUniformlyContinuous is a subclass of Proper,
i.e., uniformly continuous functions are morphisms. But if we have [f :
UniformlyContinuous], in order for uc_func f to be considered a morphism,
we need to declare uc_proof an instance. *)
Global Existing Instance uc_proof.

Global Instance uc_proper {H1 : ExtMetricSpaceClass X} {H2 : ExtMetricSpaceClass Y}
       {f : X → Y} {mu : Q → Qinf} {_ : IsUniformlyContinuous f mu}
  :  Proper ((=) ==> (=)) f.
Proof.
intros x1 x2 A. apply -> mspc_eq. intros e e_pos. apply (uc_prf f mu); trivial.
pose proof (uc_pos f mu e e_pos) as ?.
destruct (mu e); [apply mspc_eq; trivial | apply mspc_inf].
Qed.

End UniformContinuity.

Global Arguments UniformlyContinuous X {_} Y {_}.

(* In [compose_uc] below, if we don't explicitly specify [Z] as an
argument, then [`{MetricSpaceBall Z}] does not generalize [Z] but rather
interprets it as integers. For symmetry we specify [X] and [Y] as well. *)
Global Instance compose_uc {X Y Z : Type}
  `{MetricSpaceBall X, ExtMetricSpaceClass Y, MetricSpaceBall Z}
  (f : X -> Y) (g : Y -> Z) (f_mu g_mu : Q -> Qinf)
  `{!IsUniformlyContinuous f f_mu, !IsUniformlyContinuous g g_mu} :
    IsUniformlyContinuous (g ∘ f) (comp_inf f_mu g_mu Qinf.infinite).
Proof.
constructor.
+ intros e e_pos. assert (0 < g_mu e) by (apply (uc_pos g); trivial).
  unfold comp_inf. destruct (g_mu e); [apply (uc_pos f) |]; trivial.
+ intros e x1 x2 e_pos A. unfold compose. apply (uc_prf g g_mu); trivial.
  assert (0 < g_mu e) by (apply (uc_pos g); trivial).
  unfold comp_inf in A. destruct (g_mu e) as [e' |]; [| apply mspc_inf].
  apply (uc_prf f f_mu); trivial.
Qed.

Global Instance uniformly_continuous_func `{MetricSpaceBall X, MetricSpaceBall Y} :
  Func (UniformlyContinuous X Y) X Y := λ f, f.

#[global]
Hint Extern 10 (ExtMetricSpaceClass (UniformlyContinuous _ _)) =>
  apply @Linf_func_metric_space_class : typeclass_instances.

Section LocalUniformContinuity.

Context `{MetricSpaceBall X, MetricSpaceBall Y}.

Definition restrict (f : X -> Y) (x : X) (r : Q) : sig (ball r x) -> Y :=
  f ∘ @proj1_sig _ _.

(* See the remark about llip_prf below about the loop between
IsUniformlyContinuous and IsLocallyUniformlyContinuous *)

Class IsLocallyUniformlyContinuous (f : X -> Y) (lmu : X -> Q -> Q -> Qinf) :=
  luc_prf :: forall (x : X) (r : Q), IsUniformlyContinuous (restrict f x r) (lmu x r).

Global Arguments luc_prf f lmu {_} x r.

Global Instance uc_ulc (f : X -> Y)
       {mu : Q → Qinf}  {_ : IsUniformlyContinuous f mu}
  : IsLocallyUniformlyContinuous f (λ _ _, mu).
Proof.
intros x r. constructor; [now apply (uc_pos f) |].
intros e [x1 A1] [x2 A2] e_pos A. now apply (uc_prf f mu).
Qed.

Global Instance luc_proper
  {_ : ExtMetricSpaceClass X} {_ : ExtMetricSpaceClass Y}
  (f : X -> Y) `{!IsLocallyUniformlyContinuous f lmu} : Proper ((=) ==> (=)) f.
Proof.
intros x1 x2 A. apply -> mspc_eq. intros e e_pos.
assert (A1 : ball 1%Q x1 x1) by (apply mspc_refl; Qauto_nonneg).
assert (A2 : ball 1%Q x1 x2) by (rewrite A; apply mspc_refl; Qauto_nonneg).
change (ball e (restrict f x1 1 (exist _ x1 A1)) (restrict f x1 1 (exist _ x2 A2))).
unfold IsLocallyUniformlyContinuous in *. apply (uc_prf _ (lmu x1 1)); [easy |].
change (ball (lmu x1 1 e) x1 x2).
rewrite <- A. assert (0 < lmu x1 1 e) by now apply (uc_pos (restrict f x1 1)).
destruct (lmu x1 1 e) as [q |]; [apply mspc_refl; solve_propholds | apply mspc_inf].
Qed.

Lemma luc (f : X -> Y) `{IsLocallyUniformlyContinuous f lmu} (r e : Q) (a x y : X) :
  0 < e -> ball r a x -> ball r a y -> ball (lmu a r e) x y -> ball e (f x) (f y).
Proof.
intros e_pos A1 A2 A3.
change (f x) with (restrict f a r (exist _ x A1)).
change (f y) with (restrict f a r (exist _ y A2)).
apply uc_prf with (mu := lmu a r); trivial.
(* The predicate symbol of the goal is IsUniformlyContinuous, which is a
type class. Yet, without [trivial] above, instead of solving it by [apply
H3], Coq gives it as a subgoal. *)
Qed.

End LocalUniformContinuity.

Section Lipschitz.

Context `{MetricSpaceBall X, MetricSpaceBall Y}.

Class IsLipschitz (f : X -> Y) (L : Q) := {
  lip_nonneg : 0 ≤ L;
  lip_prf : forall (x1 x2 : X) (e : Q), ball e x1 x2 -> ball (L * e) (f x1) (f x2)
}.

Global Arguments lip_nonneg f L {_} _.
Global Arguments lip_prf f L {_} _ _ _ _.

Record Lipschitz := {
  lip_func :> X -> Y;
  lip_const : Q;
  lip_proof : IsLipschitz lip_func lip_const
}.

Definition lip_modulus (L e : Q) : Qinf :=
  if (decide (L = 0)) then Qinf.infinite else e / L.

Lemma lip_modulus_pos (L e : Q) : 0 ≤ L -> 0 < e -> 0 < lip_modulus L e.
Proof.
intros L_nonneg e_pos. unfold lip_modulus.
destruct (decide (L = 0)) as [A1 | A1]; [apply I |].
apply not_symmetry in A1.
change (0 < e / L). (* Changes from Qinf, which is not declared as ordered ring, to Q *)
assert (0 < L) by now apply QOrder.le_neq_lt. Qauto_pos.
Qed.

(* It is nice to declare only [MetricSpaceBall X] above because this is all
we need to know about X to define [IsLipschitz]. But for the following
theorem we also need [ExtMetricSpaceClass X], [MetricSpaceDistance X] and
[MetricSpaceClass X]. How to add these assumptions? Saying
[`{MetricSpaceClass X}] would add a second copy of [MetricSpaceBall X]. We
write the names EM and m below because "Anonymous variables not allowed in
contexts" *)

Context {EM : ExtMetricSpaceClass X} {m : MetricSpaceDistance X}.

Global Instance lip_uc {_ : MetricSpaceClass X} {_ : ExtMetricSpaceClass Y}
  (f : X -> Y) `{!IsLipschitz f L} :
  IsUniformlyContinuous f (lip_modulus L).
Proof.
constructor.
+ intros. apply lip_modulus_pos; [| assumption]. now apply (lip_nonneg f L).
+ unfold lip_modulus. intros e x1 x2 A1 A2. destruct (decide (L = 0)) as [A | A].
  - apply mspc_eq; [| easy]. unfold canonical_names.equiv, mspc_equiv. rewrite <- (Qmult_0_l (msd x1 x2)), <- A.
    now apply lip_prf; [| apply mspc_distance].
  - mc_setoid_replace e with (L * (e / L)) by now field.
    now apply lip_prf.
Qed.

End Lipschitz.

(* To be able to say [Lipschitz X Y] instead of [@Lipschitz X _ Y _] *)
Global Arguments Lipschitz X {_} Y {_}.

(* Allows concluding [IsLipschitz f _] from [f : Lipschitz] *)
Global Existing Instance lip_proof.

(* We need [ExtMetricSpaceClass Z] because we rewrite the ball radius, so
[mspc_radius_proper] is required. See comment before [compose_uc] for why
[{X Y Z : Type}] is necessary. *)
Global Instance compose_lip {X Y Z : Type}
  `{MetricSpaceBall X, MetricSpaceBall Y, ExtMetricSpaceClass Z}
  (f : X -> Y) (g : Y -> Z) (Lf Lg : Q)
  `{!IsLipschitz f Lf, !IsLipschitz g Lg} :
    IsLipschitz (g ∘ f) (Lg * Lf).
Proof.
constructor.
+ apply nonneg_mult_compat; [apply (lip_nonneg g), _ | apply (lip_nonneg f), _].
+ intros x1 x2 e A.
  (* [rewrite <- mult_assoc] does not work *)
  mc_setoid_replace (Lg * Lf * e) with (Lg * (Lf * e)) by (symmetry; apply simple_associativity).
  now apply (lip_prf g Lg), (lip_prf f Lf).
Qed.

(* [ExtMetricSpaceClass X] is needed for rewriting *)
Global Instance id_lip `{ExtMetricSpaceClass X} : IsLipschitz Datatypes.id 1.
Proof.
constructor; [solve_propholds |]. intros; now rewrite mult_1_l.
Qed.

Section LocallyLipschitz.

Context `{MetricSpaceBall X, MetricSpaceBall Y}.

(* Delaring llip_prf below an instance introduces a loop between
[IsLipschitz] and [IsLocallyLipschitz]. But if we are searching for a proof
of [IsLipschitz f _] for a specific term [f], then Coq should not enter an
infinite loop because that would require unifying [f] with [restrict _ _ _].
We need this instance to apply [lip_nonneg (restrict f x r) _] in order
to prove [0 ≤ Lf x r] when [IsLocallyLipschitz f Lf]. *)

(* We make an assumption [0 ≤ r] in llip_prf below to make proving that
functions are locally Lipschitz easier. As a part of such proof, one needs
to show that [0 ≤ L x r] ([lip_nonneg]). Proving this under the assumption
[0 ≤ r] may allow having simpler definitions of the uniform [L]. In
particular, integral_lipschitz in AbstractIntegration.v defines [L] as
[λ a r, abs (f a) + L' a r * r]. *)

Class IsLocallyLipschitz (f : X -> Y) (L : X -> Q -> Q) :=
  llip_prf :: forall (x : X) (r : Q), PropHolds (0 ≤ r) -> IsLipschitz (restrict f x r) (L x r).

Global Arguments llip_prf f L {_} x r _.

Global Instance lip_llip (f : X -> Y) `{!IsLipschitz f L} : IsLocallyLipschitz f (λ _ _, L).
Proof.
intros x r. constructor; [now apply (lip_nonneg f) |].
intros [x1 x1b] [x2 x2b] e A. change (ball (L * e) (f x1) (f x2)). now apply lip_prf.
Qed.

Lemma llip `{!ExtMetricSpaceClass X} (f : X -> Y) `{IsLocallyLipschitz f L} (r e : Q) (a x y : X) :
  ball r a x -> ball r a y -> ball e x y -> ball (L a r * e) (f x) (f y).
Proof.
intros A1 A2 A3.
change (f x) with (restrict f a r (exist _ x A1)).
change (f y) with (restrict f a r (exist _ y A2)).
assert (0 ≤ r) by now apply (radius_nonneg a x).
apply (lip_prf _ (L a r)); trivial.
Qed.

Record LocallyLipschitz := {
  llip_func :> X -> Y;
  llip_const : X -> Q -> Q;
  llip_proof : IsLocallyLipschitz llip_func llip_const
}.

End LocallyLipschitz.

Global Arguments LocallyLipschitz X {_} Y {_}.

#[global]
Instance locally_lipschitz_func `{MetricSpaceBall X, MetricSpaceBall Y} :
  Func (LocallyLipschitz X Y) X Y := λ f, f.

#[global]
Hint Extern 10 (ExtMetricSpaceClass (LocallyLipschitz _ _)) =>
  apply @Linf_func_metric_space_class : typeclass_instances.

Notation "X LL-> Y" := (LocallyLipschitz X Y) (at level 55, right associativity).

Section Contractions.

Context `{MetricSpaceBall X, MetricSpaceBall Y}.

Class IsContraction (f : X -> Y) (q : Q) := {
  contr_prf :: IsLipschitz f q;
  contr_lt_1 : q < 1
}.

Global Arguments contr_lt_1 f q {_}.
Global Arguments contr_prf f q {_}.

Record Contraction := {
  contr_func : X -> Y;
  contr_const : Q;
  contr_proof : IsContraction contr_func contr_const
}.

Global Instance const_contr `{!ExtMetricSpaceClass Y} (c : Y) : IsContraction (λ x : X, c) 0.
Proof.
constructor.
+ constructor.
  - reflexivity.
  - intros; apply mspc_refl.
    rewrite mult_0_l; reflexivity.
+ solve_propholds.
Qed.

(* Do we need the following?

Global Instance contr_to_uc `(IsContraction f q) :
  IsUniformlyContinuous f (λ e, if (decide (q = 0)) then Qinf.infinite else (e / q)).
Proof. apply _. Qed.*)

End Contractions.

Global Arguments Contraction X {_} Y {_}.

Global Instance : PreOrder Qinf.le.
Proof.
constructor.
+ intros [x |]; [apply Qle_refl | easy].
+ intros [x |] [y |] [z |]; solve [intros [] | intros _ [] | easy | apply Qle_trans].
Qed.

Global Instance : AntiSymmetric Qinf.le.
Proof.
intros [x |] [y |] A B; [apply Qle_antisym | elim B | elim A |]; easy.
Qed.

Global Instance : PartialOrder Qinf.le.
Proof. constructor; apply _. Qed.

Global Instance : TotalRelation Qinf.le.
Proof.
intros [x |] [y |]; [change (x ≤ y \/ y ≤ x); apply total, _ | left | right | left]; easy.
Qed.

Global Instance : TotalOrder Qinf.le.
Proof. constructor; apply _. Qed.

Global Instance : ∀ x y : Qinf, Decision (x ≤ y).
intros [x |] [y |]; [change (Decision (x ≤ y)); apply _ | left | right | left]; easy.
Defined.

Import minmax.

(* Instances above allow using min and max for Qinf *)

Section TotalOrderLattice.

Context `{TotalOrder A} `{Lt A} `{∀ x y: A, Decision (x ≤ y)}.

Lemma min_ind (P : A -> Prop) (x y : A) : P x → P y → P (min x y).
Proof. unfold min, sort. destruct (decide_rel _ x y); auto. Qed.

Lemma lt_min (x y z : A) : z < x -> z < y -> z < min x y.
Proof. apply min_ind. Qed.

End TotalOrderLattice.

Section ProductSpaceFunctions.

Definition diag {X : Type} (x : X) : X * X := (x, x).

Global Instance diag_lip `{ExtMetricSpaceClass X} : IsLipschitz (@diag X) 1.
Proof.
constructor.
+ solve_propholds.
+ intros x1 x2 e A. rewrite mult_1_l. now split.
Qed.

Definition together {X1 Y1 X2 Y2 : Type} (f1 : X1 -> Y1) (f2 : X2 -> Y2) : X1 * X2 -> Y1 * Y2 :=
  λ p, (f1 (fst p), f2 (snd p)).

(*Global Instance together_lip
  `{ExtMetricSpaceClass X1, ExtMetricSpaceClass Y1, ExtMetricSpaceClass X2, ExtMetricSpaceClass Y2}
   (f1 : X1 -> Y1) (f2 : X2 -> Y2)
  `{!IsLipschitz f1 L1, !IsLipschitz f2 L2} : IsLipschitz (together f1 f2) (join L1 L2).
(* What if we define the Lipschitz constant for [together f1 f2] to be [max
L1 L2], where [max] is the name of an instance of [Join A] in
orders.minmax? In fact, [Check _ : Join Q] returns [max]. I.e., [join x y]
for [x y : Q] reduces to [max x y]. However, it is difficult to apply
[lattices.join_le_compat_r] to the goal [0 ≤ max L1 L2]. Simple [apply]
does not work (probably because the theorem has to be reduced to match the
goal). As for [apply:] and [rapply], they invoke [refine (@join_le_compat_r
_ _ ...)]. Some of the _ are implicit arguments and type classes (e.g.,
[Equiv] [Le]), and they are instantiated with the instances found first,
which happen to be for [Qinf]. Apparently, unification does not try other
instances. So, [apply:] with type classes is problematic.
[apply: (@lattices.join_le_compat_r Q)] gives "Anomaly: Evd.define: cannot define an evar twice" *)
Proof.
constructor.
+ apply lattices.join_le_compat_r, (lip_nonneg f1 L1).
+ intros z1 z2 e [A1 A2].
  (* Below we prove [0 ≤ e] using [radius_nonneg], which requires
  [ExtMetricSpaceClass]. Another way is to add the assymption [0 ≤ e] to
  [lip_prf], similar to [uc_prf]. *)
  assert (0 ≤ e) by now apply (radius_nonneg (fst z1) (fst z2)).
  split; simpl.
  - apply (mspc_monotone (L1 * e)); [apply (order_preserving (.* e)); apply join_ub_l |].
    (* [apply (order_preserving (.* e)), join_ub_l.] does not work *)
    apply lip_prf; trivial.
  - apply (mspc_monotone (L2 * e)); [apply (order_preserving (.* e)); apply join_ub_r |].
    apply lip_prf; trivial.*)

Global Instance together_uc
  `{ExtMetricSpaceClass X1, ExtMetricSpaceClass Y1, ExtMetricSpaceClass X2, ExtMetricSpaceClass Y2}
   (f1 : X1 -> Y1) (f2 : X2 -> Y2)
  `{!IsUniformlyContinuous f1 mu1, !IsUniformlyContinuous f2 mu2} :
  IsUniformlyContinuous (together f1 f2) (λ e, min (mu1 e) (mu2 e)).
Proof.
constructor.
+ intros e e_pos. (* [apply min_ind] does not work if the goal has [meet] instead of [min] *)
  apply lt_min; [apply (uc_pos f1) | apply (uc_pos f2)]; trivial.
  (* [trivial] solves, in particular, [IsUniformlyContinuous f1 mu1], which should
     have been solved automatically *)
+ intros e z z' e_pos [A1 A2]. split; simpl.
  - apply (uc_prf f1 mu1); trivial.
    apply (mspc_monotone' (min (mu1 e) (mu2 e))); [apply: meet_lb_l | trivial].
  - apply (uc_prf f2 mu2); trivial.
    apply (mspc_monotone' (min (mu1 e) (mu2 e))); [apply: meet_lb_r | trivial].
Qed.

End ProductSpaceFunctions.

Section CompleteMetricSpace.

Context `{MetricSpaceBall X}.

Class IsRegularFunction (f : Q -> X) : Prop :=
  rf_prf : forall e1 e2 : Q, 0 < e1 -> 0 < e2 -> ball (e1 + e2) (f e1) (f e2).

Record RegularFunction := {
  rf_func :> Q -> X;
  rf_proof : IsRegularFunction rf_func
}.

Arguments Build_RegularFunction {_} _.

Global Existing Instance rf_proof.

Global Instance rf_eq : Equiv RegularFunction :=
  λ f1 f2, forall e1 e2 : Q, 0 < e1 -> 0 < e2 -> ball (e1 + e2) (f1 e1) (f2 e2).

Context {EM : ExtMetricSpaceClass X}.

Global Instance rf_setoid : Setoid RegularFunction.
Proof.
constructor.
+ intros f e1 e2; apply rf_prf.
+ intros f1 f2 A e1 e2 A1 A2. rewrite plus_comm. now apply mspc_symm, A.
+ intros f1 f2 f3 A1 A2 e1 e3 A3 A4. apply mspc_closed. intros d A5.
  mc_setoid_replace (e1 + e3 + d) with ((e1 + d / 2) + (e3 + d / 2))
  by (field; change ((2 : Q) ≠ 0); solve_propholds).
  apply mspc_triangle with (b := f2 (d / 2));
  [apply A1 | rewrite plus_comm; apply A2]; try solve_propholds.
Qed.

Instance rf_msb : MetricSpaceBall RegularFunction :=
  λ e f1 f2, forall e1 e2 : Q, 0 < e1 -> 0 < e2 -> ball (e + e1 + e2) (f1 e1) (f2 e2).

Lemma unit_reg (x : X) : IsRegularFunction (λ _, x).
Proof. intros e1 e2 A1 A2; apply mspc_refl; solve_propholds. Qed.

Definition reg_unit (x : X) := Build_RegularFunction (unit_reg x).

Global Instance : Setoid_Morphism reg_unit.
Proof.
constructor; [apply _ .. |].
intros x y eq_x_y e1 e2 e1_pos e2_pos. apply mspc_eq; solve_propholds.
Qed.

Class Limit := lim : RegularFunction -> X.

Class CompleteMetricSpaceClass `{Limit} := cmspc :: Surjective reg_unit (inv := lim).

Definition tends_to (f : RegularFunction) (l : X) :=
  forall e : Q, 0 < e -> ball e (f e) l.

Lemma limit_def `{CompleteMetricSpaceClass} (f : RegularFunction) :
  forall e : Q, 0 < e -> ball e (f e) (lim f).
Proof.
intros e2 A2. apply mspc_symm; apply mspc_closed.
(* [apply mspc_symm, mspc_closed.] does not work *)
intros e1 A1. change (lim f) with (reg_unit (lim f) e1). rewrite plus_comm.
rapply (surjective reg_unit (inv := lim)); trivial; reflexivity.
Qed.

End CompleteMetricSpace.

Global Arguments RegularFunction X {_}.
Global Arguments Limit X {_}.
Global Arguments CompleteMetricSpaceClass X {_ _ _}.

(* The exclamation mark before Limit avoids introducing a second assumption
MetricSpaceBall X *)
Lemma completeness_criterion `{ExtMetricSpaceClass X, !Limit X} :
  CompleteMetricSpaceClass X <-> forall f : RegularFunction X, tends_to f (lim f).
Proof.
split; intro A.
+ intros f e2 A2. apply mspc_symm, mspc_closed.
  intros e1 A1. change (lim f) with (reg_unit (lim f) e1). rewrite plus_comm.
  rapply (surjective reg_unit (A := X) (inv := lim)); trivial; reflexivity.
+ constructor; [| apply _].
  apply ext_equiv_r; [apply _|].
  intros f e1 e2 e1_pos e2_pos.
  apply (mspc_monotone e2); [apply nonneg_plus_le_compat_l; solve_propholds |].
  now apply mspc_symm, A.
Qed.

Section UCFComplete.

Context `{NonEmpty X, ExtMetricSpaceClass X, CompleteMetricSpaceClass Y}.

Program Definition pointwise_regular
  (F : RegularFunction (UniformlyContinuous X Y)) (x : X) : RegularFunction Y :=
  Build_RegularFunction (λ e, F e x) _.
Next Obligation. intros e1 e2 e1_pos e2_pos; now apply F. Qed.

Global Program Instance ucf_limit : Limit (UniformlyContinuous X Y) :=
  λ F, Build_UniformlyContinuous
         (λ x, lim (pointwise_regular F x))
         (λ e, uc_mu (F (e/3)) (e/3))
         _.
Next Obligation.
constructor.
* intros e e_pos.
  destruct (F (e/3)) as [g ? ?]; simpl; apply uc_pos with (f := g); trivial.
  apply Q.Qmult_lt_0_compat; auto with qarith.
* intros e x1 x2 e_pos A.
  apply (mspc_triangle' (e/3) (e/3 + e/3) (F (e/3) x1)); [field; discriminate | |].
  + apply mspc_symm. change ((F (e / 3)) x1) with (pointwise_regular F x1 (e/3)).
    (* without [change], neither [apply limit_def] nor [rapply limit_def] work *)
    apply completeness_criterion, Q.Qmult_lt_0_compat; auto with qarith.
  + apply mspc_triangle with (b := F (e / 3) x2).
    - destruct (F (e/3)); eapply uc_prf; eauto.
      apply Q.Qmult_lt_0_compat; auto with qarith.
    - change ((F (e / 3)) x2) with (pointwise_regular F x2 (e/3)).
      apply completeness_criterion, Q.Qmult_lt_0_compat; auto with qarith.
Qed.

Global Instance : CompleteMetricSpaceClass (UniformlyContinuous X Y).
Proof.
apply completeness_criterion. intros F e e_pos x.
change (func (lim F) x) with (lim (pointwise_regular F x)).
change (func (F e) x) with (pointwise_regular F x e).
now apply completeness_criterion.
Qed.

End UCFComplete.

Definition seq A := nat -> A.

#[global]
Hint Unfold seq : typeclass_instances.
(* This unfolds [seq X] as [nat -> X] and allows ext_equiv to find an
instance of [Equiv (seq X)] *)

Section SequenceLimits.

Context `{ExtMetricSpaceClass X}.

Definition seq_lim (x : seq X) (a : X) (N : Q -> nat) :=
  forall e : Q, 0 < e -> forall n : nat, N e ≤ n -> ball e (x n) a.

(*Global Instance : Proper (((=) ==> (=)) ==> (=) ==> ((=) ==> (=)) ==> iff) seq_lim.
Proof.
intros x1 x2 A1 a1 a2 A2 N1 N2 A3; split; intros A e e_pos n A4.
+ mc_setoid_replace (x2 n) with (x1 n) by (symmetry; now apply A1).
  rewrite <- A2. mc_setoid_replace (N2 e) with (N1 e) in A4 by (symmetry; now apply A3).
  now apply A.
+ mc_setoid_replace (x1 n) with (x2 n) by now apply A1.
  rewrite A2. mc_setoid_replace (N1 e) with (N2 e) in A4 by now apply A3.
  now apply A.
Qed.*)

(* The following instance uses Leibniz equality for the third argument of
seq_lim, i.e., the modulus of type [Q -> nat]. This is because extensional
equality = is not reflexive on functions: [f = f] iff [f] is a morphism.
And we need reflexivity when we replace the first argument of seq_lim and
leave the third one unchanged. Do we need the previous instance with
extensional equality for the third argument? *)

Global Instance : Proper (((=) ==> (=)) ==> (=) ==> (≡) ==> iff) seq_lim.
Proof.
intros x1 x2 A1 a1 a2 A2 N1 N2 A3; split; intros A e e_pos n A4.
+ mc_setoid_replace (x2 n) with (x1 n) by (symmetry; now apply A1).
  rewrite <- A2. rewrite <- A3 in A4. now apply A.
+ mc_setoid_replace (x1 n) with (x2 n) by now apply A1.
  rewrite A2. rewrite A3 in A4. now apply A.
Qed.

Lemma seq_lim_unique : ∀ (x : seq X) (a1 a2 : X) N1 N2, seq_lim x a1 N1 → seq_lim x a2 N2 → a1 = a2.
Proof.
intros x a1 a2 N1 N2 A1 A2. apply -> mspc_eq; intros q A.
assert (A3 : 0 < q / 2) by solve_propholds.
specialize (A1 (q / 2) A3); specialize (A2 (q / 2) A3).
set (M := Peano.max (N1 (q / 2)) (N2 (q / 2))).
assert (A4 : N1 (q / 2) ≤ M) by apply Nat.le_max_l.
assert (A5 : N2 (q / 2) ≤ M) by apply Nat.le_max_r.
specialize (A1 M A4); specialize (A2 M A5).
apply mspc_symm in A1.
apply (mspc_triangle' (q / 2) (q / 2) (x M)); trivial.
field; change ((2 : Q) ≠ 0); solve_propholds.
Qed.

Lemma seq_lim_S (x : seq X) (a : X) N : seq_lim x a N -> seq_lim (x ∘ S) a N.
Proof. intros A e A1 n A2. apply A; trivial. apply le_S, A2. Qed.

Lemma seq_lim_S' (x : seq X) (a : X) N : seq_lim (x ∘ S) a N -> seq_lim x a (S ∘ N).
Proof.
intros A e A1 n A2.
destruct n as [| n].
+ contradict A2; apply Nat.nle_succ_0.
+ apply A; trivial. apply le_S_n, A2.
Qed.

End SequenceLimits.
#[global] Instance: Params (@seq_lim) 2 := {}.

Theorem seq_lim_cont
        `{ExtMetricSpaceClass X, ExtMetricSpaceClass Y} (f : X -> Y)
        {mu : Q -> Qinf} {_ : IsUniformlyContinuous f mu}
  (x : seq X) (a : X) (N : Q -> nat) :
  seq_lim x a N → seq_lim (f ∘ x) (f a) (comp_inf N mu 0).
Proof.
intros A e e_pos n A1. apply (uc_prf f mu); trivial.
unfold comp_inf in A1; assert (A2 := uc_pos f mu e e_pos).
now destruct (mu e); [apply A | apply mspc_inf].
Qed.

Theorem seq_lim_contr
  `{MetricSpaceClass X, ExtMetricSpaceClass Y} (f : X -> Y) `{!IsContraction f q}
  (x : seq X) (a : X) (N : Q -> nat) :
  seq_lim x a N → seq_lim (f ∘ x) (f a) (comp_inf N (lip_modulus q) 0).
Proof. intro A; apply seq_lim_cont; [apply _ | apply A]. Qed.

Lemma iter_fixpoint
  `{ExtMetricSpaceClass X, ExtMetricSpaceClass Y}
  (f : X -> X) {mu : Q -> Qinf} {_ : IsUniformlyContinuous f mu}
  (x : seq X) (a : X) (N : Q -> nat) :
  (forall n : nat, x (S n) = f (x n)) -> seq_lim x a N -> f a = a.
Proof.
intros A1 A2; generalize A2; intro A3. apply seq_lim_S in A2. apply (seq_lim_cont f) in A3.
setoid_replace (x ∘ S) with (f ∘ x) in A2 by (intros ? ? eqmn; rewrite eqmn; apply A1).
eapply seq_lim_unique; eauto.
Qed.

Section CompleteSpaceSequenceLimits.

Context `{CompleteMetricSpaceClass X}.

Definition cauchy (x : seq X) (N : Q -> nat) :=
  forall e : Q, 0 < e -> forall m n : nat, N e ≤ m -> N e ≤ n -> ball e (x m) (x n).

Definition reg_fun (x : seq X) (N : Q -> nat) (A : cauchy x N) : RegularFunction X.
refine (Build_RegularFunction (x ∘ N) _).
(* without loss of generality, N e1 ≤ N e2 *)
assert (A3 : forall e1 e2, 0 < e1 -> 0 < e2 -> N e1 ≤ N e2 -> ball (e1 + e2) ((x ∘ N) e1) ((x ∘ N) e2)).
+ intros e1 e2 A1 A2 A3.
  apply (mspc_monotone e1).
  - apply (strictly_order_preserving (e1 +)) in A2; rewrite plus_0_r in A2; solve_propholds.
  - apply A; trivial; reflexivity.
+ intros e1 e2 A1 A2.
  assert (A4 : TotalRelation (A := nat) (≤)) by apply _; destruct (A4 (N e1) (N e2)).
  - now apply A3.
  - rewrite plus_comm; now apply mspc_symm, A3.
Defined.

Arguments reg_fun {_} {_} _.

Lemma seq_lim_lim (x : seq X) (N : Q -> nat) (A : cauchy x N) :
  seq_lim x (lim (reg_fun A)) (λ e, N (e / 2)).
Proof.
set (f := reg_fun A).
intros e A1 n A2. apply (mspc_triangle' (e / 2) (e / 2) (x (N (e / 2)))).
+ field; change ((2 : Q) ≠ 0); solve_propholds.
+ now apply mspc_symm, A; [solve_propholds | reflexivity |].
+ change (x (N (e / 2))) with (f (e / 2)).
  apply completeness_criterion; solve_propholds.
Qed.

End CompleteSpaceSequenceLimits.

(*End QField.*)
