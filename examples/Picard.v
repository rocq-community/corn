(* TODO: fix this example *)
From CoRN Require Import CRtrans Qmetric.

(* For comparison with Pattison's paper:
The ODE:
f'=λx.2f(x)+1
f(0)=0
*)

Section ODE.
Open Scope uc_scope.
From CoRN Require Import ProductMetric CompleteProduct.
From Stdlib Require Import Unicode.Utf8.
From CoRN Require Import CPoly_Newton metric2.Classified.
From examples Require Import Circle.
Notation "X * Y":=(ProductMS X Y).
Notation " f >> g ":= (Cbind_slow f ∘ g) (at level 50).
Notation " x >>= f ":= (Cbind_slow f x) (at level 50).

Section Picard_op.
From CoRN Require Import AbstractIntegration.
From CoRN Require Import SimpleIntegration.

(* 
Require Import stdlib_omissions.Pair.
For diagonal*)

Variable v: (Q*Q) -->CR.
Variable f:Q-->CR.
Notation "( f , g )":= (together f g).
Definition vxfx:= (v >> Couple ∘ (Cunit, f) ∘ diag _).

(* Uniformly continuous function should be a type class 
so that we can define functions using Program Instance *)
(* Integration takes a width, need the integral from a to b.*)

Definition integral:  ((Q-->CR) * Q * Q) -> CR.
intros [[g a] b].
destruct (QMinMax.Qlt_le_dec_fast b a).
assert (a_min_b:Qpos).  exists (a-b) . admit.
exact (- ∫ g b (a_min_b))%CR.

(* Do the zero case *)
assert (b_min_a:Qpos).  exists (b-a). admit.
exact ( ∫ g a (b_min_a))%CR.
Defined.

(* Need continuous Q--> CR then continuous CR --> CR *)


(* The integral is locally uniformly continuous *)
(* Context (f: Q -> CR) `{!LocallyUniformlyContinuous_mu f} `{!LocallyUniformlyContinuous f}.*)
(* Definition intregral_uc:= (is_UniformlyContinuousFunction integral (fun e => e)%Qpos ). *)

Definition Picard_raw:=fun t:Q => integral (f, 0, t).

Lemma Picard_uc: (is_UniformlyContinuousFunction Picard_raw (fun e => e)%Qpos).
admit.
Qed.
(* Locally Lipschitz:
∫ 0 t f - ∫ 0 s f = ∫ s t f ≤ |t-s| sup_[s,t] f
Hence the constant is: r  sup_B f on the ball B(t,r).
differentiable maps are Lipschitz.
Locally Lipschitz functions compose
on B(x,r), 
| f x - f y |  ≤ L_B |x -y|
Hence fB ⊂ B(f x, L r) and g is Lipschitz cont on this ball.
*)

Definition Picard:=(Cbind_slow (Build_UniformlyContinuousFunction Picard_uc)).
End Picard_op.

Section Banach_it.
Context {X} `(F:X-->X).
Fixpoint Banach_seq (n : nat) : X --> X :=
         match n with
         | O => F
         | S m => F ∘ (Banach_seq m)
         end.

Variable f:CR-->CR.
Check Picard.
Fixpoint Picard_seq (n : nat) : Q --> CR :=
         match n with
         | O => f ∘ Cunit
         | S m => (Picard (Picard_seq m) )∘ Cunit
         end.
End Banach_it.

Section Picard.
Variable L:Qpos.
Variable c:Qpos.
Hypothesis c_unit:1-c>0.
Program Definition oneminc:=(1-c):Qpos.
Next Obligation.
admit.
Defined.
Variables a K:Q.
Hypothesis aL_le_c:(a*L<c).
Require Import Qabs.
Require Export CRabs.
Require Import Interval.

Variable v: (Q*Q) -->CR.

Hypothesis Lipschitz: forall x, -a<=x -> x<=a -> forall y, -K<=y -> y<=K -> 
  forall y':Q, -K<=y' -> y <=K ->
 ((CRabs ((v  (x,  y)) -  (v (x, y'))))<= 'L* 'Qabs (y-y'))%CR.

Section BanachFPT.
Context (X: MetricSpace).
Context (d:X->X->CR).

(* 
Notation Qset:=QArith.QArith_base.Q.
Coercion inject_Q:Qset>-> (msp_is_setoid CR).
*)
Variable metric_function: forall e x y, ball e x y <-> ((d x y) <='e)%CR.
Class Contraction `(F:X-->X)`(c:Qpos):= contraction: 
  c<1-> forall x x', ((d x x') <= 'c*(d (F x) (F x')))%CR.

(* forall ϵ, (ball ϵ x x')-> (ball (c*ϵ) (F x) (F x' )) *)
Context {F}`{conF: Contraction F}.
Require Export CRGeometricSum.

(*
Definition InfiniteSum_raw_F rec (err_prop: (Stream X) -> bool) (s:Stream X) : X :=
if (err_prop s) then 0 else (Qplus' (hd s) (rec err_prop (tl s))).

Definition InfiniteGeometricSum_raw series (e:QposInf) : X :=
match e with
| ∞ => 0
| Qpos2QposInf err => InfiniteSum_raw_N (InfiniteGeometricSum_maxIter series err)
  (fun err s => 0) (err_prop err) series
end.
*)

Lemma bla: forall n m:nat, forall x:X, 
  (ball (c^m) (@Banach_seq _ F n x) (@Banach_seq _ F (n+m) x)).
Admitted.

Lemma bla2: forall n:nat, forall x:X,  (ball (Qpos_inv oneminc) x (@Banach_seq _ F n x)).
Admitted.

Lemma bla3: forall n m:nat, forall x:X, forall e,
  (ball e x (F x)) ->
  (ball (c^m*(Qpos_inv oneminc)*e) (@Banach_seq _ F n x) (@Banach_seq _ F m x)).
Admitted.

Variable x:X.
Definition DiffSeries:=fun n => d (@Banach_seq _ F n x) (@Banach_seq _ F (S n) x).
Require Import StreamMemo.
Definition DiffStream:=(memo_list _ DiffSeries).
Require Import CoqStreams.

(* ForAll_map in CoqStreams ?? *)
Definition GeometricSeriesCR (c:CR):= 
  (ForAll (fun s:Stream CR => (CRabs ((hd (tl s))) <= c*(CRabs(hd s)))%CR)).

Lemma GeomDiff:GeometricSeriesCR ('c)%CR DiffStream.
unfold GeometricSeriesCR.
unfold DiffStream.
unfold memo_list.
unfold memo_make.
simpl.
admit.
Qed.

(* The Banach sequence is a Cauchy sequence.*)

(* Use:
Lemma GeometricCovergenceLemma : forall (n:positive) (e:Qpos),
 /(e*(1 - a)) <= n -> a^n <= e.
with e:=ϵ *oneminc/ (d x0 x1)
*)

Lemma BanachCauchy: forall ϵ:Qpos, exists N, forall n m:nat , n >=N-> m>= N ->
   (ball ϵ (@Banach_seq _ F n x) (@Banach_seq _ F m x)).
intros.
(* Needs to be of type Qpos, want Qpos as a type class *)
(* A rational number bigger than (d x0 x1) *)
set ceil:=(Qabs (approximate (d (@Banach_seq _ F 0 x) (@Banach_seq _ F 1 x))
  (Qpos2QposInf (1#1))))+1:Qpos.

exists ( /((ϵ*oneminc/ceil)(oneminc))). 


(* Note that to apply the geomSum we do compute all the norms *)


End BanachFPT.

Section BanachFPT2.
Context {X} (F:Complete X--> Complete X) `{conF: Contraction (Complete X) F}.
Theorem BanachFPT : exists x, (F x) =x.
eexists y.
Admitted.
(* x= lim F^n
F x - x = F lim F^n - lim F^n = lim F^n+1 - lim F^n.
*)

(* Moreover, it is unique *)

Theorem PicardFPT: exists f, (Picard f) = (f ∘ Cunit).
apply BanachFPT.
Qed.
