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
(* IrrCrit.v, v1.1, 27aug2004, Bart Kirkels *)


(** printing [=] %\ensuremath=% #=# *)
(** printing [+X*] %\ensuremath{+ X*}% #&+ X*;# *)


Require Export CoRN.model.Zmod.Zm.
Require Export CoRN.model.rings.Zring.
Require Export CoRN.algebra.CPoly_Degree.

(**
* An irreducibility criterion
Let [p] be a (positive) prime number. Our goal is to prove that if an integer
polynomial is irreducible over the prime field Fp, then it is irreducible over
Z.
*)

Parameter p : positive.
Axiom Hprime : (Prime p).

Definition fp := (Fp p Hprime).

(**
** Integers modulo [p]
*)

Definition zfp (a:Z) := (a:fp).

Lemma fpeq_wd : forall a b:Z, a=b -> (zfp a)[=](zfp b).
Proof.
 intros a b heq.
 simpl.
 unfold zfp in *.
 unfold ZModeq in *.
 elim heq.
 auto with *.
Qed.

(**
** Integer polynomials over Fp
*)

Definition zx := (cpoly_cring Z_as_CRing).

Definition fpx := (cpoly_cring fp).

Fixpoint zxfpx (p:zx) : fpx :=
  match p with
  | cpoly_zero _ => (cpoly_zero fp : fpx)
  | cpoly_linear _ c p1 => (zfp c)[+X*](zxfpx p1)
  end.

Definition P (f g:zx):= f[=]g -> (zxfpx f)[=](zxfpx g).

Lemma fpxeq_wd : forall f g:zx, f[=]g -> (zxfpx f)[=](zxfpx g).
Proof.
 apply (cpoly_double_ind Z_as_CRing P); unfold P.
   induction p0 as [|c p0].
    trivial.
   intro H.
   astepl ((zfp c)[+X*](zxfpx p0)).
   apply (_linear_eq_zero fp).
   split.
    astepr (zfp 0).
    apply fpeq_wd.
    elim H.
    auto.
   apply IHp0.
   elim H.
   auto with *.
  induction p0 as [|c p0].
   trivial.
  intro H.
  astepr ((zfp c)[+X*](zxfpx p0)).
  apply (_zero_eq_linear fp).
  split.
   astepr (zfp 0).
   apply fpeq_wd.
   elim H.
   auto.
  apply IHp0.
  elim H.
  auto with *.
 intros p0 q c d H1 H2.
 astepr ((zfp d)[+X*](zxfpx q)).
 astepl ((zfp c)[+X*](zxfpx p0)).
 apply (_linear_eq_linear fp).
 split.
  apply fpeq_wd.
  elim H2.
  auto.
 apply H1.
 elim H2.
 auto.
Qed.

#[global]
Hint Resolve fpxeq_wd : algebra.



(**
** Lemmas
In this section we prove the lemmas we will need, about integer polynomials,
viewed over a prime field.
*)



Lemma mult_zero : forall (R:CRing)(f:cpoly_cring R),
(cpoly_mult_op R f (cpoly_zero R))[=](cpoly_zero R).
Proof.
 intros R f.
 simpl; apply cpoly_mult_zero.
Qed.

#[global]
Hint Resolve mult_zero : algebra.

Lemma fp_resp_zero : zxfpx(cpoly_zero Z_as_CRing)[=](cpoly_zero fp).
Proof.
 intuition; auto with *.
Qed.

Lemma fpx_resp_mult_cr : forall (c:Z_as_CRing)(f:zx),
  (cpoly_mult_cr_cs fp (zxfpx f) (zfp c)) [=]
  (zxfpx (cpoly_mult_cr_cs _ f c)).
Proof.
 induction f as [|c0 f].
  intuition; auto with *.
 astepr (zxfpx ((c[*]c0)[+X*](cpoly_mult_cr_cs _ f c))).
 astepr ((zfp (c[*]c0))[+X*](zxfpx (cpoly_mult_cr_cs _ f c))).
 astepr (((zfp c)[*](zfp c0))[+X*](zxfpx (cpoly_mult_cr_cs _ f c))).
 astepr (((zfp c)[*](zfp c0))[+X*](cpoly_mult_cr_cs fp (zxfpx f) (zfp c))).
 astepr (cpoly_mult_cr_cs fp ((zfp c0)[+X*](zxfpx f)) (zfp c)).
 intuition; auto with *.
Qed.

#[global]
Hint Resolve fpx_resp_mult_cr : algebra.

Lemma fpx_resp_plus :  forall f g:zx,
  (cpoly_plus_op fp (zxfpx f) (zxfpx g))[=]
  (zxfpx (cpoly_plus_op _ f g)).
Proof.
 induction f as [|c f].
  intuition; auto with *.
 induction g as [|c0 g].
  intuition; auto with *.
 astepl (cpoly_plus fp (zxfpx (c[+X*]f)) (zxfpx (c0[+X*]g))).
 astepr (zxfpx (cpoly_plus_op _ (c[+X*]f) (c0[+X*]g))).
 astepr (zxfpx ((c[+]c0)[+X*](cpoly_plus_op _ f g))).
 astepr ((zfp (c[+]c0))[+X*](zxfpx (cpoly_plus_op _ f g))).
 astepl (((zfp c)[+](zfp c0))[+X*] (cpoly_plus_op fp (zxfpx f) (zxfpx g))).
 auto with *.
Qed.

#[global]
Hint Resolve fpx_resp_plus : algebra.

Lemma fpx_resp_mult : forall f g:zx,
  (cpoly_mult_op fp (zxfpx f) (zxfpx g)) [=]
  (zxfpx (cpoly_mult_op _ f g)).
Proof.
 induction f as [|c f].
  intro g.
  astepl (cpoly_mult_op fp (cpoly_zero fp)(zxfpx g)).
  astepl (cpoly_zero fp).
  astepr (zxfpx (cpoly_zero Z_as_CRing)).
  astepr (cpoly_zero fp); intuition; auto with *.
 induction g as [|c0 g].
  astepl (cpoly_mult_op fp (zxfpx (c[+X*]f)) (cpoly_zero fp)).
  astepl (cpoly_zero fp).
  astepr (zxfpx (cpoly_zero Z_as_CRing));  try algebra.
  apply fpxeq_wd.
  apply eq_symmetric.
  apply (mult_zero Z_as_CRing).
 astepr (zxfpx (cpoly_mult_op Z_as_CRing (c[+X*]f) (c0[+X*]g))).
 astepl (cpoly_mult_op fp (zxfpx (c[+X*]f)) (zxfpx (c0[+X*]g))).
 astepr (zxfpx (cpoly_plus_op _ ((c[*]c0)[+X*](cpoly_mult_cr_cs _ g c))
   (([0]:Z_as_CRing)[+X*](cpoly_mult _ f (c0[+X*]g))))).
 astepr (zxfpx (((c[*]c0)[+]([0]:Z_as_CRing))[+X*](cpoly_plus_op _
   (cpoly_mult_cr_cs _ g c) (cpoly_mult _ f (c0[+X*]g))))).
 astepr (zxfpx ((c[*]c0)[+X*](cpoly_plus_op _ (cpoly_mult_cr_cs _ g c) (cpoly_mult _ f (c0[+X*]g))))).
 astepr ( (zfp c[*]c0) [+X*] (zxfpx (cpoly_plus_op _ (cpoly_mult_cr_cs _ g c)
   (cpoly_mult _ f (c0[+X*]g))))).
 astepl (cpoly_mult_op fp ((zfp c)[+X*](zxfpx f)) (zxfpx (c0[+X*]g))).
 astepl (cpoly_plus_op fp (cpoly_mult_cr_cs fp (zxfpx (c0[+X*]g)) (zfp c))
   ((zfp ([0]:Z_as_CRing))[+X*](cpoly_mult_op fp (zxfpx f) (zxfpx (c0[+X*]g))))).
 astepl (cpoly_plus_op fp (cpoly_mult_cr_cs fp ((zfp c0)[+X*](zxfpx g)) (zfp c))
   (([0]:fp)[+X*](zxfpx (cpoly_mult_op _ f (c0[+X*]g))))).
 astepl (cpoly_plus_op fp (((zfp c)[*](zfp c0))[+X*](cpoly_mult_cr_cs fp (zxfpx g) (zfp c)))
   (([0]:fp)[+X*](zxfpx (cpoly_mult_op _ f (c0[+X*]g))))).
 astepl (cpoly_plus_op fp ((zfp (c[*]c0))[+X*](zxfpx (cpoly_mult_cr_cs _ g c)))
   (([0]:fp)[+X*](zxfpx (cpoly_mult_op _ f (c0[+X*]g))))).
 astepl ((zfp (c[*]c0)[+]([0]:fp))[+X*](cpoly_plus_op fp
   (zxfpx (cpoly_mult_cr_cs _ g c)) (zxfpx (cpoly_mult_op _ f (c0[+X*]g))))).
 intuition; auto with *.
Qed.

#[global]
Hint Resolve fpx_resp_mult : algebra.

Lemma fpx_resp_coef : forall (f:zx)(n:nat), (zfp (nth_coeff n f))
  [=] (nth_coeff n (zxfpx f)).
Proof.
 induction f.
  intuition; auto with *.
 induction n.
  intuition; auto with *.
 astepl (zfp (nth_coeff n f)).
 astepr (nth_coeff n (zxfpx f)).
 apply (IHf n).
Qed.

#[global]
Hint Resolve fpx_resp_coef : algebra.



(**
** Working towards the criterion
*** Definitions
We prove the criterion for monic integers of degree greater than 1.
This property is first defined, so that reducibility can be defined next.
We then prove that a reducible integer polynomial is reducible over
Fp. Finally irreducibility is defined.
*)



Definition degree_ge_monic (R:CRing)(n:nat)(f:(cpoly_cring R)) :=
  {m:nat | (n >= m)%nat | monic m f}.

Lemma fpx_resp_deggemonic : forall (f:zx)(n:nat),
  degree_ge_monic _ n f -> degree_ge_monic _ n (zxfpx f).
Proof.
 intros f n; unfold degree_ge_monic.
 intro X; elim X.
 intros m Hm Hfmonm.
 exists m.
  exact Hm.
 elim Hfmonm.
 intros Hnthcoeff Hdegf.
 unfold monic.
 split.
  astepl (zfp (nth_coeff m f)).
  assert ([1][=]nth_coeff m f); intuition; auto with *.
  simpl in H.
  rewrite <- H.
  intuition; auto with *.
 red.
 intros.
 astepl (zfp (nth_coeff m0 f)).
 assert ([0][=]nth_coeff m0 f); intuition; auto with *.
 simpl in H0.
 rewrite <- H0.
 intuition; auto with *.
Qed.

#[global]
Hint Resolve fpx_resp_deggemonic : algebra.

Definition reducible (R:CRing)(f:(cpoly_cring R)) :=
  degree_ge_monic R 2%nat f and
  {g:(cpoly_cring R) | degree_ge_monic R 1%nat g |
    {h:(cpoly_cring R) | degree_ge_monic R 1%nat h |
      f[=](cpoly_mult_op R g h) }}.

Lemma fpx_resp_red : forall f:zx, (reducible _ f)->(reducible fp (zxfpx f)).
Proof.
 intros f Hfred; elim Hfred.
 intros Hfok Hfred2; elim Hfred2.
 intros g Hgok Hfred3; elim Hfred3.
 intros h Hhok Hfgh; unfold reducible.
 intuition; auto with *.
 exists (zxfpx g).
  intuition; auto with *.
 exists (zxfpx h).
  intuition; auto with *.
 astepr (zxfpx (cpoly_mult_op _ g h)).
 apply fpxeq_wd.
 exact Hfgh.
Qed.

#[global]
Hint Resolve fpx_resp_red : algebra.

Definition irreducible (R:CRing)(f:(cpoly_cring R)) :=
  Not (reducible R f).

(**
*** The criterion
And now we can state and prove the irreducibility criterion.
*)

Theorem irrcrit : forall f:zx, (irreducible fp (zxfpx f)) ->
  (irreducible _ f).
Proof.
 unfold irreducible.
 intro f.
 cut ((reducible _ f) -> (reducible fp (zxfpx f))).
  intros X H X0.
  apply H.
  apply X.
  exact X0.
 apply fpx_resp_red.
Qed.

