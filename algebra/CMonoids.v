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

(** printing [0] %\ensuremath{\mathbf0}% #0# *)

From Coq Require Export Euclid.
Require Export CoRN.model.Zmod.Cmod.
Require Export CoRN.algebra.CSemiGroups.
Require Export CoRN.tactics.csetoid_rewrite.
Require Export CoRN.model.structures.Nsec.
Require Import CoRN.util.SetoidPermutation Coq.Setoids.Setoid Coq.Classes.Morphisms.

(* Begin_SpecReals *)

(**
* Monoids %\label{section:monoids}%
** Definition of monoids
*)

Record is_CMonoid (M : CSemiGroup) (Zero : M) : Prop :=
  {runit : is_rht_unit (csg_op (c:=M)) Zero;
   lunit : is_lft_unit (csg_op (c:=M)) Zero}.

Record CMonoid : Type :=
  {cm_crr   :> CSemiGroup;
   cm_unit  :  cm_crr;
   cm_proof :  is_CMonoid cm_crr cm_unit}.

(**
%\begin{nameconvention}%
In the names of lemmas, we will denote [[0]] with [zero].
We denote [ [#] [0]] in the names of lemmas by [ap_zero]
(and not, e.g.%\% [nonzero]).
%\end{nameconvention}%
*)

(* Begin_SpecReals *)

(**
The predicate "non-zero" is defined.
In lemmas we will continue to write [x [#] [0]], rather than
[(nonZeroP x)], but the predicate is useful for some high-level definitions,
e.g. for the setoid of non-zeros.
*)

Notation "[0]" := (cm_unit _).

Definition nonZeroP (M : CMonoid) (x : M) : CProp := x [#] [0].

(* End_SpecReals *)

Arguments nonZeroP [M].

(**
** Monoid axioms
%\begin{convention}% Let [M] be a monoid.
%\end{convention}%
*)
Section CMonoid_axioms.
Variable M : CMonoid.

Lemma CMonoid_is_CMonoid : is_CMonoid M (cm_unit M).
Proof.
 elim M; auto.
Qed.

Lemma cm_rht_unit : is_rht_unit csg_op ([0]:M).
Proof.
 elim CMonoid_is_CMonoid; auto.
Qed.

Lemma cm_lft_unit : is_lft_unit csg_op ([0]:M).
Proof.
 elim CMonoid_is_CMonoid; auto.
Qed.

End CMonoid_axioms.

(**
** Monoid basics
%\begin{convention}% Let [M] be a monoid.
%\end{convention}%
*)
Section CMonoid_basics.
Variable M : CMonoid.

Lemma cm_rht_unit_unfolded : forall x : M, x[+][0] [=] x.
Proof cm_rht_unit M.

Lemma cm_lft_unit_unfolded : forall x : M, [0][+]x [=] x.
Proof cm_lft_unit M.

Hint Resolve cm_rht_unit_unfolded cm_lft_unit_unfolded: algebra.

Lemma cm_unit_unique_lft : forall x : M, is_lft_unit csg_op x -> x [=] [0].
Proof.
 intros x h. red in h.
 Step_final (x[+][0]).
Qed.

Lemma cm_unit_unique_rht : forall x : M, is_rht_unit csg_op x -> x [=] [0].
Proof.
 intros x h. red in h.
 Step_final ([0][+]x).
Qed.

(* Begin_SpecReals *)

(**
The proof component of the monoid is irrelevant.
*)

Lemma is_CMonoid_proof_irr : forall (S:CSetoid) (Zero:S) (plus : CSetoid_bin_op S)
 (p q : associative plus), is_CMonoid (Build_CSemiGroup S plus p) Zero ->
 is_CMonoid (Build_CSemiGroup S plus q) Zero.
Proof.
 intros S one mult p q H.
 elim H; intros runit0 lunit0.
 simpl in runit0.
 simpl in lunit0.
 apply Build_is_CMonoid; simpl in |- *; assumption.
Qed.

(* End_SpecReals *)

(**
** Submonoids
%\begin{convention}%
Let [P] a predicate on [M] containing [[0]] and closed under [[+]].
%\end{convention}%
*)

Section SubCMonoids.
Variable P : M -> CProp.
Variable Punit : P [0].
Variable op_pres_P : bin_op_pres_pred _ P csg_op.

Let subcrr : CSemiGroup := Build_SubCSemiGroup _ _ op_pres_P.

Lemma ismon_scrr : is_CMonoid subcrr (Build_subcsetoid_crr _ _ _ Punit).
Proof.
 split; red in |- *.
  (* right unit *)
  intro x. case x. intros scs_elem scs_prf.
  apply (cm_rht_unit_unfolded scs_elem).
 (* left unit *)
 intro x. case x. intros scs_elem scs_prf.
 apply (cm_lft_unit_unfolded scs_elem).
Qed.

Definition Build_SubCMonoid : CMonoid := Build_CMonoid subcrr _ ismon_scrr.

End SubCMonoids.

End CMonoid_basics.

Section Th13.
(**
** Morphism, isomorphism and automorphism of Monoids
%\begin{convention}%
Let [M1 M2 M M':CMonoid].
%\end{convention}%
*)
Variable M1:CMonoid.
Variable M2:CMonoid.

Definition morphism (f:(CSetoid_fun M1 M2)):CProp:=
(f ([0])[=][0] /\ forall (a b:M1), (f (a[+]b))[=] (f a)[+](f b)).

Definition isomorphism (f:(CSetoid_fun M1 M2)):CProp:=
(morphism f) and (bijective f).

End Th13.

Section p71E2b1.

Definition isomorphic (M:CMonoid)(M':CMonoid): CProp:=
{f:(CSetoid_fun M M')|(isomorphism M M' f)}.

End p71E2b1.

Section Th14.
(**
%\begin{convention}%
Let [f:(CSetoid_fun M1 M2)] and [isof: (isomorphism M1 M2 f)].
%\end{convention}%
*)

Variable M1: CMonoid.
Variable M2: CMonoid.
Variable f: (CSetoid_fun M1 M2).
Variable isof: (isomorphism M1 M2 f).

Lemma iso_imp_bij: (bijective f).
Proof.
 unfold isomorphism in isof.
 intuition.
Qed.

Lemma iso_inv: (isomorphism M2 M1 (Inv f (iso_imp_bij))).
Proof.
 unfold isomorphism.
 split.
  unfold morphism.
  split.
   unfold isomorphism in isof.
   unfold morphism in isof.
   elim isof.
   intros H0 H1.
   elim H0.
   clear H0.
   intros H3 H4.
   astepl ((Inv f iso_imp_bij) (f [0])).
   unfold Inv.
   simpl.
   apply inv2.
  intros a b.  elim isof. intros H0 H1. destruct H1 as [H1 H2].
  destruct (H2 a) as [a' fa'a]. destruct (H2 b) as [b' fb'b].
  unfold morphism in H0.
  astepl ((Inv f iso_imp_bij) (f a' [+] f b')).
  astepl ((Inv f iso_imp_bij) ( f ( a'[+] b'))).
   set (H3:= (inv2 M1 M2 f iso_imp_bij (a'[+]b'))).
   astepl (a'[+]b'). astepr (a'[+] b'). intuition; auto with *.
   set (H4:=(inv2 M1 M2 f iso_imp_bij a')).
   apply csbf_wd.
    astepr (Inv f iso_imp_bij (f a')); intuition; auto with *.
   astepr (Inv f iso_imp_bij (f b')).  set (H5:= (inv2 M1 M2 f iso_imp_bij b')); intuition; auto with *.
   intuition; auto with *.
 apply Inv_bij.
Qed.

End Th14.

Section p71R2.

Variable M:CMonoid.

Definition automorphism:= (isomorphism M M).

End p71R2.

Section p71E1.
(**
** Power in a monoid
%\begin{convention}%
Let [M:CMonoid] and [c:M].
%\end{convention}%
*)

Variable M:CMonoid.
Variable c:M.

Fixpoint power_CMonoid (m:M)(n:nat){struct n}:M:=
match n with
|0 => (cm_unit M)
|(S p) => m [+] (power_CMonoid m p)
end.

End p71E1.

Arguments power_CMonoid [M].

Lemma power_plus:forall (M:CMonoid)(a:M)(m n:nat),
  (power_CMonoid a (m+n))[=]
  (power_CMonoid a m)[+](power_CMonoid a n).
Proof.
 intros M a m n.
 induction m.
  simpl.
  apply eq_symmetric.
  apply cm_lft_unit.
 simpl.
 astepl (csbf_fun M M M (csg_op (c:=M)) a ((csbf_fun M M M (csg_op (c:=M)) (power_CMonoid a m)
   (power_CMonoid a n)))).
 algebra.
Qed.


(**
** Cyclicity
*)

Definition is_generator (M:CMonoid)(u:M):CProp:=
  forall (m:M),{n:nat | (power_CMonoid u n)[=]m}.

Definition cyclic : CMonoid -> CProp :=
  fun M =>
  {u:M | (forall (m:M),{n:nat | (power_CMonoid u n)[=]m}):CProp}.

Section gen_cyc.

Lemma power_k:forall (M:CMonoid)(u:M)(k l s:nat),(is_generator M u)->
  ((k<l and
  (power_CMonoid u  k [=] power_CMonoid u l)
  and ((forall (k0 l0:nat), (k0<>l0 and (k0<k or (k0=k and l0<l)))->
  (power_CMonoid u k0 [#] power_CMonoid u l0)))):CProp)->
  (power_CMonoid u  k)[=](power_CMonoid u (k+(s*(l-k)))).
Proof.
 intros M u k l s H.
 unfold is_generator in H.
 intros H0.
 induction s.
  simpl.
  replace (k+0) with k.
   intuition; auto with *.
  intuition.
 simpl.
 replace (k+((l-k)+s*(l-k)))  with (l + s*(l-k)).
  2:intuition; auto with *.
 set (H1:= (power_plus M u l (s*(l-k)))).
 astepr  (csbf_fun (csg_crr (cm_crr M)) (csg_crr (cm_crr M))
   (csg_crr (cm_crr M)) (csg_op (c:=cm_crr M)) (power_CMonoid u l) (power_CMonoid u (s * (l - k)))).
 elim H0.
 clear H0.
 intros H0 H0'.
 elim H0'.
 clear H0'.
 intros H0' H0''.
 cut ( power_CMonoid u l[=]power_CMonoid u k).
  intro H4.
  rewrite -> H4.
  2: now apply eq_symmetric.
 set (H5:=(power_plus M  u k (s*(l-k)))).
 cut (csbf_fun M M M (csg_op (c:=M)) (power_CMonoid  u k)
   (power_CMonoid u (s * (l - k)))[=]power_CMonoid u (k + s * (l - k))).
  intros H6.
  now rewrite -> H6.
 now symmetry. 
Qed.

Lemma power_k_n:forall (M:CMonoid)(u:M)(k l n :nat)
  (H2:((Z_of_nat (l-k)>0)%Z)),(is_generator M u)->(k<n)->
  ((k<l and
  (power_CMonoid u k [=] power_CMonoid u l)
  and ((forall (k0 l0:nat), (k0<> l0 and (k0<k or (k0=k and l0<l)))->
  (power_CMonoid u k0 [#] power_CMonoid u l0)))):CProp)->
  (power_CMonoid u n)[=](power_CMonoid u (k+(mod_nat (n-k) (l-k) H2))).
Proof.
 intros M u  k l n H2 H H15.
 set (H13:=(power_k M u k l)).
 intros H4.
 set (H6:=(Z_div_mod_eq_full (n-k)(l-k))).
 cut (((n - k) mod (l - k))= (n-k)%Z -((l - k) * ((n - k) / (l - k))))%Z.
  2:intuition; auto with *.
 set (H7:=(mod_nat_correct (n-k) (l-k) H2)).
 intro H8.
 cut {s:nat | (mod_nat (n-k)(l-k) H2)=(n-k)-s*(l-k) and s*(l-k)<=(n-k)}.
  intro H9.
  elim H9.
  clear H9.
  intros s H9.
  elim H9.
  clear H9.
  intros H9 H9'.
  rewrite H9.
  replace (power_CMonoid u n) with (power_CMonoid u ((k+s*(l-k))+((n-k)-s*(l-k)))).
   2: (replace ((k + s * (l - k))+((n - k) - s * (l - k))) with n). 2:reflexivity.
   rewrite -> (power_plus M  u  (k+(s*(l-k))) ((n-k)-s*(l-k))).
   rewrite -> (power_plus M u k (n-k-s*(l-k))).
   setoid_replace (power_CMonoid u (k + s * (l - k))) with (power_CMonoid u k). now reflexivity.
  unfold canonical_names.equiv. now intuition; auto with *. 
  cut (n=k+(n-k)).
   intro H10.
   cut (n=((k+(n-k))+(s*(l-k)-s*(l-k)))).
    intro H11.
    cut  ((k+(n-k))+(s*(l-k)-s*(l-k)) = (k + s * (l - k) + (n - k - s * (l - k)))).
     intro H12.
     now rewrite<- H11 in H12.
    apply minus4.
    split.
     now intuition.
    exact H9'.
   rewrite<- H10.
   cut ((s*(l-k)-s*(l-k))=0).
    intro H11.
    rewrite H11.
    now intuition.
   now intuition; auto with *.
  cut (n=n+(k-k)).
   intro H10.
   cut (n+(k-k)=k+(n-k)).
    intro H11.
    now rewrite<- H10 in H11.
   apply minus3.
   split; now intuition; auto with *.
  cut ((k-k)=0).
   intro H10.
   now rewrite H10.
  now intuition; auto with *.
 simpl.
 cut (l-k>0).
  intro H9.
  set (H10:=(quotient (l-k) H9 (n-k))).
  elim H10.
  clear H10.
  intros q H10.
  exists q.
  split.
   elim H10.
   clear H10.
   intros r H10'.
   elim H10'.
   clear H10'.
   intros H10' H10''.
   3:intuition; auto with *.
  cut ((n-k)= q*(l-k)+ (mod_nat (n-k)(l-k) H2)).
   intro H11.
   intuition; auto with *.
  cut (r= (mod_nat (n-k)(l-k)H2)).
   intro H11.
   now rewrite<- H11.
  simpl.
  cut ((Z_of_nat r)=(mod_nat (n - k) (l - k) H2)).
   intro H11.
   intuition; auto with *.
  rewrite<- H7.
  apply nat_Z_div with (n-k) q (l-k) ((Z_of_nat n - Z_of_nat k) / (Z_of_nat l - Z_of_nat k))%Z.
     exact H10'.
    intuition.
   cut (k<=l).
    intro H11.
    set (H12:=(inj_minus1 l k H11)).
    rewrite H12.
    cut (k<=n).
     intro H14.
     set (H16:=(inj_minus1 n k H14)).
     rewrite H16.
     exact H6.
    intuition; auto with *.
   intuition; auto with *.
  set (H17:=(Z_mod_lt (Z_of_nat (n-k)) (Z_of_nat (l-k)))).
  intuition; auto with *.
 elim H10.
 clear H10.
 intros r H10.
 elim H10.
 clear H10.
 intros H10 H10'.
 intuition; auto with *.
Qed.

Lemma cyc_imp_comm: forall (M:CMonoid)(H:(cyclic M)), (commutes (@csg_op M)).
Proof.
 intros M H.
 unfold commutes.
 intros x y.
 unfold cyclic in H.
 elim H.
 clear H.
 intros c0 H.
 elim (H x).
 intros nx Hx.
 elim (H y).
 intros ny Hy.
 rewrite <- Hx.
 rewrite <- Hy.
 rewrite <- (power_plus M c0 nx ny).
 replace (nx+ny) with (ny+nx).
  rewrite -> (power_plus M c0 ny nx).
  now apply eq_reflexive.
 intuition; auto with *.
Qed.

Lemma weakly_inj1:
  forall (M:CMonoid)(u:M)(k l a b:nat),(is_generator M u)->(a<l)->(b<l)->
  (k<l and (power_CMonoid u  k [=] power_CMonoid u l)
  and (forall (k0 l0:nat),k0<>l0 and (k0<k or (k0=k and l0<l))->
  (power_CMonoid u  k0 [#] power_CMonoid u l0)))->
  (power_CMonoid u a)[=](power_CMonoid u b) ->
a=b.
Proof.
 intros M u  k l a b H H0 H1.
 unfold is_generator in H.
 intros H3 H4.
 elim (eq_nat_dec a b).
  tauto.
 intro H5.
 elim (not_or a b H5).
  clear H5.
  intro H5.
  cut False.
   intuition.
  set (H6:= (eq_imp_not_ap M (power_CMonoid u a)(power_CMonoid u b) H4)).
  unfold Not in H6.
  cut (k<>a+(l-b) or k=a+(l-b)).
   intro orex.
   elim orex.
    clear orex.
    intro orex.
    cut ((power_CMonoid u a[#]power_CMonoid u b) or (power_CMonoid u (l-b)[#]power_CMonoid u (l-b))).
     intro H7.
     elim H7.
      tauto.
     clear H7.
     intro H7.
     set (H8:= (ap_irreflexive_unfolded M (power_CMonoid u (l-b)) H7)).
     intuition.
    apply bin_op_strext_unfolded with (@csg_op M).
    csetoid_rewrite_rev (power_plus M u b (l-b)).
    csetoid_rewrite_rev (power_plus M u a (l-b)).
    elim H3.
    clear H3.
    intros H3 H7.
    elim H7.
    clear H7.
    intros H7 H8.
    replace (b+(l-b)) with l.
     csetoid_rewrite_rev H7.
     apply: ap_symmetric.
     apply H8.
     split.
      intuition.
     right.
     intuition; auto with *.
    intuition; auto with *.
   clear orex.
   intro orex.
   intuition; auto with *.
  intuition auto with *.
 clear H5.
 intro H5.
 cut False.
  intuition.
 cut (power_CMonoid (M:=M) u b[=]power_CMonoid (M:=M) u a).
  intro H4'.
  set (H6:= (eq_imp_not_ap M (power_CMonoid u a)(power_CMonoid u b) H4)).
  set (H6':= (eq_imp_not_ap M (power_CMonoid u b)(power_CMonoid u a) H4')).
  unfold Not in H6.
  cut (k<>b+(l-a) or k=b+(l-a)).
   intro orex.
   elim orex.
    clear orex.
    intro orex.
    cut ((power_CMonoid u a[#]power_CMonoid u b) or (power_CMonoid u (l-a)[#]power_CMonoid u (l-a))).
     intro H7.
     elim H7.
      tauto.
     clear H7.
     intro H7.
     set (H8:= (ap_irreflexive_unfolded M (power_CMonoid u (l-a)) H7)).
     intuition.
    apply bin_op_strext_unfolded with (@csg_op M).
    csetoid_rewrite_rev (power_plus M u b (l-a)).
    csetoid_rewrite_rev (power_plus M u a (l-a)).
    elim H3.
    clear H3.
    intros H3 H7.
    elim H7.
    clear H7.
    intros H7 H8.
    replace (a+(l-a)) with l.
     csetoid_rewrite_rev H7.
     apply H8.
     split.
      intuition.
     right.
     intuition auto with *.
    intuition auto with *.
   clear orex.
   intro orex.
   intuition; auto with *.
  intuition auto with *.
 intuition; auto with *.

Qed.

(**
%\begin{convention}%
Let [M:CMonoid].
%\end{convention}%
*)

Variable M:CMonoid.

Lemma generator_imp_cyclic: (forall (u:M),
  (is_generator M u)-> (cyclic M)):CProp.
Proof.
 intros u H.
 unfold is_generator in H.
 exists u.
 exact H.
Qed.

End gen_cyc.

(**
** Invertability
*)

Definition is_inverse S (op : CSetoid_bin_op S) Zero x x_inv : Prop :=
 op x x_inv [=] Zero /\ op x_inv x [=] Zero.

Arguments is_inverse [S].

Definition invertible (M:CMonoid): M -> CProp :=
fun m =>{inv: (CSetoid_un_op M) | (is_inverse csg_op (@cm_unit M) m (inv m))}.

Section D9M.
(**
** Direct Product
%\begin{convention}%
Let [M1 M2:CMonoid]
%\end{convention}%
*)

Variable M1 M2: CMonoid.

Lemma  e1e2_is_rht_unit:
  (is_rht_unit (dprod_as_csb_fun M1 M2)(pairT (@cm_unit M1)(@cm_unit M2))).
Proof.
 unfold is_rht_unit.
 intro x.
 case x.
 intros x1 x2.
 simpl.
 split.
  apply cm_rht_unit_unfolded.
 apply cm_rht_unit_unfolded.
Qed.

Lemma  e1e2_is_lft_unit:
  (is_lft_unit (dprod_as_csb_fun M1 M2)(pairT (@cm_unit M1)(@cm_unit M2))).
Proof.
 intro x.
 case x.
 intros x1 x2.
 simpl.
 split.
  apply cm_lft_unit_unfolded.
 apply cm_lft_unit_unfolded.
Qed.

Definition direct_product_is_CMonoid:=
  (Build_is_CMonoid (direct_product_as_CSemiGroup M1 M2)
  (pairT (@cm_unit M1)(@cm_unit M2))
   e1e2_is_rht_unit  e1e2_is_lft_unit).

Definition direct_product_as_CMonoid :=
  (Build_CMonoid (direct_product_as_CSemiGroup M1 M2)
  (pairT (@cm_unit M1)(@cm_unit M2)) direct_product_is_CMonoid).

End D9M.

Section p71E2b2.

Variable M1:CMonoid.
Variable M2:CMonoid.

Let f: (direct_product_as_CMonoid M1 M2)->
  (direct_product_as_CMonoid M2 M1).
Proof.
 simpl.
 intro x.
 elim x.
 intros x1 x2.
 exact (pairT x2 x1).
Defined.

Lemma f_strext': (fun_strext f ).
Proof.
 unfold fun_strext.
 simpl.
 intros x y.
 case x.
 intros x1 x2.
 case y.
 intros y1 y2.
 simpl.
 intuition.
Qed.

Definition f_as_CSetoid_fun_:= (Build_CSetoid_fun _ _ f f_strext').

Lemma isomorphic_PM1M2_PM2M1:
  (isomorphic (direct_product_as_CMonoid M1 M2)
  (direct_product_as_CMonoid M2 M1)):CProp.
Proof.
 unfold isomorphic.
 simpl.
 exists f_as_CSetoid_fun_.
 unfold isomorphism.
 unfold morphism.
 simpl.
 split.
  split.
   intuition; auto with *.
  intros a b.
  case a.
  intros a0 a1.
  case b.
  intros b0 b1.
  simpl.
  intuition; auto with *.
 unfold bijective.
 split.
  unfold injective.
  simpl.
  intros a0 a1.
  elim a0.
  intros b0 b1.
  elim a1.
  intros c0 c1.
  simpl.
  intuition.
 unfold surjective.
 intro b.
 elim b.
 intros a0 a1.
 exists (pairT a1 a0).
 simpl.
 intuition; auto with *.
Qed.

End p71E2b2.


(**
** The Monoids of Setoid functions and bijective Setoid functions.
*)

Definition FS_id (A : CSetoid) : FS_as_CSetoid A A.
Proof.
 unfold FS_as_CSetoid in |- *.
 simpl in |- *.
 exact (id_un_op A).
Defined.

Lemma id_is_rht_unit :
 forall A : CSetoid, is_rht_unit (comp_as_bin_op A) (FS_id A).
Proof.
 unfold is_rht_unit in |- *.
 unfold comp_as_bin_op in |- *.
 unfold FS_id in |- *.
 simpl in |- *.
 unfold eq_fun in |- *.
 unfold id_un_op in |- *.
 simpl in |- *.
 intuition; auto with *.
Qed.

Lemma id_is_lft_unit :
 forall A : CSetoid, is_lft_unit (comp_as_bin_op A) (FS_id A).
Proof.
 unfold is_lft_unit in |- *.
 unfold comp_as_bin_op in |- *.
 unfold FS_id in |- *.
 simpl in |- *.
 unfold eq_fun in |- *.
 unfold id_un_op in |- *.
 simpl in |- *.
 intuition; auto with *.
Qed.

Definition FS_is_CMonoid (A : CSetoid) :=
  Build_is_CMonoid (FS_as_CSemiGroup A) (FS_id A) (
    id_is_rht_unit A) (id_is_lft_unit A).

Definition FS_as_CMonoid (A : CSetoid) :=
  Build_CMonoid (FS_as_CSemiGroup A) (FS_id A) (FS_is_CMonoid A).


Definition PS_as_CMonoid (A : CSetoid) :=
  Build_SubCMonoid (FS_as_CMonoid A) (bijective (A:=A) (B:=A)) (
    id_is_bij A) (comp_resp_bij A A A).

(**
** The free Monoid
*)

Lemma is_unit_Astar_empty_word: forall (A:CSetoid),
(is_unit (Astar_as_CSemiGroup A)(empty_word A)).
Proof.
 intro A.
 unfold is_unit.
 simpl.
 intro a.
 split.
  apply eq_fm_reflexive.
 unfold empty_word.
 induction a.
  apply eq_fm_reflexive.
 simpl.
 intuition; auto with *.
Qed.

Section Th12.

(**
%\begin{convention}%
Let [A:CSetoid].
%\end{convention}%
*)

Variable A:CSetoid.

Lemma nil_is_rht_unit: (is_rht_unit (app_as_csb_fun A) (empty_word A)).
Proof.
 unfold is_rht_unit.
 simpl.
 intro x.
 induction x.
  simpl.
  intuition.
 simpl.
 intuition; auto with *.
Qed.

Lemma nil_is_lft_unit: (is_lft_unit (app_as_csb_fun A) (empty_word A)).
Proof.
 unfold is_lft_unit.
 simpl.
 intro x.
 induction x.
  simpl.
  intuition.
 simpl.
 intuition; auto with *.
Qed.

Definition free_monoid_is_CMonoid:
  is_CMonoid (Astar_as_CSemiGroup A) (empty_word A):=
  (Build_is_CMonoid (Astar_as_CSemiGroup A) (empty_word A)
  nil_is_rht_unit nil_is_lft_unit).

Definition free_monoid_as_CMonoid:CMonoid:=
(Build_CMonoid (Astar_as_CSemiGroup A)(empty_word A) free_monoid_is_CMonoid).

End Th12.

(**
** The unit in the setoid of Setoid functions
%\begin{convention}%
Let [X:CSetoid].
%\end{convention}%
*)

Section p67R2.
Variable X: CSetoid.
Lemma is_unit_FS_id:(is_unit (FS_as_CSemiGroup X) (FS_id X)).
Proof.
 unfold is_unit.
 intros a.
 set (H:= (id_is_rht_unit X a)).
 set (H0:= (id_is_lft_unit X a)).
 split.
  exact H0.
 exact H.
Qed.

End p67R2.

Section Th11.

(**
** Intersection
The intersection of a collection of monoids is again a monoid.
%\begin{convention}%
Let [M:CMonoid], [I:type], [C:I->(M->CProp)], [Cunit: (C i [0])] and
[op_pres_C:forall (i:I), (bin_op_pres_pred _ (C i) csg_op)].
%\end{convention}%
*)

Variable M:CMonoid.
Variable I:Type.
Variable C:I->(M->CProp).
Variable Cunit: forall (i:I), (C i [0]).
Variable op_pres_C: forall (i:I),(bin_op_pres_pred _ (C i) csg_op).

Definition K : M -> CProp :=
(fun m => forall (i:I), (C i m)).

Lemma op_pres_K: bin_op_pres_pred (cm_crr M) K (csg_op (c:=M)).
Proof.
 unfold K.
 unfold bin_op_pres_pred.
 unfold bin_op_pres_pred in op_pres_C.
 intros x y Cx Cy i.
 apply op_pres_C.
  apply Cx.
 apply Cy.
Qed.

Definition K_is_Monoid :CMonoid := (Build_SubCMonoid M K Cunit op_pres_K).

End Th11.

Section Th15.
(** The Monoid generated by a Subset
%\begin{convention}%
Let [M:CMonoid] and [D:M->CProp].
%\end{convention}%
*)

Context {M:CMonoid}.

Fixpoint cm_Sum (l: list M) {struct l}: M :=
match l with
|nil => [0]
|cons a k => a [+] (cm_Sum k)
end.

Variable D : M -> CProp.

Definition Dbrack : M -> CProp :=
  fun m => {l: (list M)| (forall (a:M) , member a l -> (D a)) and
                                        (cm_Sum l)[=]m}.

Lemma Dbrack_unit: (Dbrack [0]).
Proof.
 unfold Dbrack.
 exists (@nil M).
 simpl.
 intuition; auto with *.
Qed.


Lemma cm_Sum_app:
forall (k l : (list M)), (cm_Sum (app k l))[=] (cm_Sum k)[+](cm_Sum l).
Proof.
 intros k l.
 induction k.
  simpl.
  apply eq_symmetric.
  apply cm_lft_unit_unfolded.
 simpl.
 astepr (a [+] ( (cm_Sum k)[+](cm_Sum l))).
 apply csbf_wd_unfolded.
  intuition; auto with *.
 exact IHk.
Qed.

Lemma cm_Sum_eq {A} (a: list A) (f g: A -> M):
  (forall x, f x [=] g x) -> cm_Sum (map f a) [=] cm_Sum (map g a).
  (* This is just a specialization of Proper-ness for cm_Sum which
   I'm not doing right now because I don't want to involve the list
   setoid (parameterized by the element setoid) right now. *)
Proof with try reflexivity.
 intro E.
 induction a...
 simpl. rewrite E, IHa...
Qed.

Global Instance cm_Sum_Proper: commutes (@csg_op M) ->
 Proper (SetoidPermutation (@st_eq M) ==> @st_eq M) cm_Sum.
Proof with auto; try reflexivity.
 intros E x y H.
 induction H; simpl...
   rewrite IHSetoidPermutation, H...
  rewrite plus_assoc_unfolded, plus_assoc_unfolded, (E _ y)...
 transitivity (cm_Sum l')...
Qed.

Lemma cm_Sum_units (a: list M): (forall x, In x a -> x [=] [0]) -> cm_Sum a [=] [0].
Proof with intuition.
 clear D.
 induction a. intuition; auto with *.
 intros E.
 simpl.
 rewrite IHa...
 rewrite (E a)...
 apply cm_lft_unit_unfolded.
Qed.

Lemma op_pres_Dbrack : bin_op_pres_pred _ Dbrack csg_op.
Proof.
 unfold bin_op_pres_pred.
 intros x y.
 unfold Dbrack.
 intros Hx Hy.
 elim Hx.
 clear Hx.
 intros lx Hx.
 elim Hy.
 clear Hy.
 intros ly Hy.
 exists (app lx ly).
 split.
  intro a.
  set (H:= (member_app M a ly lx)).
  elim H.
  intros H0 H1.
  intros H2.
  set (H3:= (H0 H2)).
  elim H3.
   (generalize Hx).
   intuition.
  (generalize Hy).
  intuition.
 elim Hx.
 clear Hx.
 intros Hx1 Hx2.
 astepr ((cm_Sum lx)[+] y).
 elim Hy.
 clear Hy.
 intros Hy1 Hy2.
 astepr ( (cm_Sum lx)[+](cm_Sum ly) ).
 apply cm_Sum_app.
Qed.

Definition Dbrack_as_CMonoid : CMonoid :=
(Build_SubCMonoid M Dbrack Dbrack_unit op_pres_Dbrack).


End Th15.


#[global]
Hint Resolve cm_rht_unit_unfolded cm_lft_unit_unfolded: algebra.
