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

Require Export CoRN.ftc.IntervalFunct.

Section Conversion.

(**
* Correspondence

In this file we prove that there are mappings going in both ways
between the set of partial functions whose domain contains
[[a,b]] and the set of real-valued functions with domain on
that interval.  These mappings form an adjunction, and thus they have
all the good properties for preservation results.

** Mappings

We begin by defining the map from partial functions to setoid
functions as simply being the restriction of the partial function to
the interval [[a,b]].

%\begin{convention}% Let [F] be a partial function and [a,b:IR] such
that [I [=] [a,b]] is included in the domain of [F].
%\end{convention}%
*)

Variable F : PartIR.
Variables a b : IR.
Hypothesis Hab : a [<=] b.
(* begin hide *)
Let I := compact a b Hab.
(* end hide *)

Hypothesis Hf : included I (Dom F).

Lemma IntPartIR_strext : fun_strext
 (fun x : subset I => F (scs_elem _ _ x) (Hf _ (scs_prf _ _ x))).
Proof.
 red in |- *; intros x y H.
 generalize (pfstrx _ _ _ _ _ _ H).
 case x; case y; auto.
Qed.

Definition IntPartIR : CSetoid_fun (subset I) IR.
Proof.
 apply Build_CSetoid_fun with (fun x : subset I =>
   Part F (scs_elem _ _ x) (Hf (scs_elem _ _ x) (scs_prf _ _ x))).
 exact IntPartIR_strext.
Defined.

End Conversion.

Arguments IntPartIR [F a b Hab].

Section AntiConversion.

(**
To go the other way around, we simply take a setoid function [f] with
domain [[a,b]] and build the corresponding partial function.
*)

Variables a b : IR.
Hypothesis Hab : a [<=] b.
(* begin hide *)
Let I := compact a b Hab.
(* end hide *)

Variable f : CSetoid_fun (subset I) IR.

Lemma PartInt_strext : forall x y Hx Hy,
 f (Build_subcsetoid_crr IR _ x Hx) [#] f (Build_subcsetoid_crr IR _ y Hy) -> x [#] y.
Proof.
 intros x y Hx Hy H.
 exact (csf_strext_unfolded _ _ _ _ _ H).
Qed.

Definition PartInt : PartIR.
Proof.
 apply Build_PartFunct with (pfpfun := fun (x : IR) Hx => f (Build_subcsetoid_crr IR _ x Hx)).
  exact (compact_wd _ _ _).
 exact PartInt_strext.
Defined.

End AntiConversion.

Arguments PartInt [a b Hab].

Section Inverses.

(**
In one direction these operators are inverses.
*)

Lemma int_part_int : forall a b Hab F (Hf : included (compact a b Hab) (Dom F)),
 Feq (compact a b Hab) F (PartInt (IntPartIR Hf)).
Proof.
 intros; FEQ.
Qed.

End Inverses.

Section Equivalences.

(**
** Mappings Preserve Operations

We now prove that all the operations we have defined on both sets are
preserved by [PartInt].

%\begin{convention}% Let [F,G] be partial functions and [a,b:IR] and
denote by [I] the interval [[a,b]].  Let [f,g] be setoid functions of
type [I->IR] equal respectively to [F] and [G] in [I].
%\end{convention}%
*)

Variables F G : PartIR.
Variables a b c : IR.
Hypothesis Hab : a [<=] b.
(* begin hide *)
Let I := compact a b Hab.
(* end hide *)

Variables f g : CSetoid_fun (subset (compact a b Hab)) IR.

Hypothesis Ff : Feq I F (PartInt f).
Hypothesis Gg : Feq I G (PartInt g).

Lemma part_int_const : Feq I [-C-]c (PartInt (IConst (Hab:=Hab) c)).
Proof.
 apply eq_imp_Feq.
   red in |- *; simpl in |- *; intros; auto.
  unfold I in |- *; apply included_refl.
 intros; simpl in |- *; algebra.
Qed.

Lemma part_int_id : Feq I FId (PartInt (IId (Hab:=Hab))).
Proof.
 apply eq_imp_Feq.
   red in |- *; simpl in |- *; intros; auto.
  unfold I in |- *; apply included_refl.
 intros; simpl in |- *; algebra.
Qed.

Lemma part_int_plus : Feq I (F{+}G) (PartInt (IPlus f g)).
Proof.
 elim Ff; intros incF Hf.
 elim Hf; clear Ff Hf; intros incF' Hf.
 elim Gg; intros incG Hg.
 elim Hg; clear Gg Hg; intros incG' Hg.
 apply eq_imp_Feq.
   Included.
  Included.
 intros; simpl in |- *; simpl in Hf, Hg.
 simpl in |- *; algebra.
Qed.

Lemma part_int_inv : Feq I {--}F (PartInt (IInv f)).
Proof.
 elim Ff; intros incF Hf.
 elim Hf; clear Ff Hf; intros incF' Hf.
 apply eq_imp_Feq.
   Included.
  Included.
 intros; simpl in |- *; simpl in Hf.
 simpl in |- *; algebra.
Qed.

Lemma part_int_minus : Feq I (F{-}G) (PartInt (IMinus f g)).
Proof.
 elim Ff; intros incF Hf.
 elim Hf; clear Ff Hf; intros incF' Hf.
 elim Gg; intros incG Hg.
 elim Hg; clear Gg Hg; intros incG' Hg.
 apply eq_imp_Feq.
   Included.
  Included.
 intros; simpl in |- *; simpl in Hf, Hg.
 simpl in |- *; algebra.
Qed.

Lemma part_int_mult : Feq I (F{*}G) (PartInt (IMult f g)).
Proof.
 elim Ff; intros incF Hf.
 elim Hf; clear Ff Hf; intros incF' Hf.
 elim Gg; intros incG Hg.
 elim Hg; clear Gg Hg; intros incG' Hg.
 apply eq_imp_Feq.
   Included.
  Included.
 intros; simpl in |- *; simpl in Hf, Hg.
 simpl in |- *; algebra.
Qed.

Lemma part_int_nth : forall n : nat, Feq I (F{^}n) (PartInt (INth f n)).
Proof.
 intro.
 elim Ff; intros incF Hf.
 elim Hf; clear Ff Hf; intros incF' Hf.
 apply eq_imp_Feq.
   Included.
  Included.
 intros; simpl in |- *; simpl in Hf.
 astepl (Part F x Hx[^]n); astepr (f (Build_subcsetoid_crr IR _ x Hx')[^]n).
 apply nexp_wd; algebra.
Qed.

(* begin show *)
Hypothesis HG : bnd_away_zero I G.
Hypothesis Hg : forall x : subset I, g x [#] [0].
(* end show *)

Lemma part_int_recip : Feq I {1/}G (PartInt (IRecip g Hg)).
Proof.
 elim Gg; intros incG Hg'.
 elim Hg'; clear Gg Hg'; intros incG' Hg'.
 apply eq_imp_Feq.
   Included.
  Included.
 intros; simpl in Hg'; simpl in |- *; algebra.
Qed.

Lemma part_int_div : Feq I (F{/}G) (PartInt (IDiv f g Hg)).
Proof.
 elim Ff; intros incF Hf.
 elim Hf; clear Ff Hf; intros incF' Hf.
 elim Gg; intros incG Hg'.
 elim Hg'; clear Gg Hg'; intros incG' Hg'.
 apply eq_imp_Feq.
   Included.
  Included.
 intros; simpl in Hf, Hg'; simpl in |- *.
 algebra.
Qed.

End Equivalences.
