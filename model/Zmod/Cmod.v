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

Require Export CoRN.model.Zmod.ZMod.
Require Export CoRN.logic.CLogic.

(**
* CProp-valued lemmas about 'mod'
*)

Lemma Zmod_pos:(forall (k l:nat)(H:(l>0)%Z),
  (k mod l)%Z=0 or {p:positive|(k mod l)%Z =(Zpos p)}):CProp.
Proof.
 simpl.
 intros k l.
 intro H0.
 set (H:= (Z_mod_lt k l H0)).
 elim H.
 clear H.
 intros H1 H2.
 elim (Z_le_lt_eq_dec 0 (k mod l)%Z H1).
  case (k mod l)%Z.
    intuition.
   intros p H.
   right.
   exists p.
   reflexivity.
  intros p H3.
  2:intuition.
 cut False.
  intuition.
 cut (Zneg p < 0)%Z.
  intuition; auto with *.
 unfold Z.lt.
 intuition; auto with *.
Qed.


Definition mod_nat: forall (k l:nat)(H:(l>0)%Z),nat.
Proof.
 intros k l H3.
 set (H:= (Zmod_pos k l H3)).
 elim H.
  intro H0.
  exact 0.
 intro H0.
 elim H0.
 intros p H1.
 exact (nat_of_P p).
Defined.

Lemma mod_nat_correct: forall (k l:nat)(H:(l>0)%Z),
  (k mod l)%Z = (Z_of_nat (mod_nat k l H)).
Proof.
 intros k l H.
 unfold mod_nat.
 unfold sum_rec.
 unfold sum_rect.
 case ( Zmod_pos k l H).
  tauto.
 unfold sigT_rec.
 unfold sigT_rect.
 intro H0.
 case H0.
 simpl.
 intro x.
 set (H1:= (inject_nat_convert x)).
 intuition; auto with *.
Qed.

Lemma  nat_Z_div:forall (a b c r:nat)(b' r':Z),
  a=b*c+r->r<c->((Z_of_nat a)=c*b'+r')%Z->(0<=r'<c)%Z-> ((Z_of_nat r)=r').
Proof.
 intros a b c0 r b' r' H H1 H2 H3.
 cut (c0>0)%Z.
  intro H5.
  2:intuition; auto with *.
 set (H4:=(Z_div_mod_eq_full (Z_of_nat a) (Z_of_nat c0))).
 cut ((Z_of_nat a mod (Z_of_nat c0))%Z = r').
  intro H6.
  rewrite<- H6.
  cut ((Z_of_nat a mod (Z_of_nat c0))%Z= (Z_of_nat r)).
   intro H7.
   rewrite<- H7.
   reflexivity.
  rewrite H.
  set (H8:= (Zmod_cancel_multiple c0 r b H5)).
  set (H9:= (inj_mult b c0)).
  set (H10:= (inj_plus (b*c0) r)).
  rewrite H10.
  rewrite H9.
  rewrite H8.
  apply Zmod_small.
   intuition; auto with *.
  intuition.
 rewrite H2.
 replace (Z_of_nat c0 * b' + r')%Z with ( b'*Z_of_nat c0 + r')%Z.
  2:intuition; auto with *.
 set (H8:= (Zmod_cancel_multiple c0 r' b' H5)).
 rewrite H8.
 apply Zmod_small; intuition; auto with *.
Qed.
