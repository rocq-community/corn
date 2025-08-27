(*
Copyright © 2006 Russell O’Connor

Permission is hereby granted, free of charge, to any person obtaining a copy of
this proof and associated documentation files (the "Proof"), to deal in
the Proof without restriction, including without limitation the rights to
use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies of
the Proof, and to permit persons to whom the Proof is furnished to do so,
subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Proof.

THE PROOF IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS
FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR
COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER
IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN
CONNECTION WITH THE PROOF OR THE USE OR OTHER DEALINGS IN THE PROOF.
*)
From CoRN Require Import CRtrans.

Local Open Scope Q_scope.

(* This file illustrates how to use the computational reals CR *)

(* `∗' is used for trival proofs that a some concrete number is less than another *)
Definition star := @refl_equal _ Lt.
Notation "∗" := star.

(* The answer function returns an approximation of r within 10^-n.
Take the resulting integer and divide by 10^n to get the actual rational approximation.
answer is useful for because it displays a familar list of digits rather
than an unfamiliar fraction that approximate would return *)

Definition answer (n:positive) (r:CR) : Z :=
 let m := (iter_pos _ (Pmult 10) 1%positive n) in
 let (a,b) := (approximate r (Qpos2QposInf (1#m)))*(Zpos m#1) in
 Z.div a (Zpos b).

(* Here are some example approximations to real numbers *)

(* approximate the integer 7 *)
Time Eval vm_compute in answer 10 ('7)%CR.
(* approximate the rational 0.5 *)
Time Eval vm_compute in answer 10 ('(1#2))%CR.
(* approximate pi *)
Time Eval vm_compute in answer 50 (CRpi)%CR.
(* approximate e *)
Time Eval vm_compute in answer 50 (rational_exp 1)%CR.
(* approximate e^-1 *)
Time Eval vm_compute in answer 50 (rational_exp (-(1)))%CR.
(* approximate e^pi - pi.  May take a minute *)
Time Eval vm_compute in answer 20 (exp (compress CRpi) - CRpi)%CR.

(* The following expressions are taken from the
  Many Digits friendly competition practice set,
  which in turn are taken from the CCA 2000 competition *)
(* sin (sin (sin(1))) *)
Time Eval vm_compute in answer 20 (sin (compress (sin (compress (rational_sin 1)))))%CR.
(* sqrt (pi) *)
Time Eval vm_compute in answer 20 (CRsqrt (compress CRpi))%CR.
(* sin e *)
Time Eval vm_compute in answer 20 (sin (compress (rational_exp 1)))%CR.
(* exp (pi * sqrt(163)) : Takes upt 3 minutes
Time Eval vm_compute in answer 1 (exp (compress (rational_sqrt 163 * CRpi)))%CR. *)
(* exp (exp (exp (1))) *)
Time Eval vm_compute in answer 1 (exp (compress (exp (compress (rational_exp 1)))))%CR. 

(* The following expressions are taken from the
  Many Digits friendly competition problem set *)
(* sqrt (e/pi) *)
Time Eval vm_compute in answer 20 (CRsqrt (compress (rational_exp (1))*compress (CRinv_pos (3#1) CRpi)))%CR.
(* sin((e+1)^3) *)
Time Eval vm_compute in answer 20 (sin (compress (CRpower_slow (translate (1#1) (compress (rational_exp (1)))) 3)))%CR.
(* sin(10^22) still takes too long, see http://www.derekroconnor.net/DAMQ/FPArithSlidesHO.pdf *)
Time Eval vm_compute in answer 10 (rational_sin (10^14))%CR.
(* exp (exp (exp (1/2))) *)
Time Eval vm_compute in answer 10 (exp (compress (exp (compress (rational_exp (1#2))))))%CR.

From CoRN Require Import CRsign.

(* This example shows how to automatically solve inequalites for CR *)
Example xkcd217A : (exp (CRpi) - CRpi < '(20#1))%CR.
unfold CRlt.
Time CR_solve_pos (1#1000)%Qpos.
Qed.

From CoRN Require Import Exponential Pi.

(* This example shows how to automatically solve inequalites for IR *)

Example xkcd217B : (Exp Pi [-] Pi [<] (nring 20)).
Time IR_solve_ineq (1#1000)%Qpos.
Qed.

From CoRN Require Import MultivariatePolynomials.

(* approximate 4*(1/e)*(1-(1/e)) while sharing the expression (1/e)
   using multivariable polynomial library (which only uses one variable
   in this case). *)
(*
Time Eval vm_compute in 
 answer 20 (MVP_uc_fun 1 ((_C_ (4#1))[*]_X_[*](One[-]_X_)) (rational_exp (-1#1))%CR).
*)

