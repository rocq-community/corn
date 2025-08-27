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

From Stdlib Require Import NArith.
From CoRN Require Import Integration AbstractIntegration SimpleIntegration
(* SimpsonIntegration *)
  CRtrans QnonNeg.
Import QnonNeg.notations.

(* The answer function returns an approximation of r within 10^-n.
Take the resulting integer and divide by 10^n to get the actual rational approximation.
answer is useful for because it displays a familar list of digits rather
than an unfamiliar fraction that approximate would return *)

Definition answer (n:positive) (r:CR) : Z :=
 let m := (Pos.iter (Pmult 10) 1%positive n) in
 let (a,b) := (approximate r (1#m :> Qpos))*(Zpos m#1) in
 Z.div a (Zpos b).

(* This file illustrates how to use the computational integration *)
(* Please review RealFast.v for examples on how to compute with CR *)

(* Integrate01 requires that we integrate uniformly continuous functions.
   Therefore we cannot integerate (sin : CR -> CR), we must instead
   integrate the UniformlyContinuousFunction (sin_uc : Q --> CR). *)

Time Eval vm_compute in answer 3 (Integrate sin_uc 3 (1#2)).
(*Time Eval vm_compute in answer 3 (SimpleIntegration.integrate sin_uc 3 (1#2)%Qnn).*)
(* 1 is a bound for the absolute value of sin's fourth derivative *)
(*Time Eval vm_compute in answer 10 (SimpsonIntegration.integrate sin_uc 1 3 (1#2)%Qnn).*)

(* Integrate01 the x^2 function 
Time Eval vm_compute in answer 3 (Integrate01 (uc_compose (CRpower_positive_bounded 2 (1#1)) Cunit)).
Time Eval vm_compute in answer 4 (Integrate01 (uc_compose (CRpower_positive_bounded 2 (1#1)) Cunit)).
*)
(* find the supremum of cos on [0,1] *)
Time Eval vm_compute in answer 3 (ContinuousSup01 cos_uc).

(* find the supremum of id on [0,1] *)
Time Eval vm_compute in answer 3 (ContinuousSup01 Cunit).

(* An example of an elliptic integral that cannot be solved symbolically
\int_0^1  (1-\fract{1}{4}\sin^2\phi)^{-\fract{1}{2}} d\phi *)

Definition sinsquare:= (uc_compose (CRpower_N_bounded 2 (1#1)) sin_uc).
Definition quartersinsquare:=(uc_compose (scale (1#4)) sinsquare).
Definition body:=(uc_compose (translate 1) quartersinsquare).
Definition rootbody:=(uc_compose CRsqrt body).
Time Eval vm_compute in answer 1 (Integrate01 rootbody).
