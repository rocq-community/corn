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

From CoRN Require Import Plot CRtrans.

(* `∗' is used for trival proofs that a some concrete number is less than another *)
Notation star := (@refl_equal _ Lt).
Notation "∗" := star.

Local Open Scope Q_scope.
Local Open Scope uc_scope.
Local Open Scope raster.

(* This file illustrates how to plot funcitons *)
(* PlotQ requires that we plot uniformly continuous functions.
   Therefore we cannot plot (sin : CR -> CR), me must instead
   plot the UniformlyContinuousFunction (sin_uc : Q --> CR). *)
(* Here we plot sin on [-3,3] (= [-3,-3+6]) with range [-1,1] (= [-1,-1+2]) on a 36x12 raster *)
Time Eval vm_compute in PlotQ (- (3)) (- (1)) (exist _ 6 star) (exist _ 2 star) sin_uc 36 12.

(* Here we explore the proof that plots are correct *)
Goal True.
(* Plot_correct is a proof that the plot is correct.*)
(* below we plot exp on [-3, 0] with range [0,1] *)
(* (exp_bound_uc 0) is exp on ]-inf,0] which is one domain where it is uniformly continuous *)
assert (X:=@Plot_correct (-(3)) 0 (exist _ 3 star) (exist _ 1 star)
 (exp_bound_uc 0)
 45 15).
(* No plot is seen.  It is hidden in the uncomputed
  PlotQ (- (3)) 0 ∗ 0 1 ∗ (exp_bound_uc 0) 45 15 *)
(* We use patern matchin to extract the parts of the statement we
   wish to normalize *)
match goal with
 [X:ball ?e ?a (@ucFun _ _ _ (_⇱?b⇲_))|-_] => set (E:=e) in X; set (B:=b) in X
end.
(* E is the error; a bound on the distance between our plot and the actual function *)
set (E' := E: Q).
vm_compute in E'.
(* The error is 90/1800 *)
(* B is the plot *)
Time vm_compute in B.
(* The plot is a 45 by 15 raster. *)
(* The plot and error can be reinserted into the statement if you wish *)
unfold E, B in X.
clear E B.
(* end this example *)
split.
Qed.
