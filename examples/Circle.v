(** Plotting graphs in the plane *)
(* This file is based on examples/Plot.v *)
(* I define the image of a path, a [Compact] subset of the plane.*)
(* Finally, plot a hi-res Circle*)

From CoRN Require Import Plot RasterQ Qmetric
  reals.fast.Interval
  metric2.MetricMorphisms
  reals.faster.ARArith
  ARplot
  reals.faster.ARcos
  reals.faster.ARsin
  reals.faster.ARexp
  reals.faster.ARbigD
  reals.faster.ARinterval
  reals.fast.CRtrans
  write_image.WritePPM.

Local Open Scope uc_scope.

Section PlotCirclePath.
Context `{AppRationals AQ}.

Definition CirclePath_faster
  : AQ_as_MetricSpace --> Complete (ProductMS AQ_as_MetricSpace AQ_as_MetricSpace) := 
  (uc_compose (uc_compose Couple (together ARcos_uc ARsin_uc))
              (diag AQ_as_MetricSpace)).

Definition CosPath_faster
  : AQ_as_MetricSpace --> Complete (ProductMS AQ_as_MetricSpace AQ_as_MetricSpace) := 
  (uc_compose (uc_compose Couple (together Cunit ARcos_uc))
              (diag AQ_as_MetricSpace)).

(* 7 is above 2 pi, which finishes a circle. *)
(* Lemma zeroSeven : (0 <= 7)%Q.
Proof. discriminate. Qed. *)

Definition Circle_faster : sparse_raster _ _
  := let (_,r) := ARplot.PlotPath 0 7 (-(1)) 1 (reflexivity _)
                             (-(1)) 1 (reflexivity _) 200 CirclePath_faster
      in r.

Definition Cos_faster : sparse_raster _ _
  := let (_,r) := ARplot.PlotPath 0 7 0 7 (reflexivity _)
                             (-(1)) 1 (reflexivity _) 800 CosPath_faster
      in r.

End PlotCirclePath.

Definition Circle_bigD : sparse_raster _ _
  := @Circle_faster bigD _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ bigD_appRat.

(* 3.7s on Apple M1 - this is mostly the creation of the sparse raster *)
Time Elpi WritePPM "Circle.ppm" ( Circle_bigD ).
(* Now have a look at Circle.ppm *)

Definition Cos_bigD : sparse_raster _ _
  := @Cos_faster bigD _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ bigD_appRat.

(* 3.1s on Apple M1 *)
Time Elpi WritePPM "Cos.ppm" ( Cos_bigD ).
(* Now have a look at Cos.ppm *)

Definition CircleFunction_aux
  : ProductMS Q_as_MetricSpace Q_as_MetricSpace --> ProductMS CR CR
  := together cos_uc sin_uc.

Definition CirclePath : Q_as_MetricSpace --> Complete Q2:= 
  (uc_compose (uc_compose Couple CircleFunction_aux) (diag Q_as_MetricSpace)).
(* The following hangs:
   TODO this does not even compile
Definition CirclePath': UCFunction Q R2:= 
  ucFunction (fun q:Q => Couple (cos_uc q, sin_uc q)). *)


Definition Circle : sparse_raster _ _
  := (let (_,r) := Plot.PlotPath 0 7 (-(1)) 1 (reflexivity _)
                             (-(1)) 1 (reflexivity _) 200 CirclePath
      in r).

(* 16.3 seconds on Apple M1 *)
Time Elpi WritePPM "Circle2.ppm" ( Circle ).
(* Now have a look at Circle2.ppm *)


