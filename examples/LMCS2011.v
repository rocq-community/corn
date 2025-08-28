From CoRN Require Import CRtrans Compress ARtrans ARbigD.

Definition eval (n:positive) (r : CR) :=
 let m := Pos.iter (Pmult 10) 1%positive n in let _ := approximate r (1#m :> Qpos) in tt.

Definition deval (n:positive) (r : ARbigD) :=
 let m := Pos.iter (Pmult 10) 1%positive n in let _ := approximate r (1#m :> Qpos) in tt.

Definition P01 : CR := sin (compress (sin (compress (rational_sin 1)))).
Definition dP01 : ARbigD := ARsin (ARsin (AQsin 1)).

Definition P02 : CR := CRsqrt (compress CRpi).
Definition dP02 : ARbigD := ARsqrt (ARcompress ARpi).

Definition P03 : CR := sin (compress (rational_exp 1)).
Definition dP03 : ARbigD := ARsin (AQexp 1).

Definition P04 : CR := exp (compress (CRpi * rational_sqrt ('163%Z))).
Definition dP04 : ARbigD := ARexp (ARcompress (ARpi * AQsqrt ('163%Z))).

Definition P05 : CR := exp (compress (exp (compress (rational_exp 1)))).
Definition dP05 : ARbigD := ARexp (ARexp (AQexp 1)).

Definition P07 : CR := rational_exp ('1000%Z).
Definition dP07 : ARbigD := AQexp ('1000%Z).

Definition P08 : CR := cos (cast Q CR (cast Z Q (10^50)%Z)).
Definition dP08 : ARbigD := AQcos ('(10^50)%Z).

From Stdlib Require Import String.

Eval compute in "old"%string.
Time Eval vm_compute in (eval 25 P01).
Time Eval vm_compute in (eval 25 P02).
Time Eval vm_compute in (eval 25 P03).
Time Eval vm_compute in (eval 10 P04).
Time Eval vm_compute in (eval 10 P05).
Time Eval vm_compute in (eval 10 P07). 
Time Eval vm_compute in (eval 25 P08).

Eval compute in "new"%string.
Time Eval vm_compute in (deval 25 dP01).
Time Eval vm_compute in (deval 25 dP02).
Time Eval vm_compute in (deval 25 dP03).
Time Eval vm_compute in (deval 10 dP04).
Time Eval vm_compute in (deval 10 dP05).
Time Eval vm_compute in (deval 10 dP07).
Time Eval vm_compute in (deval 25 dP08).

Eval compute in "new bigger"%string.
Time Eval vm_compute in (deval 500 dP01).
Time Eval vm_compute in (deval 500 dP02).
Time Eval vm_compute in (deval 500 dP03).
Time Eval vm_compute in (deval 500 dP04).
Time Eval vm_compute in (deval 500 dP05).
Time Eval vm_compute in (deval 2000 dP07).
Time Eval vm_compute in (deval 2000 dP08).
