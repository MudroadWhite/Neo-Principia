Require Import PM.pm.lib.
Require Import PM.pm.ch1.
Require Import PM.pm.ch2.
Require Import PM.pm.ch3.
Require Import PM.pm.ch4.
Require Import PM.pm.ch5.
Require Import PM.pm.ch10.
Require Import PM.pm.ch11.
Require Import PM.pm.ch12.

(* TODO: since this equality is different from definitional equality, maybe we can define 
  a new symbol for this equality *)

(* 
p.165: `Phi x^` without a `!` will be a function with order unspecified, and this kind of function is
forbidden to be a quantified variable
*)

Definition n13_01 (X Y : Prop) : 
  (X = Y) = (forall Phi : Predicate 1, (Phi X) = (Phi Y)).
Admitted.

Definition n13_02 (X Y : Prop) :
  (~(X = Y)) = ~(X = Y).
Admitted.

Definition n13_03 (X Y Z : Prop) :
  ((X = Y) /\ (Y = Z)) = ((X = Y) /\ (Y = Z)).
Admitted.

Open Scope single_app_impl.

Theorem n13_1 (X Y : Prop) : 
  (X = Y) <-> 
    (forall Phi : Predicate 1, (Phi X) -> (Phi Y)).
Proof.
Admitted.

Theorem n13_101 (X Y : Prop) (Psi : Prop -> Prop) :
  (X = Y) -> (Psi X -> Psi Y).
Proof.
Admitted.

Open Scope single_app_equiv.

Theorem n13_11 (X Y : Prop) :
  (X = Y) <-> 
    (forall Phi : Predicate 1, (Phi X) <-> (Phi Y)).
Proof.
Admitted.

Theorem n13_12 (X Y : Prop) (Psi : Prop -> Prop) :
  (X = Y) -> (Psi X <-> Psi Y).
Proof.
Admitted.

Theorem n13_13 (X Y : Prop) (Psi : Prop -> Prop) :
  ((Psi X) /\ (X = Y)) -> Psi Y.
Proof.
Admitted.

