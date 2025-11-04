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

Theorem n13_14 (X Y : Prop) (Psi : Prop -> Prop) :
  (Psi X) /\ (~ Psi Y) -> (~ (X = Y)).
Proof.
Admitted.

Theorem n13_15 (X : Prop) : X = X.
Proof.
Admitted.

Theorem n13_16 (X Y : Prop) : (X = Y) <-> (Y = X).
Proof.
Admitted.

Theorem n13_17 (X Y Z : Prop) :
  ((X = Y) /\ (Y = Z)) -> (X = Z).
Proof.
Admitted.

Theorem n13_18 (X Y Z : Prop) :
  ((X = Y) /\ (~(X = Z))) -> ~(Y = Z).
Proof.
Admitted.

Theorem n13_181 (X Y Z : Prop) :
  ((X = Y) /\ (~(Y = Z))) -> ~(X = Z).
Proof.
Admitted.

Theorem n13_182 (X Y Z : Prop) :
  (X = Y) -> ((Z = X) <-> (Z = Y)).
Proof.
Admitted.

Theorem n13_183 (X Y : Prop) :
  (X = Y) <-> ((X = z) <[- z -]> (z = Y)).
Proof.
Admitted.

Theorem n13_19 (X : Prop) : exists y, y = X.
Proof.
Admitted.

Theorem n13_191 (X : Prop) (Phi : Prop -> Prop) :
  (y = X) -[ y ]> (Phi y = Phi X).
Proof.
Admitted.

Theorem n13_192 (B : Prop) (Psi : Prop -> Prop) :
  exists c, ((x = B) <[- x -]> (x = c)) /\ (Psi c <-> Psi B).
Proof.
Admitted.

Theorem n13_193 (X Y : Prop) (Phi : Prop -> Prop) :
  (Phi X /\ (X = Y)) <-> (Phi Y /\ (X = Y)).
Proof.
Admitted.

Theorem n13_194 (X Y : Prop) (Phi : Prop -> Prop) :
  (Phi X /\ (X = Y)) <-> (Phi X /\ Phi Y /\ (X = Y)).
Proof.
Admitted.

Theorem n13_195 (X : Prop) (Phi : Prop -> Prop) : 
  (exists y, (y = X) /\ Phi y) <-> Phi X.
Proof.
Admitted.

Theorem n13_196 (X : Prop) (Phi : Prop -> Prop) : 
  (~Phi X) <-> (Phi y <[- y -]> (~(y = X))).
Proof.
Admitted.

Close Scope single_app_impl.
Open Scope double_app_impl.

Theorem n13_21 (X Y : Prop) (Phi : Prop -> Prop -> Prop) : 
  (((z = X) /\ (w = Y)) -[ z w ]> ((Phi z w) <-> (Phi X Y))).
Proof.
Admitted.

Theorem n13_22 (X Y : Prop) (Phi : Prop -> Prop -> Prop) : 
  exists z w, (z = X) /\ (w = Y) /\ (Phi z w <-> Phi X Y).
Proof.
Admitted.

Theorem n13_3 (A X : Prop) (Phi : Prop -> Prop) : 
  (Phi A \/ (~Phi A)) -> ((Phi X \/ (~Phi X)) <-> ((X = A) \/ (~(X = A)))).
Proof.
Admitted.

Close Scope double_app_impl.
Close Scope single_app_equiv.
