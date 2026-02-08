Require Import PM.pm.lib.
Require Import PM.pm.ch1.
Require Import PM.pm.ch2.
Require Import PM.pm.ch3.
Require Import PM.pm.ch4.
Require Import PM.pm.ch5.
Require Import PM.pm.ch10.
Require Import PM.pm.ch11.
Require Import PM.pm.ch12.
Require Import PM.pm.ch13.
Require Import PM.pm.ch14.

(* The ^x in the very beginning of this chapter is intended to label "the class of 
arguments" for a function Phi. We are making this opaque to see where it goes, but
just in case, there is still a very easy interpretation for this... *)

(* Somewhere in Principia says arg class might be something just like iota, an 
incomplete definition. We should also change the style into that... *)

(* TODO: define a scope for all this *)

(* Class determined by *function* Phi...is this definition correct? *)
Definition Class (Phi : Prop -> Prop) : Type := Prop -> Prop.

Definition mk_class (Phi : Prop -> Prop) : Class Phi. Admitted.

(* TODO: design the parameter type for `f` ecarefully *)
Definition app_class (Phi : Prop -> Prop) (f : (Prop -> Prop) -> Prop)
  (cls : Class Phi) : Prop. 
Admitted.

Notation "[ ^ z => B ]" := (mk_class (fun z => B))
  (at level 130, z binder, right associativity).

(* TODO: refer to iota and see if we can make the f more flexible *)
(* TODO: f is supposed to be able to use both the class name and the z? *)
Notation "[ ^ z => B1 @ z_clsname => Bf ]" := 
  ( let Psi := (fun z => B1) in
    (app_class Psi ((fun z z2 => B1 z) Psi) (mk_class Psi)) )
  (at level 110, z1 binder, z2 binder right associativity).

Example test_example := [ ^z => z = z].
Print test_example.

Open Scope single_app_equiv.

Definition n20_01 (n : nat) (Psi : Prop -> Prop) (f : (Prop -> Prop) -> Prop) :=
  ([ f |^ z => Psi z])
  = 
  (exists Phi : Predicate 1, (Phi x <[- x -]> Psi x)
    /\ f Phi).

Definition in_class (X : Prop) (n : nat) (Phi : Prop -> Prop) : Prop.
Admitted.

Notation "[ x 'in_class' Phi % n ]" := 
    (in_class x n Phi)
    (at level 200, right associativity).

(* TODO: rewrite below... *)

(* TODO: format... *)
Example debug_iota_notation_example := [ iota (fun x => x) | iotaφ => iotaφ = iotaφ ].



Definition Cls (alpha : Prop) : Prop. Admitted.

Definition in_pred (n : nat) (X : Prop) (Phi : Predicate n) : Prop. Admitted.

(* NOTE FOR MYSELF: alpha IS A SYMBOL THAT IS SUPPOSED TO BE EXACTLY THE
ArgClass DEFINE ABOVE *)

Definition forall_class : Prop. Admitted.



Definition n20_02 (n : nat) (X : Prop) (Phi : Predicate n) :=
  in_pred n X Phi = Phi X.
  (* TODO: is this correct?? *)

(* cf. p.188: The definition of `Cls` is also a "partial definition" and
should be considered in specific context. Therefore we want to also apply
our "dual definition" method to fix everything it "failed" to concern 
Also in *20_03: "we have merely defined certain *uses* of such expressions..."
we can see explicitly that for all definitions in Principia it is allowed
to add more "uses" to the expressioins whenever we want 
*)
Definition n20_03 (alpha : Prop) (Z : Prop) :
  (Cls alpha) = ArgClass (fun alpha =>
    exists Phi : Predicate 1, alpha = ArgClass Phi).
Admitted.