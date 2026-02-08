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
(* Should we change to a sigT in the future? *)
Definition Class (Phi : Prop -> Prop) : Type := Prop -> Prop.
Example class_example := Class (fun x => x = x).

Definition mk_class (Phi : Prop -> Prop) : Class Phi. Admitted.
Example mk_class_example : class_example := mk_class (fun x => x = x).

(* 
Note that we are utilizing the fact that `f` can be both a function
taking a normal function as param, and a function dedicated to take
a class as a parameter. This is also how it works for descriptions
*)
Definition app_class (Phi : Prop -> Prop) (f : (Class Phi) -> Prop)
  (cls : Class Phi) : Prop. 
Admitted.
Example app_class_example := app_class (fun x => x = x)
  (fun p => p = p) mk_class_example.

(* We might just leave the Psi be Psi...in the future *)
Notation "[ ^ z => B ]" := (mk_class (fun z => B))
  (at level 130, z binder, right associativity).

(* TODO: integrate the two notations so that they are composed together? *)
(* TODO: refer to iota and see if we can make the f more flexible
 f is supposed to be able to use only the class name
 This seems to also be what should be expected for descriptions in
 its most complete sense *)

 (* TODO: let (_class: Class Psi) := class in
  ...... *)
Notation "[ ^ z => B1 @ classname => Bf ]" := 
  (let Psi := (fun z => B1) in
    (app_class Psi (fun (classname : Class Psi) => Bf) (mk_class Psi)))
  (at level 150, z binder, classname binder, right associativity).

Open Scope single_app_equiv.

(* `f` in this definition has been very ambiguous and very annoying. It's
  been used in 3 ways:
  - accepts a parameter of a class
  - accepts a normal function
  - within the `exists` subexp, accepts a predicate 
  Such ambiguity seems to be deliberately designed even in the Principia
  itself, and the untyped part of the rewriting system seems to serve as
  a way to escape all the restrictions and define what is the "least 
  acceptable type"
  Or, it is just a nature manifested from our formalization, and we will
  need to design a "type transformer" for this...
*)
Definition n20_01 (Psi : Prop -> Prop) (f : (Prop -> Prop) -> Prop) :=
  ([^ z => Psi z @ zPsi => f zPsi])
  = (exists Phi : Predicate 1, (Phi x <[- x -]> Psi x) /\ f Phi).

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