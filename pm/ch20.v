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

Open Scope single_app_equiv.

(* Notation support for argument class *)
Definition ArgClass 
  (x : Prop) 
  (Phi : Prop -> Prop) := Phi x.

Definition app_arg_class 
  (n : nat) 
  (Phi : Prop -> Prop) 
  (* We will expect that the body of `f` is also allowed to have expression
    with `ArgClass` *)
  (f : Predicate n -> Prop) 
  : Prop. Admitted.

Definition Cls (a : Prop) : Prop. Admitted.

Definition in_pred (n : nat) (X : Prop) (Phi : Predicate n) : Prop. Admitted.

(* NOTE FOR MYSELF: alpha IS A SYMBOL THAT IS SUPPOSED TO BE EXACTLY THE
ArgClass DEFINE ABOVE *)

Definition forall_class : Prop. Admitted.

Definition n20_01 (n : nat) (Psi : Prop -> Prop) (f : Predicate n -> Prop) :=
  app_arg_class n Psi f = (exists Phi : Predicate 1, (Phi x <[- x -]> Psi x)
    /\ f Phi).

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
  (Cls alpha) = ArgClass alpha (fun alpha =>
    exists Phi : Predicate 1, alpha = ArgClass Z Phi).
Admitted.