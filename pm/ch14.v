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

(* TODO: polish the note: the definition of description in text is left with ambiguity with regard to 
the dot notation so we add a scope operator to patch the notation

scope operator should be considered at the same level as dot notation, but it has been actually written 
down into definition

How does the description work
1. original idea: [scope] ( *the expression containing the iota operator* )
2. since scope is usually the minimal expression containing the iota, we often omit the [scope] part
3. finally we add corner cases: definitions for scope specification for multiple iotas, and case 
  when `a != x` is necessary to be concerned

My plan: in the future we might want to utilize currying to define some combinators and see if can be used
as an alternative.....
*)

(* `_f` suffix means it's for typical (untyped) functions *)
Definition iota_f (Phi Psi : Prop -> Prop) :=
  (exists b, (Phi x <[- x -]> (x = b)) /\ Psi b).

(* `_p` suffix means it's for predicates. 
  This definition could have several meanings(?to be checked):
  1. We're fixing the `x` and letting the function `E` varying, just as in ch12 & 13
  2. We need to consider something like `a != x`, as being explained in p.173
  Commentary. We can see that one issue of definitions in PM is that "what is the actual variable" is not that
  clear which could be quite an issue. To generalize the issue: When mathematicans define something, they not
  only have to check if the system they define is working correctly, they also have to check if their definition
  has made a clear distinction between the object and the meta system. For example when we define a cat and dog
  system we don't want to involve with an extra comma(as used in the text) for the cat
  TODO: check how will the `E` be used
*)
Definition iota_p (E : Predicate 1) (Phi : Prop -> Prop) := exists b, (Phi x <[- x -]> (x = b)).

Definition scope_iota (index : nat) 