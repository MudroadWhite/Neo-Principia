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

We won't treat the scope operator seriously since we can resolve this easily with brackets in rocq
*)

(* `_f` suffix means it's for typical (untyped) functions *)
Definition iota_f (Phi Psi : Prop -> Prop) :=
  (exists b, (Phi x <[- x -]> (x = b)) /\ Psi b).

(* `_p` suffix means it's for predicates. This definition is for case when we need to consider
  something like `a != x`. This seems unsatisfying because we might be unable to determine which
  definition to use *)
Definition iota_p (E : Prop) (Phi : Prop -> Prop) := exists b, (Phi x <[- x -]> (x = b)).

Definition scope_iota_f. Admitted.