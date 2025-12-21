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

(* TODO: polish the note: the definition of description in text is left with ambiguity:
since the original definition is defined in a pure substitutional way without 
any considerations for scopes, there has an attempt being made to set up a 
naive considerations on how the scope should be resolved 

How does the notation work
1. original idea: [scope] ( *the expression containing the iota operator* )
2. since scope is usually the minimal expression containing the iota, we often omit the [scope] part
3. finally we add corner cases: definitions for scope specification for multiple iotas, and case 
  when `a != x` is necessary to be concerned

We want to ignore the scope notation since it's a patch to the dot notation, while we can 
resolve this easily with brackets
*)

(* `_f` suffix means it's for typical (untyped) functions *)
Definition iota_f (Phi Psi : Prop -> Prop) :=
  (exists b, (Phi x <[- x -]> (x = b)) /\ Psi b).

(* `_p` suffix means it's for predicates. This definition is for case when we need to consider
  something like `a != x`. This seems unsatisfying because we might be unable to determine which
  definition to use *)
Definition iota_p (E : Prop) (Phi : Prop -> Prop) := exists b, (Phi x <[- x -]> (x = b)).