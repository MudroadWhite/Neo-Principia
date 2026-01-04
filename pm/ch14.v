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

(* TODO: make the definitions into a notation in the future *)
(* Declare Scope single_description. *)

Open Scope single_app_equiv.

(* Definition Iota (s : string) (x : Prop) : Type := Prop. *)
Definition Iota (s : string) (x : Prop) : Prop := x.

Example iota_function (i1 i2 : Prop) : Prop -> Prop :=
  fun x =>
    (Iota "Phi" i1) = (Iota "Psi" i2).

(* `_f` suffix means it's for typical (untyped) functions *)
Definition iota_f 
  (* s is just a string for identification *)
  (s : string)
  (Phi : Prop -> Prop) 
  (* This function below is supposed to be a function of the iota term. Since the 
  variable is provided within the proposition, we only type it just as a normal 
  function. Unavailability of the existential `b` var from an external view is the 
  major reason why this notation is hard to define.
  While the definition doesn't express anything, this function is allowed to use 
  `Iota s1` in its body *)
  (Psi : Prop -> Prop) : Prop
  := (exists b, (Phi x <[- x -]> (x = b)) /\ Psi b).

Example scoped_iota_expression (Phi : Prop -> Prop) :=
  iota_f "Phi" Phi 
    (* A function will be written like this... *)
    (fun b => (Iota "Phi" b) = (Iota "Phi" b)).

(* cf. p174, example after *14.03. Interpretation for a function containing 
  multiple descriptions *)
Definition iota_f2 
  (s1 s2 : string)
  (Phi Psi : Prop -> Prop)
  (f : Prop -> Prop -> Prop) :=
  iota_f s1 Phi 
    (fun b => iota_f s2 Psi 
      (fun c => f (Iota s1 b) (Iota s2 c))).

(* cf. p174, explanation after *14.04. The iota variant where inner function has 
  larger scope than outer function. This variant will be proven later unecessary. *)
Definition iota_f2_1 
  (s2 s1 : string)
  (Psi Phi : Prop -> Prop)
  (f : Prop -> Prop -> Prop) :=
  iota_f2 s2 s1 Psi Phi.
  (* exists b, (Phi x <[- x -]> (x = b)) /\ 
    ((exists c, Psi x <[- x -]> (x = c) /\ f b c)). *)

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

Definition n14_01 (s1 : string) (Phi Psi : Prop -> Prop) : 
  (iota_f s1 Phi Psi) = exists b, (Phi x <[- x -]> (x = b)) /\ Psi b. 
Admitted.

(* TODO: check if iota_p and *14.02 is correctly defined *)
Definition n14_02 (E : Predicate 1) (Phi : Prop -> Prop) :
  (iota_p E Phi) = exists b, (Phi x <[- x -]> (x = b)). 
Admitted.

Definition n14_03 (s1 s2 : string) (Phi Psi : Prop -> Prop) (f : Prop -> Prop -> Prop) :
  (iota_f2 s1 s2 Phi Psi f) = exists b, (Phi x <[- x -]> (x = b)) 
    /\ ((exists c, Psi x <[- x -]> (x = c) /\ f b c)).
Admitted.

Definition n14_04 (s2 s1 : string) (Psi Phi : Prop -> Prop) (f : Prop -> Prop -> Prop) : 
  (iota_f2_1 s2 s1 Psi Phi f) = exists b, (Phi x <[- x -]> (x = b)) 
    /\ ((exists c, Psi x <[- x -]> (x = c) /\ f b c)).
Admitted.

Theorem n14_1 (Phi Psi : Prop -> Prop) : (iota_f Phi Psi) <-> 
  exists b, (Phi x <[- x -]> (x = b)) /\ Psi b.
Proof.
  pose proof (n4_2 (iota_f Phi Psi)) as n4_2.
  now rewrite -> n14_01 in n4_2 at 2.
Qed.

(* The equivalent with n14_1, with scope notation in its original 
  representation omitted  *)
Theorem n14_101 (Phi Psi : Prop -> Prop) : (iota_f Phi Psi) <-> 
  exists b, (Phi x <[- x -]> (x = b)) /\ Psi b.
Proof.
  exact (n14_1 Phi Psi).
Qed.

Theorem n14_11 (E : Predicate 1) (Phi : Prop -> Prop) : 
  (iota_p E Phi) <-> (exists b, Phi x <[- x -]> (x = b)).
Proof.
  pose proof (n4_2 (iota_p E Phi)) as n4_2.
  now rewrite -> n14_02 in n4_2 at 2.
Qed.

Theorem n14_111 (Phi Psi : Prop -> Prop) (f : Prop -> Prop -> Prop) :
  (iota_f2_1 Psi Phi f) <-> (exists b c, 
    (Phi x <[- x -]> (x = b)) /\ (Psi x <[- x -]> (x = c)) /\  (f b c)).
Proof.
  assert (S1 : iota_f2_1 Psi Phi f ↔ iota_f2 Phi Psi f).
  {
    pose proof (n4_2 (exists b, (Phi x <[- x -]> (x = b)) 
      /\ ((exists c, Psi x <[- x -]> (x = c) /\ f b c)))) as n4_2.
    rewrite <- n14_03 in n4_2 at 2.
    now rewrite <- n14_04 in n4_2.
  }
  (* TODO: design the iota_f & iota_f2 correctly so that we can transform 
    from f2 to f smoothly
    Warning: the `b` of `exists b` in the descriptions can also be expanded 
    into a description
  *)
  assert (S2 : iota_f2_1 Psi Phi f <-> 
    (iota_f Psi (fun y =>
      exists b, Phi x <[- x -]> (x = b) /\ f b y))).
  {
    pose proof n14_1 as n14_1.
    unfold iota_f2 in S1.
    rewrite <- n14_1 in S1.
  }
  pose proof n14_1 as n14_1.
  pose proof n11_55 as n11_55.
Admitted.


Close Scope single_app_equiv.