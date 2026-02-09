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

(* 
The class in this chapter has been discussed like pretty bad. It is not being stated
clearly like a structure, and instead, how is it defined is written *in the middle 
of the text*, and is defined with a `^x` that looks so similar to the "function 
abstraction" being used in chapter 9.
Another seemingly ambiguity is what do we mean by `Phi ! x`. In chapter 12-14, `Phi ! x`
is restricting `Phi` to be a predicate, that is, a "typed" function. The `Phi ! x` 
in this chapter, albeit its same appearance, only means "we want to talk about the 
function, not its parameters", in order words, can be untyped.
**Due to such ambiguity in the `!`, whether functions should be defined as predicates,
appeared through all the notation definitions, is highly volatile and is encouraged 
to be examined and corrected.**
*)

(* TODO: define a scope for all this *)

Module Experimental.
  (* ATTEMPT 1 *)
  (* TODO: design a dependent type version of Class to contain the information *)

  (* ATTEMPT 2 - we only demonstrate the idea because it's not very different
    from using inductive types on this purpose *)
  Module ClassRecord.
    Record t := {
      (* The actual function in the class *)
      get_class : Prop -> Prop;
    }.
  End ClassRecord.

  (* ATTEMPT 3 *)
  Inductive ClassInductive :=
    | mk_classind (Phi : Prop -> Prop) 
  .
  Example classinductive_example := mk_classind (fun x => x = x).

  Notation "[ '^ind' z => B ]" := (mk_classind (fun z => B))
    (at level 130, z binder, right associativity).

  Example test_destruct_ind := 
    let '(mk_classind p) := classinductive_example in p.

  (* We can see here `f` is just a normal function taking `Prop -> Prop` 
  as its argument, but such way of our formalization on class will fail
  to utilize the ambiguity of types for f *)
  Definition app_class_ind (f : (Prop -> Prop) -> Prop) (cls : ClassInductive) 
    : Prop.
  Admitted.

  Notation "[ '^ind' cls @ classname => Bf ]" := 
    (let '(mk_classind Phi) := cls in
      (app_class_ind Phi (fun (classname : Prop -> Prop) => Bf)))
    (at level 150, classname binder, right associativity).

End Experimental.

(* Class determined by *function* Phi...is this definition correct? 
Although it is being defined 
*)
(* WARNING: THIS TYPE IS VOLATILE AND SHOULD BE REDEFINED *)
Definition Class (Phi : Prop -> Prop) : Type := Prop -> Prop.
Example class_example := Class (fun x => x = x).

(* NOTE: mk_class should have the same type as app_class???? *)
Definition mk_class {A : Type} (Phi : A -> Prop) : Prop. Admitted.
Example mk_class_example := mk_class (fun (x : Prop) => x = x).

(* We might just leave the Psi be Psi...in the future *)
(* Notation "[ ^ z => B ]" := (fun z => B) *)
Notation "[ ^ z => B ]" := (mk_class (fun z => B))
  (at level 130, z binder, right associativity).
(* Print mk_class_example. *)
Example mk_class_example1 := [ ^ (z : Prop) => z = z].
Example mk_class_example2 := [ ^ (z : Prop -> Prop) => z = z].

(* 
Note that we are utilizing the fact that `f` can be both a function
taking a normal function as param, and a function dedicated to take
a class as a parameter. This is also how it works for descriptions

It seems that whatever the predicate is, its eventual type should be `Prop`
rather than anything like `Prop -> Prop`... maybe there will be a better clue
in the future how to design this type
*)
(* WARNING: VOLATILE DEFINITION *)
Definition app_class (Phi : Prop -> Prop) (f : (Class Phi) -> Prop) : Prop. 
Admitted.
Example app_class_example := app_class (fun x => x = x)
  (fun p => p = p).

(* This kind of representation suffers a lack of compositional property,
with the inductive type demonstrated above as a counter example. By which
I mean, we cannot reuse the definition for just a class, but we have to 
redefine how a class is being applied on something else separately, and
I think this is what exactly the book is telling us *)
Notation "[ ^ z => B1 @ classname => Bf ]" := 
  (let Psi := (fun z => B1) in
    (app_class Psi (fun (classname : Class Psi) => Bf)))
  (at level 130, z binder, classname binder, right associativity).

Open Scope single_app_equiv.

(* So far, `f` as a random function to be applied a class parameter, has 
  been allowed for 3 parameter "types"(not Principia type):
  - a type of a Class parameter
  - a type of a normal function
  - maybe a type of a predicate, appeared in the `exists` subexp
  Such ambiguity seems to be deliberately designed even in the Principia
  itself, and the untyped part of the rewriting system seems to serve as
  a way to escape all the restrictions and define what is the "least 
  acceptable type"
  Or, it is just a nature manifested from our formalization, and we will
  need to design a "type transformer" for this...
  I'm pretty sure Axiom of Reducibility given such practical usage should
  be really and actually a problem of PLT
*)
Definition n20_01 (Psi : Prop -> Prop) (f : (Prop -> Prop) -> Prop) :=
  ([^ z => Psi z @ zPsi => f zPsi])
  = (exists Phi : Predicate 1, (Phi x <[- x -]> Psi x) /\ f Phi).

(* We can gradually see that by following Principia's way to define the 
things, despite the annoying writing style, `in` is really the first 
operator for classes. As further examples, `=` is allowed on classes,
while `/\` seems not to be(?) *)
Definition in_class (X : Prop) (Phi : Prop -> Prop) : Prop.
Admitted.

Notation "[ x '<in_class>' Phi ]" := (in_class x Phi)
  (at level 200, x name, right associativity).

Notation "[ x '<in_class>' ^ classname => B ]" := (in_class x (fun classname => B))
  (at level 200, x name, classname binder, right associativity).

Example in_class_example (x : Prop) := [x <in_class> (fun x => x = x)].
Example in_class_expanded_example (x : Prop) := [x <in_class> ^ c => c = c].

(* We don't know if Phi should be a predicate or a function *)
Definition n20_02 (n : nat) (X : Prop) (Phi : Prop -> Prop) :=
  [X <in_class> Phi] = Phi X.

(* TODO: is this the correct type for alpha? Or should it be some `Class Phi`? *)
Definition Cls : Prop. Admitted.

(* TODO: FIND A BETTER WAY TO DEFINE THIS *)
Definition n20_03 (Phi : Prop -> Prop) :=
  Cls = ([ ^ (alpha : Prop -> Prop) => (exists (Phi : Prop -> Prop), 
    [ ^ z => Phi z @ zPhiz => alpha = zPhiz ])]).

(* NOTE FOR MYSELF: alpha IS A SYMBOL THAT IS SUPPOSED TO BE EXACTLY THE
ArgClass DEFINE ABOVE *)

Definition forall_class : Prop. Admitted.




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