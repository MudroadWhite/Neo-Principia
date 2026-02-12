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
The class in this chapter has been discussed like pretty obscure. It is not being stated
clearly like a structure, and instead, how is it defined is written *in the middle of 
the text*, and is defined with a `^x` that looks so similar to the "function abstraction" 
being used in chapter 9.

Another seemingly ambiguity is what do we mean by `Phi ! x`. In chapter 12-14, `Phi ! x`
is restricting `Phi` to be a predicate, that is, a "typed" function. The `Phi ! x` 
in this chapter, albeit its same appearance, only means "we want to talk about the 
function, not its parameters", in order words, can be untyped.

**Due to such ambiguity in the `!`, whether functions should be defined as predicates,
appeared through all the notation definitions, is highly volatile and is encouraged 
to be examined and corrected.**

Even worse, the notation for class has becoming more sensitive to types. Which means,
what should be the type for an argument? What should be the type for a predicate(designed
by us to contain the necessary information for a symbol)? What will happen if a class
uses another class?
*)

(* TODO: 
- check every notations are under the scope and organize the notations 
- For implicit `Phi`s, rename them with `IPhi` and same for any other occurences
*)

Declare Scope class_notation.

Module Experimental.
  (* ATTEMPT 1 *)
  (* TODO: design a dependent type version of Class to contain the information *)

  (* ATTEMPT 2 - we only demonstrate the idea because it's not very different
    from using inductive types on this purpose *)
  Module ClassRecord.
    Record t := {
      (* The actual function in the class *)
      class_get : Prop -> Prop;
    }.
  End ClassRecord.

  (* ATTEMPT 3 *)
  Inductive ClassInductive :=
    | classind_mk (Phi : Prop -> Prop) 
  .
  Example classinductive_example := classind_mk (fun x => x = x).

  Notation "[ '^ind' z => B ]" := (classind_mk (fun z => B))
    (at level 130, z binder, right associativity).

  Example test_destruct_ind := 
    let '(classind_mk p) := classinductive_example in p.

  (* We can see here `f` is just a normal function taking `Prop -> Prop` 
  as its argument, but such way of our formalization on class will fail
  to utilize the ambiguity of types for f *)
  Definition classind_app (f : (Prop -> Prop) -> Prop) (cls : ClassInductive) 
    : Prop.
  Admitted.

  Notation "[ '^ind' cls @ classname => Bf ]" := 
    (let '(classind_mk Phi) := cls in
      (classind_app Phi (fun (classname : Prop -> Prop) => Bf)))
    (at level 150, classname binder, right associativity).

End Experimental.

(* Class determined by *function* Phi...is this definition correct? *)
Definition Class {A : Type} (Phi : A -> Prop) : Type := Prop -> Prop.
Example class_example := Class (fun (x : Prop) => x = x).
(* An example to show that this definition doesn't strictly distinguish
between different functions *)
Example class_eq (Phi Psi : Prop -> Prop) : Class Phi = Class Psi.
Proof. reflexivity. Qed.

Definition class_mk {A : Type} (Phi : A -> Prop) : Prop. Admitted.
Example class_mk_example := class_mk (fun (x : Prop) => x = x).

Open Scope class_notation.

(* Notation "[ ^ z => B ]" := (fun z => B) *)
Notation "[ ^ z => B ]" := (class_mk (fun z => B))
  (at level 130, z binder, right associativity): class_notation.
Example class_mk_example1 := [^ (z : Prop) => z = z].
Example class_mk_example2 := [^ (z : Prop -> Prop) => z = z].
Example class_mk_example3 := [^ (z : (Prop -> Prop) -> (Prop -> Prop)) 
  => z = z].
Example class_mk_example4 := [^ (z : Prop -> Prop) => 
  [^ (x : ((Prop -> Prop) -> (Prop -> Prop))) => x z = x z]].

(* 
Note that we are utilizing the fact that `f` can be both a function
taking a normal function as param, and a function dedicated to take
a class as a parameter. This is also how it works for descriptions

It seems that whatever the predicate is, its eventual type should be `Prop`
rather than anything like `Prop -> Prop`... maybe there will be a better clue
in the future how to design this type
*)
Definition class_app {A : Type} (Phi : A -> Prop) (f : (Class Phi) -> Prop) : Prop. 
Admitted.
Example class_app_example := class_app (fun (x : Prop) => x = x)
  (fun p => p = p).

(* This kind of representation suffers a lack of compositional property,
with the inductive type demonstrated above as a counter example. By which
I mean, we cannot reuse the definition for just a class, but we have to 
redefine how a class is being applied on something else separately, and
I think this is what exactly the book is telling us *)
Notation "[ ^ z => B1 @ classname => Bf ]" := 
  (let class_func := (fun z => B1) in
    (class_app class_func (fun (classname : Class class_func) => Bf)))
  (at level 130, z binder, classname binder, right associativity).
Example class_app_example1 : Prop := [^ (z : Prop) => z = z @ cz => cz = cz].
Example class_app_example2 : Prop := [^ (z : Prop -> Prop) => z = z @ cz => cz = cz].
Example class_app_example3 : Prop := [^ (z : (Prop -> Prop) -> Prop) => 
  z = z @ cz => cz = cz].
Example class_app_example4 := [^ (z1 : Prop) => z1 = z1 @ cz1 =>
[^ (z2 : Prop) => z2 = z2 @ cz2 => cz1 = cz1 ]].
Example class_app_example5 := [^ (z1 : Prop) => z1 = z1 @ cz1 =>
  [^ (z2 : Prop) => z2 = z2 @ cz2 => cz1 = cz2 ]].

Open Scope single_app_equiv.

(* NOTE: return type of `class_app` should be not just a Prop, as it allows
malign usage on other theorems. What should be the return type of `class_app`? *)

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
(* NOTE: only use `A` if necessary *)
Definition class_in (X : Prop) (Phi : Prop -> Prop) : Prop.
Admitted.

(* Note: this is just the special notation said to be used for *20.02 
  solely *)
Notation "[ x '<class_in>' Phi ]" := (class_in x Phi)
  (at level 200, x name, right associativity).

Notation "[ x '<class_in>' ^ classname => B ]" := (class_in x (fun classname => B))
  (at level 200, x name, classname binder, right associativity).

Example class_in_example (x : Prop) := [x <class_in> (fun x => x = x)].
Example class_in_expanded_example (x : Prop) := [x <class_in> ^ c => c = c].

(* We don't know if Phi should be a predicate or a function *)
Definition n20_02 (n : nat) (X : Prop) (Phi : Prop -> Prop) :=
  [X <class_in> Phi] = Phi X.

Definition Cls : Prop. Admitted.

(* cf. p.188: The definition of `Cls` is also a "partial definition" and
should be considered in specific context. It turns out that partial 
definitions can be brilliantly modeled with the notation system in Rocq
Also: "we have merely defined certain *uses* of such expressions..."
we can see explicitly that for all definitions in Principia it is allowed
to add more "uses" to the expressioins whenever we want 
*)
(* NOTE: we restrict the `Phi` to `Prop -> Prop` at the moment. `A` polymorphism
should be used with care in the future... *)
Definition n20_03 (Phi : Prop -> Prop) :=
  Cls = ([^ (alpha : Prop -> Prop) => (exists (Phi : Prop -> Prop), 
    [^ z => Phi z @ zPhiz => alpha = zPhiz ])]).

(* We won't define notation for *20.04 because I think it is unnecessary. *)
Definition n20_04 {A : Type} {Phi : A -> Prop} (X Y : Prop) (alpha : Class Phi) :
  [X <class_in> alpha] /\ [Y <class_in> alpha] = [X <class_in> alpha] /\ [Y <class_in> alpha].
Admitted.

Definition n20_05 {A : Type} {Phi : A -> Prop} (X Y Z : Prop) (alpha : Class Phi) :
  ([X <class_in> alpha] /\ [Y <class_in> alpha]) /\ [Z <class_in> alpha] 
  = ([X <class_in> alpha] /\ [Y <class_in> alpha]) /\ [Z <class_in> alpha].
Admitted.

Definition n20_06 {A : Type} {Phi : A -> Prop} (X : Prop) (alpha : Class Phi) :
  (~ [X <class_in> alpha]) = (~ [X <class_in> alpha]).
Admitted.

(* Fortunately, we don't have to define extra definitions separately for existing
symbols applying on classes. Turns out that our notation essentially expressed such 
things... *)
Definition n20_07 {A : Type} {Psi : A -> Prop} (X : Prop) (f : (Prop -> Prop) -> Prop) :
  forall (alpha : Class Psi), [^ z => alpha z @ calpha => f calpha]
  = forall Phi : Predicate 1, [^ z => Phi z @ cPhi => f Phi].
Admitted.

Definition n20_071 {A : Type} {Psi : A -> Prop} (X : Prop) (f : (Prop -> Prop) -> Prop) :
  exists (alpha : Class Psi), [^ z => alpha z @ calpha => f calpha]
  = exists Phi : Predicate 1, [^ z => Phi z @ cPhi => f Phi].
Admitted.

(* EXPERIMENTAL: below is a copy of definitions from ch14 modified so that it supports 
  polymorphic type. It if works in the future, we will have to mitigrate these defs and 
  rewrite ch14 with the polymorphic version 
  Commented defs are to be uncommented when needed
*)
Declare Scope debug_iota_description_poly.

Definition DescriptionArgPoly {A : Type} (φ : A -> Prop) : Type := Prop.
Example descriptionarg_example := (fun iotaφ : (DescriptionArg (fun x => x)) =>
  iotaφ = iotaφ).

Definition description_poly {A : Type} (φ : A -> Prop) (expr : (DescriptionArgPoly φ) -> Prop) 
  : Prop. 
Admitted.

(* Definition description_exists_poly {A : Type} (φ : A -> Prop) : Prop. Admitted. *)

(* Definition description2_poly {A B : Type} (φ : A -> Prop) (ψ : B -> Prop)
  (expr : (DescriptionArgPoly φ) -> (DescriptionArgPoly ψ) -> Prop) : Prop. 
Admitted. *)

(* Definition description2_rev_poly {A B : Type} (φ : A -> Prop) (ψ : B -> Prop)
  (expr : (DescriptionArgPoly ψ) -> (DescriptionArgPoly φ) -> Prop) : Prop. 
Admitted. *)

Open Scope debug_iota_description_poly.

Notation "[ 'iotapoly' φ | x => B ]" := (description_poly φ (fun (x : DescriptionArgPoly φ) => B))
  (at level 200, x binder, right associativity) : debug_iota_description_poly.
Example debug_iota_poly_example := [ iotapoly (fun x => x) | iotaφ => iotaφ = iotaφ ].

(* Notation "[ 'iotaE' P ]" := (description_exists (P : Prop -> Prop))
  (at level 100, P constr at level 200, right associativity) : debug_iota_description. *)
(* Example debug_iota_exists_example := [ iotaE (fun x => x) ]. *)

(* Notation "[ 'iota2' φ , ψ | x y => B ]" := 
  (description2 φ ψ (fun (x : DescriptionArg φ) (y : DescriptionArg ψ) => B))
  (at level 200, x binder, y binder, right associativity) : debug_iota_description.
Example debug_iota2_example := 
  [ iota2 (fun x => x) , (fun x => x) | x y => (x = y) ]. *)

(* Notation "[ 'iota2rev' φ , ψ | y x => B ]" := 
  (description2 φ ψ (fun (y : DescriptionArg ψ) (x : DescriptionArg φ) => B))
  (at level 200, x binder, y binder, right associativity) : debug_iota_description. *)

Close Scope debug_iota_description_poly.
  
Open Scope debug_iota_description_poly.
Definition n20_072 {A : Type} {Chi : A -> Prop} (X : Prop) (Phi : (Class Chi) -> Prop) 
  (f : (Prop -> Prop) -> Prop) :
  [ iotapoly Phi | iotaPhi => f iotaPhi ]
  = exists Gamma, forall alpha : Class Psi, Phi 


Close Scope debug_iota_description_poly.

Close Scope single_app_equiv.
Close Scope single_app_impl.
Close Scope double_app_equiv.
Close Scope double_app_impl.
Close Scope debug_iota_description_poly.