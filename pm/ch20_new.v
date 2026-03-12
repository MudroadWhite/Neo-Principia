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

(* NOTE: to be added to `audit`:
- f has the ambiguity to take in different "kind"s of things, because these kinds are defined 
  to be the same thing; doubt if this is a bug rather than a feature; TODO: reexamine if this 
  statement is true
*)

(* NOTE: general rules for designing custom notation
1. make it clear what the symbol wants to replace with
2. set its type same as the replacant's type
3. 


*)

(* TODO:
- When starting eliminating the TODOs, make a clear distinction between untyped functions 
  represented as `A -> Prop` and Predicative functions
- When starting eliminating the TODOs, for implicit `Phi`s, rename them with `IPhi` and same 
  for any other occurences(??); address this naming convention in the documentation
- Unify the convention for namings of class vaiables, by noticing things after `@`s
*)

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
Declare Scope debug_class.
Declare Scope class.

(* 
Failed attempts:
- Defining `Class` as (A, Phi)
- Defining `Class` as inductive type
- Defining `Class` only using functions
*)
Module Class.
  Record t {A : Type} : Type := {
    (* For storing the A type *)
    get_A : Type;
    get_func : A -> Prop;
  }.
  Definition mk {A : Type} (Phi : A -> Prop) := Build_t A A Phi.
End Class.

Example class_example_1 := Class.mk (fun (x : Prop) => x = x).
Example class_mk_destruct_example := 
  class_example_1.(Class.get_func).

(* This should be the correct way to define application on class *)
Definition class_app {A B : Type} (f : (A -> Prop) -> B) (cls : @Class.t A) : B. Admitted.

(* NOTE: according to *20.02, `in` needs to be interpreted as a function working directly
on the underlying function `Phi` *)
Definition class_in {A : Type} (X : A) (Phi : A -> Prop) : Prop. Admitted.

Definition Cls : Prop. Admitted.

Open Scope debug_class.

Notation "'^' z => B" := (Class.mk (fun z => B))
  (at level 130, z binder, right associativity) : debug_class.
Example class_example_2 := ^ (z : Prop) => z = z.

Notation "[ cls @ classname => B ]" := (
    let A := cls.(Class.get_A) in
    class_app (fun (classname : A -> Prop) => B) cls)
  (at level 150, classname binder, right associativity) : debug_class.
Example class_app_example_1 := [class_example_1 @ x => x = x].
Example class_app_example_2 := [^(z : Prop) => z = z @ cz => cz = cz].
Example class_app_example_3 := [class_example_1 @ c1 => [class_example_1 @ c2 => c1 = c2]].

Notation "[ x '<class_in>' Phi ]" := (class_in x Phi)
  (at level 200, right associativity) : debug_class.
Example class_in_example (x : Prop) := [x <class_in> (fun z => z = z)].

Notation "[ x '<class_in>' ^ classname => B ]" := (class_in x (fun classname => B))
  (at level 200, x name, classname binder, right associativity) : debug_class.
Example class_in_expanded_example (x : Prop) := [x <class_in> ^ c => c = c].

(* EXPERIMENTAL: below is a copy of definitions from ch14 modified so that it supports 
  polymorphic type. It if works in the future, we will have to mitigrate these defs and 
  rewrite ch14 with the polymorphic version 
  Commented defs are to be uncommented when needed
*)
Declare Scope debug_iota_description_poly.

Definition DescriptionArgPoly {A : Type} (φ : A -> Prop) : Type := A.
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

Open Scope formal_equiv.

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

(* We don't know if Phi should be a predicate or a function *)
Definition n20_02 (n : nat) (X : Prop) (Phi : Prop -> Prop) :=
  [X <class_in> Phi] = Phi X.

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

Open Scope debug_iota_description_poly.

(* The Phi here might need further investigation in the future *)
Definition n20_072 {A : Type} {Psi : A -> Prop} (X : Prop) 
  (Phi : (Prop -> Prop) -> Prop) (f : (Prop -> Prop) -> Prop) :
  [ iotapoly Phi | iotaPhi => f iotaPhi ]
    = (exists gamma : Class Psi, (forall alpha : Class Psi, 
      Phi alpha <-> (alpha = gamma)) /\ ([^ z => gamma z @ cgamma => f cgamma])).
Admitted.

Close Scope debug_iota_description_poly.

(* Should we define notations for f applying on class? *)
(* If we use the inductive type defs, here will be even better to express *)
Definition n20_08 {A : Type} (Chi : A -> Prop) (alpha : Class Chi) (f : (Prop -> Prop) -> Prop)
  (Psi : Class Chi -> Prop) : 
  [^ (alpha : Class Chi) => Psi alpha @ calpha => f calpha]
  (* It will be harder to see the nature of Phi being a predicate in this definition,
  as the type of class and predicate interferes with each other, and we are not sure
  if class can be considered as a predicate *)
  = (exists (Phi : Class Chi -> Prop), (forall alpha : Class Chi,Psi alpha <-> Phi alpha) 
  (* I guess the alpha here is also different from the alpha in `forall` *)
    /\ ([^ (alpha : Class Chi) => Phi alpha @ calpha => f calpha])).
Admitted.

Definition n20_081 {A : Type} (Chi : A -> Prop) (alpha : Class Chi) (f : (Prop -> Prop) -> Prop)
  (Psi : Class Chi -> Prop) :
  [alpha <class_in> Psi] = Psi alpha.
Admitted.

(* **************** *)

(* As always, whether we should use `Predicate 1` or `Predicate n` here is still pretty much 
  unspecified *)
Theorem n20_1 (Psi : Prop -> Prop) (f : (Prop -> Prop) -> Prop) :
  ([^ (z : Prop) => Psi z @ zPsi => f zPsi]) = exists Phi : Predicate 1, 
    (Phi x <[- x -]> Psi x) /\ f Phi.
Proof.
Admitted.

Theorem n20_11 (Psi Chi : Prop -> Prop) (f : (Prop -> Prop) -> Prop) :
  (Psi x <[- x -]> Chi x) -> (([^z => Psi z @ cz => f cz]) 
    <-> ([^z => Chi z @ cz => f cz])).
Proof.
Admitted.

Theorem n20_111 (f g : (Prop -> Prop) -> Prop) : 
  (forall Phi : Predicate 1, f Phi <-> g Phi)
  -> (forall Phi : Predicate 1, 
    (([^z => Phi z @ cz => f cz]) <-> ([^z => Phi z @ cz => g cz]))).
Proof.
Admitted.

(* TODO: `g` here cannot be `Predicate 1` and have to be `(Prop -> Prop) -> Prop`.
  Investigate this in the future and design a better `Predicate` type. The original 
  text is also indicate this clearly *)
Theorem n20_112 (f : (Prop -> Prop) -> Prop) : exists g : (Prop -> Prop) -> Prop, 
  forall Phi : Predicate 1, ([^z => Phi z @ cz => f cz]) <-> ([^z => Phi z @ cz => g cz]).
Proof.
Admitted.

(* TODO: CHECK CH12 AXIOM OF REDUCIBILITY TO ENSURE THE CORRECT FORMALIZATION FOR THIS
  THEOREM *)
Theorem n20_12 (Psi : Prop -> Prop) (f : (Prop -> Prop) -> Prop): 
  exists Phi : Predicate 1, (Phi x <[- x -]> Psi x) /\
    (([^z => Psi z @ cz => f cz]) <-> ([^z => Phi z @ cz => f cz])).
Proof.
Admitted.

(* NOTE: we can see that with our notation all function body has to be put within the 
innermost `class_app`, leaving nothing at the outmost part... I wonder if it will have some
troubling thing rise from this 
TODO: revisit other ways to write this expression and see if we can have a more natural 
composition
*)
Theorem n20_13 (Psi Chi : Prop -> Prop) : (Psi x <[- x -]> Chi x)
  -> ([^z1 => Psi z1 @ cz1 => ([^z2 => Chi z2 @ cz2 => cz1 = cz2])]).
Proof.
Admitted.

Theorem n20_14 (Psi Chi : Prop -> Prop) :
  ([^z1 => Psi z1 @ cz1 => ([^z2 => Chi z2 @ cz2 => cz1 = cz2])])
  -> (Psi x <[- x -]> Chi x).
Proof.
Admitted.

Theorem n20_15 (Psi Chi : Prop -> Prop) : (Psi x <[- x -]> Chi x)
  <-> ([^z1 => Psi z1 @ cz1 => ([^z2 => Chi z2 @ cz2 => cz1 = cz2])]).
Proof.
Admitted.

(* This expression still has some ambiguity... *)
(* [^z => Phi z] = [^z => Phi z] *)
Theorem n20_151 (Psi : Prop -> Prop) : 
  exists Phi : Predicate 1, [^z => Psi z @ cz1 => 
    [^z => Phi z @ cz2 => cz1 = cz2]].
Proof.
Admitted.

Theorem n20_16 (Psi : Prop -> Prop) (f : (Prop -> Prop) -> Prop) :
  exists Phi : Predicate 1, 
Proof.
Admitted.

Theorem n20_17 : Prop.
Proof.
Admitted.

Theorem n20_18 : Prop.
Proof.
Admitted.

Theorem n20_19 : Prop.
Proof.
Admitted.

Theorem n20_191 : Prop.
Proof.
Admitted.

Theorem n20_2 : Prop.
Proof.
Admitted.

Theorem n20_21 : Prop.
Proof.
Admitted.

Theorem n20_22 : Prop.
Proof.
Admitted.

Theorem n20_23 : Prop.
Proof.
Admitted.

Theorem n20_24 : Prop.
Proof.
Admitted.

Theorem n20_25 : Prop.
Proof.
Admitted.

Theorem n20_3 : Prop.
Proof.
Admitted.

Theorem n20_31 : Prop.
Proof.
Admitted.

Theorem n20_32 : Prop.
Proof.
Admitted.

Theorem n20_33 : Prop.
Proof.
Admitted.

Theorem n20_34 : Prop.
Proof.
Admitted.

Theorem n20_35 : Prop.
Proof.
Admitted.

Theorem n20_4 : Prop.
Proof.
Admitted.

Theorem n20_41 : Prop.
Proof.
Admitted.

Theorem n20_42 : Prop.
Proof.
Admitted.

Theorem n20_43 : Prop.
Proof.
Admitted.

Theorem n20_5 : Prop.
Proof.
Admitted.

Theorem n20_51 : Prop.
Proof.
Admitted.

Theorem n20_52 : Prop.
Proof.
Admitted.

Theorem n20_53 : Prop.
Proof.
Admitted.

Theorem n20_54 : Prop.
Proof.
Admitted.

Theorem n20_55 : Prop.
Proof.
Admitted.

Theorem n20_56 : Prop.
Proof.
Admitted.

Theorem n20_57 : Prop.
Proof.
Admitted.

Theorem n20_58 : Prop.
Proof.
Admitted.

Theorem n20_59 : Prop.
Proof.
Admitted.

Theorem n20_61 : Prop.
Proof.
Admitted.

Theorem n20_62 : Prop.
Proof.
Admitted.

Theorem n20_63 : Prop.
Proof.
Admitted.

Theorem n20_631 : Prop.
Proof.
Admitted.

Theorem n20_632 : Prop.
Proof.
Admitted.

Theorem n20_633 : Prop.
Proof.
Admitted.

Theorem n20_64 : Prop.
Proof.
Admitted.

Theorem n20_7 : Prop.
Proof.
Admitted.

Theorem n20_701 : Prop.
Proof.
Admitted.

Theorem n20_702 : Prop.
Proof.
Admitted.

Theorem n20_703 : Prop.
Proof.
Admitted.

Theorem n20_71 : Prop.
Proof.
Admitted.

Theorem n20_8 : Prop.
Proof.
Admitted.

Theorem n20_81 : Prop.
Proof.
Admitted.

Close Scope formal_equiv.
Close Scope formal_impl.
Close Scope debug_iota_description_poly.
Close Scope debug_class_notation.