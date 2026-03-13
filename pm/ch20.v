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

**Due to such ambiguity in the `!`, whether functions should be defined as predicates,
appeared through all the notation definitions, is highly volatile and is encouraged 
to be examined and corrected.**

Our current implementation is a mixture of
- using a special `Class` type to express class-related symbol
- using the ambiguity on function `f`'s type, on whether it should receive a "class"-defined 
argument or just a normal function as an argument, since "class"es also seem to have the same
(Rocq)type as a normal function

Furthermore: determining whether a function is an untyped function or a predicative function
in this chapter is very confusing
*)
Declare Scope debug_class.
Declare Scope class.
Declare Scope debug_iota_description_poly.

(* 
Failed attempts:
- Defining `Class` only using functions
- Defining `Class` as (A, Phi)
- Defining `Class` as inductive type

Using Records to define the Class symbol seems to be the best balance to 
expose the `A` type when needed and hide away the underlying function against 
unnecessary argument passes
*)

Record t {A : Type} : Type := {
  get_A : Type; 
}. 
Definition test := Build_t Prop Prop. 
Definition test_get_A : test.(get_A). Admitted. 

Definition test_1 : Prop.
  pose (test_get_A := test_get_A).
  cbn in test_get_A.
  exact test_get_A.
Defined.

Definition test_1_1 : Prop :=
  ltac:(
    pose (x := test_get_A);
    cbn in x;
    exact x
  ).

Print test_1_1.
Compute test_1_1.

Definition test_1_2 := ltac:(
  let x := eval cbn in test_get_A in 
  let f := constr:(fun y : Prop => y) in
  exact (f x)).

Print test_1_2.

Module Class.
  Record t : Type := {
    (* For storing the A type *)
    get_A : Type;
    get_func : get_A -> Prop;
  }.
  Definition mk {A : Type} (Phi : A -> Prop) := Build_t A Phi.
End Class.

Example class_example_1 := Class.mk (fun (x : Prop) => x = x).
Example class_mk_destruct_example_1 := 
  class_example_1.(Class.get_func).
Example class_mk_destruct_example_2 := 
  class_example_1.(Class.get_A).  
(* Compute class_mk_destruct_example_2. *)

(* This should be the correct way to define application on class *)
Definition class_app {A B : Type} (f : (A -> Prop) -> B) (cls : Class.t) : B. Admitted.

(* By *20.02, `in` needs to be interpreted as a function working directly
on the underlying function `Phi`. `in` itself is considered a special function *)
Definition class_in {A : Type} (X : A) (Phi : A -> Prop) : Prop. Admitted.

(* 
To be used in the future: 
Definition Cls {A : Type} {Phi : A -> Prop} : Class.t
  := Class.Build_t A Phi. 
*)
Definition Cls : Class.t. Admitted.

Open Scope debug_class.
Notation "'^' z => B" := (Class.mk (fun z => B))
  (at level 130, z binder, right associativity) : debug_class.
Example class_example_2 := ^ (z : Prop) => z = z.

Definition testtest (cls : Class.t) := ltac:(
  let A := eval cbn in (cls.(Class.get_A)) in 
  let f := constr:((fun (classname : A -> Prop) => classname = classname)) in
  exact (class_app f cls)).
Compute testtest.

(* Definition testtest (cls : @Class.t Prop) := ltac:(
  let A := eval cbn in cls.(Class.get_A) in 
  exact (class_app (fun (classname : A -> Prop) => classname = classname) cls)). *)

(* Notation "[ cls @ classname => B ]" := (
  ltac:(let A := eval cbn in cls.(Class.get_A) in 
    exact (class_app (fun (classname : A -> Prop) => B) cls)))
  (at level 150, classname binder, right associativity) : debug_class. *)

(* Definition testtest2 := ltac:(
  let A := eval cbn in (class_example_1.(Class.get_A)) in 
  let f := constr:((fun (x : A -> Prop) => x = x)) in
  exact (class_app f class_example_1)
). *)
Notation "[ cls @ classname => B ]" := (
    let A := cls.(Class.get_A) in
    class_app (fun (classname : A -> Prop) => B) cls)
  (at level 150, classname binder, right associativity) : debug_class.
Example class_app_example_1 := [class_example_1 @ x => x = x].
Example class_app_example_2 := [^(z : Prop) => z = z @ cz => cz = cz].
Example class_app_example_3 := [class_example_1 @ c1 => [class_example_1 @ c2 => c1 = c2]].

(* In contrast to our notation, the actual `class_in` will be something like ^z => z <class_in> Phi *)
Notation "x '<class_in>' Phi" := (class_in x Phi)
  (at level 120, right associativity) : debug_class.
Example class_in_example (x : Prop) := x <class_in> (fun z => z = z).

Notation "x '<class_in_f>^' C" := 
  (let Phi := C.(Class.get_func) in class_in x Phi)
  (at level 120, right associativity) : debug_class.
Example class_in_f_example (x : Prop) := x <class_in_f>^ class_example_1.
(* EXPERIMENTAL: below is a copy of definitions from ch14 modified so that it supports 
  polymorphic type. It if works in the future, we will have to mitigrate these defs and 
  rewrite ch14 with the polymorphic version 
  Commented defs are to be uncommented when needed
*)
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
  (at level 190, x binder, right associativity) : debug_iota_description_poly.
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

Definition n20_01 (Psi : Prop -> Prop) (f : (Prop -> Prop) -> Prop) :=
  ([^ z => Psi z @ zPsi => f zPsi])
  = (exists Phi : Order 1, (Phi x <[- x -]> Psi x) /\ f Phi).

Definition n20_02 (n : nat) (X : Prop) (Phi : Prop -> Prop) :=
  (X <class_in> Phi) = Phi X.

(* cf. p.188: The definition of `Cls` is also a "partial definition" and
should be considered in specific context.
Also: "we have merely defined certain *uses* of such expressions..."
we can see explicitly that for all definitions in Principia it is allowed
to add more "uses" to the expressioins whenever we want 
*)
Definition n20_03 {A : Type} :=
  Cls = (^ (alpha : A -> Prop) => (exists (Phi : A -> Prop), 
    [^ (z : A) => Phi z @ zPhiz => alpha = zPhiz])).

Definition n20_04 (alpha : Class.t) (X Y : alpha.(Class.get_A)) :
  ((X <class_in_f>^ alpha) /\ (Y <class_in_f>^ alpha))
  = (X <class_in_f>^ alpha) /\ (Y <class_in_f>^ alpha).
Admitted.

Definition n20_05 (alpha : Class.t) (X Y Z : alpha.(Class.get_A)) :
  ((X <class_in_f>^ alpha) /\ (Y <class_in_f>^ alpha) /\ (Z <class_in_f>^ alpha))
  = ((X <class_in_f>^ alpha) /\ (Y <class_in_f>^ alpha)) /\ (Z <class_in_f>^ alpha).
Admitted.

(* We won't refine anything on this symbol so far *)
Definition n20_06 (alpha : Class.t) (X : alpha.(Class.get_A)) :
  (~ (X <class_in_f>^ alpha)) = (~ (X <class_in_f>^ alpha)).
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