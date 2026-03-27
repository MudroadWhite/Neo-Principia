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
- Resolve the conflict between `Order` and Classes' `A` type. Currently we cannot express both
  of them in a unified way
- TODO in docs: 
  1. A hidden trait of propositions are props written in natural language. They might be also derived 
    from certain propositions; i.e. typing rules are not completely axioms in PM
  2. composition nature for types/defs, ref. *20.62
  3. "generalization" for class variables seems to be different from treatments in ch9; 
    they are theorems not pps?
  4. "function X" means "an anonymous function with body of X, and parameters are all symbols 
    appeared in the body"
  5. after 12, `!` comes to significance of application
  6. difficulty: what should be the correct type for all parameters?
  7. explain how soft embedding allows us to perform development in ease: there are always more 
  details to come; no one has done this before; we don't need to reconstruct a hard model
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

Definition n10_11_pred (Y : Order 1) (φ : Order 1 → Prop)
  : φ Y → ∀ x, φ x.
Admitted.

Definition n10_21_pred (φ : Order 1 → Prop) (P : Prop) :
  (∀ x : Order 1, P → φ x) ↔ (P → (∀ x : Order 1, φ x)).
Admitted.

Definition n10_281_pred (φ ψ : (Prop -> Prop) → Prop) :
  (∀ x, φ x ↔ ψ x) → ((∃ x, φ x) ↔ (∃ x, ψ x)).
Admitted.

(* 
Failed attempts:
- Defining `Class` only using functions
- Defining `Class` as (A, Phi)
- Defining `Class` as inductive type

Using Records to define the Class symbol seems to be the best balance to 
expose the `A` type when needed and hide away the underlying function against 
unnecessary argument passes
*)
(* TODO: should we make `A` explicit? *)
Module Class.
  Record t (A : Type) : Type := {
    (* For storing the A type *)
    get_A := A;
    get_func : get_A -> Prop;
  }.
  Definition mk {A : Type} (Phi : A -> Prop) := Build_t A Phi.
End Class.

Example class_example_1 := Class.mk (fun (x : Prop) => x = x).
Example class_mk_destruct_example_1 := 
  class_example_1.(Class.get_func Prop).
Example class_mk_destruct_example_2 := 
  class_example_1.(Class.get_A Prop).  

(* This should be the correct way to define application on class
  We need the `B` because `f` could maybe accept more parameters *)
Definition class_app {A B : Type} (f : (A -> Prop) -> B) (cls : Class.t A) : B. Admitted.

(* This is a very ad-hoc implementation for functions that takes classes as parameters. 
We are still figuring out the correct way to correctly define functions taking arbitrary 
"level"s of class as parameter. See n20_08. From the nature of this definition, it seems 
that `app` is supposed to generate the related `mk` in a "smart" way. `c` suffix stands for 
"applying on another *c*lass" *)
Definition class_app_c {A B : Type} (f : ((A -> Prop) -> Prop) -> B) 
  (Psi : (A -> Prop) -> Prop) : B. Admitted.

(* By *20.02, `in` needs to be interpreted as a function working directly
on the underlying function `Phi`. `in` itself is considered a propositional 
function *)
Definition class_in {A : Type} (X : A) (Phi : A -> Prop) : Prop. Admitted.

Definition class_in_c {A : Type} (alpha : Class.t A) (Psi : (A -> Prop) -> Prop) : Prop.
Admitted.

(* 
To be used in the future: 
Definition Cls {A : Type} {Phi : A -> Prop} : Class.t
  := Class.Build_t A Phi. 
*)
Definition Cls {A : Type} : Class.t A. Admitted.

Open Scope debug_class.
Notation "'^' z => B" := (Class.mk (fun z => B))
  (at level 130, z binder, right associativity) : debug_class.
Example class_example_2 := ^ (z : Prop) => z = z.

(* 
With the `class_app_c` below, it seems that `mk` surprisingly should be redundant,
and we should only generate the class related notation from `app`s and `iota`s
*)
Notation "[ cls @ classname => B ]" := (
    let A := cls.(Class.get_A _) in
    (* let f := (fun (classname : A -> Prop) => B) in
    let Af := cls.(Class.get_func) in
    f Af *)
    class_app (fun (classname : A -> Prop) => B) cls)
  (at level 150, classname binder, right associativity) : debug_class.
Example class_app_example_1 := [class_example_1 @ cx => cx = cx].
Example class_app_example_2 := [^(z : Prop) => z = z @ cz => cz = cz].
Example class_app_example_3 := [class_example_1 @ c1 => [class_example_1 @ c2 => c1 = c2]].
(* TODO: add failing case for class_app_c equivalent *)

(* TODO: add `alpha` support in the future *)
Notation "[ ^ ^ Psi @ cclassname => B ]" :=
  (class_app_c (fun cclassname => B) Psi)
  (at level 150, cclassname binder, right associativity) : debug_class.
Example class_app_c_example_1 {A : Type} (Psi : (A -> Prop) -> Prop) := 
  [^^ Psi @ calphaPsi => calphaPsi].

Notation "x '<class_in_f>' Phi" := (class_in x Phi)
  (at level 120, right associativity) : debug_class.
Example class_in_f_example (x : Prop) := x <class_in_f> (fun z => z = z).

Notation "x '<class_in>' C" := 
  (let Phi := C.(Class.get_func _) in class_in x Phi)
  (at level 120, right associativity) : debug_class.
Example class_in_example (x : Prop) := x <class_in> class_example_1.

(* Another `class_in` specifically for classes. All above should be subject to
future refinements... *)
Notation "c '<class_in_fc>^' Psi" := (class_in_c c Psi) 
  (at level 120, right associativity) : debug_class.

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

Definition description_exists_poly {A : Type} (φ : A -> Prop) : Prop. Admitted.

(* Definition description2_poly {A B : Type} (φ : A -> Prop) (ψ : B -> Prop)
  (expr : (DescriptionArgPoly φ) -> (DescriptionArgPoly ψ) -> Prop) : Prop. 
Admitted. *)

(* Definition description2_rev_poly {A B : Type} (φ : A -> Prop) (ψ : B -> Prop)
  (expr : (DescriptionArgPoly ψ) -> (DescriptionArgPoly φ) -> Prop) : Prop. 
Admitted. *)

Open Scope debug_iota_description_poly.

Notation "[ 'iotapoly' φ | x => B ]" := (description_poly φ (fun (x : DescriptionArgPoly φ) => B))
  (at level 150, x binder, right associativity) : debug_iota_description_poly.
Example debug_iota_poly_example := [ iotapoly (fun x => x) | iotaφ => iotaφ = iotaφ ].

Notation "[ 'iotaEpoly' P ]" := (description_exists_poly (P : _ -> Prop))
  (at level 150, P constr at level 200, right associativity) : debug_iota_description_poly.
Example debug_iota_exists_poly_example := [ iotaEpoly (fun (x : Prop) => x) ].

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

Definition n20_01 (Psi : Prop -> Prop) (f : (Prop -> Prop) -> Prop) :
  ([^ z => Psi z @ cPsi => f cPsi])
  = (exists Phi : Order 1, (Phi x <[- x -]> Psi x) /\ f Phi).
Admitted.

Definition n20_02 (n : nat) (X : Prop) (Phi : Prop -> Prop) :
  (X <class_in_f> Phi) = Phi X.
Admitted.

(* cf. p.188: The definition of `Cls` is also a "partial definition" and
should be considered in specific context.
Also: "we have merely defined certain *uses* of such expressions..."
we can see explicitly that for all definitions in Principia it is allowed
to add more "uses" to the expressioins whenever we want 
*)
Definition n20_03 {A : Type} :
  Cls = (^ (alpha : A -> Prop) => (exists (Phi : A -> Prop), 
    [^ (z : A) => Phi z @ cPhi => alpha = cPhi])).
Admitted.

Definition n20_04 {A : Type} (X Y : A) (alpha : Class.t A) :
  ((X <class_in> alpha) /\ (Y <class_in> alpha))
  = (X <class_in> alpha) /\ (Y <class_in> alpha).
Admitted.

Definition n20_05 {A : Type} (X Y Z : A) (alpha : Class.t A):
  ((X <class_in> alpha) /\ (Y <class_in> alpha) /\ (Z <class_in> alpha))
  = ((X <class_in> alpha) /\ (Y <class_in> alpha)) /\ (Z <class_in> alpha).
Admitted.

(* We won't refine anything on this symbol so far *)
Definition n20_06 {A : Type} (X : A) (alpha : Class.t A) :
  (~ (X <class_in> alpha)) = (~ (X <class_in> alpha)).
Admitted.

Definition n20_07 {A : Type} (X : A) (f : (A -> Prop) -> Prop) :
  (* NOTE: we can see here `Phi` has been unsatisfying: it is not defined with \
  `Order` anymore... maybe we need to adjust `A` in the future to make it compatible
  with `Order`s *)
  forall (alpha : Class.t A), [alpha @ calpha => f calpha]
  = forall Phi : (A -> Prop), [^ z => Phi z @ cPhi => f cPhi].
Admitted.

(* TODO: same as above *)
Definition n20_071 {A : Type} (X : A) (f : (A -> Prop) -> Prop) :
  exists (alpha : Class.t A), [alpha @ calpha => f calpha]
  = exists Phi : (A -> Prop), [^ z => Phi z @ cPhi => f Phi].
Admitted.

Open Scope debug_iota_description_poly.

(* TODO: our current iota notation doesn't express the `alpha`. maybe
we can redesign the iota in the future... *)
Definition n20_072 {A : Type} (X : A) (Phi f : (A -> Prop) -> Prop) :
  [iotapoly Phi | iotaPhi => f iotaPhi]
    = (exists gamma : Class.t A, ([alpha @ calpha => Phi calpha] 
      <[- (alpha : Class.t A) -]> (alpha = gamma)) 
      /\ ([gamma @ cgamma => f cgamma])).
Admitted.

Close Scope debug_iota_description_poly.

Definition n20_08 {A : Type} (f : ((A → Prop) → Prop) -> Prop)
  (Psi : (A -> Prop) -> Prop) :
  [^^ Psi @ calphaPsi => f calphaPsi]
  = ((exists Phi : (A -> Prop) -> Prop, [alpha @ calpha => Psi calpha] 
      <[- (alpha : Class.t A) -]> [alpha @ calpha => Phi calpha]
    /\ f Phi)).
Admitted.

Definition n20_081 {A : Type} (alpha : Class.t A) (Psi : (A -> Prop) -> Prop) :
  (alpha <class_in_fc>^ Psi) = [alpha @ calpha => Psi calpha].
Admitted.

(* **************** *)

Theorem n20_1 (Psi : Prop -> Prop) (f : (Prop -> Prop) -> Prop) :
  ([^ (z : Prop) => Psi z @ zPsi => f zPsi]) <-> exists Phi : Order 1, 
    (Phi x <[- x -]> Psi x) /\ f Phi.
Proof.
  pose proof (n4_2 ([^ (z : Prop) => Psi z @ zPsi => f zPsi])) as n4_2.
  now rewrite -> n20_01 in n4_2 at 2.
Qed.  

Theorem n20_11 (Psi Chi : Prop -> Prop) (f : (Prop -> Prop) -> Prop) :
  (Psi x <[- x -]> Chi x) -> (([^ z => Psi z @ cPsi => f cPsi]) 
    <-> ([^ z => Chi z @ cChi => f cChi])).
Proof.
  (* TOOLS *)
  set (X := Intro_individual "x").
  set (IPhi := Intro_pred "Phi" 1).
  (* ******** *)
  assert (S1 : (Psi x <[- x -]> Chi x) -> ((Phi x <[- x -]> Psi x)
      <[- Phi -]> (Phi x <[- x -]> Chi x))).
  {
    pose proof (n4_86 (Psi X) (Chi X) (IPhi X)) as n4_86.
    setoid_rewrite -> n4_21 in n4_86 at 3.
    setoid_rewrite -> n4_21 in n4_86 at 4.
    pose proof (n10_11 X (fun x => Psi x ↔ Chi x 
      → (IPhi x ↔ Psi x) ↔ (IPhi x ↔ Chi x))) as n10_11a.
    MP n10_11a n4_86.
    pose proof (n10_27 (fun x => Psi x ↔ Chi x)
      (fun x => (IPhi x ↔ Psi x) ↔ (IPhi x ↔ Chi x))) as n10_27.
    MP n10_27 n10_11.
    pose proof (n10_271 (fun x => IPhi x ↔ Psi x)
      (fun x => IPhi x ↔ Chi x)) as n10_271.
    Syll n10_27 n10_271 Sy1.
    pose proof (n10_11_pred IPhi (fun Phi => (Phi z <[- z -]> Psi z) 
      ↔ Phi z <[- z -]> Chi z)) as n10_11b.
    clear n4_86 n10_11a n10_27 n10_271.
    now Syll Sy1 n10_11b Sy2.
  }
  assert (S2 : (Psi x <[- x -]> Chi x) 
    -> (((Phi x <[- x -]> Psi x) /\ f Phi)
      <[- Phi -]> ((Phi x <[- x -]> Chi x) /\ f Phi))).
  {
    intro Hp.
    pose proof (S1 Hp) as S1.
    pose proof (n4_36 (IPhi x <[- x -]> Psi x) (IPhi x <[- x -]> Chi x) 
      (f IPhi)) as n4_36.
    pose proof (n10_11_pred IPhi (fun Phi => 
      (Phi x <[- x -]> Psi x) ↔ (Phi x <[- x -]> Chi x)
        → (Phi x <[- x -]> Psi x) ∧ f Phi↔ (Phi x <[- x -]> Chi x) ∧ f Phi)) 
        as n10_11.
    MP n10_11 n4_36.
    pose proof (n10_27_pred (fun Phi => (Phi x<[- x -]> Psi x) 
      ↔ (Phi x <[- x -]> Chi x))
      (fun Phi => (Phi x <[- x -]> Psi x) ∧ f Phi
        ↔ (Phi x <[- x -]> Chi x) ∧ f Phi)) as n10_27.
    MP n10_27 n10_11.
    now MP n10_27 S1.
  }
  assert (S3 : (Psi x <[- x -]> Chi x) 
    -> ((exists Phi : Order 1, (Phi x <[- x -]> Psi x) /\ f Phi)
      <-> (exists Phi : Order 1, (Phi x <[- x -]> Chi x) /\ f Phi))).
  {
    intro Hp.
    pose proof (S2 Hp) as S2.
    pose proof (n10_281_pred
      (fun Phi => (Phi x <[- x -]> Psi x) /\ f Phi)
      (fun Phi => (Phi x <[- x -]> Chi x) /\ f Phi)) as n10_281.
    clear S1.
    now MP n10_281 S2.
  }
  assert (S4 : (Psi x <[- x -]> Chi x)
    -> (([^ z => Psi z @ cPsi => f cPsi]) 
      <-> ([^ z => Chi z @ cChi => f cChi]))).
  {
    intro Hp.
    pose proof (S3 Hp) as S3.
    now repeat rewrite <- n20_1 in S3.
  }
  exact S4.
Qed.

Theorem n20_111 (f g : (Prop -> Prop) -> Prop) : 
  (forall Phi : Order 1, f Phi <-> g Phi)
  -> (forall Phi : Order 1, 
    (([^ z => Phi z @ cz => f cz]) <-> ([^ z => Phi z @ cz => g cz]))).
Proof.
  (* TOOLS *)
  set (IPhi := Intro_pred "Phi" 1).
  set (IPsi := Intro_pred "Psi" 1).
  (* ******** *)
  
Admitted.

(* TODO: `g` here cannot be `Order 1` and have to be `(Prop -> Prop) -> Prop`.
  Investigate this in the future and design a better `Order` type. The original 
  text is also indicate this clearly *)
Theorem n20_112 (f : (Prop -> Prop) -> Prop) : exists g : (Prop -> Prop) -> Prop, 
  forall Phi : Order 1, ([^z => Phi z @ cz => f cz]) <-> ([^z => Phi z @ cz => g cz]).
Proof.
Admitted.

(* This is the class version of n12_1. While it is typed in Rocq, it might not express 
the real nature of AoR. Also see critics in n12_1. *)
Theorem n20_12 (Psi : Prop -> Prop) (f : (Prop -> Prop) -> Prop): 
  exists Phi : Order 1, (Phi x <[- x -]> Psi x) /\
    (([^z => Psi z @ cz => f cz]) <-> ([^z => Phi z @ cz => f cz])).
Proof.
Admitted.

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

Theorem n20_151 (Psi : Prop -> Prop) : 
  exists Phi : Order 1, [^z => Psi z @ cz1 => 
    [^z => Phi z @ cz2 => cz1 = cz2]].
Proof.
Admitted.

Theorem n20_16 (Psi : Prop -> Prop) (f : (Prop -> Prop) -> Prop) :
  exists Phi : Order 1, [^z => Psi z @ cz1 => f cz1] <-> 
    [^z => Phi z @ cz2 => f cz2].
Proof.
Admitted.

Theorem n20_17 (Psi : Prop -> Prop) (f : (Prop -> Prop) -> Prop) :
  forall Phi : Order 1, [^z => Psi z @ cz1 => f cz1] -> 
    [^z => Phi z @ cz2 => f cz2].
Proof.
Admitted.

Theorem n20_18 (Phi Psi : Prop -> Prop) (f : (Prop -> Prop) -> Prop) : 
  [^z => Phi z @ cz1 => [^z => Psi z @ cz2 => cz1 = cz2]]
  -> [^z => Phi z @ cz1 => [^z => Psi z @ cz2 => f cz1 = f cz2]].
Proof.
Admitted.

(* Should this actually be order 2?? *)
Theorem n20_19 (Psi Chi : Prop -> Prop) : 
  [^z => Psi z @ cz1 => [^z => Chi z @ cz2 => cz1 = cz2]]
  <-> forall f : (Order 1 -> Prop), [^z => Psi z @ cz1 => 
    [^z => Chi z @ cz2 => f cz1 -> f cz2]].
Proof.
Admitted.

Theorem n20_191 (Psi Chi : Prop -> Prop) : 
  [^z => Psi z @ cz1 => [^z => Chi z @ cz2 => cz1 = cz2]]
  <-> forall f : (Order 1 -> Prop), [^z => Psi z @ cz1 => 
    [^z => Chi z @ cz2 => f cz1 <-> f cz2]].
Proof.
Admitted.

Theorem n20_2 (Phi : Prop -> Prop) : [^z => Phi z @ cz1 => cz1 = cz1].
Proof.
Admitted.

(* TODO: there might be some scope issues that only to be found after
  digging into the proofs... *)
Theorem n20_21 (Phi Psi : Prop -> Prop) : [^z => Phi z @ cz1 => 
  [^z => Psi z @ cz2 => cz1 = cz2]] <-> [^z => Phi z @ cz1 => 
  [^z => Psi z @ cz2 => cz2 = cz1]].
Proof.
Admitted.

Theorem n20_22 (Phi Psi Chi : Prop -> Prop) : 
  ([^z => Phi z @ cz1 => [^z => Psi z @ cz2 => cz1 = cz2]] 
    /\ [^z => Psi z @ cz2 => [^z => Chi z @ cz3 => cz2 = cz3]])
  -> [^z => Phi z @ cz1 => [^z => Chi z @ cz3 => cz1 = cz3]].
Proof.
Admitted.

Theorem n20_23 (Phi Psi Chi : Prop -> Prop) : 
  ([^z => Phi z @ cz1 => [^z => Psi z @ cz2 => cz1 = cz2]] 
    /\ [^z => Phi z @ cz1 => [^z => Chi z @ cz3 => cz1 = cz3]])
  -> [^z => Psi z @ cz2 => [^z => Chi z @ cz3 => cz2 = cz3]].
Proof.
Admitted.

Theorem n20_24 (Phi Psi Chi : Prop -> Prop) : 
  ([^z => Psi z @ cz2 => [^z => Phi z @ cz1 => cz2 = cz1]] 
    /\ [^z => Chi z @ cz3 => [^z => Phi z @ cz1 => cz3 = cz1]])
  -> [^z => Psi z @ cz2 => [^z => Chi z @ cz3 => cz2 = cz3]].
Proof.
Admitted.

Theorem n20_25 (Phi Psi : Prop -> Prop) :
  ([alpha @ cz1 => [^z => Phi z @ cz2 => cz1 = cz2]] <[- alpha : Class.t Prop -]>
    [alpha @ cz1 => [^z => Psi z @ cz3 => cz1 = cz3]])
  -> [^z => Phi z @ cz2 => [^z => Psi z @ cz3 => cz2 = cz3]].
Proof.
Admitted.

Theorem n20_3 (X : Prop) (Psi : Prop -> Prop ) : 
  (X <class_in> (^ z => Psi z)) <-> Psi X.
Proof.
Admitted.

Theorem n20_31 (Psi Chi : Prop -> Prop) : 
  [^z => Psi z @ cz1 => [^z => Chi z @ cz2 => cz1 = cz2]]
  <-> ((x <class_in> (^ z => Psi z)) 
    <[- x -]> (x <class_in> (^ z => Chi z))).
Proof.
Admitted.

Theorem n20_32 (Phi : Prop -> Prop) :
  [(^x => x <class_in> (^z => Phi z)) @ cx =>
    [^z => Phi z @ cz => cx = cz]].
Proof.
Admitted.

Theorem n20_33 (alpha : Class.t Prop) (Phi : Prop -> Prop) :
  [alpha @ calpha => [^z => Phi z @ cz => calpha = cz]]
  <-> ((x <class_in> alpha) <[- x -]> Phi x).
Proof.
Admitted.

Open Scope formal_impl.

Theorem n20_34 (X Y : Prop) :
  (X = Y) <-> ((X <class_in> alpha) -[ (alpha : Class.t Prop) ]> (Y <class_in> alpha)).
Proof.
Admitted.

Theorem n20_35 (X Y : Prop) :
  (X = Y) <-> ((X <class_in> alpha) <[- (alpha : Class.t Prop) -]> (Y <class_in> alpha)).
Proof.
Admitted.

Theorem n20_4 (alpha : Class.t Prop) :
  (alpha <class_in> Cls) <-> (exists (Phi : Order 1), [alpha @ calpha => 
    [^z => Phi z @ cz => calpha = cz]]).
Proof.
Admitted.

Theorem n20_41 (Psi : Prop -> Prop) : (^z => Psi z) <class_in> Cls.
Proof.
Admitted.

Theorem n20_42 (alpha : Class.t Prop) : [(^z => z <class_in> alpha)
  @ cz => [alpha @ calpha => cz = calpha]].
Proof.
Admitted.

(* NOTE: note that we won't use `alpha = beta` directly for now *)
Theorem n20_43 (alpha beta : Class.t Prop) : 
  [alpha @ calpha => [beta @ cbeta => calpha = cbeta]]
    <-> ((x <class_in> alpha) <[- x -]> (x <class_in> beta)).
Proof.
Admitted.

Open Scope debug_iota_description.

(* NOTE: descriptions should have larger scope than classes *)
Theorem n20_5 (Phi Psi : Prop -> Prop) :
  [iota Phi | iotaPhi => iotaPhi <class_in> (^z => Psi z)]
  <-> [iota Phi | iotaPhi => Psi iotaPhi].
Proof.
Admitted.

Theorem n20_51 (Phi : Prop -> Prop) (B : Prop) :
  [iota Phi | iotaPhi => iotaPhi = B]
  <-> ([iota Phi | iotaPhi => iotaPhi <class_in> alpha]
    <[- (alpha : Class.t Prop) -]> (B <class_in> alpha)).
Proof.
Admitted.

Theorem n20_52 (Phi : Prop -> Prop) : [iotaE Phi]
  <-> (exists b, [iota Phi | iotaPhi => (iotaPhi <class_in> alpha)]
    <[- (alpha : Class.t Prop) -]> (b <class_in> alpha)).
Proof.
Admitted.

(* Should Phi here be a function of order 1..? *)
Theorem n20_53 (alpha : Class.t Prop) (Phi : (Prop -> Prop) -> Prop) : 
  (beta = alpha) -[ beta ]> [beta @ cbeta => Phi cbeta] <-> [alpha @ calpha => Phi calpha].
Proof.
Admitted.

Theorem n20_54 (alpha : Class.t Prop) (Phi : (Prop -> Prop) -> Prop) : exists beta, 
  ((beta = alpha) /\ [beta @ cbeta => Phi cbeta]) <-> [alpha @ calpha => Phi calpha].
Proof.
Admitted.

Close Scope debug_iota_description.
Open Scope debug_iota_description_poly. 
(* TODO: when filling the theorem, we will merge the two definitions of iotas in ch14 & 20 *)
Theorem n20_55 (Phi : Prop -> Prop) : 
  [iotapoly (fun alpha => (x <class_in> alpha) <[- x -]> Phi x) | iotaalpha =>
    (^z => Phi z) = iotaalpha].
Proof.
Admitted.

Theorem n20_56 (Phi : Prop -> Prop) : [iotaEpoly (fun alpha : Class.t Prop =>
  (x <class_in> alpha) <[- x -]> Phi x)].
Proof.
Admitted.

Theorem n20_57 (Phi : Prop -> Prop) (f g : (Prop -> Prop) -> Prop) : 
  [iotapoly (fun alpha => [alpha @ calpha => f calpha]) | iotaalpha =>
    (^z => Phi z) = iotaalpha]
  -> ([^ z => Phi z @ cz => g cz] <-> [iotapoly (fun alpha => [alpha @ calpha => f calpha]) 
    | iotaalpha => [iotaalpha @ ciotaalpha => g ciotaalpha]]).
Proof.
Admitted.

(* NOTE: rigorously speaking, `=` shouldn't be directly used like this and should be applied
within another class block. Might have some notational issue when comes to implementation *)
Theorem n20_58 (Phi : Prop -> Prop) :
  [iotapoly (fun alpha => alpha = (^z => Phi z)) | iotaalpha =>
    (^z => Phi z) = iotaalpha].
Proof.
Admitted.

(* same as above *)
Theorem n20_59 (Phi : Prop -> Prop) (f : (Prop -> Prop) -> Prop) :
  [iotapoly (fun alpha => [alpha @ calpha => f calpha]) | iotaalpha => 
    (^z => Phi z) = iotaalpha] 
  <->
  [iotapoly (fun alpha => [alpha @ calpha => f calpha]) | iotaalpha => 
    iotaalpha = (^z => Phi z)].
Proof.
Admitted.

Theorem n20_6 (f : (Prop -> Prop) -> Prop) :
  exists alpha, [alpha @ calpha => f calpha]
  <-> ~ (forall alpha, [alpha @ calpha => f calpha]).
Proof.
Admitted.

Theorem n20_61 (f : (Prop -> Prop) -> Prop) (beta : Class.t Prop) :
  (forall alpha, [alpha @ calpha => f calpha])
  -> [beta @ cbeta => f cbeta].
Proof.
Admitted.

(* *20.62 : type formation rule for `forall alpha` *)
Theorem n20_63 (P : Prop) (f : (Prop -> Prop) -> Prop) :
  (forall alpha, P \/ [alpha @ calpha => f calpha]) 
  -> (P \/ forall alpha, [alpha @ calpha => f calpha]).
Proof.
Admitted.

(* *20.631 - 633: omitted, other typing rules... TODO: fill in the future *)

Theorem n20_64 (f g : (Prop -> Prop) -> Prop) (beta : Class.t Prop) : 
  ((forall alpha, [alpha @ calpha => f calpha]) 
    /\ (forall alpha, [alpha @ calpha => g calpha]))
  -> ((forall beta, [beta @ cbeta => f cbeta])
    /\ (forall beta, [beta @ cbeta => g cbeta])).
Proof.
Admitted.

(* Another analogue to *12.1. Same as all above, we cannot formalize this for now *)
Theorem n20_7 (f : (Prop -> Prop) -> Prop) :
  exists (g : (Prop -> Prop) -> Prop), [alpha @ calpha => f calpha] 
    <[- alpha -]> [alpha @ calpha => g calpha].
Proof.
Admitted.

Theorem n20_701 (Phi : Prop -> Prop) (f : (Prop -> Prop) -> Prop -> Prop) :
  exists (g : (Prop -> Prop) -> Prop -> Prop), ([^z => Phi z @ cz => f cz x]
    <[- (Phi : Prop -> Prop) (x : Prop) -]> [^z => Phi z @ cz => g cz x]).
Proof.
Admitted.

Theorem n20_702 (f : Prop -> (Prop -> Prop) -> Prop) :
  exists (g : Prop -> (Prop -> Prop) -> Prop), ([^z => Phi z @ cz => f x cz]
    <[- (Phi : Prop -> Prop) (x : Prop) -]> [^z => Phi z @ cz => g x cz]).
Proof.
Admitted.

Theorem n20_703 (f : (Prop -> Prop) -> (Prop -> Prop) -> Prop) :
  exists (g : (Prop -> Prop) -> (Prop -> Prop) -> Prop), ([^z => Phi z @ cz1 => 
    [^z => Psi z @ cz2 => f cz1 cz2]]
  <[- (Phi : Prop -> Prop) (Psi : Prop -> Prop) -]> [^z => Phi z @ cz1 => 
    [^z => Psi z @ cz2 => g cz1 cz2]]).
Proof.
Admitted.

Theorem n20_71 (alpha beta : Class.t Prop) :
  (alpha = beta) <-> ([alpha @ calpha => g calpha]
    <[- g : (Prop -> Prop) -> Prop -]> [beta @ cbeta => g cbeta]).
Proof.
Admitted.

Theorem n20_8 (Phi : Prop -> Prop) (A : Prop) :
  (Phi A \/ (~ Phi A)) -> [^x => (Phi x \/ (~ Phi x)) @ cx1 =>
    [^x => (x = A \/ (~ (x = A))) @ cx2 => cx1 = cx2]].
Proof.
Admitted.

Theorem n20_81 (Phi Psi : Prop -> Prop) (A : Prop) :
  ((Phi A \/ (~ Phi A)) /\ (Psi A \/ (~ Psi A)))
  -> [^x => Phi x \/ (~ Phi x) @ cx1 => [
    ^x => Psi x \/ (~ Psi x) @ cx2 => cx1 = cx2]].
Proof.
Admitted.

Close Scope formal_equiv.
Close Scope formal_impl.
Close Scope debug_iota_description_poly.
Close Scope debug_class.
