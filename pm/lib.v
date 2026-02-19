(* PM.pm.lib - tools, libraries, notations(temporarily?), and others to be used through the project *)

Require Import Unicode.Utf8.
Require Import ClassicalFacts.
Require Import Classical_Prop.
Require Import PropExtensionality.
Require Import String.

Export Unicode.Utf8.
Export Classical_Prop.
Export ClassicalFacts.
Export PropExtensionality.
Export String.

(* cf.p.23: `=` propositions are allowed to be turned into `↔` propositions. An 
alternative tactic to this is `apply propositional_extensionality`. *)
Theorem eq_to_equiv : ∀ (P Q : Prop),
  (P = Q) → (P ↔ Q).
Proof.
  intros P Q H.
  split; try rewrite -> H; trivial.
Qed.

(* cf.p.51: `!` notation *)
(* EXPERIMENTAL/DRAFT: 
`!` notation mostly declares the order of a matrix, and the function is strictly a matrix(p.166)
Should we treat `!` as something being denotational just like the dot notations in Principia?
*)

(* Chapter 12 & 13: a function, typed, of order `n`.
NOTE: 
- Unless necessary, we should never use ANYTHING beyond `Predicate 1`. It is for convenience 
  when we really need this we can search all occurences of Predicates to be adapted
- For chapter 12, we might want to define an extra `Predicate2`. This should be implemented when
  necessary
TODO: maybe in the future, checkout the definition for matrix and try to see if we can also integrate
in a definition for matrix

TODO: add an extra implicit argument {shift : nat} where shift = 0 by default
*)
Fixpoint Predicate (n : nat) : Type :=
  match n with
  | 0 => Prop
  | (S m) => let A := Predicate m in (A -> Prop)
  end.

(* cf.p.51: To instantiate variables appeared in a propositional function, we use the concept 
of "individual", designed as as wrapper just to tag an real variable. This allows easy identification 
on them and they are free to be created everywhere.
From chapter 13 it turns out that an individual is just a Predicate of type 0. So we just adopt and 
merge with the definition of `Predicate`
*)
Definition Individual := Predicate 0.

(* EXPERIMENTAL: the predicate below serves merely just for "how an untyped function of PM should be
defined in Rocq". Currently it is never used anywhere and only demonstrates an experimental idea *)
Definition Intro_untyped {A : Type} (s : string) : A -> Prop. Admitted.

(* `Intro` Rocq predicates are used for introducing a term in the middle of the proof, which 
is something specific for PM's proofs. Here we provide the version for individuals and predicates *)
Definition Intro_individual (s : string) : Individual. Admitted.

Definition Intro_pred (s : string) (n : nat) : Predicate n. Admitted.

(* **************** *)
(* Chapter 14 *)
(* **************** *)
Declare Scope debug_iota_description.
Declare Scope iota_description.

Definition DescriptionArg (φ : Prop -> Prop) : Type := Prop.
Example descriptionarg_example := (fun iotaφ : (DescriptionArg (fun x => x)) =>
  iotaφ = iotaφ).

(* Here we only define the signature to avoid repetitive definitions, and the actual 
  definition starts after *14.01. *)
Definition Description (φ : Prop -> Prop) (expr : (DescriptionArg φ) -> Prop) : Prop. 
Admitted.
Example description_example := 
  Description (fun (iotaφ : DescriptionArg (fun x => x)) =>
    iotaφ = iotaφ).

(* iota's predicate, "Exists" which states that a description exist. My understanding
is that `E` in `E!` is the capital letter of `Exists` and `!` indicates that it is a 
predicate. 

TODO: give this iota_E the correct `Predicate` type
*)
Definition DescriptionExists (φ : Prop -> Prop) : Prop. Admitted.
Example descriptionexists_example := DescriptionExists (fun x => x).

(* cf. p174, example after *14.03. Interpretation for a function containing 
  multiple descriptions *)
Definition Description2 (φ ψ : Prop -> Prop) 
  (expr : (DescriptionArg φ) -> (DescriptionArg ψ) -> Prop): Prop. 
Admitted.
Example description2_example (φ ψ : Prop -> Prop) :=
  Description2 φ ψ (fun x y => x = y).

(* cf. p174, explanation after *14.04. The iota variant where inner function has 
  larger scope than outer function. This variant will be proven later unecessary. 

  The original definition depends on `iota_f2`. The function `iota_f` here, 
  provided with parameters, gets a similar role to the idea of scope
*)
Definition Description2_rev (φ ψ : Prop -> Prop) 
  (expr : (DescriptionArg ψ) -> (DescriptionArg φ) -> Prop): Prop. 
Admitted.

Open Scope debug_iota_description.

Notation "[ 'iota' φ | x => B ]" := (Description φ (fun (x : DescriptionArg φ) => B))
  (at level 200, x binder, right associativity) : debug_iota_description.
(* TODO: format... *)
Example debug_iota_notation_example := [ iota (fun x => x) | iotaφ => iotaφ = iotaφ ].

Notation "[ 'iotaE' P ]" := (DescriptionExists (P : Prop -> Prop))
  (at level 100, P constr at level 200, right associativity) : debug_iota_description.
Example debug_iota_exists_example := [ iotaE (fun x => x) ].

Notation "[ 'iota2' φ , ψ | x y => B ]" := 
  (Description2 φ ψ (fun (x : DescriptionArg φ) (y : DescriptionArg ψ) => B))
  (at level 200, x binder, y binder, right associativity) : debug_iota_description.
Example debug_iota2_example := 
  [ iota2 (fun x => x) , (fun x => x) | x y => (x = y) ].

Notation "[ 'iota2rev' φ , ψ | y x => B ]" := 
  (Description2 φ ψ (fun (y : DescriptionArg ψ) (x : DescriptionArg φ) => B))
  (at level 200, x binder, y binder, right associativity) : debug_iota_description.

Close Scope debug_iota_description.

Open Scope iota_description.

Notation "[ 'ι' φ | x => B ]" := (Description φ (fun (x : DescriptionArg φ) => B))
  (at level 200, x binder, right associativity) : iota_description.
(* TODO: format... *)
Example iota_notation_example := [ι (fun x => x) | ιφ => ιφ = ιφ].

Notation "[ 'ιE' P ]" := (DescriptionExists (P : Prop -> Prop))
  (at level 100, P constr at level 200, right associativity) : iota_description.
Example iota_exists_example := [ ιE (fun x => x) ].

Notation "[ 'ι2' φ , ψ | x y => B ]" := 
  (Description2 φ ψ (fun (x : DescriptionArg φ) (y : DescriptionArg ψ) => B))
  (at level 200, x binder, y binder, right associativity) : iota_description.
Example iota2_example := 
  [ ι2 (fun x => x) , (fun x => x) | x y => (x = y) ].

Notation "[ 'ι2rev' φ , ψ | y x => B ]" := 
  (Description2 φ ψ (fun (y : DescriptionArg ψ) (x : DescriptionArg φ) => B))
  (at level 200, x binder, y binder, right associativity) : iota_description.

Definition iota2_arg_comm (φ ψ : Prop → Prop) (f : Prop → Prop → Prop) : 
  [ι2 φ, ψ | ιφ ιψ => f ιφ ιψ] ↔ [ι2 φ, ψ | ιψ ιφ => f ιφ ιψ].
Admitted.

Close Scope iota_description.

(* For this new notation, we have to design some special axioms to make 
  it work... *)
