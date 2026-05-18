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
- Resolve the conflict between `Order` and Classes' `A` type. Currently we cannot express both
  of them in a unified way
- Add a special `as_class` to generate the class from a function
- EXPERIMENT: there might be a way to use `replace` to eliminate the `let`s in the window
*)

(* TODO: address following in the documentation; 
adapt following naming convention in the project: 

scoping convention:
- scoping is under consideration but can be fixed nicely
- if possible we want to moreover internalize the scopes (maybe determining the scope
  when computing?) so that it can be automatically
  inferred
- default scope is the minimum subexp containing the symbol, except for only itself
- the 1st operand of a binop has larger scope than the 2nd operand. e.g. `x=y`
- descriptions have larger scope than classes
- the swapping between the scopes seems to be lacking of consideration(?)TODO: recheck 
  related theorems
- axioms related to notaion is exceptionally allowed to be directly applied 
  on the goal
- conflicts between `_pred` and `_class` variant
On representation of class:

failed attempts:
- Defining `Class` only using functions
- Defining `Class` as (A, Phi)
- Defining `Class` as inductive type

representation which turns out to be illegal:
- X <class_in> (^ z => Psi z)
- [^z => Phi z @ cz1 => cz1 = cz1]
- Definition Intro_class {A : Type} (s : string) : Class.t A. Admitted.

ambiguity between symbol and its underlying representation has affected:
- parameter representation (`x : Class.t A` vs `fx : A`)
- the correct representation for a proposition
- should `A` be cut down to `Order` props or should we allow for more symbols
  in the future
- theorems in text *might* mutually utilize both of them without enforcing their 
  relationships. TODO: check this? For example claiming `^z => Psi z` is underlying 
  representation for `alpha`
*)

(* 
TODO: move it to chapter 20 introduction in mechanics

The class in this chapter has been discussed like pretty obscure. It is not being stated
clearly like a structure, and instead, how is it defined is written *in the middle of 
the text*, and is defined with a `^x` that looks so similar to the "function abstraction" 
being used in chapter 9. 

**Due to such ambiguity in the `!`, whether functions should be defined as predicates,
appeared through all the notation definitions, is highly volatile and is encouraged 
to be examined and corrected.**
*)
Declare Scope debug_class.
Declare Scope class.

Definition n10_11_pred (Y : Order 1) (φ : Order 1 → Prop)
  : φ Y → ∀ x, φ x.
Admitted.

Definition n10_11_pred_1 (Y : Order 2) (φ : Order 2 → Prop)
  : φ Y → ∀ x, φ x.
Admitted.

Definition n10_21_pred (φ : Order 1 → Prop) (P : Prop) :
  (∀ x : Order 1, P → φ x) ↔ (P → (∀ x : Order 1, φ x)).
Admitted.

Definition n10_21_pred_1 (φ : Order 2 → Prop) (P : Prop) :
  (∀ x : Order 2, P → φ x) ↔ (P → (∀ x : Order 2, φ x)).
Admitted.

Definition n10_28_pred (φ ψ : (Prop -> Prop) → Prop) :
  (∀ x, φ x → ψ x) → ((∃ x, φ x) → (∃ x, ψ x)).
Admitted.

Definition n10_281_pred (φ ψ : (Prop -> Prop) → Prop) :
  (∀ x, φ x ↔ ψ x) → ((∃ x, φ x) ↔ (∃ x, ψ x)).
Admitted.

Definition n10_28_pred_1 (φ ψ : ((Prop -> Prop) -> Prop) → Prop) :
  (∀ x, φ x → ψ x) → ((∃ x, φ x) → (∃ x, ψ x)).
Admitted.

Definition n10_35_pred (φ : (Prop -> Prop) → Prop) (P : Prop) :
  (∃ x, P ∧ φ x) ↔ P ∧ (∃ x, φ x).
Admitted.

Definition n10_5_pred (φ ψ : (Prop -> Prop) → Prop) :
  (∃ x, φ x ∧ ψ x) → ((∃ x, φ x) ∧ (∃ x, ψ x)).
Admitted.

Open Scope iota_description.

Definition n14_21_pred (φ ψ : (Prop -> Prop) → Prop) : 
  [ι φ | ιφ => ψ ιφ] → [ιE φ]. Admitted.

Close Scope iota_description.

Open Scope formal_equiv.

(* This is a very ironic variant: we shouldn't write down such a variant
if we have designed the AoR correctly *)
Definition n12_1_pred (φ : (Prop -> Prop) → Prop) : 
  ∃ f : (Order 2), (φ x) <[- (x : Order 1) -]> ((fun (F : Order 2) =>
    F x) f).
Admitted.

(* 
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

(* NOTE: draft
Definition Cls {A : Type} {Phi : A -> Prop} : Class.t
  := Class.Build_t A Phi. 
*)
Definition Cls {A : Type} : Class.t A. Admitted.

Open Scope debug_class.
Notation "'^' z => B" := (Class.mk (fun z => B))
  (at level 130, z binder, right associativity) : debug_class.
Example class_example_2 := ^ (z : Prop) => z = z.

Notation "[ cls @ classname => B ]" := (
    let A := cls.(Class.get_A _) in
    (* let f := (fun (classname : A -> Prop) => B) in
    let Af := cls.(Class.get_func) in
    f Af *)
    class_app (fun (classname : A -> Prop) => B) cls)
  (at level 150, classname binder, right associativity, only parsing) : debug_class.
(* Dark magic: we re-define the notation exactly the same way to eliminate the 
  `let`s when simplifying the definition.
  Tradeoff: it might affect how `setoid_rewrite` identify the terms
*)
Notation "[ cls @ classname => B ]" := (class_app (fun classname => B) cls)
  (at level 150, classname binder, right associativity, only printing) : debug_class.
Example class_app_example_1 := [class_example_1 @ cx => cx = cx].
Example class_app_example_2 := [^(z : Prop) => z = z @ cz => cz = cz].
Example class_app_example_3 := [class_example_1 @ c1 => [class_example_1 @ c2 => c1 = c2]].

(* TODO: add `alpha` support in the future *)
Notation "[ ^ ^ Psi @ cclassname => B ]" :=
  (class_app_c (fun cclassname => B) Psi)
  (at level 150, cclassname binder, right associativity) : debug_class.
Example class_app_c_example_1 {A : Type} (Psi : (A -> Prop) -> Prop) := 
  [^^ Psi @ calphaPsi => calphaPsi].

Notation "x '<class_in>' Phi" := (class_in x Phi)
  (at level 120, right associativity) : debug_class.
Example class_in_example (x : Prop) := x <class_in> (fun z => z = z).

(* Another `class_in` specifically for classes. All above should be subject to
future refinements... *)
Notation "c '<class_in_fc>^' Psi" := (class_in_c c Psi) 
  (at level 120, right associativity) : debug_class.

(* Might still not work for even more and worse complicated situations.
TODO: generalize to `f alpha` and name it `class_scope_dup`
*)
Definition class_scope_eq {A : Type} (Alpha : Class.t A) :
  [Alpha @ cz => cz = cz] <-> [Alpha @ cz1 => [Alpha @ cz2 => cz1 = cz2]].
Admitted.

Open Scope debug_iota_description.

Definition iota_class_scope_eq {A : Type} (Alpha : Class.t A) (f : (A -> Prop) -> Prop) 
  (g : (A -> Prop) -> (A -> Prop) -> Prop) :
  [Alpha @ cAlpha => [iota (fun alpha => [alpha @ calpha => f calpha])
  | iotaalpha => [iotaalpha @ ciotaalpha => g ciotaalpha cAlpha]]]
  <->
  [iota (fun alpha => [alpha @ calpha => f calpha]) | iotaalpha =>
  [iotaalpha @ ciotaalpha => [Alpha @ cAlpha => g ciotaalpha cAlpha]]]. Admitted.

Close Scope debug_iota_description.

(* **************** *)
Definition n10_1_class {A : Type} (φ : Class.t A → Prop) (Y : Class.t A) :
  (∀ x, φ x) → φ Y. Admitted.

Definition n10_11_class {A : Type} (Y : Class.t A) (φ : Class.t A → Prop) 
  : φ Y → ∀ x, φ x. Admitted.

Definition n10_21_class {A : Type} (φ : Class.t A → Prop) (P : Prop) :
  (∀ x, P → φ x) ↔ (P → (∀ x, φ x)). Admitted.

Definition n10_23_class {A : Type} (φ : Class.t A → Prop) (P : Prop) :
  (∀ x, φ x → P) ↔ ((∃ x, φ x) → P). Admitted.

Definition n10_24_class {A : Type} (φ : Class.t A → Prop) (Y : Class.t A) :
  φ Y → ∃ x, φ x. Admitted.

Definition n13_183_class {A : Type} (X Y : Class.t A) :
  ([X @ cx => [Y @ cy => cx = cy]]) ↔ 
    ([X @ cx => [z @ cz => cx = cz]] 
      <[- z -]> [z @ cz => [Y @ cy => cz = cy]]). Admitted.

Open Scope iota_description.

(* NOTE: here we can see a non-trivial variant involving the scoping...
  and we cannot determine the right representation so far. When it comes to 
  deep embedding, specifying how to automatically determine the `app`somehow
  for different apolications seems to be critical
*)
Definition n14_1_class {A : Type} (φ ψ : Class.t A → Prop) : [ι φ | ιφ => ψ ιφ]
  ↔ ∃ b, (φ x <[- x -]> [x @ cx => [b @ cb => cx = cb]]) 
    ∧ ψ b. Admitted.

(* This is a variant that has never been used so far *)
Definition n14_13_class {B : Type} (A : Class.t B) (φ : Class.t B → Prop) : 
  [ι φ | ιφ => [A @ cA => [ιφ @ cιφ => cA = cιφ]]] 
  ↔ [ι φ | ιφ => [ιφ @ cιφ => [A @ cA => cιφ = cA]]]. Admitted.

(* Another possible variant, which is actually used... This is why such
  variants are annoying *)
Definition n14_13_class_alt {B : Type} (A : B → Prop) (φ : Class.t B → Prop) : 
  [ι φ | ιφ => [ιφ @ cιφ => A = cιφ]]
  ↔ [ι φ | ιφ => [ιφ @ cιφ => cιφ = A]]. Admitted.

Close Scope iota_description.

(* **************** *)
Definition n20_01 (Psi : Prop -> Prop) (f : (Prop -> Prop) -> Prop) :
  ([^ z => Psi z @ cPsi => f cPsi])
  = (∃ Phi : Order 1, (Phi x <[- x -]> Psi x) ∧ f Phi).
Admitted.

Definition n20_02 (X : Prop) (Phi : Prop -> Prop) :
  (X <class_in> Phi) = Phi X.
Admitted.

(* cf. p.188: The definition of `Cls` is also a "partial definition" and
should be considered in specific context.
Also: "we have merely defined certain *uses* of such expressions..."
we can see explicitly that for all definitions in Principia it is allowed
to add more "uses" to the expressioins whenever we want 
*)
Definition n20_03 {A : Type} :
  Cls = (^ (alpha : A -> Prop) => (∃ (Phi : A -> Prop), 
    [^ (z : A) => Phi z @ cPhi => alpha = cPhi])).
Admitted.

(* We won't define a notation for this abbreviation for now *)
Definition n20_04 {A : Type} (X Y : A) (Alpha : Class.t A) :
  ([Alpha @ calpha => X <class_in> calpha] 
    ∧ [Alpha @ calpha => Y <class_in> calpha])
  = 
  ([Alpha @ calpha => X <class_in> calpha] 
  ∧ [Alpha @ calpha => Y <class_in> calpha]).
Admitted.

Definition n20_05 {A : Type} (X Y Z : A) (Alpha : Class.t A):
  ([Alpha @ calpha => X <class_in> calpha] 
    ∧ [Alpha @ calpha => Y <class_in> calpha]
    ∧ [Alpha @ calpha => Z <class_in> calpha])
  = (([Alpha @ calpha => X <class_in> calpha] 
      ∧ [Alpha @ calpha => Y <class_in> calpha]) 
    ∧ [Alpha @ calpha => Z <class_in> calpha]).
Admitted.

(* We won't define a notation for this abbreviation for now *)
Definition n20_06 {A : Type} (X : A) (Alpha : Class.t A) :
  (~ [Alpha @ calpha => X <class_in> calpha]) 
  = (~ [Alpha @ calpha => X <class_in> calpha]).
Admitted.

Definition n20_07 {A : Type} (X : A) (f : (A -> Prop) -> Prop) :
  (* NOTE: we can see here `Phi` has been unsatisfying: it is not defined with \
  `Order` anymore... maybe we need to adjust `A` in the future to make it compatible
  with `Order`s 
  If we change `A` to `Order x`, it means we don't allow future symbols other than class
  which has been a very annoying ambiguity
  *)
  ∀ (alpha : Class.t A), [alpha @ calpha => f calpha]
  = ∀ Phi : (A -> Prop), [^ z => Phi z @ cPhi => f cPhi].
Admitted.

Definition n20_071 {A : Type} (X : A) (f : (A -> Prop) -> Prop) :
  ∃ (alpha : Class.t A), [alpha @ calpha => f calpha]
  = ∃ Phi : (A -> Prop), [^ z => Phi z @ cPhi => f Phi].
Admitted.

Open Scope debug_iota_description.

(* TODO: our current iota notation doesn't express the `alpha`. maybe
we can redesign the iota in the future... *)
Definition n20_072 {A : Type} (X : A) (Phi f : (A -> Prop) -> Prop) :
  [iota Phi | iotaPhi => f iotaPhi]
    = (∃ gamma : Class.t A, ([alpha @ calpha => Phi calpha] 
      <[- (alpha : Class.t A) -]> (alpha = gamma)) 
      ∧ ([gamma @ cgamma => f cgamma])).
Admitted.

Close Scope debug_iota_description.

Definition n20_08 {A : Type} (f : ((A → Prop) → Prop) -> Prop)
  (Psi : (A -> Prop) -> Prop) :
  [^^ Psi @ calphaPsi => f calphaPsi]
  = ((∃ Phi : (A -> Prop) -> Prop, [alpha @ calpha => Psi calpha] 
      <[- (alpha : Class.t A) -]> [alpha @ calpha => Phi calpha]
    ∧ f Phi)).
Admitted.

Definition n20_081 {A : Type} (alpha : Class.t A) (Psi : (A -> Prop) -> Prop) :
  (alpha <class_in_fc>^ Psi) = [alpha @ calpha => Psi calpha].
Admitted.

(* **************** *)
Theorem n20_1 (Psi : Prop -> Prop) (f : (Prop -> Prop) -> Prop) :
  ([^ (z : Prop) => Psi z @ zPsi => f zPsi]) <-> ∃ Phi : Order 1, 
    (Phi x <[- x -]> Psi x) ∧ f Phi.
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
    MP n10_27 n10_11a.
    pose proof (n10_271 (fun x => IPhi x ↔ Psi x)
      (fun x => IPhi x ↔ Chi x)) as n10_271.
    Syll_as n10_27 n10_271 Sy1.
    pose proof (n10_11_pred IPhi (fun Phi => (Phi z <[- z -]> Psi z) 
      ↔ Phi z <[- z -]> Chi z)) as n10_11b.
    clear n4_86 n10_11a n10_27 n10_271.
    now Syll_as Sy1 n10_11b S1.
  }
  assert (S2 : (Psi x <[- x -]> Chi x) 
    -> (((Phi x <[- x -]> Psi x) ∧ f Phi)
      <[- Phi -]> ((Phi x <[- x -]> Chi x) ∧ f Phi))).
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
    -> ((∃ Phi : Order 1, (Phi x <[- x -]> Psi x) ∧ f Phi)
      <-> (∃ Phi : Order 1, (Phi x <[- x -]> Chi x) ∧ f Phi))).
  {
    intro Hp.
    pose proof (S2 Hp) as S2.
    pose proof (n10_281_pred
      (fun Phi => (Phi x <[- x -]> Psi x) ∧ f Phi)
      (fun Phi => (Phi x <[- x -]> Chi x) ∧ f Phi)) as n10_281.
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
  (f Phi <[- Phi -]> g Phi)
  -> (([^ z => Phi z @ cz => f cz]) <[- Phi -]> ([^ z => Phi z @ cz => g cz])).
Proof.
  (* TOOLS *)
  set (IPhi := Intro_pred "Phi" 1).
  set (IPsi := Intro_pred "Psi" 1).
  (* ******** *)
  assert (S1 : (f Phi <[- Phi -]> g Phi)
    -> ((IPhi x <[- x -]> IPsi x) ∧ f IPsi
      <-> (IPhi x <[- x -]> IPsi x) ∧ g IPsi)).
  {
    (* We don't use Fact3_45 here as n4_36 suits better *)
    pose proof (n4_36 (f IPsi) (g IPsi) (IPhi x<[-x : Prop-]>IPsi x)) 
      as n4_36.
    setoid_rewrite -> n4_3 in n4_36 at 3.
    setoid_rewrite -> n4_3 in n4_36 at 5.
    pose proof (n10_1_pred (fun Phi => f Phi <-> g Phi) IPsi)
      as n10_1.
    now Syll_as n10_1 n4_36 S1.
  }
  assert (S2 : (f Phi <[- Phi -]> g Phi)
    -> (((IPhi x <[- x -]> Psi x) ∧ f Psi)
      <[- Psi -]> ((IPhi x <[- x -]> Psi x) ∧ g Psi))).
  {
    pose proof (n10_11_pred
      IPsi (fun Psi => (f Phi <[- Phi -]> g Phi) 
      -> (((IPhi x <[- x -]> Psi x) ∧ f Psi)
        ↔ ((IPhi x <[- x -]> Psi x) ∧ g Psi)))) as n10_11.
    MP n10_11 S1.
    now rewrite -> n10_21_pred in n10_11.
  }
  assert (S3 : (f Phi <[- Phi -]> g Phi)
    -> ((∃ Psi, (IPhi x <[- x -]> Psi x) ∧ f Psi)
      <-> (∃ Psi, (IPhi x <[- x -]> Psi x) ∧ g Psi))).
  {
    intro Hp.
    pose proof (S2 Hp) as S2.
    clear S1.
    pose proof (n10_281_pred
      (fun Psi => (IPhi x <[- x -]> Psi x) ∧ f Psi)
      (fun Psi => (IPhi x <[- x -]> Psi x) ∧ g Psi)) as n10_281.
    now MP n10_281 S2.
  }
  assert (S4 : (f Phi <[- Phi -]> g Phi)
    -> (([^ z => IPhi z @ cz => f cz]) 
      <-> ([^ z => IPhi z @ cz => g cz]))).
  {
    setoid_rewrite -> n4_21 in S3 at 3.
    setoid_rewrite -> n4_21 in S3 at 4.
    now repeat setoid_rewrite <- n20_1 in S3.
  }
  assert (S5 : (f Phi <[- Phi -]> g Phi)
    -> (([^ z => Phi z @ cz => f cz]) 
      <[- Phi -]> ([^ z => Phi z @ cz => g cz]))).
  {
    pose proof n10_11_pred.
    pose proof (n10_11_pred IPhi
      (fun Phi0 => (f Phi<[-Phi : Prop → Prop-]>g Phi)
        → ([^ z => Phi0 z @ zPsi => f zPsi])
          ↔ ([^ z => Phi0 z @ zPsi => g zPsi]))) as n10_11.
    MP n10_11 S4.
    now rewrite -> n10_21_pred in n10_11.
  }
  exact S5.
Qed.

(* NOTE: 
  `g` here cannot be `Order 1` and have to be `(Prop -> Prop) -> Prop`. TODO: 
  Investigate this in the future and design a better `Order` type. The original 
  text is also indicate this clearly 
*)
Theorem n20_112 (f : (Prop -> Prop) -> Prop) : ∃ g : (Prop -> Prop) -> Prop, 
  ([^z => Phi z @ cz => f cz]) <[- Phi -]> ([^z => Phi z @ cz => g cz]).
Proof.
  (* TOOLS *)
  set (Ig := Intro_pred "g" 2).
  (* ******** *)
  assert (S1 : ∃ g, f Phi <[- Phi -]> g Phi).
  { apply n12_1_pred. }
  assert (S2 : ∃ g : (Prop -> Prop) -> Prop, 
    ([^z => Phi z @ cz => f cz]) <[- Phi -]> ([^z => Phi z @ cz => g cz])).
  {
    pose proof (n20_111 f Ig) as n20_111.
    pose proof (n10_11_pred_1 Ig (fun g => (f Phi <[- Phi -]> g Phi)
      → ([^ z => Phi z @ cz => f cz]) <[- Phi -]>
        ([^ z => Phi z @ cz => g cz]))) as n10_11.
    MP n10_11 n20_111.
    pose proof (n10_28_pred_1 (fun g => (f Phi <[- Phi -]> g Phi))
      (fun g => ([^ z => Phi z @ cz => f cz]) 
        <[- Phi -]> ([^ z => Phi z @ cz => g cz]))) as n10_28.
    MP n10_28 n10_11.
    now MP n10_28 S1.
  }
  exact S2.
Qed.

(* This is the class version of n12_1. As we currently cannot correctly 
  implement n12_1, our implementation in n20_12 isn't nice as well *)
Theorem n20_12 (Psi : Prop -> Prop) (f : (Prop -> Prop) -> Prop): 
  ∃ Phi : Order 1, (Phi x <[- x -]> Psi x) ∧
    (([^z => Psi z @ cz => f cz]) <-> ([^z => Phi z @ cz => f cz])).
Proof.
  pose proof n20_11 as n20_11.
  (* TODO: unprovable *)
Admitted.

Theorem n20_13 (Psi Chi : Prop -> Prop) : (Psi x <[- x -]> Chi x)
  -> ([^z1 => Psi z1 @ cz1 => ([^z2 => Chi z2 @ cz2 => cz1 = cz2])]).
Proof.
  (* TOOLS *)
  set (IPhi := Intro_pred "Phi" 1).
  (* ******** *)
  assert (S1 : ([^z1 => Psi z1 @ cz1 => [^z2 => Chi z2 @ cz2 => cz1 = cz2]])
    <-> ∃ Phi, (Psi x <[- x -]> Phi x) ∧ ([^z => Chi z @ cz2 => Phi = cz2])).
  {
    (* Yes: below code has really taken me a lot of time to figure out *)
    pose proof (n20_1 Psi (fun cz1 => [^z2 => Chi z2 @ cz2 => cz1 = cz2])) 
      as n20_1.
    now setoid_rewrite -> n4_21 in n20_1 at 2.
  }
  assert (S2 : ([^z1 => Psi z1 @ cz1 => [^z2 => Chi z2 @ cz2 => cz1 = cz2]])
    <-> ∃ Phi Theta, (Psi x <[- x -]> Phi x) ∧ (Chi x <[- x -]> Theta x)
      ∧ (Phi = Theta)).
  {
    (* We have to generalize the IPhi to fit in the proof *)
    pose proof (n20_1 Chi (fun cz2 => IPhi = cz2)) as n20_1.
    pose proof (n4_36 ([^ z => Chi z @ zPsi => IPhi = zPsi])
      (∃ Theta : Order 1, (Theta x <[- x -]> Chi x)
        ∧ IPhi = Theta)
      (Psi x <[- x -]> IPhi x)) as n4_36.
    MP n4_36 n20_1.
    pose proof (n10_11_pred IPhi (fun Phi =>
      (([^ z => Chi z @ zPsi => Phi = zPsi]) 
          ∧ (Psi x <[- x -]> Phi x))
          <-> ((∃ Theta : Order 1, (Theta x <[- x -]> Chi x)
          ∧ Phi = Theta) ∧ (Psi x <[- x -]> Phi x)))) 
      as n10_11.
    MP n10_11 n4_36.
    pose proof (n10_281_pred
      (fun Phi => ([^ z => Chi z @ zPsi => Phi = zPsi]) 
        ∧ (Psi x <[- x -]> Phi x))
      (fun Phi => (∃ Theta : Order 1, (Theta x <[- x -]> Chi x)
        ∧ Phi = Theta) ∧  (Psi x <[- x -]> Phi x))) 
      as n10_281.
    MP n10_281 n10_11.
    setoid_rewrite -> n4_3 in n10_281 at 2.
    setoid_rewrite -> n4_3 in n10_281 at 4.
    setoid_rewrite <- n10_35_pred in n10_281.
    setoid_rewrite -> n4_21 in n10_281 at 4.
    now rewrite -> n10_281 in S1.
  }
  assert (S3 : (Psi x <[- x -]> Chi x)
    -> ∃ Phi, (Psi x <[- x -]> Phi x) ∧ (Chi x <[- x -]> Phi x)).
  {
    pose proof (n12_1 Psi) as n12_1a.
    pose proof (n12_1 Chi) as n12_1b.
    (* Unprovable: we cannot merge the `∃` for now *)
    pose proof n10_321 as n10_321.
    admit.
  }
  assert (S4 : (Psi x <[- x -]> Chi x) ->
    ∃ Phi Theta, (Psi x <[- x -]> Phi x)
      ∧ (Chi x <[- x -]> Theta x) ∧ (Phi = Theta)).
  {
    pose proof n13_195 as n13_195.
    (* TODO: provable by bottom up construction; to be filled 
      in future *)
    admit.
  }
  assert (S5 : (Psi x <[- x -]> Chi x)
    -> ([^z1 => Psi z1 @ cz1 => ([^z2 => Chi z2 @ cz2 => cz1 = cz2])])).
  {
    now rewrite <- S2 in S4.
  }
  exact S5.
Admitted.

Theorem n20_14 (Psi Chi : Prop -> Prop) :
  ([^z1 => Psi z1 @ cz1 => ([^z2 => Chi z2 @ cz2 => cz1 = cz2])])
  -> (Psi x <[- x -]> Chi x).
Proof.
  assert (S1 : [^z => Psi z @ cz1 => [^z => Chi z @ cz2 => cz1 = cz2]]
    <-> (∃ Phi, (Psi x <[- x -]> Phi x) 
      ∧ [^z => Chi z @ cz2 => Phi = cz2])).
  {
    pose proof (n20_1 Psi (fun cz1 => [^z => Chi z @ cz2 => cz1 = cz2])) 
      as n20_1.
    setoid_rewrite <- n4_21 in n20_1 at 2.
    exact n20_1.
  }
  assert (S2 : [^z => Psi z @ cz1 => [^z => Chi z @ cz2 => cz1 = cz2]]
    <-> (∃ (Phi Theta : Prop -> Prop), (Psi x <[- x -]> Phi x) 
      ∧ (Chi x <[- x -]> Theta x) ∧ (Phi = Theta))).
  {
    setoid_rewrite -> n20_1 in S1 at 2.
    setoid_rewrite -> n4_21 in S1 at 3.
    now setoid_rewrite <- n10_35_pred in S1.
  }
  assert (S3 : [^z => Psi z @ cz1 => [^z => Chi z @ cz2 => cz1 = cz2]]
    <-> (∃ Phi, (Psi x <[- x -]> Phi x) ∧ (Chi x <[- x -]> Phi x))).
  {
    pose proof n13_195 as n13_195.
    (* TODO: provable with bottom-up construction *)
    admit.
  }
  assert (S4 : [^z => Psi z @ cz1 => [^z => Chi z @ cz2 => cz1 = cz2]]
    -> (Psi x <[- x -]> Chi x)).
  {
    pose proof n10_322 as n10_322.
    (* TODO: might be unprovable... we cannot eliminate `∃` in 
      this way *)
    admit.
  }
  exact S4.
Admitted.

Theorem n20_15 (Psi Chi : Prop -> Prop) : (Psi x <[- x -]> Chi x)
  <-> ([^z1 => Psi z1 @ cz1 => ([^z2 => Chi z2 @ cz2 => cz1 = cz2])]).
Proof.
  pose proof (n20_13 Psi Chi) as n20_13.
  pose proof (n20_14 Psi Chi) as n20_14.
  Conj_as n20_13 n20_14 C1.
  now Equiv C1.
Qed.

Theorem n20_151 (Psi : Prop -> Prop) : 
  ∃ Phi : Order 1, [^z => Psi z @ cz1 => 
    [^z => Phi z @ cz2 => cz1 = cz2]].
Proof.
  (* TOOLS *)
  set (IPhi := Intro_pred "Phi" 1).
  (* ******** *)
  assert (S1 : (Psi x <[- x -]> IPhi x) -> [^z => Psi z @ cz1 => 
    [^z => IPhi z @ cz2 => cz1 = cz2]]).
  { apply n20_15. }
  assert (S2 : (∃ Phi, Psi x <[- x -]> Phi x) 
    -> (∃ Phi, [^z => Psi z @ cz1 => [^z => Phi z @ cz2 => cz1 = cz2]])).
  {
    pose proof (n10_11_pred IPhi (fun Phi =>
      (Psi x <[- x -]> Phi x) -> [^z => Psi z @ cz1 => 
        [^z => Phi z @ cz2 => cz1 = cz2]])) as n10_11.
    MP n10_11 S1.
    pose proof (n10_28_pred
      (fun Phi => Psi x <[- x -]> Phi x)
      (fun Phi => [^z => Psi z @ cz1 => [^z => Phi z @ cz2 => cz1 = cz2]])) 
      as n10_28.
    now MP n10_28 n10_11.
  }
  assert (S3 : ∃ Phi : Order 1, [^z => Psi z @ cz1 => 
    [^z => Phi z @ cz2 => cz1 = cz2]]).
  {
    pose proof (n12_1 Psi) as n12_1.
    (* Surprisingly, we can use n12_1 here *)
    now MP S2 n12_1.
  }
  exact S3.
Qed.

Theorem n20_16 (Psi : Prop -> Prop) (f : (Prop -> Prop) -> Prop) :
  ∃ Phi : Order 1, [^z => Psi z @ cz1 => f cz1] <-> 
    [^z => Phi z @ cz2 => f cz2].
Proof.
  pose proof (n20_12 Psi f) as n20_12.
  pose proof (n10_5_pred
    (fun Phi => Phi x <[- x -]> Psi x)
    (fun Phi => ([^ z => Psi z @ cz => f cz]) 
      ↔ ([^ z => Phi z @ cz => f cz]))) as n10_5.
  MP n10_5 n20_12.
  (* simplification *)
  now destruct n10_5.
Qed.

Theorem n20_17 (Psi : Prop -> Prop) (f : (Prop -> Prop) -> Prop) :
  ∀ Phi : Order 1, [^z => Psi z @ cz1 => f cz1] -> 
    [^z => Phi z @ cz2 => f cz2].
Proof.
  pose proof n20_16 as n20_16.
  pose proof n10_1 as n10_1.
  (* unprovable *)
Admitted.

Theorem n20_18 (Phi Psi : Prop -> Prop) (f : (Prop -> Prop) -> Prop) : 
  [^z => Phi z @ cz1 => [^z => Psi z @ cz2 => cz1 = cz2]]
  -> ([^z => Phi z @ cz1 => f cz1] <-> [^z => Psi z @ cz2 => f cz2]).
Proof.
  pose proof (n20_11 Phi Psi f) as n20_11.
  now rewrite -> n20_15 in n20_11.
Qed.

Theorem n20_19 (Psi Chi : Prop -> Prop) : 
  [^z => Psi z @ cz1 => [^z => Chi z @ cz2 => cz1 = cz2]]
  <-> (∀ f : (Order 1 -> Prop), [^z => Psi z @ cz1 => f cz1]
    -> [^z => Chi z @ cz2 => f cz2]).
Proof.
  (* TOOLS *)
  set (X := Intro_individual "x").
  set (If := Intro_pred "f" 2).
  set (IPhi := Intro_pred "Phi" 1).
  set (ITheta := Intro_pred "Theta" 1).
  (* ******** *)
  assert (S1 : [^z => Psi z @ cz1 => [^z => Chi z @ cz2 => cz1 = cz2]]
    -> (∀ f, [^z => Psi z @ cz1 => f cz1] ->
      [^z => Chi z @ cz2 => f cz2])).
  {
    pose proof (n20_18 Psi Chi If) as n20_18.
    pose proof (n10_11_pred_1 If (fun f =>
      [^z => Psi z @ cz1 => [^z => Chi z @ cz2 => cz1 = cz2]]
        -> ([^z => Psi z @ cz1 => f cz1] <-> [^z => Chi z @ cz2 => f cz2]))) as n10_11.
    MP n10_11 n20_18.
    rewrite -> n10_21_pred_1 in n10_11.
    (* simplification *)
    intros Hp f.
    pose proof (n10_11 Hp f) as n10_11.
    now destruct n10_11.
  }
  assert (S2 : ((IPhi x <[- x -]> Psi x) ∧ (ITheta x <[- x -]> Chi x)
      ∧ ([^z => Psi z @ cz1 => If cz1] -> [^z => Chi z @ cz2 => If cz2]))
    -> ([^z => IPhi z @ cz3 => If cz3] -> [^z => ITheta z @ cz4 => If cz4])).
  {
    pose proof (n20_18) as n20_18.
    pose proof (n20_15 IPhi Psi) as n20_15a.
    pose proof (n20_15 ITheta Chi) as n20_15b. 
    (* TODO: fill it in the future... *)
    admit.
  }
  assert (S3 : (((IPhi x <[- x -]> Psi x) ∧ (ITheta x <[- x -]> Chi x))
      ∧ (∀ f, [^z => Psi z @ cz1 => f cz1] -> [^z => Chi z @ cz2 => f cz2]))
    -> ∀ f, ([^z => IPhi z @ cz3 => f cz3] -> [^z => ITheta z @ cz4 => f cz4])).
  {
    (* TODO: fill it in the future *)
    admit.
  }
  assert (S4 : (((IPhi x <[- x -]> Psi x) ∧ (ITheta x <[- x -]> Chi x))
      ∧ (∀ f, [^z => Psi z @ cz1 => f cz1] -> [^z => Chi z @ cz2 => f cz2]))
    -> ((IPhi x <[- x -]> IPhi x) -> (IPhi x <[- x -]> ITheta x))).
  {
    admit.
  }
  assert (S5 : (((IPhi x <[- x -]> Psi x) ∧ (ITheta x <[- x -]> Chi x))
      ∧ (∀ f, [^z => Psi z @ cz1 => f cz1] -> [^z => Chi z @ cz2 => f cz2]))
    -> (IPhi x <[- x -]> ITheta x)).
  {
    (* simplification *)
    intro Hp.
    pose proof (S4 Hp) as S4.
    pose proof (n4_2 (IPhi X)) as n4_2.
    pose proof (n10_11 X (fun x => IPhi x <-> IPhi x)) as n10_11.
    MP n10_11 n4_2.
    now MP S4 n10_11.
  }
  assert (S6 : (((IPhi x <[- x -]> Psi x) ∧ (ITheta x <[- x -]> Chi x))
      ∧ (∀ f, [^z => Psi z @ cz1 => f cz1] -> [^z => Chi z @ cz2 => f cz2]))
    -> (Psi x <[- x -]> Chi x)).
  {
    (* *10.301 *10.32 ignored *)
    (* simplification *)
    intros Hp.
    pose proof (S5 Hp) as S5.
    destruct Hp as [Hp1 Hp3].
    destruct Hp1 as [Hp1 Hp2].
    setoid_rewrite -> Hp1 in S5.
    now setoid_rewrite -> Hp2 in S5.
  }
  assert (S7 : (((IPhi x <[- x -]> Psi x) ∧ (ITheta x <[- x -]> Chi x))
      ∧ (∀ f, [^z => Psi z @ cz1 => f cz1] -> [^z => Chi z @ cz2 => f cz2]))
    -> ([^z => Psi z @ cz1 => [^z => Chi z @ cz2 =>  cz1 = cz2]])).
  { now setoid_rewrite -> n20_15 in S6 at 3. }
  assert (S8 : (∃ Phi Theta, ((Phi x <[- x -]> Psi x) ∧ (Theta x <[- x -]> Chi x)))
      ∧ (∀ f, [^z => Psi z @ cz1 => f cz1] -> [^z => Chi z @ cz2 => f cz2])
    -> [^z => Psi z @ cz1 => [^z => Chi z @ cz2 =>  cz1 = cz2]]).
  {
    pose proof n10_11 as n10_11.
    pose proof n10_23 as n10_23.
    pose proof n10_35 as n10_35.
    admit.
  }
  assert (S9 : (∀ f, [^z => Psi z @ cz1 => f cz1] -> [^z => Chi z @ cz2 => f cz2])
    -> [^z => Psi z @ cz1 => [^z => Chi z @ cz2 =>  cz1 = cz2]]).
  {
    pose proof n12_1 as n12_1.
    admit.
  }
  assert (S10 : [^z => Psi z @ cz1 => [^z => Chi z @ cz2 => cz1 = cz2]]
    <-> (∀ f : (Order 1 -> Prop), [^z => Psi z @ cz1 => f cz1]
      -> [^z => Chi z @ cz2 => f cz2])).
  {
    admit.
  }
  exact S10.
Admitted.

Theorem n20_191 (Psi Chi : Prop -> Prop) : 
  [^z => Psi z @ cz1 => [^z => Chi z @ cz2 => cz1 = cz2]]
  <-> ∀ f : (Order 1 -> Prop), [^z => Psi z @ cz1 => 
    [^z => Chi z @ cz2 => f cz1 <-> f cz2]].
Proof.
  (* TODO: figure out the correct way for the proof *)
  (* 
  Theorem n20_18 (Phi Psi : Prop -> Prop) (f : (Prop -> Prop) -> Prop) : 
  [^z => Phi z @ cz1 => [^z => Psi z @ cz2 => cz1 = cz2]]
  -> ([^z => Phi z @ cz1 => f cz1] <-> [^z => Psi z @ cz2 => f cz2]).
  *)
  pose proof n20_18 as n20_18.
  pose proof n20_19 as n20_19.
  pose proof n10_22 as n10_22.
Admitted.

Theorem n20_2 (Phi : Prop -> Prop) : [^z => Phi z @ cz1 => 
  [^z => Phi z @ cz2 => cz1 = cz2]].
Proof.
  (* TOOLS *)
  set (X := Intro_individual "x").
  (* ******** *)
  assert (S1 : [^z => Phi z @ cz1 => 
    [^z => Phi z @ cz2 => cz1 = cz2]] <-> (Phi x <[- x -]> Phi x)).
  {
    pose proof (n20_15 Phi Phi) as n20_15.
    now rewrite -> n4_21 in n20_15.
  }
  assert (S2 : [^z => Phi z @ cz1 => [^z => Phi z @ cz2 => cz1 = cz2]]).
  {
    destruct S1 as [_ S1].
    pose proof (n4_2 (Phi X)) as n4_2.
    pose proof (n10_11 X (fun x => Phi x <-> Phi x)) as n10_11.
    MP n10_11 n4_2.
    now MP S1 n10_11.
  }
  exact S2.
Qed.

Theorem n20_21 (Phi Psi : Prop -> Prop) : [^z => Phi z @ cz1 => 
  [^z => Psi z @ cz2 => cz1 = cz2]] <-> [^z => Psi z @ cz2 => 
  [^z => Phi z @ cz1 => cz2 = cz1]].
Proof.
  pose proof (n20_15 Phi Psi) as n20_15a.
  pose proof (n20_15 Psi Phi) as n20_15b.
  pose proof (n10_32 Phi Psi) as n10_32.
  now rewrite -> n20_15a, -> n20_15b in n10_32.
Qed.

(* This is a custom alternative for convinient reconstruction in our code *)
Definition n20_21_alt {A : Type} (alpha beta : Class.t A) :
  [alpha @ calpha => [beta @ cbeta => calpha = cbeta]]
  <-> [beta @ cbeta => [alpha @ calpha => cbeta = calpha]].
Admitted.

Theorem n20_22 (Phi Psi Chi : Prop -> Prop) : 
  ([^z => Phi z @ cz1 => [^z => Psi z @ cz2 => cz1 = cz2]] 
    ∧ [^z => Psi z @ cz2 => [^z => Chi z @ cz3 => cz2 = cz3]])
  -> [^z => Phi z @ cz1 => [^z => Chi z @ cz3 => cz1 = cz3]].
Proof.
  pose proof (n20_15 Phi Psi) as n20_15a.
  pose proof (n20_15 Psi Chi) as n20_15b.
  pose proof (n20_15 Phi Chi) as n20_15c.
  pose proof (n10_301 Phi Psi Chi) as n10_301.
  now rewrite -> n20_15a, -> n20_15b, -> n20_15c in n10_301.
Qed.

Theorem n20_23 (Phi Psi Chi : Prop -> Prop) : 
  ([^z => Phi z @ cz1 => [^z => Psi z @ cz2 => cz1 = cz2]] 
    ∧ [^z => Phi z @ cz1 => [^z => Chi z @ cz3 => cz1 = cz3]])
  -> [^z => Psi z @ cz2 => [^z => Chi z @ cz3 => cz2 = cz3]].
Proof.
  pose proof (n20_21 Phi Psi) as n20_21.
  pose proof (n20_22 Psi Phi Chi) as n20_22.
  now rewrite <- n20_21 in n20_22.
Qed.

Theorem n20_24 (Phi Psi Chi : Prop -> Prop) : 
  ([^z => Psi z @ cz2 => [^z => Phi z @ cz1 => cz2 = cz1]] 
    ∧ [^z => Chi z @ cz3 => [^z => Phi z @ cz1 => cz3 = cz1]])
  -> [^z => Psi z @ cz2 => [^z => Chi z @ cz3 => cz2 = cz3]].
Proof.
  pose proof (n20_21 Phi Chi) as n20_21.
  pose proof (n20_22 Psi Phi Chi) as n20_22.
  now rewrite -> n20_21 in n20_22.
Qed.

(* 
  NOTE: While class is said to be an "incomplete symbol", the utilization of *10.1 in 
  this proof reveals that Russell might actually want to give class a "type"(as in Rocq) 
  that is beyond the hierarchy of propositions and functions.
  This is also the first proof where we have to provide a "class individual" by
  providing a underlying function for the class
*)
Theorem n20_25 (Phi Psi : Prop -> Prop) :
  ([alpha @ cz1 => [^z => Phi z @ cz2 => cz1 = cz2]] <[- alpha -]>
    [alpha @ cz1 => [^z => Psi z @ cz3 => cz1 = cz3]])
  -> [^z => Phi z @ cz2 => [^z => Psi z @ cz3 => cz2 = cz3]].
Proof.
  (* TOOLS *)
  set (Falpha := Intro_pred "Falpha" 1).
  set (Alpha := (^z => Falpha z)).
  (* ******** *)
  assert (S1 : ([alpha @ cz1 => [^z => Phi z @ cz2 => cz1 = cz2]] 
      <[- alpha -]> [alpha @ cz1 => [^z => Psi z @ cz3 => cz1 = cz3]])
    -> ([^z => Phi z @ cz1 => [^z => Phi z @ cz2 => cz1 = cz2]]
     <-> [^z => Phi z @ cz1 => [^z => Psi z @ cz3 => cz1 = cz3]])).
  {
    pose proof (n10_1_class (fun alpha => [alpha @ cz1 => 
        [^z => Phi z @ cz2 => cz1 = cz2]] <-> 
      [alpha @ cz1 => [^z => Psi z @ cz3 => cz1 = cz3]])
      (^z => Phi z)) as n10_1.
    exact n10_1.
  }
  assert (S2 : ([alpha @ cz1 => [^z => Phi z @ cz2 => cz1 = cz2]] 
      <[- alpha -]> [alpha @ cz1 => [^z => Psi z @ cz3 => cz1 = cz3]])
    -> [^z => Phi z @ cz1 => [^z => Psi z @ cz3 => cz1 = cz3]]).
  {
    (* simplification *)
    intro Hp.
    pose proof (S1 Hp) as S1.
    destruct S1 as [S1 _].
    pose proof (n20_2 Phi) as n20_2.
    now MP S1 n20_2.
  }
  assert (S3 : ([Alpha @ cz1 => [^z => Phi z @ cz2 => cz1 = cz2]]
      ∧ [^z => Phi z @ cz2 => [^z => Psi z @ cz3 => cz2 = cz3]])
    -> [Alpha @ cz1 => [^z => Psi z @ cz3 => cz1 = cz3]]).
  { apply n20_22. }
  assert (S4 : ([^z => Phi z @ cz1 => [^z => Psi z @ cz2 => cz1 = cz2]])
    -> ([Alpha @ cz3 => [^z => Phi z @ cz1 => cz3 = cz1]]
      -> [Alpha @ cz3 => [^z => Psi z @ cz2 => cz3 = cz2]])).
  {
    pose proof (Exp3_3 
      ([Alpha @ cz1 => [^z => Phi z @ cz2 => cz1 = cz2]])
      ([^z => Phi z @ cz2 => [^z => Psi z @ cz3 => cz2 = cz3]])
      ([Alpha @ cz1 => [^z => Psi z @ cz3 => cz1 = cz3]]))
      as Exp3_3.
    MP Exp3_3 S3.
    pose proof (Comm2_04
      ([Alpha @ cz1 => [^z => Phi z @ cz2 => cz1 = cz2]])
      ([^z => Phi z @ cz2 => [^z => Psi z @ cz3 => cz2 = cz3]])
      ([Alpha @ cz1 => [^z => Psi z @ cz3 => cz1 = cz3]]))
      as Comm2_04.
    now MP Comm2_04 Exp3_3.
  }
  assert (S5 : ([^z => Phi z @ cz1 => [^z => Psi z @ cz2 => cz1 = cz2]]
      ∧ [Alpha @ cz3 => [^z => Psi z @ cz2 => cz3 = cz2]])
    -> ([Alpha @ cz3 => [^z => Phi z @ cz1 => cz3 = cz1]])).
  {
    pose proof (n20_24 Psi Phi Falpha) as n20_24.
    now setoid_rewrite -> n20_21 in n20_24 at 3.
  }
  assert (S6 : [^z => Phi z @ cz1 => [^z => Psi z @ cz2 => cz1 = cz2]]
    -> ([Alpha @ cz3 => [^z => Psi z @ cz2 => cz3 = cz2]]
      -> [Alpha @ cz3 => [^z => Phi z @ cz1 => cz3 = cz1]])).
  {
    pose proof (Exp3_3
      ([^z => Phi z @ cz1 => [^z => Psi z @ cz2 => cz1 = cz2]])
      ([Alpha @ cz3 => [^z => Psi z @ cz2 => cz3 = cz2]])
      ([Alpha @ cz3 => [^z => Phi z @ cz1 => cz3 = cz1]])) 
      as Exp3_3.
    now MP Exp3_3 S5.
  }
  assert (S7 : [^z => Phi z @ cz1 => [^z => Psi z @ cz2 => cz1 = cz2]]
    -> ([Alpha @ cz3 => [^z => Phi z @ cz1 => cz3 = cz1]]
      <-> [Alpha @ cz3 => [^z => Psi z @ cz2 => cz3 = cz2]])).
  {
    (* simplification *)
    intro Hp.
    pose proof (S4 Hp) as S4.
    pose proof (S6 Hp) as S6.
    clear S1 S2 S3 S5.
    Conj_as S4 S6 C1.
    now Equiv C1.
  }
  assert (S8 : [^z => Phi z @ cz1 => [^z => Psi z @ cz2 => cz1 = cz2]]
    -> ([alpha @ cz3 => [^z => Phi z @ cz1 => cz3 = cz1]]
      <[- alpha -]> [alpha @ cz3 => [^z => Psi z @ cz2 => cz3 = cz2]])).
  {
    pose proof (n10_11_class Alpha
      (fun alpha => [^z => Phi z @ cz1 => [^z => Psi z @ cz2 => cz1 = cz2]]
        -> ([alpha @ cz3 => [^z => Phi z @ cz1 => cz3 = cz1]]
          <-> [alpha @ cz3 => [^z => Psi z @ cz2 => cz3 = cz2]])))
      as n10_11.
    MP n10_11 S7.
    now rewrite -> n10_21_class in n10_11.
  }
  assert (S9 : ([alpha @ cz1 => [^z => Phi z @ cz2 => cz1 = cz2]] <[- alpha -]>
      [alpha @ cz1 => [^z => Psi z @ cz3 => cz1 = cz3]])
    -> [^z => Phi z @ cz2 => [^z => Psi z @ cz3 => cz2 = cz3]]).
  {
    Conj_as S2 S8 C1.
    now Equiv C1.
  }
  exact S9.
Qed.

(* TODO in doc: the 1st step of this proof reveals some deeper notation consistency 
  issue... designing a custum representation of these symbols seems to be a interesting
  technical problem 
*)
Theorem n20_3 (X : Prop) (Psi : Prop -> Prop ) : 
  ([^ z => Psi z @ cz1 => X <class_in> cz1]) <-> Psi X.
Proof.
  assert (S1 : [^ z => Psi z @ cz1 => X <class_in> cz1]
    <-> ∃ Phi, (Psi y <[- y -]> Phi y) 
      ∧ (X <class_in> Phi)).
  {
    pose proof (n20_1 Psi (fun cz => X <class_in> cz)) as n20_1.
    now setoid_rewrite -> n4_21 in n20_1 at 2.
  }
  assert (S2 : [^ z => Psi z @ cz1 => X <class_in> cz1]
    <-> ∃ Phi, (Psi y <[- y -]> Phi y) ∧ Phi X).
  { now setoid_rewrite -> n20_02 in S1. }
  assert (S3 : [^ z => Psi z @ cz1 => X <class_in> cz1]
    <-> ∃ Phi, (Psi y <[- y -]> Phi y) ∧ Psi X).
  {
    (* TODO: reconstruct `∃` bottom-up *)
    (* setoid_rewrite -> n10_43 in S2. *)
    admit.
  }
  assert (S4 : [^ z => Psi z @ cz1 => X <class_in> cz1]
    <-> (∃ Phi, Psi y <[- y -]> Phi y) ∧ Psi X).
  {
    pose proof n10_35 as _n10_35.
    setoid_rewrite -> n4_3 in S3 at 2.
    setoid_rewrite -> n10_35_pred in S3.
    now setoid_rewrite <- n4_3 in S3 at 2.
  }
  assert (S5 : [^ z => Psi z @ cz1 => X <class_in> cz1]
    <-> Psi X).
  {
    (* unprovable?. *)
    pose proof n12_1.
    admit.
  }
  exact S5.
Admitted.

Theorem n20_31 (Psi Chi : Prop -> Prop) : 
  [^z => Psi z @ cz1 => [^z => Chi z @ cz2 => cz1 = cz2]]
  <-> (([^ z => Psi z @ cz1 => x <class_in> cz1])
    <[- x -]> [^ z => Chi z @ cz2 => x <class_in> cz2]).
Proof.
  pose proof (n20_15 Psi Chi) as n20_15.
  setoid_rewrite <- n20_3 in n20_15 at 3.
  setoid_rewrite <- n20_3 in n20_15 at 3.
  now rewrite -> n4_21 in n20_15.
Qed.

Theorem n20_32 (Phi : Prop -> Prop) :
  [^x => [^z => Phi z @ cz2 => x <class_in> cz2] @ cz1
    => [^z => Phi z @ cz2 => cz1 = cz2]].
Proof.
  pose proof n20_3 as n20_3.
  pose proof n20_15 as n20_15.
  (* TODO: bottom-up construct this in the future *)
Admitted.

(* NOTE: this proposition is explicitly passing in the `Alpha` as a class variable.
  In the proof we need to access its underlying function. might be tricky...
  TODO: resolve this issue in the future *)
Theorem n20_33 (FAlpha : Prop -> Prop) (Phi : Prop -> Prop) :
  let Alpha := (^z => FAlpha z) in
  [Alpha @ calpha => [^z => Phi z @ cz => calpha = cz]]
  <-> ([Alpha @ calpha => x <class_in> calpha] <[- x -]> Phi x).
Proof.
  (* TOOLS *)
  set (Alpha := (^z => FAlpha z)).
  (* ******** *)
  assert (S1 : [Alpha @ calpha => [^z => Phi z @ cz => calpha = cz]]
    <-> ([Alpha @ calpha => x <class_in> calpha] 
      <[- x -]> [^z => Phi z @ cz2 => x <class_in> cz2])).
  {
    pose proof n20_31 as n20_31.
    admit.
  }
  assert (S2 : [Alpha @ calpha => [^z => Phi z @ cz => calpha = cz]]
    <-> ([Alpha @ calpha => x <class_in> calpha] <[- x -]> Phi x)).
  { now setoid_rewrite -> n20_3 in S1. }
  exact S2.
Admitted.

Open Scope formal_impl.

Theorem n20_34 (X Y : Prop) :
  (X = Y) <-> ([alpha @ calpha => X <class_in> calpha]  
    -[ alpha ]> [alpha @ calpha => Y <class_in> calpha]).
Proof.
  assert (S1 : ([alpha @ calpha => X <class_in> calpha]  
      -[ alpha ]> [alpha @ calpha => Y <class_in> calpha])
    <-> ([^z => Phi z @ cz1 => X <class_in> cz1] 
      -[ Phi ]> [^z => Phi z @ cz1 => Y <class_in> cz1])).
  {
    pose proof (n4_2 ([alpha @ calpha => X <class_in> calpha]  
      -[ alpha ]> [alpha @ calpha => Y <class_in> calpha])) as n4_2.
    (* TODO: resolve the `∀ Phi` maybe with `replace` *)
    setoid_rewrite -> n20_07 in n4_2.
    (* 
    Definition n20_07 {A : Type} (X : A) (f : (A -> Prop) -> Prop) :
    ∀ (alpha : Class.t A), [alpha @ calpha => f calpha]
    = ∀ Phi : (A -> Prop), [^ z => Phi z @ cPhi => f cPhi].
    *)
    admit.
  }
  assert (S2 : ([alpha @ calpha => X <class_in> calpha]  
      -[ alpha ]> [alpha @ calpha => Y <class_in> calpha])
    <-> (Phi X -[ Phi ]> Phi Y)).
  {
    setoid_rewrite -> n20_3 in S1 at 1.
    now setoid_rewrite -> n20_3 in S1 at 1.
  }
  assert (S3 : ([alpha @ calpha => X <class_in> calpha]  
      -[ alpha ]> [alpha @ calpha => Y <class_in> calpha])
    <-> (X = Y)).
  { now rewrite <- n13_1 in S2. }
  (* simplification... *)
  symmetry.
  exact S3.
Admitted.

Theorem n20_35 (X Y : Prop) :
  (X = Y) <-> ([alpha @ calpha => X <class_in> calpha] 
    <[- alpha -]> [alpha @ calpha => Y <class_in> calpha]).
Proof.
  pose proof (n13_11 X Y) as n13_11.
  (* TODO: bottom-up construction *)
  pose proof n20_3 as n20_3.
Admitted.

(* TODO: figure a good way to provide `Alpha` with a function
  idea: maybe we will just never use `Alpha` directly? we can also try the `let` *)
Theorem n20_4 (Alpha : Class.t Prop) :
  ([Alpha @ calpha => [Cls @ Cls => calpha <class_in> Cls]]) <-> 
    (∃ (Phi : Order 1), [Alpha @ calpha => 
    [^z => Phi z @ cz => calpha = cz]]).
Proof.
  (* unprovable due to `Alpha` lacking of underlying function.
    TODO: we can require `Alpha` being passed in with underlying 
      function... *)
  pose proof n20_3 as n20_3.
  (* pose proof n20_03 as n20_03. *)
Admitted.

Theorem n20_41 (Psi : Prop -> Prop) : [^z => Psi z @ cz1 => 
  [Cls @ Cls => cz1 <class_in> Cls]].
Proof.
  pose proof n20_4 as n20_4.
  pose proof n20_151 as n20_151.
  (* TODO: figure out what does it mean *)
Admitted.

(* In this proof, `Psi` is associated with `alpha` in the text without being 
claimed explicitly
TODO: in the future, remove the `alpha` parameter
*)
Theorem n20_42 (Alpha : Class.t Prop) : [(^z => [Alpha @ calpha => z <class_in> calpha])
  @ cz => [Alpha @ calpha => cz = calpha]].
Proof.
  (* TOOLS *)
  set (X := Intro_individual "x").
  set (Psi := Intro_pred "Psi" 1).
  (* ******** *)
  assert (S1 : ([^z => Psi z @ cz => x <class_in> cz]) <[- x -]> Psi x).
  {
    pose proof (n20_3 X Psi) as n20_3.
    pose proof (n10_11 X (fun x =>
      (([^ z => Psi z @ cz1 => x <class_in> cz1]) ↔ Psi x))) 
      as n10_11.
    now MP n10_11 n20_3.
  }
  assert (S2 : [^x => [^z => Psi z @ cz1 => x <class_in> cz1] @ cz2 
    => [^x => Psi x @ cz3 => cz2 = cz3]]).
  {
    pose proof n20_15 as n20_15.
    admit.
  }
  (* TODO: rename the ^z => Psi z into alpha *)
  admit.
Admitted.

Theorem n20_43 (alpha beta : Class.t Prop) : 
  [alpha @ calpha => [beta @ cbeta => calpha = cbeta]]
    <-> ([alpha @ calpha => x <class_in> calpha] 
      <[- x -]> [beta @ cbeta => x <class_in> cbeta]).
Proof.
  (* TODO: alpha function conversion *)
  pose proof n20_31 as n20_31.
Admitted.

Open Scope debug_iota_description.

Theorem n20_5 (Phi Psi : Prop -> Prop) :
  [iota Phi | iotaPhi => [^z => Psi z @ cz1 => iotaPhi <class_in> cz1]]
  <-> [iota Phi | iotaPhi => Psi iotaPhi].
Proof.
  assert (S1 : [iota Phi | iotaPhi => [^z => Psi z @ cz1 => iotaPhi <class_in> cz1]]
    <-> (∃ c, (Phi x <[- x -]> (x = c)) ∧ [^z => Psi z @ cz1 => c <class_in> cz1])).
  { apply n14_1. }
  assert (S2 : [iota Phi | iotaPhi => [^z => Psi z @ cz1 => iotaPhi <class_in> cz1]]
    <-> (∃ c, (Phi x <[- x -]> (x = c)) ∧ Psi c)).
  { now setoid_rewrite -> n20_3 in S1 at 2. }
  assert (S3 : [iota Phi | iotaPhi => [^z => Psi z @ cz1 => iotaPhi <class_in> cz1]]
    <-> [iota Phi | iotaPhi => Psi iotaPhi]).
  { now setoid_rewrite <- n14_1 in S2. }
  exact S3.
Qed.

Theorem n20_51 (Phi : Prop -> Prop) (B : Prop) :
  [iota Phi | iotaPhi => iotaPhi = B]
  <-> ([iota Phi | iotaPhi => [alpha @ calpha => iotaPhi <class_in> calpha]]
    <[- alpha -]> [alpha @ calpha => B <class_in> calpha]).
Proof.
  (* TOOLS *)
  set (IPsi := Intro_pred "Psi" 1).
  set (Alpha := (^z => IPsi z)).
  (* ******** *)
  assert (S1 : ([iota Phi | iotaPhi => [^z => IPsi z @ cz1 => iotaPhi <class_in> cz1]]
      <-> [^z => IPsi z @ cz1 => B <class_in> cz1])
    <-> ([iota Phi | iotaPhi => IPsi iotaPhi] <-> IPsi B)).
  {
    pose proof (n20_5 Phi IPsi) as n20_5.
    pose proof (n20_3 B IPsi) as n20_3.
    pose proof n4_86 as _n4_86.
    pose proof (n4_86
      ([iota Phi | iotaPhi => [^z => IPsi z @ cz1 => iotaPhi <class_in> cz1]])
      ([iota Phi | iotaPhi => IPsi iotaPhi])
      ([^ z => IPsi z @ cz1 => B <class_in> cz1])) 
      as n4_86.
    MP n4_86 n20_5.
    now setoid_rewrite -> n20_3 in n4_86 at 2.
  }
  (* NOTE: here is an interesting conflict: we are generalizing both on a class made
    out of `Psi` and `Psi` itself in different parts of a proposition *)
  assert (S2 : ([iota Phi | iotaPhi => [alpha @ calpha => iotaPhi <class_in> calpha]]
      <[- alpha -]> [alpha @ calpha => B <class_in> calpha])
    <-> ([iota Phi | iotaPhi => Psi iotaPhi] <[- Psi -]> Psi B)).
  {
    (* unprovable: we're missing theorem of the form of
      `(∀ x, Phi x <-> P) -> ((∀ x, Phi x) <-> P)`
      destructing the equivalence does the work, but become extremely tedious *)
    pose proof (n10_11_class Alpha (fun alpha =>
      ([iota Phi | iotaPhi => [alpha @ cz1 => iotaPhi <class_in> cz1]]
        <-> [alpha @ cz1 => B <class_in> cz1])
      <-> ([iota Phi | iotaPhi => IPsi iotaPhi] <-> IPsi B))) as n10_11_class.
    MP n10_11_class S1.
    pose proof n10_11_pred as _n10_11_pred.
    admit.
  }
  assert (S3 : ([iota Phi | iotaPhi => [alpha @ calpha => iotaPhi <class_in> calpha]]
      <[- alpha -]> [alpha @ calpha => B <class_in> calpha])
    <-> [iota Phi | iotaPhi => iotaPhi = B]).
  { now setoid_rewrite <- n14_17 in S2. }
  assert (S4 : [iota Phi | iotaPhi => iotaPhi = B]
    <-> ([iota Phi | iotaPhi => [alpha @ calpha => iotaPhi <class_in> calpha]]
      <[- alpha -]> [alpha @ calpha => B <class_in> calpha])).
  { now rewrite -> n4_21 in S3. }
  exact S4.
Admitted.

Theorem n20_52 (Phi : Prop -> Prop) : [iotaE Phi]
  <-> (∃ b, [iota Phi | iotaPhi => [alpha @ calpha =>
    (iotaPhi <class_in> calpha)]]
    <[- alpha -]> [alpha @ calpha => b <class_in> calpha]).
Proof.
  (* TOOLS *)
  set (B := Intro_individual "b").
  (* ******** *)
  assert (S1 : (∃ b : Prop, [iota Phi | iotaPhi => iotaPhi = b])
    <-> ∃ b : Prop, ([iota Phi | iotaPhi => [alpha @ calpha => 
      iotaPhi <class_in> calpha]] <[- alpha -]> 
        [alpha @ calpha => b <class_in> calpha])).
  {
    pose proof (n20_51 Phi B) as n20_51.
    pose proof (n10_11 B (fun b =>
      ([iota Phi | iotaPhi => iotaPhi = b])
        ↔ ([iota Phi | iotaPhi => [alpha @ calpha => iotaPhi <class_in> calpha]])
          <[- alpha -]>([alpha @ calpha => b <class_in> calpha]))) 
      as n10_11.
    MP n10_11 n20_51.
    pose proof (n10_281 
      (fun b => [iota Phi | iotaPhi => iotaPhi = b])
      (fun b => ([iota Phi | iotaPhi => [alpha @ calpha => iotaPhi <class_in> calpha]])
        <[- alpha -]> ([alpha @ calpha => b <class_in> calpha])))
      as n10_281.
    now MP n10_281 n10_11.
  }
  assert (S2 : [iotaE Phi]
    <-> (∃ b, [iota Phi | iotaPhi => [alpha @ calpha =>
      (iotaPhi <class_in> calpha)]]
      <[- alpha -]> [alpha @ calpha => b <class_in> calpha])).
  { now rewrite <- n14_204 in S1. }
  exact S2.
Qed.

(* Should Phi here be a function of order 1..? *)
Theorem n20_53 (FAlpha : Prop -> Prop) (Phi : (Prop -> Prop) -> Prop) : 
  let Alpha := (^z => FAlpha z) in
  ([beta @ cbeta => [Alpha @ calpha => cbeta = calpha]]
    -[ beta ]> [beta @ cbeta => Phi cbeta])
      <-> [Alpha @ calpha => Phi calpha].
Proof.
  (* TOOLS *)
  set (FBeta := Intro_pred "beta" 1).
  set (Alpha := ^z => FAlpha z).
  set (Beta := ^z => FBeta z).
  (* ******** *)
  assert (S1 : ([beta @ cbeta => [Alpha @ calpha => cbeta = calpha]]
      -[ beta ]> [beta @ cbeta => Phi cbeta])
    -> ([Alpha @ calpha => calpha = calpha]
      -> [Alpha @ calpha => Phi calpha])).
  {
    setoid_rewrite -> class_scope_eq.
    apply (n10_1_class (fun beta =>
      ([beta @ cbeta => [Alpha @ calpha => cbeta = calpha]]
        -> [beta @ cbeta => Phi cbeta])) Alpha).
  }
  assert (S2 : ([beta @ cbeta => [Alpha @ calpha => cbeta = calpha]]
      -[ beta ]> [beta @ cbeta => Phi cbeta])
    -> [Alpha @ calpha => Phi calpha]).
  {
    (* simplification *)
    intro Hp.
    pose proof (S1 Hp) as S1.
    pose proof (n20_2 FAlpha) as n20_2.
    rewrite <- class_scope_eq in n20_2.
    now MP S1 n20_2.
  }
  assert (S3 : [Beta @ cbeta => [Alpha @ calpha => cbeta = calpha]]
    -> ([Alpha @ calpha => Phi calpha] -> [Beta @ cbeta => Phi cbeta])).
  {
    (* *20.21 ignored *)
    pose proof (n20_18 FBeta FAlpha Phi) as n20_18.
    (* simplification... *)
    intro Hp.
    pose proof (n20_18 Hp) as n20_18.
    rewrite -> n4_21 in n20_18.
    now destruct n20_18.
  }
  assert (S4 : [Alpha @ calpha => Phi calpha]
    -> ([Beta @ cbeta => [Alpha @ calpha => cbeta = calpha]]
      -> [Beta @ cbeta => Phi cbeta])).
  {
    pose proof (Comm2_04
      ([Beta @ cbeta => [Alpha @ calpha => cbeta = calpha]])
      ([Alpha @ calpha => Phi calpha])
      ([Beta @ cbeta => Phi cbeta])) as Comm2_04.
    now MP Comm2_04 S3.
  }
  assert (S5 : [Alpha @ calpha => Phi calpha]
    -> ([beta @ cbeta => [Alpha @ calpha => cbeta = calpha]]
      -[ beta ]> [beta @ cbeta => Phi cbeta])).
  {
    pose proof (n10_11_class Beta (fun beta =>
      [Alpha @ calpha => Phi calpha]
        -> ([beta @ cbeta => [Alpha @ calpha => cbeta = calpha]]
          -> [beta @ cbeta => Phi cbeta]))) as n10_11.
    MP n10_11 S4.
    now rewrite -> n10_21_class in n10_11.
  }
  assert (S6 : (([beta @ cbeta => [Alpha @ calpha => cbeta = calpha]]) 
    -[ beta ]> [beta @ cbeta => Phi cbeta]) 
      <-> [Alpha @ calpha => Phi calpha]).
  {
    Conj_as S2 S5 C1.
    now Equiv C1.
  }
  exact S6.
Qed.

Theorem n20_54 (FAlpha : Prop -> Prop) (Phi : (Prop -> Prop) -> Prop) : 
  let Alpha := (^z => FAlpha z) in (∃ beta, 
    [beta @ cbeta => [Alpha @ calpha => cbeta = calpha]] ∧ [beta @ cbeta => Phi cbeta])
      <-> [Alpha @ calpha => Phi calpha].
Proof.
  (* TOOLS *)
  set (Alpha := ^z => FAlpha z).
  set (FBeta := Intro_pred "beta" 1).
  set (Beta := ^z => FBeta z).
  (* ******** *)
  assert (S1 : ([beta @ cbeta => [Alpha @ calpha => cbeta = calpha]] 
    ∧ [beta @ cbeta => Phi cbeta]) -[ beta ]> [Alpha @ calpha => Phi calpha]).
  {
    (* unprovable: it seems to be not fit. TODO: figure out what is going on
    in the future *)
    admit.
  }
  assert (S2 : (∃ beta, [beta @ cbeta => [Alpha @ calpha => cbeta = calpha]]
      ∧ [beta @ cbeta => Phi cbeta])
    -> [Alpha @ calpha => Phi calpha]).
  { now rewrite -> n10_23_class in S1. }
  assert (S3 : [Alpha @ calpha => Phi calpha]
    -> ([Alpha @ calpha => calpha = calpha] 
      ∧ [Alpha @ calpha => Phi calpha])).
  {
    setoid_rewrite -> class_scope_eq.
    pose proof (n20_2 FAlpha) as n20_2.
    pose proof (n3_2
      ([Alpha @ calpha1 => [Alpha @ calpha2 => calpha1 = calpha2]])
      ([Alpha @ calpha => Phi calpha])) as n3_2.
    now MP n3_2 n20_2.
  }
  assert (S4 : [Alpha @ calpha => Phi calpha]
    -> (∃ beta, [beta @ cbeta => 
        [Alpha @ calpha => cbeta = calpha]]
      ∧ [beta @ cbeta => Phi cbeta])).
  {
    (* NOTE: we dont pick all `alpha`s in this step *)
    setoid_rewrite -> class_scope_eq in S3.
    pose proof (n10_24_class (fun beta => [beta @ cbeta => 
      [Alpha @ calpha => cbeta = calpha]]
      ∧ [beta @ cbeta => Phi cbeta])
      Alpha) as n10_24.
    now Syll_as S3 n10_24 S4.
  }
  assert (S5 : (∃ beta, [beta @ cbeta => [Alpha @ calpha => cbeta = calpha]] 
    ∧ [beta @ cbeta => Phi cbeta]) 
      <-> [Alpha @ calpha => Phi calpha]).
  {
    Conj_as S2 S4 C1.
    now Equiv C1.
  }
  exact S5.
Admitted.

(* TODO: redesign n20_55 *)
(* I'm quite proud that the class notation can work nicely together with iotas *)
Theorem n20_55 (Phi : Prop -> Prop) : 
  [iota (fun alpha => ([alpha @ calpha => x <class_in> calpha]) <[- x -]> Phi x)
    | iotaalpha => [^z => Phi z @ cz1 => [iotaalpha @ cz2 => cz1 = cz2]]].
Proof.
  (* TOOLS *)
  set (FAlpha := Intro_pred "alpha" 1).
  set (Alpha := ^z => FAlpha z).
  (* ******** *)
  assert (S1 : ([alpha @ calpha => x <class_in> calpha]
      <[- x -]> Phi x)
    <[- alpha -]> ([alpha @ calpha => [^z => Phi z @ cz => calpha = cz]])).
  {
    pose proof (n20_33 FAlpha Phi) as n20_33.
    rewrite -> n4_21 in n20_33.
    pose proof (n10_11_class Alpha (fun alpha =>
      ([alpha @ calpha => x <class_in> calpha]  <[- x -]> Phi x)
      <-> ([alpha @ calpha => [^z => Phi z @ cz => calpha = cz]])))
      as n10_11.
    now MP n10_11 n20_33.
  }
  assert (S2 : ∃ beta, (([alpha @ calpha => x <class_in> calpha]
        <[- x -]> Phi x)
      <[- alpha -]> [alpha @ calpha => [beta @ cbeta => calpha = cbeta]])
    ∧ [^z => Phi z @ cz => [beta @ cbeta => cz = cbeta]]).
  {
    pose proof (n20_54 Phi (fun Phi =>
      ([alpha @ calpha => x <class_in> calpha]
        <[- x -]> Phi x)
      <[- alpha -]> ([alpha @ calpha => [^z => Phi z @ cz => calpha = cz]])
      )) as n20_54.
    simpl in n20_54.
    setoid_rewrite -> n4_3 in n20_54 at 2.
    setoid_rewrite -> n20_21_alt in n20_54 at 2.
    (* TODO:
    [alpha @ cz => Phi (Psi cz)]
    <->
    Phi ([alpha @ cz => Psi cz])
    *)
    (* rewrite <- n20_54 in S1. *)
    admit.
  }
  assert (S3 : [iota (fun alpha => ([alpha @ calpha => x <class_in> calpha]) 
    <[- x -]> Phi x) | iotaalpha => 
    [^z => Phi z @ cz1 => [iotaalpha @ cz2 => cz1 = cz2]]]).
  {
    simpl in S2.
    (* TODO: make a class specific vertsion for n14_1 *)
    pose proof n14_1 as n14_1.
    admit.
  }
  exact S3.
Admitted.

(* TODO: this might have some severe denotational problem about what kind of function
should we use for the iota Phi... *)
Theorem n20_56 (Phi : Prop -> Prop) : [iotaE (fun alpha : Class.t Prop =>
  [alpha @ calpha => x <class_in> calpha] <[- x -]> Phi x)].
Proof.
  pose proof (n20_55 Phi) as n20_55.
  pose proof (n14_21_pred 
    (fun falpha => 
      let alpha := (^z => falpha z) in
      ([alpha @ calpha => x <class_in> calpha] <[- x -]> Phi x))
    (fun iota => [^z => Phi z @ cz => cz = iota]))
    as n14_21.
  (* unprovable: n20_55 doesn't have the correct form
  TODO: redesign n20_55 in the future. Or is *20.55 ill desigend? Since it
  is a new notation with new interpretation but without equipping with 
  notation supps *)
  admit.
Admitted.

Theorem n20_57 (Phi : Prop -> Prop) (f g : (Prop -> Prop) -> Prop) : 
  [iota (fun alpha => [alpha @ calpha => f calpha]) | iotaalpha =>
    [(^z => Phi z) @ cz => [iotaalpha @ ciotaalpha => cz = ciotaalpha]]]
  -> ([^ z => Phi z @ cz => g cz] <-> [iota (fun alpha => [alpha @ calpha => f calpha]) 
    | iotaalpha => [iotaalpha @ ciotaalpha => g ciotaalpha]]).
Proof.
  assert (S1 : [iota (fun alpha => [alpha @ calpha => f calpha]) | iotaalpha =>
    [(^z => Phi z) @ cz => [iotaalpha @ ciotaalpha => cz = ciotaalpha]]]
    <-> (exists beta, ([alpha @ calpha => f calpha] <[- alpha -]> 
      [alpha @ calpha => [beta @ cbeta => calpha = cbeta]])
      /\ [^z => Phi z @ cz => [beta @ cbeta => cz = cbeta]])).
  { apply n14_1_class. }
  assert (S2 : [iota (fun alpha => [alpha @ calpha => f calpha]) | iotaalpha =>
    [(^z => Phi z) @ cz => [iotaalpha @ ciotaalpha => cz = ciotaalpha]]]
    <-> ([alpha @ calpha => f calpha] 
      <[- alpha -]> [alpha @ calpha => [^z => Phi z @ cz => calpha = cz]])).
  {
    setoid_rewrite -> n20_21_alt in S1 at 2.
    (* TODO: is there some rule to extend the n20_54? *)
    (* setoid_rewrite -> n20_54 in S1 at 2. *)
    admit.
  }
  assert (S3 : [iota (fun alpha => [alpha @ calpha => f calpha]) | iotaalpha =>
    [iotaalpha @ ciotaalpha => g ciotaalpha]]
    <-> (exists beta, ([alpha @ calpha => f calpha] 
        <[- alpha -]> [alpha @ calpha => [beta @ cbeta => calpha = cbeta]])
      /\ [beta @ cbeta => g cbeta])).
  { apply n14_1_class. }
  assert (S4 : [iota (fun alpha => [alpha @ calpha => f calpha]) | iotaalpha =>
      [(^z => Phi z) @ cz => [iotaalpha @ ciotaalpha => cz = ciotaalpha]]]
    -> ([iota (fun alpha => [alpha @ calpha => f calpha]) | iotaalpha =>
      [iotaalpha @ ciotaalpha => g ciotaalpha]]
      <-> (exists beta, ([alpha @ calpha => [^z => Phi z @ cz => calpha = cz]]
        <[- alpha -]> [alpha @ calpha => [beta @ cbeta => calpha = cbeta]])
        /\ [beta @ cbeta => g cbeta]))).
  {
    (* simplification *)
    intro Hp.
    destruct S2 as [S2 _].
    pose proof (S2 Hp) as S2.
    now setoid_rewrite -> S2 in S3 at 2.
  }
  assert (S5 : [iota (fun alpha => [alpha @ calpha => f calpha]) | iotaalpha =>
      [(^z => Phi z) @ cz => [iotaalpha @ ciotaalpha => cz = ciotaalpha]]]
    -> ([iota (fun alpha => [alpha @ calpha => f calpha]) | iotaalpha =>
        [iotaalpha @ ciotaalpha => g ciotaalpha]]
      <-> (exists beta, [^z => Phi z @ cz => 
        [beta @ cbeta => cz = cbeta]] 
        /\ [beta @ cbeta => g cbeta]))).
  {
    setoid_rewrite -> n20_21_alt in S4 at 2.
    now setoid_rewrite <- n13_183_class in S4.
  }
  assert (S6 : [iota (fun alpha => [alpha @ calpha => f calpha]) | iotaalpha =>
      [(^z => Phi z) @ cz => [iotaalpha @ ciotaalpha => cz = ciotaalpha]]]
    -> ([iota (fun alpha => [alpha @ calpha => f calpha]) | iotaalpha =>
      [iotaalpha @ ciotaalpha => g ciotaalpha]]
      <-> [^z => Phi z @ cz => g cz])).
  {
    setoid_rewrite -> n20_21_alt in S5 at 2.
    now setoid_rewrite -> n20_54 in S5.
  }
  assert (S7 : [iota (fun alpha => [alpha @ calpha => f calpha]) | iotaalpha =>
      [(^z => Phi z) @ cz => [iotaalpha @ ciotaalpha => cz = ciotaalpha]]]
    -> ([^ z => Phi z @ cz => g cz] <-> [iota (fun alpha => [alpha @ calpha => f calpha]) 
      | iotaalpha => [iotaalpha @ ciotaalpha => g ciotaalpha]])).
  { now setoid_rewrite -> n4_21 in S6 at 1. }
  exact S7.
Admitted.

Theorem n20_58 (Phi : Prop -> Prop) :
  [iota (fun alpha => [alpha @ calpha => [^z => Phi z @ cz => calpha = cz]]) 
    | iotaalpha => [^z => Phi z @ cz => [iotaalpha @ ciotaalpha =>
      cz = ciotaalpha]]].
Proof.
  (* TOOLS *)
  set (FAlpha := Intro_pred "alpha" 1).
  set (Alpha := ^z => FAlpha z).
  (* ******** *)
  assert (S1 : [alpha @ calpha => [^z => Phi z @ cz => calpha = cz]]
    <[- alpha -]> [alpha @ calpha => [^z => Phi z @ cz => calpha = cz]]).
  {
    pose proof (n4_2 ([Alpha @ calpha => [^z => Phi z @ cz => calpha = cz]])) 
      as n4_2.
    Print n10_11_class.
    pose proof (n10_11_class Alpha (fun alpha => 
      [alpha @ calpha => [^z => Phi z @ cz => calpha = cz]]
      <-> [alpha @ calpha => [^z => Phi z @ cz => calpha = cz]]))
      as n10_11.
    now MP n10_11 n4_2.
  }
  assert (S2 : exists beta, ([alpha @ calpha => 
    [^z => Phi z @ cz => calpha = cz]] 
      <[- alpha -]> [alpha @ calpha => [beta @ cbeta => calpha = cbeta]])
    /\ [^z => Phi z @ cz => [beta @ cbeta => cz = cbeta]]).
  {
    (* NOTE: i think the proof order is wrong. we should have first constructed
      the `exists` and then generalize the `alpha`. Otherwise it's making things
      so tedious that we will break everything down to reconstruct again. *)
    (* TODO: I want to instantiate S1 again and find another way to construct the 
      proof *)
    (* setoid_rewrite <- n20_54 in S1. *)
    admit.
  }
  assert (S3 : [iota (fun alpha => [alpha @ calpha => [^z => Phi z @ cz => calpha = cz]]) 
    | iotaalpha => [^z => Phi z @ cz => [iotaalpha @ ciotaalpha =>
      cz = ciotaalpha]]]).
  { now rewrite <- n14_1_class in S2. }
  exact S3.
Admitted.

(* NOTE: 
  1. notice that we can see `Psi z^` being used in the text to represent
  the function itself 
  2. (p.194) "When there are no contrary, descriptions have larger scope
  than classes." The contrary can be witnessed, exclusively, in this 
  theoremby, as the first step is taking *20.1 to unfolding the definition *)
Theorem n20_59 (Phi : Prop -> Prop) (f : (Prop -> Prop) -> Prop) :
  [^z => Phi z @ cz => [iota (fun alpha => [alpha @ calpha => f calpha])
    | iotaalpha => [iotaalpha @ ciotaalpha => cz = ciotaalpha]]]
  <->
  [iota (fun alpha => [alpha @ calpha => f calpha]) | iotaalpha => 
    [iotaalpha @ ciotaalpha => 
      [^z => Phi z @ cz => ciotaalpha = cz]]].
Proof.
  assert (S1 : [^z => Phi z @ cz => [iota (fun alpha => [alpha @ calpha => f calpha])
    | iotaalpha => [iotaalpha @ ciotaalpha => cz = ciotaalpha]]]
    <-> (exists Psi, (Phi x <[- x -]> Psi x)
      /\ [iota (fun alpha => [alpha @ calpha => f calpha]) 
        | iotaalpha => [iotaalpha @ ciotaalpha =>
          Psi = ciotaalpha]])).
  {
    pose proof (n20_1 Phi (fun zPsi =>
      [iota (fun alpha => [alpha @ calpha => f calpha])
      | iotaalpha => [iotaalpha @ ciotaalpha => zPsi = ciotaalpha]]
    )) as n20_1.
    now setoid_rewrite -> n4_21 in n20_1 at 2.
  }
  assert (S2 : [^z => Phi z @ cz => [iota (fun alpha => [alpha @ calpha => f calpha])
    | iotaalpha => [iotaalpha @ ciotaalpha => cz = ciotaalpha]]]
    <-> (exists Psi, (Phi x <[- x -]> Psi x)
      /\ [iota (fun alpha => [alpha @ calpha => f calpha]) 
        | iotaalpha => [iotaalpha @ ciotaalpha =>
          ciotaalpha = Psi]])).
  { now setoid_rewrite -> n14_13_class_alt in S1. }
  assert (S3 : [^z => Phi z @ cz => [iota (fun alpha => [alpha @ calpha => f calpha])
    | iotaalpha => [iotaalpha @ ciotaalpha => cz = ciotaalpha]]]
    <-> [iota (fun alpha => [alpha @ calpha => f calpha]) | iotaalpha => 
      [iotaalpha @ ciotaalpha => 
        [^z => Phi z @ cz => ciotaalpha = cz]]]).
  {
    setoid_rewrite -> n4_21 in S2 at 2.
    setoid_rewrite <- n20_1 in S2.
    pose proof (iota_class_scope_eq 
      (^z => Phi z) f
      (fun ciotaalpha cAlpha => ciotaalpha = cAlpha)) 
      as iota_class_scope_eq.
      simpl in iota_class_scope_eq, S2.
    now setoid_rewrite -> (iota_class_scope_eq) in S2.
  }
  exact S3.
Qed.

Theorem n20_6 (f : (Prop -> Prop) -> Prop) :
  ∃ alpha, [alpha @ calpha => f calpha]
  <-> ~ (∀ alpha, [alpha @ calpha => f calpha]).
Proof.
Admitted.

Theorem n20_61 (f : (Prop -> Prop) -> Prop) (beta : Class.t Prop) :
  (∀ alpha, [alpha @ calpha => f calpha])
  -> [beta @ cbeta => f cbeta].
Proof.
Admitted.

(* *20.62 : type formation rule for `∀ alpha` *)
Theorem n20_63 (P : Prop) (f : (Prop -> Prop) -> Prop) :
  (∀ alpha, P ∨ [alpha @ calpha => f calpha]) 
  -> (P ∨ ∀ alpha, [alpha @ calpha => f calpha]).
Proof.
Admitted.

(* *20.631 - 633: omitted, other typing rules... TODO: fill in the future *)

Theorem n20_64 (f g : (Prop -> Prop) -> Prop) (beta : Class.t Prop) : 
  ((∀ alpha, [alpha @ calpha => f calpha]) 
    ∧ (∀ alpha, [alpha @ calpha => g calpha]))
  -> ((∀ beta, [beta @ cbeta => f cbeta])
    ∧ (∀ beta, [beta @ cbeta => g cbeta])).
Proof.
Admitted.

(* Another analogue to *12.1. Same as all above, we cannot formalize this for now *)
Theorem n20_7 (f : (Prop -> Prop) -> Prop) :
  ∃ (g : (Prop -> Prop) -> Prop), [alpha @ calpha => f calpha] 
    <[- alpha -]> [alpha @ calpha => g calpha].
Proof.
Admitted.

Theorem n20_701 (Phi : Prop -> Prop) (f : (Prop -> Prop) -> Prop -> Prop) :
  ∃ (g : (Prop -> Prop) -> Prop -> Prop), ([^z => Phi z @ cz => f cz x]
    <[- (Phi : Prop -> Prop) (x : Prop) -]> [^z => Phi z @ cz => g cz x]).
Proof.
Admitted.

Theorem n20_702 (f : Prop -> (Prop -> Prop) -> Prop) :
  ∃ (g : Prop -> (Prop -> Prop) -> Prop), ([^z => Phi z @ cz => f x cz]
    <[- (Phi : Prop -> Prop) (x : Prop) -]> [^z => Phi z @ cz => g x cz]).
Proof.
Admitted.

Theorem n20_703 (f : (Prop -> Prop) -> (Prop -> Prop) -> Prop) :
  ∃ (g : (Prop -> Prop) -> (Prop -> Prop) -> Prop), ([^z => Phi z @ cz1 => 
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
  (Phi A ∨ (~ Phi A)) -> [^x => (Phi x ∨ (~ Phi x)) @ cx1 =>
    [^x => (x = A ∨ (~ (x = A))) @ cx2 => cx1 = cx2]].
Proof.
Admitted.

Theorem n20_81 (Phi Psi : Prop -> Prop) (A : Prop) :
  ((Phi A ∨ (~ Phi A)) ∧ (Psi A ∨ (~ Psi A)))
  -> [^x => Phi x ∨ (~ Phi x) @ cx1 => [
    ^x => Psi x ∨ (~ Psi x) @ cx2 => cx1 = cx2]].
Proof.
Admitted.

Close Scope formal_equiv.
Close Scope formal_impl.
Close Scope debug_class.
