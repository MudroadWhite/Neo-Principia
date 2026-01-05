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

Require Import Logic.FunctionalExtensionality.

(* TODO: How does the iota description work-

*)

(* TODO: make the definitions into a notation in the future *)
(* Declare Scope single_description. *)

Open Scope single_app_equiv.

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
  larger scope than outer function. This variant will be proven later unecessary. 

  The original definition depends on `iota_f2`. The function `iota_f` here, 
  provided with parameters, gets a similar role to the idea of scope
*)
Definition iota_f2_1 
  (s1 s2 : string)
  (Phi Psi : Prop -> Prop)
  (f : Prop -> Prop -> Prop) :=
  iota_f s2 Psi
    (fun c => iota_f s1 Phi
      (fun b => f (Iota s1 b) (Iota s2 c))).

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

Definition n14_01 (s : string) (Phi Psi : Prop -> Prop) : 
  (iota_f s Phi Psi) = exists b, (Phi x <[- x -]> (x = b)) /\ Psi b. 
Admitted.

(* TODO: check if iota_p and *14.02 is correctly defined *)
Definition n14_02 (E : Predicate 1) (Phi : Prop -> Prop) :
  (iota_p E Phi) = exists b, (Phi x <[- x -]> (x = b)). 
Admitted.

(*  *)
Definition n14_03 (s1 s2 : string) (Phi Psi : Prop -> Prop) (f : Prop -> Prop -> Prop) :
  (iota_f2 s1 s2 Phi Psi f) = 
    iota_f s1 Phi 
    (fun b => iota_f s2 Psi 
      (fun c => f (Iota s1 b) (Iota s2 c))).
  (* exists b, (Phi x <[- x -]> (x = b)) 
    /\ ((exists c, Psi x <[- x -]> (x = c) /\ f b c)). *)
Admitted.

Definition n14_04 (s1 s2 : string) (Phi Psi : Prop -> Prop) (f : Prop -> Prop -> Prop) : 
  (iota_f2_1 s2 s1 Psi Phi f) = iota_f2 s2 s1 Psi Phi (fun x y => f y x).
Admitted.

Theorem n14_1 (s : string) (Phi Psi : Prop -> Prop) : (iota_f s Phi Psi) <-> 
  exists b, (Phi x <[- x -]> (x = b)) /\ Psi b.
Proof.
  pose proof (n4_2 (iota_f s Phi Psi)) as n4_2.
  now rewrite -> n14_01 in n4_2 at 2.
Qed.

(* The equivalent with n14_1, with scope notation in its original 
  representation omitted  *)
Theorem n14_101 (s : string) (Phi Psi : Prop -> Prop) : (iota_f s Phi Psi) <-> 
  exists b, (Phi x <[- x -]> (x = b)) /\ Psi b.
Proof.
  exact (n14_1 s Phi Psi).
Qed.

Theorem n14_11 (E : Predicate 1) (Phi : Prop -> Prop) : 
  (iota_p E Phi) <-> (exists b, Phi x <[- x -]> (x = b)).
Proof.
  pose proof (n4_2 (iota_p E Phi)) as n4_2.
  now rewrite -> n14_02 in n4_2 at 2.
Qed.

Theorem n14_111 (s1 s2 : string) (Phi Psi : Prop -> Prop) 
  (f : Prop -> Prop -> Prop) :
  (iota_f2_1 s2 s1 Psi Phi f) <-> (exists b c, 
    (Phi x <[- x -]> (x = b)) /\ (Psi x <[- x -]> (x = c)) /\ (f b c)).
Proof.
  assert (S1 : iota_f2_1 s2 s1 Psi Phi f ↔ 
    iota_f s2 Psi 
      (fun c => iota_f s1 Phi 
        (fun b => f (Iota s1 b) (Iota s2 c)))).
  {
    pose proof (n4_2 (iota_f2_1 s2 s1 Psi Phi f)) as n4_2.
    rewrite -> n14_04 in n4_2 at 2.
    now rewrite -> (n14_03 s2 s1) in n4_2.
  }
  assert (S2 : iota_f2_1 s2 s1 Psi Phi f <-> 
    (iota_f s2 Psi (fun c =>
      exists b, (Phi x <[- x -]> (x = b)) /\ f b c))).
  {
    replace (λ c : Prop, iota_f s1 Phi (λ b : Prop, f (Iota s1 b) (Iota s2 c)))
      with (λ c : Prop, iota_f s1 Phi (λ b : Prop, f b c))
      in S1 by reflexivity.
    (* Simplification: this place needs functional extentionality for our designed 
    notation of iota. Seems like the only way to survive *)
    assert (S1_1:
      (λ c : Prop, iota_f s1 Phi (λ b : Prop, f b c))
      =
      (λ c : Prop, (exists b, (Phi x <[- x -]> (x = b)) /\ f b c))).
    {
      extensionality c. (* function extentionality *)
      pose proof (n14_1 s1 Phi (fun b => f b c)) as n14_1.
      apply propositional_extensionality.
      exact n14_1.
    }
    now rewrite -> S1_1 in S1.
  }
  assert (S3 : iota_f2_1 s2 s1 Psi Phi f <-> 
    (exists c, (Psi x <[- x -]> (x = c)) 
    /\ exists b, (Phi x <[- x -]> (x = b)) /\ f b c)).
  { now rewrite -> n14_1 in S2. }
  assert (S4 : iota_f2_1 s2 s1 Psi Phi f <-> 
    (exists b c, (Phi x <[- x -]> (x = b)) /\ (Psi x <[- x -]> (x = c))
      /\ f b c)).
  {
    pose proof (n11_55
      (fun c => (Psi x <[- x -]> (x = c)))
      (fun c b => ( Phi x<[- x -]> (x = b)) ∧ f b c)
    ) as n11_55.
    rewrite <- n11_55 in S3.
    (* We can see that there are some trivial steps that still need to be
    finished... *)
    pose proof (n11_42
      (fun x y => ( Psi x0<[-x0-]>x0 = x ))
      (fun x y => ( Phi x0<[-x0-]>x0 = y ) ∧ f y x)
    ) as n11_42. simpl in n11_42.
    (* rewrite -> n11_42 in S3. *)
    pose proof n11_58 as n11_58.
    admit.
  }
  exact S4.
Admitted.

Theorem n14_112 (s1 s2 : string) (Phi Psi : Prop -> Prop) 
  (f : Prop -> Prop -> Prop) : 
  (iota_f2 s1 s2 Phi Psi f) <-> exists b c, 
    (Phi x <[- x -]> x = b) /\ (Psi x <[- x -]> x = c) /\ f b c.
Admitted.

Theorem n14_113 : Set. Admitted.

Theorem n14_12 : Set. Admitted.

Theorem n14_121 : Set. Admitted.

Theorem n14_122 : Set. Admitted.

Theorem n14_123 : Set. Admitted.

Theorem n14_124 : Set. Admitted.

Theorem n14_13 : Set. Admitted.

Theorem n14_131 : Set. Admitted.

Theorem n14_131_alt : Set. Admitted.

Theorem n14_14 : Set. Admitted.

Theorem n14_142 : Set. Admitted.

Theorem n14_144 : Set. Admitted.

Theorem n14_145 : Set. Admitted.

Theorem n14_15 : Set. Admitted.

Theorem n14_16 : Set. Admitted.

Theorem n14_17 : Set. Admitted.

Theorem n14_171 : Set. Admitted.

Theorem n14_18 : Set. Admitted.

Theorem n14_2 : Set. Admitted.

Theorem n14_201 : Set. Admitted.

Theorem n14_202 : Set. Admitted.

Theorem n14_203 : Set. Admitted.

Theorem n14_204 : Set. Admitted.

Theorem n14_205 : Set. Admitted.

Theorem n14_21 : Set. Admitted.

Theorem n14_22 : Set. Admitted.

Theorem n14_23 : Set. Admitted.

Theorem n14_24 : Set. Admitted.

Theorem n14_241 : Set. Admitted.

Theorem n14_242 : Set. Admitted.

Theorem n14_25 : Set. Admitted.

Theorem n14_26 : Set. Admitted.

Theorem n14_27 : Set. Admitted.

Theorem n14_271 : Set. Admitted.

Theorem n14_28 : Set. Admitted.

Theorem n14_3 : Set. Admitted.

Theorem n14_31 : Set. Admitted.

Theorem n14_32 : Set. Admitted.

Theorem n14_33 : Set. Admitted.

Theorem n14_331 : Set. Admitted.

Theorem n14_332 : Set. Admitted.

Theorem n14_34 : Set. Admitted.

Close Scope single_app_equiv.