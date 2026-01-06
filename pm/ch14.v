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

(* 
The decription, or I would more likely to call it the iota operator, works quite differently 
because it technically requires you to be passed into a propositional function like normal
parameters, but unlike normal parameters, once you have passed in a iota-variable, the whole
function will be rewritten. In other words, the parameter itself has to know how to rewrite 
the function's body, and becomes part of the definition of how a function application works.

An extra "scope" notation is used for the iota operator, to determine the sub expression that
should be treated as the proposisional function.

Our way to simulate this idea is firstly define a series of functions, names prefixed 
with `iota`. Functions provide a similar functionality to scopes. Then we allow people to 
write `Iota "name" x` if we need a iota variable, but it's just for readability. ** There 
are nothing to rely on to check if they have been used correctly**, nor does it actually 
modify the rest of the function it is contained in. 

With this notation, all propositional functions with iota variables have to be written explicitly
starting with `(fun x => ...)`, in contrast to just build an arbitary proposition with iota 
variables immediately. The resulted notation is quite different from how it looks like 
originally, but it can correctly express what should a iota do and limit its scope as in the
text.
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

(* iota's predicate, "Exists" which states that a description exist. My understanding
is that `E` in `E!` is the capital letter of `Exists` and `!` indicates that it is a 
predicate. 

TODO: give this iota_E the correct `Predicate` type
*)
Definition iota_E (Phi : Prop -> Prop) := exists b, (Phi x <[- x -]> (x = b)).

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

Definition n14_01 (s : string) (Phi Psi : Prop -> Prop) : 
  (iota_f s Phi Psi) = exists b, (Phi x <[- x -]> (x = b)) /\ Psi b. 
Admitted.

Definition n14_02 (Phi : Prop -> Prop) :
  (iota_E Phi) = exists b, (Phi x <[- x -]> (x = b)). 
Admitted.

Definition n14_03 (s1 s2 : string) (Phi Psi : Prop -> Prop) (f : Prop -> Prop -> Prop) :
  (iota_f2 s1 s2 Phi Psi f) = 
    iota_f s1 Phi (fun b => iota_f s2 Psi 
      (fun c => f (Iota s1 b) (Iota s2 c))).
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
Proof. exact (n14_1 s Phi Psi). Qed.

Theorem n14_11  (Phi : Prop -> Prop) : (iota_E Phi) 
  <-> (exists b, Phi x <[- x -]> (x = b)).
Proof.
  pose proof (n4_2 (iota_E Phi)) as n4_2.
  now rewrite -> n14_02 in n4_2 at 2.
Qed.

Theorem n14_111 (s1 s2 : string) (Phi Psi : Prop -> Prop) 
  (f : Prop -> Prop -> Prop) :
  (iota_f2_1 s2 s1 Psi Phi f) <-> (exists b c, 
    (Phi x <[- x -]> (x = b)) /\ (Psi x <[- x -]> (x = c)) /\ (f b c)).
Proof.
  assert (S1 : iota_f2_1 s2 s1 Psi Phi f ↔ 
    iota_f s2 Psi (fun c => iota_f s1 Phi 
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

Theorem n14_113 (s1 s2 : string) (Phi Psi : Prop -> Prop) 
  (f : Prop -> Prop -> Prop) : 
  iota_f2 s2 s1 Psi Phi (fun y x => f x y) <-> iota_f2 s1 s2 Phi Psi f. 
Admitted.

Open Scope double_app_equiv.

Theorem n14_12 (Phi : Prop -> Prop) : 
  iota_E Phi -> ((Phi x /\ Phi y) <[- x y -]> (x = y)).
Admitted.

Close Scope double_app_equiv.

Theorem n14_121 (B C : Prop) (Phi : Prop -> Prop) : 
  ((Phi x <[- x -]> x = B) /\ (Phi x <[- x -]> x = C))
  -> B = C. 
Admitted.

Open Scope single_app_impl.

Theorem n14_122 (B : Prop) (Phi : Prop -> Prop) :
  ((Phi x <[- x -]> x = B) <-> ((Phi x -[ x ]> x = B) /\ Phi B))
  /\
  (((Phi x -[ x ]> x = B) /\ Phi B) <-> ((Phi x -[ x ]> x = B) /\ exists x, Phi x)). 
Admitted.

Open Scope double_app_equiv.
Open Scope double_app_impl.

Theorem n14_123 (X Y : Prop) (Phi : Prop -> Prop -> Prop) : 
  ((Phi z w <[- z w -]> (z = X /\ w = Y)) 
    <-> ((Phi z w -[ z w ]> (z = X /\ w = Y)) /\ Phi X Y))
  /\
  (((Phi z w -[ z w ]> (z = X /\ w = Y)) /\ Phi X Y)
    <-> ((Phi z w -[ z w ]> (z = X /\ w = Y)) /\ exists z w, Phi z w)).
Admitted.

(* TODO: 4-var impl notation will be supported in the future *)
Theorem n14_124 (Phi : Prop -> Prop -> Prop) : 
  (exists x y, (Phi z w <[- z w -]> (z = x /\ w = y)))
  <-> ((exists x y, Phi x y) 
    /\ forall z w u v, (Phi z w /\ Phi u v) -> (z = w /\ u = v)). Admitted.

Theorem n14_13 (A : Prop) (Phi : Prop -> Prop) : 
  (iota_f "Phi" Phi (fun x => A = (Iota "Phi" x)))
  <-> (iota_f "Phi" Phi (fun x => (Iota "Phi" x) = A)). 
Admitted.

Theorem n14_131 (Phi Psi : Prop -> Prop) : 
  iota_f2 "Phi" "Psi" Phi Psi (fun x y => (Iota "Phi" x) = (Iota "Psi" y))
  <->
  iota_f2 "Psi" "Phi" Psi Phi (fun x y => (Iota "Psi" x) = (Iota "Phi" y)). 
Admitted.

Theorem n14_131_alt (Phi Psi : Prop -> Prop) : 
  iota_f2 "Phi" "Psi" Phi Psi (fun x y => (Iota "Phi" x) = (Iota "Psi" y))
  <->
  iota_f2 "Psi" "Phi" Psi Phi (fun x y => (Iota "Psi" x) = (Iota "Phi" y)). 
Admitted.

Theorem n14_14 (A B : Prop) (Phi : Prop -> Prop) :
  ((A = B) /\ (iota_f "Phi" Phi (fun x => B = (Iota "Phi" x))))
  -> (iota_f "Phi" Phi (fun x => A = (Iota "Phi" x))).
Admitted.

Theorem n14_142 (A : Prop) (Phi Psi : Prop -> Prop) :
  ((iota_f "Phi" Phi (fun x => A = (Iota "Phi" x))) 
    /\ iota_f2 "Phi" "Psi" Phi Psi 
      (fun x y => (Iota "Phi" x) = (Iota "Psi" y)))
  -> (iota_f "Psi" Psi (fun x => A = (Iota "Psi" x))).
Admitted.

Theorem n14_144 (Phi Psi Chi : Prop -> Prop) : 
  ((iota_f2 "Phi" "Psi" Phi Psi (fun x y => (Iota "Phi" x) = (Iota "Psi" y)))
    /\ (iota_f2 "Psi" "Chi" Psi Chi (fun x y => (Iota "Psi" x) = (Iota "Chi" y))))
  -> (iota_f2 "Phi" "Chi" Phi Chi (fun x y => (Iota "Phi" x) = (Iota "Chi" y))).
Admitted.

Theorem n14_145 (A : Prop) (Phi Psi : Prop -> Prop) : 
  ((iota_f "Phi" Phi (fun x => A = (Iota "Phi" x))) 
    /\ (iota_f "Psi" Psi (fun x => A = (Iota "Psi" x))))
  -> (iota_f2 "Phi" "Psi" Phi Psi (fun x y => (Iota "Phi" x) = (Iota "Psi" y))).
Admitted.

Theorem n14_15 (B : Prop) (Phi Psi : Prop -> Prop) : 
  (iota_f "Phi" Phi (fun x => (Iota "Phi" x) = B))
  -> (iota_f "Phi" Phi (fun x => Psi (Iota "Phi" x))
    <-> Psi B).
Admitted.

Theorem n14_16 (Phi Psi Chi : Prop -> Prop) :
  (iota_f2 "Phi" "Psi" Phi Psi (fun x y => (Iota "Phi" x) = (Iota "Psi" y)))
  ->
  (iota_f2 "Phi" "Psi" Phi Psi (fun x y => 
    (Chi (Iota "Phi" x)) = (Chi (Iota "Psi" y)))).
Admitted.

Theorem n14_17 (B : Prop) (Phi : Prop -> Prop) (Psi : Predicate 1) : 

Admitted.

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
Close Scope single_app_impl.
Close Scope double_app_equiv.
Close Scope double_app_impl.