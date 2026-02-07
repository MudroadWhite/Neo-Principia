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

(* TODO: don't forget to copy comments into here *)
(* TODO: add scope for notations *)

Definition DescriptionArg (φ : Prop -> Prop) : Type := Prop.

Definition Description (φ : Prop -> Prop) (expr : (DescriptionArg φ) -> Prop) : Prop. 
Admitted.
Example descriptionarg_example := (fun iotaφ : (DescriptionArg (fun x => x)) =>
  iotaφ = iotaφ).

Definition DescriptionExists (φ : Prop -> Prop) : Prop. Admitted.
Example descriptionexists_example := DescriptionExists (fun x => x).

Example description_example := 
  Description (fun (iotaφ : DescriptionArg (fun x => x)) =>
    iotaφ = iotaφ).

Notation "[ 'iota' φ | x => B ]" := (Description φ (fun (x : DescriptionArg φ) => B))
  (at level 200, x binder, right associativity).
(* TODO: format... *)
Example iota_notation_example := [ iota (fun x => x) | iotaφ => iotaφ = iotaφ ].

Notation "[ 'iotaE' P ]" := (DescriptionExists (P : Prop -> Prop))
  (at level 100, P constr at level 200, right associativity).
Example iota_exists_example := [ iotaE (fun x => x) ].

Definition Description2 (φ ψ : Prop -> Prop) 
  (expr : (DescriptionArg φ) -> (DescriptionArg ψ) -> Prop): Prop. 
Admitted.
Example description2_example (φ ψ : Prop -> Prop) :=
  Description2 φ ψ (fun x y => x = y).

Notation "[ 'iota2' φ , ψ | x y => B ]" := 
  (Description2 φ ψ (fun (x : DescriptionArg φ) (y : DescriptionArg ψ) => B))
  (at level 200, x binder, y binder, right associativity).
Example iota2_example := 
  [ iota2 (fun x => x) , (fun x => x) | x y => (x = y) ].

Definition Description2_rev (φ ψ : Prop -> Prop) 
  (expr : (DescriptionArg ψ) -> (DescriptionArg φ) -> Prop): Prop. 
Admitted.

Notation "[ 'iota2rev' φ , ψ | y x => B ]" := 
  (Description2 φ ψ (fun (y : DescriptionArg ψ) (x : DescriptionArg φ) => B))
  (at level 200, x binder, y binder, right associativity).

(* ******** *)

Open Scope single_app_equiv.

Definition n14_01 (φ ψ : Prop → Prop) : 
  [iota φ | iotaφ => ψ iotaφ] 
    = ∃ b, (φ x <[- x -]> (x = b)) ∧ ψ b. 
Admitted.

Definition n14_02 (φ : Prop → Prop) :
  [iotaE φ] = ∃ b, (φ x <[- x -]> (x = b)). 
Admitted.

(* Although `iota2` has been defined, expressions that involves 2 functions often
comes up with the default interpretations as two `iota` rather than one `iota2`.
While this doen't affect significantly how the definition organizes, it still affects
how we should write down a theorem *)
Definition n14_03 (φ ψ : Prop → Prop) (f : Prop → Prop → Prop) :
  [iota2 φ, ψ | iotaφ iotaψ => f iotaφ iotaψ] = 
    [iota φ | iotaφ => [iota ψ | iotaψ => f iotaφ iotaψ]].
Admitted.
  
Definition n14_04 (φ ψ : Prop → Prop) (f : Prop → Prop → Prop) : 
  [iota2rev φ, ψ | iotaψ iotaφ => f iotaψ iotaφ]
  = [iota2 ψ, φ | iotaψ iotaφ => f iotaψ iotaφ].
Admitted.

Theorem n14_1 (φ ψ : Prop → Prop) : [iota φ | iotaφ => ψ iotaφ]
  ↔ ∃ b, (φ x <[- x -]> (x = b)) ∧ ψ b.
Proof.
  pose proof (n4_2 ([iota φ | iotaφ => ψ iotaφ] )) as n4_2.
  now rewrite -> n14_01 in n4_2 at 2.
Qed.

(* The equivalent with n14_1, with scope notation in its original 
  representation omitted. With our definition, we might just make 
  another definition copying `iota_f` to indicate it is getting 
  scope notation in the text... *)
Theorem n14_101 (φ ψ : Prop → Prop) : [iota φ | iotaφ => ψ iotaφ] 
  ↔ ∃ b, (φ x <[- x -]> (x = b)) ∧ ψ b.
Proof. exact (n14_1 φ ψ). Qed.

Theorem n14_11  (φ : Prop → Prop) : [iotaE φ]
  ↔ (∃ b, φ x <[- x -]> (x = b)).
Proof.
  pose proof (n4_2 ([iotaE φ])) as n4_2.
  now rewrite -> n14_02 in n4_2 at 2.
Qed.

Theorem n14_111 (φ ψ : Prop → Prop) (f : Prop → Prop → Prop) :
  [iota2rev φ, ψ | iotaψ iotaφ => f iotaψ iotaφ]
  ↔ (∃ b c, (φ x <[- x -]> (x = b)) ∧ (ψ x <[- x -]> (x = c)) ∧ (f b c)).
Proof.
  assert (S1 : [iota2rev φ, ψ | iotaψ iotaφ => f iotaψ iotaφ] 
    ↔ [iota ψ | iotaψ => [iota φ | iotaφ => f iotaψ iotaφ]]).
  {
    pose proof (n4_2 ([iota2rev φ, ψ | iotaψ iotaφ => f iotaψ iotaφ])) 
      as n4_2.
    rewrite -> n14_04 in n4_2 at 2.
    now rewrite -> n14_03 in n4_2.
  }
  assert (S2 : [iota2rev φ, ψ | iotaψ iotaφ => f iotaψ iotaφ]
    ↔ [iota ψ | iotaψ => (exists b, (φ x <[- x -]> (x = b)) /\ f b iotaψ)]).
  {
    (* TODO: try the proof on the new notation... *)

    (* Simplification: for functions not being instantiated, we use 
    functional extentionality as a shortcut. *)
    replace (λ c, iota_f s1 φ (λ b, f b c))
      with (λ c, (∃ b, (φ x <[- x -]> (x = b)) ∧ f b c))
      in S1.
    2: {
      extensionality c. (* function extentionality *)
      apply propositional_extensionality.
      pose proof (n14_1 s1 φ (fun b => f b c)) as n14_1.
      now symmetry.
    }
    exact S1.
  }
  assert (S3 : iota_f2_rev s2 s1 ψ φ f ↔
    (∃ c, (ψ x <[- x -]> (x = c)) 
    ∧ ∃ b, (φ x <[- x -]> (x = b)) ∧ f b c)).
  { now rewrite -> n14_1 in S2. }
  assert (S4 : iota_f2_rev s2 s1 ψ φ f ↔
    (∃ b c, (φ x <[- x -]> (x = b)) ∧ (ψ x <[- x -]> (x = c))
      ∧ f b c)).
  {
    pose proof (n11_55
      (fun c => (ψ x <[- x -]> (x = c)))
      (fun c b => (φ x <[- x -]> (x = b)) ∧ f b c)) as n11_55.
    setoid_rewrite <- n4_32 in n11_55.
    setoid_rewrite -> n4_3 in n11_55 at 3.
    setoid_rewrite -> n4_32 in n11_55.
    rewrite <- n11_55 in S3.
    now rewrite -> n11_23 in S3.
  }
  exact S4.
Qed.