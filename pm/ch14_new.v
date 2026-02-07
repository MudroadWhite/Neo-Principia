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

(* TODO:
- fix all the `replace`s
- fill in missing proofs
*)

(* 
The decription, or I would personally call it the iota operator, is an incomplete symbol(cf. 
p. 67), and is the first "definition" that will only have meaning "in specific context". It 
is a special kind of parameter for functions. They will be passed into propositional functions 
normally, but unlike normal parameters that only calculates everything within themselves, they 
will rewrite on the whole propositional function, and on other terms that are not within them.

An extra "scope" notation is used for the iota operator, to determine the sub expression that
should be treated as the proposisional function.

Suprisingly, Rocq has an excellent notation system to simulate such "incomplete" definition. 
As we can see, the description has been modeled by `DescriptionArg`, and with a notation assigning
a binder of the `DescriptionArg` type, our notation has been written down just as in the original 
text.

TODO: check if all the following paragraph still apply:
From n14_17 and onward, we're seeing how iota should cope with the predicative functions. Currently
we are still letting iotas being "untyped", that is, being constructed based on untyped function. 
Whether we can restrict the iotas to typed functions only is a future question.

The definitions are being put into the `lib.v`. 
*)

Declare Scope debug_iota_description.
Declare Scope iota_description.

Definition DescriptionArg (φ : Prop -> Prop) : Type := Prop.
Example descriptionarg_example := (fun iotaφ : (DescriptionArg (fun x => x)) =>
  iotaφ = iotaφ).

Definition Description (φ : Prop -> Prop) (expr : (DescriptionArg φ) -> Prop) : Prop. 
Admitted.
Example description_example := 
  Description (fun (iotaφ : DescriptionArg (fun x => x)) =>
    iotaφ = iotaφ).

Definition DescriptionExists (φ : Prop -> Prop) : Prop. Admitted.
Example descriptionexists_example := DescriptionExists (fun x => x).

Definition Description2 (φ ψ : Prop -> Prop) 
  (expr : (DescriptionArg φ) -> (DescriptionArg ψ) -> Prop): Prop. 
Admitted.
Example description2_example (φ ψ : Prop -> Prop) :=
  Description2 φ ψ (fun x y => x = y).

Definition Description2_rev (φ ψ : Prop -> Prop) 
  (expr : (DescriptionArg ψ) -> (DescriptionArg φ) -> Prop): Prop. 
Admitted.

Open Scope debug_iota_description.
Notation "[ 'iota' φ | x => B ]" := (Description φ (fun (x : DescriptionArg φ) => B))
  (at level 200, x binder, right associativity).
(* TODO: format... *)
Example debug_iota_notation_example := [ iota (fun x => x) | iotaφ => iotaφ = iotaφ ].

Notation "[ 'iotaE' P ]" := (DescriptionExists (P : Prop -> Prop))
  (at level 100, P constr at level 200, right associativity).
Example debug_iota_exists_example := [ iotaE (fun x => x) ].

Notation "[ 'iota2' φ , ψ | x y => B ]" := 
  (Description2 φ ψ (fun (x : DescriptionArg φ) (y : DescriptionArg ψ) => B))
  (at level 200, x binder, y binder, right associativity).
Example debug_iota2_example := 
  [ iota2 (fun x => x) , (fun x => x) | x y => (x = y) ].

Notation "[ 'iota2rev' φ , ψ | y x => B ]" := 
  (Description2 φ ψ (fun (y : DescriptionArg ψ) (x : DescriptionArg φ) => B))
  (at level 200, x binder, y binder, right associativity).
Close Scope debug_iota_description.

Open Scope iota_description.
Notation "[ 'ι' φ | x => B ]" := (Description φ (fun (x : DescriptionArg φ) => B))
  (at level 200, x binder, right associativity).
(* TODO: format... *)
Example iota_notation_example := [ι (fun x => x) | ιφ => ιφ = ιφ].

Notation "[ 'ιE' P ]" := (DescriptionExists (P : Prop -> Prop))
  (at level 100, P constr at level 200, right associativity).
Example iota_exists_example := [ ιE (fun x => x) ].

Notation "[ 'ι2' φ , ψ | x y => B ]" := 
  (Description2 φ ψ (fun (x : DescriptionArg φ) (y : DescriptionArg ψ) => B))
  (at level 200, x binder, y binder, right associativity).
Example iota2_example := 
  [ ι2 (fun x => x) , (fun x => x) | x y => (x = y) ].

Notation "[ 'ι2rev' φ , ψ | y x => B ]" := 
  (Description2 φ ψ (fun (y : DescriptionArg ψ) (x : DescriptionArg φ) => B))
  (at level 200, x binder, y binder, right associativity).

Close Scope iota_description.

(* ******** *)

Open Scope debug_iota_description.
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
  [iota2rev φ, ψ | iotaψ iotaφ => f iotaφ iotaψ]
  ↔ (∃ b c, (φ x <[- x -]> (x = b)) ∧ (ψ x <[- x -]> (x = c)) ∧ (f b c)).
Proof.
  assert (S1 : [iota2rev φ, ψ | iotaψ iotaφ => f iotaφ iotaψ] 
    ↔ [iota ψ | iotaψ => [iota φ | iotaφ => f iotaφ iotaψ]]).
  {
    pose proof (n4_2 ([iota2rev φ, ψ | iotaψ iotaφ => f iotaφ iotaψ])) 
      as n4_2.
    rewrite -> n14_04 in n4_2 at 2.
    now rewrite -> n14_03 in n4_2.
  }
  assert (S2 : [iota2rev φ, ψ | iotaψ iotaφ => f iotaφ iotaψ]
    ↔ [iota ψ | iotaψ => (exists b, (φ x <[- x -]> (x = b)) /\ f b iotaψ)]).
  {
    (* Simplification: for functions not being instantiated, we use 
    functional extentionality as a shortcut. *)
    replace (λ (iotaψ : DescriptionArg ψ), [iota φ | iotaφ => (f iotaφ iotaψ)])
      with (λ (iotaψ : DescriptionArg ψ), (∃ b, 
        (φ x <[- x -]> (x = b)) ∧ f b iotaψ)) in S1.
    2: {
      extensionality iotaψ.
      apply propositional_extensionality.
      now rewrite -> n14_1.
    }
    exact S1.
  }
  assert (S3 : [iota2rev φ, ψ | iotaψ iotaφ => f iotaφ iotaψ]
    ↔ (∃ c, (ψ x <[- x -]> (x = c)) 
      ∧ ∃ b, (φ x <[- x -]> (x = b)) ∧ f b c)).
  { now rewrite -> n14_1 in S2. }
  assert (S4 : [iota2rev φ, ψ | iotaψ iotaφ => f iotaφ iotaψ] 
    ↔ (∃ b c, (φ x <[- x -]> (x = b)) ∧ (ψ x <[- x -]> (x = c))
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

Theorem n14_112 (φ ψ : Prop → Prop) (f : Prop → Prop → Prop) : 
  [iota2 φ, ψ | iotaφ iotaψ => f iotaφ iotaψ] ↔ ∃ b c, 
    (φ x <[- x -]> x = b) ∧ (ψ x <[- x -]> x = c) ∧ f b c.
Proof.
  assert (S1 : [iota2 φ, ψ | iotaφ iotaψ => f iotaφ iotaψ] 

(* TODO: rewrite all below *)

    ↔ (iota_f s1 φ 
    (fun b => iota_f s2 ψ (fun c => f (Iota s1 b) (Iota s2 c))))).
  {
    pose proof (n4_2 (iota_f2 s1 s2 φ ψ f)) as n4_2.
    now rewrite -> n14_03 in n4_2 at 2.
  }
  assert (S2 : (iota_f2 s1 s2 φ ψ f) ↔ (iota_f s1 φ (fun b => 
    ∃ c, (ψ x <[- x -]> (x = c)) ∧ f b c))).
  {
    replace ((λ b, iota_f s2 ψ (λ c, f (Iota s1 b) (Iota s2 c))))
      with (λ b, iota_f s2 ψ (λ c, f b c)) in S1 
      by reflexivity.
    (* TODO: eliminate the usage of function extensionality in the futrue *)
    assert (S1_1 : (λ b, iota_f s2 ψ (λ c : Prop, f b c))
      = (λ b, ∃ c, (ψ x <[- x -]> (x = c)) ∧ f b c)).
    {
      extensionality b.
      pose proof (n14_1 s2 ψ (fun c => f b c)) as n14_1. 
      now apply propositional_extensionality.
    }
    now rewrite -> S1_1 in S1.
  }
  assert (S3 : (iota_f2 s1 s2 φ ψ f) ↔ ∃ b, 
    (φ x <[- x -]> x = b) ∧ (∃ c, (ψ x <[- x -]> x = c) ∧ f b c)).
  { now rewrite -> n14_1 in S2. } 
  assert (S4 : (iota_f2 s1 s2 φ ψ f) ↔ ∃ b c, 
    (φ x <[- x -]> x = b) ∧ (ψ x <[- x -]> x = c) ∧ f b c).
  { 
    pose proof (n11_55
      (fun b => (φ x <[- x -]> x = b))
      (fun b c => (ψ x <[- x -]> x = c) ∧ f b c)) as n11_55.
    now rewrite <- n11_55 in S3.
  }
  exact S4.
Qed.

Theorem n14_113 (s1 s2 : string) (φ ψ : Prop → Prop) 
  (f : Prop → Prop → Prop) : 
  iota_f2 s2 s1 ψ φ (fun y x => f x y) ↔ iota_f2 s1 s2 φ ψ f. 
Proof.
  pose proof (n14_111 s1 s2 φ ψ f) as n14_111.
  rewrite <- (n14_112 s1 s2) in n14_111.
  now rewrite -> n14_04 in n14_111.
Qed.

Open Scope double_app_equiv.
Open Scope double_app_impl.

Theorem n14_12 (φ : Prop → Prop) : 
  iota_E φ → ((φ x ∧ φ y) -[ x y ]> (x = y)).
Proof.
  (* TOOLS *)
  set (B := Individual "b").
  set (X := Individual "x").
  (* ******** *)
  assert (S1 : iota_E φ → ∃ b, φ x <[- x -]> x = b).
  {
    pose proof (n14_11 φ) as n14_11.
    (* simplification: we use `Simp` if necessary *)
    now destruct n14_11.
  }
  assert (S2 : (φ x <[- x -]> x = B) 
    → ((φ x ∧ φ y) <[- x y -]> (x = B ∧ y = B))).
  {
    (* NOTE: this place shows that we cannot assign a instance 
    automatically: in this complicated situation we are having 
    candidates being not unique. Might be interesting to check 
    in the future... *)
    pose proof (n4_38
      (φ X) (φ X) (X = B) (X = B)) as n4_38.
    rewrite <- n4_24 in n4_38.
    pose proof (n10_1 (fun x => (φ x ↔ x = B)) X) as n10_1.
    Syll n10_1 n4_38 Sa.
    pose proof (n11_11 X X (fun z w => 
      (∀ x : Prop, φ x ↔ x = B) →
      (φ z ∧ φ w ↔ z = B ∧ w = B))) as n11_11.
    MP n11_11 Sa.
    now rewrite <- n11_3 in n11_11.
  }
  assert (S3 : (φ x <[- x -]> x = B) 
  → ((φ x ∧ φ y) -[ x y ]> (x = y))).
  {
    intros Hp.
    pose proof (S2 Hp) as S2.
    (* simplifications... don't want to figure out how to do 
    it correctly atm *)
    intros x y.
    pose proof (S2 x y) as S2.
    destruct S2 as [S2l _].
    pose proof (n13_172 B x y) as n13_172.
    now Syll S2l n13_172 S3.
  }
  assert (S4 : (∃ b, (φ x <[- x -]> (x = b)))
    → ((φ x ∧ φ y) -[ x y ]> (x = y))).
  {
    pose proof (n10_11 B (fun b =>
      φ x <[- x -]> x = b  →  (φ x ∧ φ y) -[ x y ]> (x = y))) as n10_11.
    MP n10_11 S3.
    now rewrite -> n10_23 in n10_11.
  }
  assert (S5 : iota_E φ → ((φ x ∧ φ y) -[ x y ]> (x = y))).
  { now Syll S1 S4 S5. }
  exact S5.
Qed.

Close Scope double_app_equiv.

Theorem n14_121 (B C : Prop) (φ : Prop → Prop) : 
  ((φ x <[- x -]> x = B) ∧ (φ x <[- x -]> x = C))
  → B = C. 
Proof.
  assert (S1 : ((φ x <[- x -]> x = B) ∧ (φ x <[- x -]> x = C))
    → ((φ B ↔ (B = B)) ∧ (φ B ↔ (B = C)))).
  {
    pose proof (n10_1 (fun x => φ x ↔ (x = B)) B) as n10_1a.
    pose proof (n10_1 (fun x => φ x ↔ (x = C)) B) as n10_1b.
    Conj n10_1a n10_1b C1.
    pose proof (n3_47
      (φ x <[- x -]> x = B) (φ x <[- x -]> x = C)
      (φ B ↔ (B = B)) (φ B ↔ (B = C))) as n3_47.
    now MP n3_47 C1.
  }
  assert (S2 : ((φ x <[- x -]> x = B) ∧ (φ x <[- x -]> x = C))
    → (φ B ∧ (φ B ↔ (B = C)))).
  {
    (* TODO: Design a special rule for *13.15. This is something unusual
      for the rewriting system *)
    pose proof n13_15.
    admit.
  }
  assert (S3 : ((φ x <[- x -]> x = B) ∧ (φ x <[- x -]> x = C))
    → (B = C)).
  {
    (* Simplifications... *)
    intro Hp.
    pose proof (S2 Hp) as S2.
    destruct S2 as [A1 A2].
    destruct A2 as [A2l _].
    assert (S2_1 : φ B ∧ (φ B → B = C)).
    { 
      clear S1.
      now Conj A1 A2l S2_1. 
    }
    pose proof (Ass3_35 (φ B) (B = C)) as Ass3_35.
    now MP Ass3_35 S2_1.
  }
  exact S3.
Admitted.

Open Scope single_app_impl.


Close Scope debug_iota_description.