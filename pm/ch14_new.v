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
    ↔ [iota φ | iotaφ => [iota ψ | iotaψ => f iotaφ iotaψ]]).
  {
    pose proof (n4_2 ([iota2 φ, ψ | iotaφ iotaψ => f iotaφ iotaψ])) as n4_2.
    now rewrite -> n14_03 in n4_2 at 2.
  }
  assert (S2 : [iota2 φ, ψ | iotaφ iotaψ => f iotaφ iotaψ] 
    ↔ [iota φ | iotaφ => ∃ c, (ψ x <[- x -]> (x = c)) ∧ f iotaφ c]).
  {
    assert (S1_1 : (λ (iotaφ : DescriptionArg φ), [iota ψ | iotaψ => f iotaφ iotaψ])
      = (λ (iotaφ : DescriptionArg φ), ∃ c, (ψ x <[- x -]> (x = c)) ∧ f iotaφ c)).
    {
      extensionality iotaφ.
      apply propositional_extensionality.
      now apply n14_1.
    }
    now rewrite -> S1_1 in S1.
  }
  assert (S3 : [iota2 φ, ψ | iotaφ iotaψ => f iotaφ iotaψ] 
    ↔ ∃ b, (φ x <[- x -]> x = b) ∧ (∃ c, (ψ x <[- x -]> x = c) ∧ f b c)).
  { now rewrite -> n14_1 in S2. } 
  assert (S4 : [iota2 φ, ψ | iotaφ iotaψ => f iotaφ iotaψ] 
    ↔ ∃ b c, (φ x <[- x -]> x = b) ∧ (ψ x <[- x -]> x = c) ∧ f b c).
  { 
    pose proof (n11_55
      (fun b => (φ x <[- x -]> x = b))
      (fun b c => (ψ x <[- x -]> x = c) ∧ f b c)) as n11_55.
    now rewrite <- n11_55 in S3.
  }
  exact S4.
Qed.

Theorem n14_113 (φ ψ : Prop → Prop) (f : Prop → Prop → Prop) : 
  [iota2 ψ, φ | iotaψ iotaφ => f iotaφ iotaψ] 
  ↔ [iota2 φ, ψ | iotaφ iotaψ => f iotaφ iotaψ].
Proof.
  pose proof (n14_111 φ ψ f) as n14_111.
  rewrite <- n14_112 in n14_111.
  now rewrite -> n14_04 in n14_111.
Qed.

Open Scope double_app_equiv.
Open Scope double_app_impl.

Theorem n14_12 (φ : Prop → Prop) : 
  [iotaE φ] → ((φ x ∧ φ y) -[ x y ]> (x = y)).
Proof.
  (* TOOLS *)
  set (B := Individual "b").
  set (X := Individual "x").
  (* ******** *)
  assert (S1 : [iotaE φ] → ∃ b, φ x <[- x -]> x = b).
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
      φ x <[- x -]> x = b → (φ x ∧ φ y) -[ x y ]> (x = y))) as n10_11.
    MP n10_11 S3.
    now rewrite -> n10_23 in n10_11.
  }
  assert (S5 : [iotaE φ] → ((φ x ∧ φ y) -[ x y ]> (x = y))).
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

(* TODO: rewrite all below *)

Theorem n14_122 (B : Prop) (φ : Prop → Prop) :
  ((φ x <[- x -]> (x = B)) ↔ ((φ x -[ x ]> (x = B)) ∧ φ B))
  ∧
  (((φ x -[ x ]> (x = B)) ∧ φ B) ↔ ((φ x -[ x ]> (x = B)) ∧ ∃ x, φ x)). 
Proof.
  (* TOOLS *)
  set (X := Individual "x").
  (* ******** *)
  assert (S1 : (φ x <[- x -]> (x = B)) 
    ↔ ((φ x -[ x ]> (x = B)) ∧ ((x = B) -[ x ]> φ x))).
  { apply  n10_22. }
  assert (S2 : (φ x <[- x -]> (x = B)) 
    ↔ ((φ x -[ x ]> (x = B)) ∧ φ B)).
  {
    pose proof (n13_191 B φ) as n13_191.
    now rewrite -> n13_191 in S1.
  }
  assert (S3 : (φ X → (X = B))
    → (φ X ↔ (φ X ∧ (X = B)))).
  {
    pose proof (n4_71 (φ X) (X = B)) as n4_71.
    now destruct n4_71.
  }
  assert (S4 : (φ x -[ x ]> (x = B))
    → (φ x <[- x -]> (φ x ∧ (x = B)))).
  {
    pose proof (n10_11 X (fun x =>
      (φ x → (x = B)) → (φ x 
        ↔ (φ x ∧ (x = B))))) as n10_11.
    MP n10_11 S3.
    pose proof (n10_27 (fun x => φ x → (x = B))
      (fun x => φ x ↔ (φ x ∧ (x = B)))) 
      as n10_27.
    now MP n10_27 n10_11.
  }
  assert (S5 : (φ x -[ x ]> (x = B))
    → ((∃ x, φ x) ↔ (∃ x, φ x ∧ (x = B)))).
  {
    pose proof (n10_281 φ (fun x => φ x ∧ x = B)) 
      as n10_281.
    now Syll S4 n10_281 S5.
  }
  assert (S6 : (φ x -[ x ]> (x = B)) → ((∃ x, 
    φ x) ↔ φ B)).
  {
    setoid_rewrite -> n4_3 in S5 at 2.
    now rewrite -> n13_195 in S5.
  }
  assert (S7 : ((φ x -[ x ]> (x = B)) ∧ (∃ x, φ x))
    ↔ ((φ x -[ x ]> (x = B)) ∧ φ B)).
  { now rewrite -> n5_32 in S6. }
  assert (S8 : ((φ x <[- x -]> (x = B)) ↔ ((φ x -[ x ]> (x = B)) ∧ φ B))
    ∧ (((φ x -[ x ]> (x = B)) ∧ φ B) 
      ↔ ((φ x -[ x ]> (x = B)) ∧ ∃ x, φ x))).
  {
    clear S1 S3 S4 S5 S6.
    now Conj S2 S7 S8.
  }
  exact S8.
Qed.

Open Scope double_app_equiv.
Open Scope double_app_impl.

Theorem n14_123 (X Y : Prop) (φ : Prop → Prop → Prop) : 
  ((φ z w <[- z w -]> (z = X ∧ w = Y)) 
    ↔ ((φ z w -[ z w ]> (z = X ∧ w = Y)) ∧ φ X Y))
  ∧
  (((φ z w -[ z w ]> (z = X ∧ w = Y)) ∧ φ X Y)
    ↔ ((φ z w -[ z w ]> (z = X ∧ w = Y)) ∧ ∃ z w, φ z w)).
Proof.
  (* TOOLS *)
  set (Z := Individual "z").
  set (W := Individual "w").
  set (λ P0 Q0 : Prop, eq_to_equiv (P0 ↔ Q0) ((P0 → Q0) ∧ (Q0 → P0)) 
    (Equiv4_01 P0 Q0)) as Equiv4_01a.
  (* ******** *)
  assert (S1 : (φ z w <[- z w -]> (z = X ∧ w = Y)) 
    ↔ ((φ z w -[ z w ]> (z = X ∧ w = Y)) 
      ∧ (((z = X ∧ w = Y) -[ z w ]> φ z w)))).
  {
    pose proof (n11_31 
      (fun z w => φ z w → ((z = X) ∧ (w = Y)))
      (fun z w => (((z = X) ∧ (w = Y)) → φ z w))) as n11_31a.
    rewrite -> n11_31 in n11_31a.
    (* NOTE: this place seems to be uneliminatable *)
    replace (∀ x y, (φ x y → x = X ∧ y = Y) ∧ (x = X ∧ y = Y → φ x y))
      with (∀ x y, φ x y <-> x = X ∧ y = Y) in n11_31a at 1
      by apply n11_06.
    now rewrite <- n11_31 in n11_31a.
  }
  assert (S2 : (φ z w <[- z w -]> (z = X ∧ w = Y)) 
    ↔ ((φ z w -[ z w ]> (z = X ∧ w = Y)) ∧ φ X Y)).
  { now rewrite -> n13_21 in S1. }
  assert (S3 : (φ Z W → ((Z = X) ∧ (W = Y)))
    → (φ Z W ↔ (φ Z W ∧ (Z = X) ∧ (W = Y)))).
  {
    pose proof (n4_71 (φ Z W) ((Z = X) ∧ (W = Y))) as n4_71.
    now destruct n4_71.
  } 
  assert (S4 : (φ z w -[ z w ]> ((z = X) ∧ (w = Y)))
    → (φ z w <[- z w -]> (φ z w ∧ (z = X) ∧ (w = Y)))).
  {
    pose proof (n11_11 Z W (fun z w =>
      (φ z w → ((z = X) ∧ (w = Y)))
        → (φ z w ↔ (φ z w 
          ∧ (z = X) ∧ (w = Y))))) as n11_11.
    MP n11_11 S4.
    pose proof (n11_32 (fun z w => φ z w → ((z = X) ∧ (w = Y)))
      (fun z w => φ z w ↔ (φ z w 
        ∧ (z = X) ∧ (w = Y)))) as n11_32.
    now MP n11_32 n11_11.
  }
  assert (S5 : (φ z w -[ z w ]> ((z = X) ∧ (w = Y)))
    → ((∃ z w, φ z w) ↔ (∃ z w, 
      φ z w ∧ (z = X) ∧ (w = Y)))).
  {
    pose proof (n11_341 φ (fun z w => 
      φ z w ∧ (z = X) ∧ (w = Y))) as n11_341.
    now Syll n11_341 S4 S5.
  }
  assert (S6 : (φ z w -[ z w ]> ((z = X) ∧ (w = Y)))
    → ((∃ z w, φ z w) ↔ φ X Y)).
  {
    setoid_rewrite -> n4_3 in S5 at 3.
    setoid_rewrite -> n4_32 in S5.
    now rewrite -> n13_22 in S5.
  }
  assert (S7 : ((φ z w -[ z w ]> ((z = X) ∧ (w = Y)))
      ∧ (∃ z w, φ z w)
    ↔ ((φ z w -[ z w ]> (z = X ∧ w = Y)) ∧ φ X Y))).
  { now rewrite -> n5_32 in S6. }
  assert (S8 : ((φ z w <[- z w -]> (z = X ∧ w = Y)) 
      ↔ ((φ z w -[ z w ]> (z = X ∧ w = Y)) ∧ φ X Y))
    ∧ (((φ z w -[ z w ]> (z = X ∧ w = Y)) ∧ φ X Y)
      ↔ ((φ z w -[ z w ]> (z = X ∧ w = Y)) ∧ ∃ z w, φ z w))).
  {
    clear S1 S3 S4 S5 S6.
    now Conj S2 S7 S8.
  }
  exact S8.
Qed.

(* TODO: 4-var impl notation will be supported in the future *)
Theorem n14_124 (φ : Prop → Prop → Prop) : 
  (∃ x y, (φ z w <[- z w -]> (z = x ∧ w = y)))
  ↔ ((∃ x y, φ x y) 
    ∧ ∀ z w u v, (φ z w ∧ φ u v) → (z = u ∧ w = v)). 
Proof.
  (* TOOLS *)
  set (X := Individual "x").
  set (Y := Individual "y").
  set (Z := Individual "z").
  set (W := Individual "w").
  set (U := Individual "u").
  set (V := Individual "v").
  (* ******** *)
  assert (S1 : (∃ x y, (φ z w <[- z w -]> (z = x ∧ w = y)))
    → ∃ x y, φ x y).
  { 
    pose proof (n14_123 X Y φ) as n14_123.
    destruct n14_123 as [n14_123l _].
    destruct n14_123l as [n14_123ll _].
    pose proof (Simp3_27
      (φ z w -[ z w ]> z = X ∧ w = Y)
      (φ X Y)) as Simp3_27.
    Syll n14_123l Simp3_27 Sy1.
    pose proof (n11_11 X Y (fun x y =>
      φ z w <[- z w -]> z = x ∧ w = y → φ x y)) as n11_11.
    MP n11_11 Sy1.
    pose proof (n11_34 (fun x y => φ z w <[- z w -]> z = x ∧ w = y)
      φ) as n11_34.
    now MP n11_34 n11_11.
  }
  assert (S2 : (φ z w <[- z w -]> ((z = X) ∧ (w = Y)))
    → (((φ Z W) ∧ (φ U V))
      → (Z = X ∧ W = Y ∧ U = X ∧ V = Y))).
  {
    intro Hp.
    pose proof (n11_1 Z W (fun z w =>
      (φ z w) ↔ ((z = X) ∧ (w = Y)))) as n11_1a.
    pose proof (n11_1 U V (fun z w =>
      (φ z w) ↔ ((z = X) ∧ (w = Y)))) as n11_1b.
    MP n11_1b Hp.
    destruct n11_1b as [n11_1bl _].
    MP n11_1a Hp.
    destruct n11_1a as [n11_1al _].
    Conj n11_1al n11_1bl C1.
    pose proof (n3_47 (φ Z W) (φ U V)
      (Z = X ∧ W = Y) (U = X ∧ V = Y)) as n3_47.
    MP n3_47 C1.
    now rewrite -> n4_32 in n3_47.
  }
  assert (S3 : (φ z w <[- z w -]> ((z = X) ∧ (w = Y)))
    → (((φ Z W) ∧ (φ U V)) → ((Z = U) ∧ (W = V)))).
  {
    (* simplification: tedious reordering... *)
    intros Hp.
    pose proof (S2 Hp) as S2.
    assert (S2_1 : (Z = X ∧ W = Y ∧ U = X ∧ V = Y)
      ↔ ((Z = X ∧ U = X) ∧ (W = Y ∧ V = Y))).
    { now rewrite <- n4_32. }
    rewrite -> S2_1 in S2. clear S2_1.
    pose proof (n13_172 X Z U) as n13_172a.
    pose proof (n13_172 Y W V) as n13_172b.
    pose proof (n3_47
      (Z = X ∧ U = X) (W = Y ∧ V = Y)
      (Z = U) (W = V)) as n3_47.
    assert (C1 : (Z = X ∧ U = X → Z = U) ∧ (W = Y ∧ V = Y → W = V)).
    { clear n3_47; now Conj n13_172a n13_172b C1. }
    MP n3_47 C1.
    (* simplification for syll *)
    now Syll S2 n3_47 S3.
  }
  assert (S4 : (∃ x y, φ z w <[- z w -]> ((z = x) ∧ (w = y)))
    → (((φ Z W) ∧ (φ U V)) → ((Z = U) ∧ (W = V)))).
  {
    pose proof (n11_11 X Y (fun x y =>
      (φ z w <[- z w -]> ((z = x) ∧ (w = y)))
        → (((φ Z W) ∧ (φ U V)) → ((Z = U) ∧ (W = V))))) 
      as n11_11.
    MP n11_11 S3.
    now rewrite -> n11_35 in n11_11.
  }
  assert (S5 : (∃ x y, φ z w <[- z w -]> ((z = x) ∧ (w = y)))
    → (∀ z w u v, (φ z w ∧ φ u v) → ((z = u) ∧ (w = v)))).
  {
    (* For 4 variables, the generalization has applied twice! *)
    pose proof (n11_11 U V (fun u v =>
      (∃ x y, φ z w <[- z w -]> ((z = x) ∧ (w = y)))
      → (((φ Z W) ∧ (φ u v)) → ((Z = u) ∧ (W = v))))) 
      as n11_11a.
    MP n11_11a S4.
    rewrite <- n11_3 in n11_11a.
    pose proof (n11_11 Z W (fun z w =>
    (∃ x y, φ z w <[- z w -]> ((z = x) ∧ (w = y)))
      → (∀ u v, ((φ z w) ∧ (φ u v)) → ((z = u) ∧ (w = v))))) as n11_11b.
    MP n11_11b n11_11a.
    now rewrite <- n11_3 in n11_11b.
  }
  assert (S6 : ((φ X Y) ∧ (∀ z w u v, 
    ((φ z w) ∧ (φ u v)) → ((z = u) ∧ (w = v)))
      → (φ X Y ∧ ((φ z w ∧ φ X Y) -[ z w ]> ((z = X) ∧ (w = Y)))))).
  {
    (* The ordering here is annoying... *)
    pose proof (n11_1 X Y (fun u v =>
      (∀ z w, φ z w ∧ φ u v → z = u ∧ w = v))) as n11_1.
    assert (A1 : (∀ x y z w : Prop, φ z w ∧ φ x y → z = x ∧ w = y)
      ↔ (∀ z w x y : Prop, φ z w ∧ φ x y → z = x ∧ w = y)).
    {
      setoid_rewrite -> n11_2 at 2.
      setoid_rewrite -> n11_2 at 3.
      setoid_rewrite -> n11_2 at 1.
      now setoid_rewrite -> n11_2 at 2.
    }
    rewrite -> A1 in n11_1.
    pose proof (Fact3_45
      (∀ z w x y : Prop, φ z w ∧ φ x y → z = x ∧ w = y)
      ((φ z w ∧ φ X Y) -[ z w ]> z = X ∧ w = Y)
      (φ X Y)) as Fact3_45.
    MP Fact3_45 n11_1.
    rewrite -> n4_3 in Fact3_45.
    now setoid_rewrite -> n4_3 in Fact3_45 at 4.
  }
  assert (S7 : ((φ X Y) ∧ (∀ z w u v, 
    ((φ z w) ∧ (φ u v)) → ((z = u) ∧ (w = v))))
    → (φ X Y ∧ (φ z w -[ z w ]> ((z = X) ∧ (w = Y))))).
  {
    pose proof (n5_33 (φ X Y) (φ Z W) (Z = X ∧ W = Y)) as n5_33.
    setoid_rewrite -> n4_3 in n5_33 at 5.
    pose proof (n11_11 Z W (fun z w =>
      φ X Y ∧ (φ z w → z = X ∧ w = Y) 
      ↔ φ X Y ∧ (φ z w ∧ φ X Y → z = X ∧ w = Y))) as n11_11.
    MP n11_11 n5_33.
    pose proof (n11_33
      (fun z w => φ X Y ∧ (φ z w → z = X ∧ w = Y))
      (fun z w => φ X Y ∧ (φ z w ∧ φ X Y → z = X ∧ w = Y))) 
      as n11_33.
    MP n11_33 n11_11.
    rewrite -> n11_47 in n11_33.
    setoid_rewrite -> n11_47 in n11_33.
    now rewrite <- n11_33 in S6.
  }
  assert (S8 : ((φ X Y) ∧ (∀ z w u v, 
    ((φ z w) ∧ (φ u v)) → ((z = u) ∧ (w = v))))
    → (φ z w <[- z w -]> ((z = X) ∧ (w = Y)))).
  {
    pose proof (n14_123 X Y φ) as n14_123.
    destruct n14_123 as [n14_123l _].
    setoid_rewrite -> n4_3 in S7 at 4.
    now rewrite <- n14_123l in S7.
  }
  assert (S9 : ((∃ x y, φ x y) ∧ (∀ z w u v,
      (φ z w ∧ φ u v) → ((z = u) ∧ (w = v)))
    → (∃ x y, φ z w <[- z w -]> ((z = x) ∧ (w = y))))).
  {
    pose proof (n11_11 X Y (fun x y =>
      ((φ x y) ∧ (∀ z w u v, 
        ((φ z w) ∧ (φ u v)) → ((z = u) ∧ (w = v))))
        → (φ z w <[- z w -]> ((z = x) ∧ (w = y))))) as n11_11.
    MP n11_11 S8.
    pose proof (n11_34
      (fun x y => φ x y ∧ (∀ z w u v,
        (φ z w ∧ φ u v) → ((z = u) ∧ (w = v))))
      (fun x y => (φ z w <[- z w -]> ((z = x) ∧ (w = y))))) 
      as n11_34.
    MP n11_34 n11_11.
    setoid_rewrite -> n4_3 in n11_34 at 1.
    rewrite -> n11_45 in n11_34.
    now rewrite -> n4_3 in n11_34 at 1.
  }
  assert (S10 : (∃ x y,  φ z w <[- z w -]> z = x ∧ w = y)
    ↔ (∃ x y, φ x y) 
      ∧ ∀ z w u v, φ z w ∧ φ u v → z = u ∧ w = v).
  {
    clear S2 S3 S4 S6 S7 S8.
    assert (C1 : ((∃ x y,  φ z w <[- z w -]> z = x ∧ w = y) → ∃ x y : Prop, φ x y)
      ∧ ((∃ x y,  φ z w <[- z w -]> z = x ∧ w = y)
        → ∀ z w u v, φ z w ∧ φ u v → z = u ∧ w = v)).
    { clear S9. now Conj S1 S5 C1. }
    pose proof (Comp3_43
      (∃ x y, φ z w <[- z w -]> z = x ∧ w = y)
      (∃ x y, φ x y)
      (∀ z w u v, φ z w ∧ φ u v → z = u ∧ w = v)) 
      as Comp3_43.
    MP Comp3_43 C1.
    clear S1 S5 C1.
    move S9 after Comp3_43.
    Conj Comp3_43 S9 S10.
    now Equiv S10.
  }
  exact S10.
Qed.

Theorem n14_13 (A : Prop) (s : string) (φ : Prop → Prop) : 
  [iota φ | iotaφ => A = iotaφ] ↔ [iota φ | iotaφ => iotaφ = A].
Proof.
  (* TOOLS *)
  set (B := Individual "b").
  (* ******** *)
  assert (S1 : [iota φ | iotaφ => A = iotaφ]
    ↔ (∃ b, (φ x <[- x -]> (x = b)) ∧ A = b)).
  { apply n14_1. }
  assert (S2 : ((φ x <[- x -]> (x = B)) ∧ (A = B))
    ↔ ((φ x <[- x -]> (x = B)) ∧ (B = A))).
  {
    pose proof (n13_16 A B) as n13_16.
    pose proof (n4_36 (A = B) (B = A) (φ x <[- x -]> (x = B))) as n4_36.
    MP n4_36 n13_16.
    rewrite -> n4_3 in n4_36.
    now setoid_rewrite -> n4_3 in n4_36 at 2.
  }
  assert (S3 : (∃ b, (φ x <[- x -]> x = b) ∧ (A = b))
    ↔ (∃ b, (φ x <[- x -]> x = b) ∧ (b = A))).
  {
    pose proof (n10_11 B (fun b => 
        ((φ x <[- x -]> (x = b)) ∧ (A = b))
      ↔ ((φ x <[- x -]> (x = b)) ∧ (b = A)))) as n10_11.
    MP n10_11 S2.
    pose proof (n10_281 
      (fun b => (φ x <[- x -]> (x = b)) ∧ (A = b))
      (fun b => (φ x <[- x -]> (x = b)) ∧ (b = A))) as n10_281.
    now MP n10_281 n10_11.
  }
  assert (S4 : (∃ b, (φ x <[- x -]> x = b) ∧ (A = b))
    ↔ [iota φ | iotaφ => iotaφ = A]).
  { now rewrite <- (n14_1 φ (fun b => b = A)) in S3. }
  assert (S5 : [iota φ | iotaφ => A = iotaφ] 
    ↔ [iota φ | iotaφ => iotaφ = A]).
  { now rewrite -> S4 in S1. }
  exact S5.
Qed.

(* There are 2 ways to intrepret the iotas in this proposition. Original text
has also given both ways to interpre them correspondingly. It seems that
we will take the one-at-a-time as the usual way *)
Theorem n14_131 (s1 s2 : string) (φ ψ : Prop → Prop) : 
  iota_f s1 φ (fun x => iota_f s1 ψ (fun y =>
    (Iota s1 x) = (Iota s1 y)))
  ↔
  iota_f s1 ψ (fun y => iota_f s1 φ (fun x =>
    (Iota s1 y) = (Iota s1 x))).
Proof.
  assert (S1 : iota_f s1 φ (fun x => iota_f s1 ψ (fun y =>
      (Iota s1 x) = (Iota s1 y)))
    ↔ (∃ b, (φ x <[- x -]> (x = b)) 
      ∧ iota_f s1 ψ (fun y => b = (Iota s1 y)))).
  { apply n14_1. }
  assert (S2 : iota_f s1 φ (fun x => iota_f s1 ψ (fun y =>
      (Iota s1 x) = (Iota s1 y)))
    ↔ (∃ b, (φ x <[- x -]> (x = b)) 
      ∧ (∃ c, (ψ x <[- x -]> (x = c)) ∧ (b = c)))).
  { now setoid_rewrite -> n14_1 in S1 at 3. }
  assert (S3 : iota_f s1 φ (fun x => iota_f s1 ψ (fun y =>
      (Iota s1 x) = (Iota s1 y)))
    ↔ (∃ c, (ψ x <[- x -]> (x = c))
      ∧ (∃ b, (φ x <[- x -]> (x = b)) ∧ (b = c)))).
  {
    setoid_rewrite -> n4_3 in S2 at 2.
    setoid_rewrite -> n4_3 in S2 at 3.
    rewrite -> n11_6 in S2.
    setoid_rewrite <- n4_3 in S2 at 3.
    now setoid_rewrite <- n4_3 in S2 at 2.
  }
  assert (S4 : iota_f s1 φ (fun x => iota_f s1 ψ (fun y =>
      (Iota s1 x) = (Iota s1 y)))
    ↔ (∃ c, (ψ x <[- x -]> (x = c)) 
      ∧ iota_f s1 φ (fun x => (Iota s1 x) = c))).
  { now setoid_rewrite <- (n14_1 s1) in S3 at 2. }
  assert (S5 : iota_f s1 φ (fun x => iota_f s1 ψ (fun y =>
      (Iota s1 x) = (Iota s1 y)))
    ↔ (∃ c, (ψ x <[- x -]> (x = c)) 
      ∧ iota_f s1 φ (fun x => c = (Iota s1 x)))).
  { now setoid_rewrite <- n14_13 in S4. }
  assert (S6 : iota_f s1 φ (fun x => iota_f s1 ψ 
      (fun y => (Iota s1 x) = (Iota s1 y)))
    ↔ iota_f s1 ψ (fun y => iota_f s1 φ (fun x =>
      (Iota s1 y) = (Iota s1 x)))).
  { now rewrite <- (n14_1 s1) in S5. }
  exact S6.
Qed.



Close Scope debug_iota_description.