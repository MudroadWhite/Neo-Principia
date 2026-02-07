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
- design a notation for all the iota functions
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

Our way to simulate this idea is firstly define a series of functions prefixed with `iota`. Functions 
provide a similar functionality to scopes. Then we allow people to write `Iota "name" x` if we 
need a iota variable, but it's just for readability. **There are nothing to rely on to check 
if they have been used correctly**, nor does it actually modify the rest of the function it 
is contained in. 

With this notation, all propositional functions with iota variables have to be written explicitly
starting with `(fun x => ...)`, in contrast to just building an arbitary proposition with iota 
variables immediately. The resulted notation is quite different from how it looks like originally, 
but it can correctly express what should a iota do and limit its scope as in the text. I suppose 
in this way we actually defined a "dual" of an incomplete definition - instead of having an unclear 
context with clear meaning, here we have a clear context with meaning out of the system.

From n14_17 and onward, we're seeing how iota should cope with the predicative functions. Currently
we are still letting iotas being "untyped", that is, being constructed based on untyped function. 
Whether we can restrict the iotas to typed functions only is a future question.

The definitions are being put into the `lib.v`. 
*)

(* TODO: make the definitions into a notation in the future 
Declare Scope single_description. *)

Definition n10_1_pred (φ : Predicate 1 → Prop) (Y : Predicate 1) : 
  (∀ x, φ x) → φ Y.
Admitted.

Definition n10_11_pred (Y : Predicate 1) (φ : Predicate 1 → Prop) : 
  φ Y → ∀ x, φ x.
Admitted.

(* NOTE: note that how the `P` here has to be Prop while the `Y` in n10_1
variant is set to `Predicate 1` *)
Definition n10_21_pred (φ : Predicate 1 → Prop) (P : Prop) :
  (∀ x : Predicate 1, P → φ x) ↔ (P → (∀ x : Predicate 1, φ x)).
Admitted.

Open Scope single_app_equiv.

Definition n14_01 (s : string) (φ ψ : Prop → Prop) : 
  (iota_f s φ ψ) = ∃ b, (φ x <[- x -]> (x = b)) ∧ ψ b. 
Admitted.

Definition n14_02 (φ : Prop → Prop) :
  (iota_E φ) = ∃ b, (φ x <[- x -]> (x = b)). 
Admitted.

(* Although `iota_f2` has been defined, expressions that involves 2 functions often
  comes up with the default interpretations as two `iota_f` rather than one `iota_f2`.
  While this doen't affect significantly how the definition organizes, it still affects
  how we should write down a theorem *)
Definition n14_03 (s1 s2 : string) (φ ψ : Prop → Prop) (f : Prop → Prop → Prop) :
  (iota_f2 s1 s2 φ ψ f) = 
    iota_f s1 φ (fun b => iota_f s2 ψ 
      (fun c => f (Iota s1 b) (Iota s2 c))).
Admitted.

Definition n14_04 (s1 s2 : string) (φ ψ : Prop → Prop) (f : Prop → Prop → Prop) : 
  (iota_f2_rev s2 s1 ψ φ f) = iota_f2 s2 s1 ψ φ (fun x y => f y x).
Admitted.

Theorem n14_1 (s : string) (φ ψ : Prop → Prop) : (iota_f s φ ψ) ↔
  ∃ b, (φ x <[- x -]> (x = b)) ∧ ψ b.
Proof.
  pose proof (n4_2 (iota_f s φ ψ)) as n4_2.
  now rewrite -> n14_01 in n4_2 at 2.
Qed.

(* The equivalent with n14_1, with scope notation in its original 
  representation omitted. With our definition, we might just make 
  another definition copying `iota_f` to indicate it is getting 
  scope notation in the text... *)
Theorem n14_101 (s : string) (φ ψ : Prop → Prop) : (iota_f s φ ψ) ↔
  ∃ b, (φ x <[- x -]> (x = b)) ∧ ψ b.
Proof. exact (n14_1 s φ ψ). Qed.

Theorem n14_11  (φ : Prop → Prop) : (iota_E φ) 
  ↔ (∃ b, φ x <[- x -]> (x = b)).
Proof.
  pose proof (n4_2 (iota_E φ)) as n4_2.
  now rewrite -> n14_02 in n4_2 at 2.
Qed.

Theorem n14_111 (s1 s2 : string) (φ ψ : Prop → Prop) 
  (f : Prop → Prop → Prop) :
  (iota_f2_rev s2 s1 ψ φ f) ↔ (∃ b c, 
    (φ x <[- x -]> (x = b)) ∧ (ψ x <[- x -]> (x = c)) ∧ (f b c)).
Proof.
  assert (S1 : iota_f2_rev s2 s1 ψ φ f ↔
    iota_f s2 ψ (fun c => iota_f s1 φ 
      (fun b => f (Iota s1 b) (Iota s2 c)))).
  {
    pose proof (n4_2 (iota_f2_rev s2 s1 ψ φ f)) as n4_2.
    rewrite -> n14_04 in n4_2 at 2.
    now rewrite -> (n14_03 s2 s1) in n4_2.
  }
  assert (S2 : iota_f2_rev s2 s1 ψ φ f ↔
    (iota_f s2 ψ (fun c =>
      ∃ b, (φ x <[- x -]> (x = b)) ∧ f b c))).
  {
    replace (λ c, iota_f s1 φ (λ b, f (Iota s1 b) (Iota s2 c)))
      with (λ c, iota_f s1 φ (λ b, f b c)) in S1 by reflexivity.
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

Theorem n14_112 (s1 s2 : string) (φ ψ : Prop → Prop) 
  (f : Prop → Prop → Prop) : 
  (iota_f2 s1 s2 φ ψ f) ↔ ∃ b c, 
    (φ x <[- x -]> x = b) ∧ (ψ x <[- x -]> x = c) ∧ f b c.
Proof.
  assert (S1 : (iota_f2 s1 s2 φ ψ f) ↔ (iota_f s1 φ 
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
  (iota_f s φ (fun x => A = (Iota s x)))
  ↔ (iota_f s φ (fun x => (Iota s x) = A)). 
Proof.
  (* TOOLS *)
  set (B := Individual "b").
  (* ******** *)
  assert (S1 : (iota_f s φ (fun x => A = (Iota s x)))
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
    ↔ (iota_f s φ (fun x => (Iota s x) = A))).
  { now rewrite <- (n14_1 s φ  (fun b => b = A)) in S3. }
  assert (S5 : (iota_f s φ (fun x => A = (Iota s x)))
    ↔ (iota_f s φ (fun x => (Iota s x) = A))).
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

Theorem n14_131_alt (s1 s2 : string) (φ ψ : Prop → Prop) : 
  iota_f2 s1 s2 φ ψ (fun x y => (Iota s1 x) = (Iota s2 y))
  ↔
  iota_f2 s2 s1 ψ φ (fun x y => (Iota s2 y) = (Iota s1 x)). 
Proof.
  assert (S1 : iota_f2 s1 s2 φ ψ (fun x y => (Iota s1 x) = (Iota s2 y))
    ↔ ∃ b c, (φ x <[- x -]> (x = b)) 
      ∧ (ψ x <[- x -]> (x = c)) ∧ (b = c)).
  {
    (* We use the definition of iota_f2 instead, for the obvious reason.
     *14.111 ignored *)
    apply n14_112.
  }
  assert (S2 : iota_f2 s1 s2 φ ψ (fun x y => (Iota s1 x) = (Iota s2 y))
    ↔ ∃ b c, (ψ x <[- x -]> (x = c)) 
      ∧ (φ x <[- x -]> (x = b)) ∧ (c = b)).
  {
    (* *11.11, *11.341 ignored *)
    setoid_rewrite -> n13_16 in S1 at 4.
    setoid_rewrite -> n4_3 in S1 at 2.
    setoid_rewrite -> n4_32 in S1.
    now setoid_rewrite -> n4_3 in S1 at 4.
  }
  assert (S3 : iota_f2 s1 s2 φ ψ (fun x y => 
      (Iota s1 x) = (Iota s2 y))
    ↔ iota_f2 s2 s1 ψ φ (fun x y => (Iota s2 y) = (Iota s1 x))).
  {
    (* much of the citations are wrong... *)
    rewrite -> n11_23 in S2.
    pose proof (n14_112 s2 s1 ψ φ
      (fun x y => Iota s2 y = Iota s1 x)) as n14_112.
    setoid_rewrite -> n13_16 in S2 at 4.
    now rewrite <- n14_112 in S2.
  }
  exact S3.
Qed.

Theorem n14_14 (A B : Prop) (s : string) (φ : Prop → Prop) :
  ((A = B) ∧ (iota_f s φ (fun x => B = (Iota s x))))
  → (iota_f s φ (fun x => A = (Iota s x))).
Proof.
  rewrite -> n4_3.
  rewrite -> n13_16.
  exact (n13_13 B A (fun a => 
      (iota_f s φ (fun x => a = (Iota s x))))).
Qed.

Theorem n14_142 (A : Prop) (s1 s2 : string) (φ ψ : Prop → Prop) :
  iota_f s1 φ (fun x => A = Iota s1 x)
    ∧ iota_f s1 φ (fun x => iota_f s2 ψ 
      (fun y => Iota s1 x = Iota s2 y))
  → iota_f s2 ψ (fun x => A = Iota s2 x).
Proof.
  assert (S1 : (iota_f s1 φ (fun x => A = Iota s1 x)
      ∧ iota_f s1 φ (fun x => iota_f s2 ψ 
        (fun y => Iota s1 x = Iota s2 y)))
    → ((∃ b, (φ x <[- x -]> (x = b)) ∧ (A = b)) 
      ∧ (∃ c, (φ x <[- x -]> (x = c)) ∧ iota_f s2 ψ 
        (fun x => c = (Iota s2 x))))).
  {
    pose proof (n14_1 s1 φ (fun b => A = Iota s1 b)) 
      as n14_1a.
    destruct n14_1a as [n14_1al _].
    pose proof (n14_1 s1 φ (fun c =>
      iota_f s2 ψ (fun y => c = Iota s2 y))) as n14_1b.
    destruct n14_1b as [n14_1bl _].
    Conj n14_1al n14_1bl C1.
    pose proof (n3_47
      (iota_f s1 φ (λ b, A = Iota s1 b))
      (iota_f s1 φ (λ c, iota_f s2 ψ (λ y, c = Iota s2 y)))
      (∃ b, (φ x <[- x -]> x = b) ∧ A = Iota s1 b)
      (∃ b, (φ x <[- x -]> x = b) ∧ iota_f s2 ψ (λ y, b = Iota s2 y))) 
      as n3_47.
    now MP n3_47 C1.
  }
  assert (S2 : (iota_f s1 φ (fun x => A = Iota s1 x)
    ∧ iota_f s1 φ (fun x => iota_f s2 ψ 
      (fun y => Iota s1 x = Iota s2 y)))
  → ((φ x <[- x -]> (x = A))
    ∧ (∃ c, (φ x <[- x -]> (x = c)) ∧ iota_f s2 ψ 
        (fun x => c = (Iota s2 x))))).
  {
    setoid_rewrite -> n4_3 in S1 at 3.
    setoid_rewrite -> n13_16 in S1 at 3.
    now rewrite -> n13_195 in S1.
  }
  assert (S3 : (iota_f s1 φ (fun x => A = Iota s1 x)
    ∧ iota_f s1 φ (fun x => iota_f s2 ψ 
      (fun y => Iota s1 x = Iota s2 y)))
  → ∃ c, (φ x <[- x -]> (x = A)) ∧ (φ x <[- x -]> (x = c)) 
      ∧ iota_f s2 ψ (fun x => c = (Iota s2 x))).
  { now rewrite <- n10_35 in S2. }
  assert (S4 : (iota_f s1 φ (fun x => A = Iota s1 x)
    ∧ iota_f s1 φ (fun x => iota_f s2 ψ 
      (fun y => Iota s1 x = Iota s2 y)))
  → ∃ c, (φ x <[- x -]> (x = A)) ∧ (A = c)
      ∧ iota_f s2 ψ (fun x => c = (Iota s2 x))).
  {
    intros Hp.
    pose proof (S3 Hp) as S3.
    (* I don't think here is provable *)
    pose proof n14_121 as n14_121.
    admit.
  }
  assert (S5 : iota_f s1 φ (fun x => A = Iota s1 x)
      ∧ iota_f s1 φ (fun x => iota_f s2 ψ 
        (fun y => Iota s1 x = Iota s2 y))
    → iota_f s2 ψ (fun x => A = Iota s2 x)).
  {
    (* I think it could be that *14.121 should be used in last step
    but in that case the *3.27 here will not be used. Aka S4 has been
    typed wrong in original text with an extra `↔` term
    TODO: we can correct both of the steps in the future *)
    pose proof Simp3_27 as Simp3_27.
    pose proof n13_195 as n13_195.
    admit.
  }
  exact S5.
Admitted.

Theorem n14_144 (s1 s2 s3 : string) (φ ψ χ : Prop → Prop) : 
  (iota_f2 s1 s2 φ ψ (fun x y => (Iota s1 x) = (Iota s2 y))
    ∧ iota_f2 s2 s3 ψ χ (fun x y => (Iota s2 x) = (Iota s3 y)))
  → iota_f2 s1 s3 φ χ (fun x y => (Iota s1 x) = (Iota s3 y)).
Proof.
  (* TOOLS *)
  set (X := Individual "x").
  set (Y := Individual "y").
  (* ******** *)
  assert (S1 : (iota_f2 s1 s2 φ ψ (fun x y => (Iota s1 x) = (Iota s2 y))
    ∧ iota_f2 s2 s3 ψ χ (fun x y => (Iota s2 x) = (Iota s3 y)))
    → ((∃ a b, (φ x <[- x -]> (x = a)) 
          ∧ (ψ x <[- x -]> (x = b)) ∧ (a = b)))
        ∧ (∃ c d, (ψ x <[- x -]> (x = c)) 
          ∧ (χ x <[- x -]> (x = d)) ∧ (c = d))).
  {
    pose proof (n14_112 s1 s2 φ ψ
      (fun x y => Iota s1 x = Iota s2 y)) as n14_112a.
    destruct n14_112a as [n14_112al _].
    pose proof (n14_112 s2 s3 ψ χ
      (fun x y => Iota s2 x = Iota s3 y)) as n14_112b.
    destruct n14_112b as [n14_112bl _].
    assert (C1 : (iota_f2 s1 s2 φ ψ (λ x y, x = y)
        → ∃ b c, (φ x <[- x -]> x = b) 
          ∧ (ψ x <[- x -]> x = c) ∧ b = c)
      ∧ (iota_f2 s2 s3 ψ χ (λ x y, x = y)
      → ∃ b c, (ψ x <[- x -]> x = b)
          ∧ (χ x <[- x -]> x = c) ∧ b = c)).
    { now Conj n14_113al n14_113bl C1. }
    pose proof (n3_47
      (iota_f2 s1 s2 φ ψ (fun x y => Iota s1 x = Iota s2 y))
      (iota_f2 s2 s3 ψ χ (fun x y => Iota s2 x = Iota s3 y))
      (∃ b c, (φ x <[- x -]> x = b) 
        ∧ (ψ x <[- x -]> x = c) ∧ b = c)
      (∃ b c, (ψ x <[- x -]> x = b)
        ∧ (χ x <[- x -]> x = c) ∧ b = c)) as n3_47.
    now MP n3_47 C1.
  }
  assert (S2 : (iota_f2 s1 s2 φ ψ (fun x y => (Iota s1 x) = (Iota s2 y))
      ∧ iota_f2 s2 s3 ψ χ (fun x y => (Iota s2 x) = (Iota s3 y)))
    → ((∃ a, (φ x <[- x -]> (x = a)) ∧ (ψ x <[- x -]> (x = a)))
      ∧ (∃ c, (ψ x <[- x -]> (x = c)) ∧ (χ x <[- x -]> (x = c))))).
  {
    (* simplifications... look at how organized it has been! *)
    intro Hp.
    pose proof (S1 Hp) as S1.
    destruct S1 as [S1l S1r].
    setoid_rewrite -> n4_3 in S1l.
    setoid_rewrite -> n4_3 in S1l at 2.
    setoid_rewrite -> n4_32 in S1l.
    setoid_rewrite -> n13_16 in S1l at 1.
    setoid_rewrite -> n13_195 in S1l.
    setoid_rewrite -> n4_3 in S1l.
    setoid_rewrite -> n4_3 in S1r.
    setoid_rewrite -> n4_3 in S1r at 2.
    setoid_rewrite -> n4_32 in S1r.
    setoid_rewrite -> n13_16 in S1r at 1.
    setoid_rewrite -> n13_195 in S1r.
    setoid_rewrite -> n4_3 in S1r.
    clear Hp.
    now Conj S1l S1r C1.
  }
  assert (S3 : (iota_f2 s1 s2 φ ψ (fun x y => (Iota s1 x) = (Iota s2 y))
      ∧ iota_f2 s2 s3 ψ χ (fun x y => (Iota s2 x) = (Iota s3 y)))
    → ∃ a c, (φ x <[- x -]> (x = a))
      ∧ (ψ x <[- x -]> (x = a)) ∧ (ψ x <[- x -]> (x = c))
      ∧ (χ x <[- x -]> (x = c))).
  {
    rewrite <- n11_54 in S2.
    now setoid_rewrite -> n4_32 in S2.
  }
  assert (S4 : (iota_f2 s1 s2 φ ψ (fun x y => (Iota s1 x) = (Iota s2 y))
      ∧ iota_f2 s2 s3 ψ χ (fun x y => (Iota s2 x) = (Iota s3 y)))
    → ∃ a c, (φ x <[- x -]> (x = a)) ∧ (χ x <[- x -]> (x = c))
      ∧ (a = c)).
  {
    (* simplifications to avoid all the tedious works *)
    (* *11.42 ignored *)
    intro Hp.
    pose proof (S3 Hp) as S3.
    pose proof n4_32 as n4_32.
    setoid_rewrite <- n4_32 in S3.
    setoid_rewrite <- n4_32 in S3.
    setoid_rewrite -> n4_3 in S3.
    setoid_rewrite -> n4_32 in S3.
    setoid_rewrite <- n4_32 in S3.
    setoid_rewrite -> n4_3 in S3 at 2.
    setoid_rewrite -> n4_3 in S3.
    clear Hp.
    (* Now we are going to construct something, "bottom up",
    with ad-hoc individuals *)
    pose proof (n14_121 X Y ψ) as n14_121.
    pose proof (Fact3_45
      ((ψ x <[- x -]> x = X) ∧ ψ x <[- x -]> x = Y)
      (X = Y)
      ((φ x <[- x -]> x = X) ∧ χ x <[- x -]> x = Y)) as Fact3_45.
    MP Fact3_45 n14_121.
    pose proof (n11_11 X Y (fun a c =>
        ((ψ x <[- x -]> x = a) ∧ ψ x <[- x -]> x = c)
        ∧ (φ x <[- x -]> x = a) ∧ χ x <[- x -]> x = c
      → a = c ∧ (φ x <[- x -]> x = a) ∧ χ x <[- x -]> x = c)) 
      as n11_11.
    MP n11_11 Fact3_45.
    pose proof (n11_34
      (fun x y =>
        (((ψ x0 <[- x0 -]> x0 = x) ∧ ψ x0 <[- x0 -]> x0 = y)
        ∧ (φ x0 <[- x0 -]> x0 = x) ∧ χ x0 <[- x0 -]> x0 = y))
      (fun x y => x = y
        ∧ (φ x0 <[- x0 -]> x0 = x) ∧ χ x0 <[- x0 -]> x0 = y)) 
      as n11_34.
    MP n11_34 n11_11.
    clear n4_32 n14_121 Fact3_45 n11_11.
    MP n11_34 S3.
    setoid_rewrite -> n4_3 in n11_34.
    now setoid_rewrite -> n4_32 in n11_34.
  }
  assert (S5 : (iota_f2 s1 s2 φ ψ (fun x y => (Iota s1 x) = (Iota s2 y))
      ∧ iota_f2 s2 s3 ψ χ (fun x y => (Iota s2 x) = (Iota s3 y)))
    → iota_f2 s1 s3 φ χ (fun x y => (Iota s1 x) = (Iota s3 y))).
  {
    pose proof (n14_112 s1 s3 φ χ (fun a c => (Iota s1 a) = (Iota s3 c))) 
      as n14_112.
    now rewrite <- n14_112 in S4.
  }
  exact S5.
Qed.

Theorem n14_145 (A : Prop) (s1 s2 : string) (φ ψ : Prop → Prop) : 
  ((iota_f s1 φ (fun x => A = (Iota s1 x))) 
    ∧ (iota_f s2 ψ (fun x => A = (Iota s2 x))))
  → (iota_f2 s1 s2 φ ψ (fun x y => (Iota s1 x) = (Iota s2 y))).
Proof.
  assert (S1 : (iota_f s1 φ (fun x => A = (Iota s1 x)))
    ↔ ∃ b, (φ x <[- x -]> (x = b)) ∧ (A = b)).
  { apply n14_1. }
  assert (S2 : (iota_f s1 φ (fun x => A = (Iota s1 x)))
    ↔ (φ x <[- x -]> (x = A))).
  {
    setoid_rewrite -> n4_3 in S1 at 2.
    setoid_rewrite -> n13_16 in S1 at 2.
    now rewrite -> n13_195 in S1.
  }
  assert (S3 : ((iota_f s1 φ (fun x => A = (Iota s1 x))) 
      ∧ (iota_f s2 ψ (fun x => A = (Iota s2 x))))
    ↔ ((φ x <[- x -]> (x = A)) ∧ (∃ b,
      (ψ x <[- x -]> (x = b)) ∧ (A = b)))).
  {
    pose proof (n14_1 s2 ψ (fun x => A = (Iota s2 x))) 
      as n14_1.
      simpl in n14_1.
    assert (C1 : (iota_f s1 φ (λ x, A = Iota s1 x) 
        ↔ φ x <[- x -]> x = A)
      ∧ (iota_f s2 ψ (λ x, A = Iota s2 x)
        ↔ ∃ b, (ψ x <[- x -]> x = b) ∧ A = Iota s2 b)).
    { clear S1. now Conj S2 n14_1 C1. }
    pose proof (n4_38
      (iota_f s1 φ (fun x => A = (Iota s1 x)))
      (iota_f s2 ψ (λ x : Prop, A = Iota s2 x))
      (φ x <[- x -]> (x = A))
      (∃ b, (ψ x <[- x -]> x = b) ∧ A = Iota s2 b)) 
      as n4_38.
    now MP n4_38 C1.
  }
  assert (S4 : ((iota_f s1 φ (fun x => A = (Iota s1 x))) 
      ∧ (iota_f s2 ψ (fun x => A = (Iota s2 x))))
    ↔ (∃ b, (φ x <[- x -]> (x = A))
      ∧ (ψ x <[- x -]> (x = b)) ∧ (A = b))).
  { now rewrite <- n10_35 in S3. }
  assert (S5 : ((iota_f s1 φ (fun x => A = (Iota s1 x))) 
      ∧ (iota_f s2 ψ (fun x => A = (Iota s2 x))))
    → (iota_f2 s1 s2 φ ψ (fun x y => (Iota s1 x) = (Iota s2 y)))).
  {
    destruct S4 as [S4 _].
    pose proof (n10_24 (fun a => ∃ b, (φ x <[- x -]> x = a) 
      ∧ (ψ x <[- x -]> x = b) ∧ a = b) A) as n10_24.
    Syll n10_24 S4 S4_1.
    pose proof (n14_112 s1 s2 φ ψ (fun a b => a = b)) as n14_112.
    now rewrite <- n14_112 in S4_1.
  }
  exact S5.
Qed.

Theorem n14_15 (B : Prop) (s : string) (φ ψ : Prop → Prop) : 
  (iota_f s φ (fun x => (Iota s x) = B))
  → (iota_f s φ (fun x => ψ (Iota s x)) ↔ ψ B).
Proof.
  assert (S1 : (iota_f s φ (fun x => (Iota s x) = B))
    → (∃ c, (φ x <[- x -]> (x = c)) ∧ (c = B))).
  { apply n14_1. }
  assert (S2 : (iota_f s φ (fun x => (Iota s x) = B))
    → (φ x <[- x -]> (x = B))).
  {
    setoid_rewrite -> n4_3 in S1.
    now rewrite -> n13_195 in S1.
  }
  assert (S3 : (iota_f s φ (fun x => (Iota s x) = B))
    → ((iota_f s φ ψ) ↔ ∃ c, 
      ((x = B) <[- x -]> (x = c)) ∧ ψ c)).
  {
    (* Simplification: for this step to be performed, S2 has become the 
    one to rewrite on the others. Technically speaking this involves the 
    alternative form for `Syll` *)
    intro Hp.
    pose proof (S2 Hp) as S2.
    pose proof (n14_1 s φ ψ) as n14_1.
    now setoid_rewrite -> S2 in n14_1.
  }
  assert (S4 : (iota_f s φ (fun x => (Iota s x) = B))
    → (iota_f s φ ψ ↔ ψ B)).
  { now rewrite -> n13_192 in S3. }
  exact S4.
Qed.

(* Predicative Variant *)
Definition n14_15_pred (B : Prop) (s : string) (φ : Prop → Prop) 
  (ψ : Predicate 1) : 
  (iota_f s φ (fun x => (Iota s x) = B))
  → (iota_f s φ (fun x => ψ (Iota s x)) ↔ ψ B).
Admitted.

Theorem n14_16 (s1 s2 : string) (φ ψ χ : Prop → Prop) :
  iota_f s1 φ (fun x => iota_f s2 ψ 
    (fun y => (Iota s1 x) = (Iota s2 y)))
  →
  (iota_f s1 φ χ ↔ iota_f s2 ψ χ).
Proof.
  (* TOOLS *)
  set (B := Individual "b").
  (* ******** *)
  assert (S1 : iota_f s1 φ (fun x => iota_f s2 ψ 
    (fun y => (Iota s1 x) = (Iota s2 y)))
    → ∃ b, (φ x <[- x -]> (x = b)) ∧
      iota_f s2 ψ (fun y => b = Iota s2 y)).
  { apply n14_1. }
  assert (S2 : (φ x <[- x -]> (x = B)) 
    → (iota_f s1 φ χ ↔ (∃ c, 
      ((x = B) <[- x -]> (x = c)) ∧ χ c))).
  {
    (* simplification as the same as previous one
    we might need to use P → P in normal way *)
    intro Hp.
    pose proof (n14_1 s1 φ χ) as n14_1.
    now setoid_rewrite -> Hp in n14_1.
  }
  assert (S3 : (φ x <[- x -]> (x = B)) →
    (iota_f s1 φ χ ↔ χ B)).
  { now rewrite -> n13_192 in S2. }
  assert (S4 : iota_f s2 ψ (fun y => B = (Iota s2 y))
    → (χ B ↔ iota_f s2 ψ (fun y => χ (Iota s2 y)))).
  {
    pose proof (n14_15 B s2 ψ χ) as n14_15.
    rewrite <- n14_13 in n14_15.
    now rewrite <- n4_21 in n14_15.
  }
  assert (S5 : ((φ x <[- x -]> (x = B)) ∧
      iota_f s2 ψ (fun y => B = (Iota s2 y)))
    → (iota_f s1 φ χ ↔ iota_f s2 ψ χ)).
  {
    assert (C1 : ((∀ x : Prop, φ x ↔ x = B) 
        → iota_f s1 φ χ ↔ χ B)
      ∧ (iota_f s2 ψ (λ y : Prop, B = Iota s2 y)
        → χ B ↔ iota_f s2 ψ (λ y : Prop, χ (Iota s2 y)))).
    { clear S1 S2. now Conj S3 S4 C1. }
    pose proof (n3_47
      (φ x <[- x -]> x = B)
      (iota_f s2 ψ (λ y, B = Iota s2 y))
      (iota_f s1 φ χ ↔ χ B)
      (χ B ↔ iota_f s2 ψ (λ y, χ (Iota s2 y)))) as n3_47.
    MP n3_47 C1.
    pose proof (n4_22 (iota_f s1 φ χ) (χ B)
      (iota_f s2 ψ (λ y : Prop, χ (Iota s2 y)))) as n4_22.
    now Syll n3_47 n4_22 S5.
  }
  assert (S6 : iota_f s1 φ (fun x => iota_f s2 ψ 
      (fun y => (Iota s1 x) = (Iota s2 y)))
    → iota_f s1 φ χ ↔ iota_f s2 ψ χ).
  {
    (* *10.2 ignored -  it doesn't fit in *)
    pose proof (n10_11 B (fun b =>
      ((∀ x, φ x ↔ x = b) ∧ iota_f s2 ψ (λ y, b = Iota s2 y))
      → (iota_f s1 φ χ ↔ iota_f s2 ψ χ))) as n10_11.
    MP n10_11 S5.
    rewrite -> n10_23 in n10_11.
    now Syll S1 n10_11 S6.
  }
  exact S6.
Qed.

Theorem n14_17 (B : Prop) (s : string) (φ : Prop → Prop) : 
  (iota_f s φ (fun x => (Iota s x) = B))
  ↔
  (∀ ψ : Predicate 1, (iota_f s φ (fun x =>
    ψ (Iota s x)) ↔ ψ B)).
Proof.
  (* TOOLS *)
  set (Iχ := Intro_pred "χ" 1).
  set (X := Individual "x").
  (* ******** *)
  assert (S1 : iota_f s φ (fun x => (Iota s x) = B)
    → (∀ ψ : Predicate 1, (iota_f s φ (fun x =>
      ψ (Iota s x)) ↔ ψ B))).
  {
    (* *10.11 ignored *)
    pose proof (n14_15_pred B s φ) as n14_15.
    now rewrite -> n10_21_pred in n14_15.
  }
  (* The following step is a beautiful demonstration on how our iota works
    with predicates. During formalization, we find out that there are even
    shorter ways to finish the proof, *but* that is due to our lack in setting
    up correct abstraction. We prefer the most conservative way to procceed
    on this step. In this way, quantified propositions will not be passed as
    parameters into functions/predicates so that the types should still be
    correct *)
  assert (S2 : ((Iχ x <[- x -]> (x = B)) 
      ∧ (∀ ψ : Predicate 1, iota_f s φ ψ ↔ ψ B))
    → (iota_f s φ (fun x => (Iota s x) = B) ↔ (B = B))).
  {
    (* left part of the ∧ *)
    pose proof (n10_1 (fun x => Iχ x ↔ (x = B)) B) 
      as n10_1a.
    (* right part of the ∧ *)
    pose proof (n10_1_pred (fun x : Predicate 1 => 
      (iota_f s φ x) ↔ x B) Iχ) as n10_1b.
    assert (C1 : ((∀ x, Iχ x ↔ x = B) → Iχ B ↔ B = B)
      ∧ ((∀ x : Predicate 1, iota_f s φ x ↔ x B) 
        → iota_f s φ Iχ ↔ Iχ B)).
    { now Conj n10_1a n10_1b C1. }
    pose proof (n3_47
      (∀ x, Iχ x ↔ x = B)
      (∀ x : Predicate 1, iota_f s φ x ↔ x B)
      (Iχ B ↔ B = B)
      (iota_f s φ Iχ ↔ Iχ B)) as n3_47.
    MP n3_47 C1.
    pose proof (n4_22 (iota_f s φ Iχ) (Iχ B)
      (B = B)) as n4_22.
    clear n10_1a n10_1b C1.
    rewrite -> n4_3 in n4_22.
    Syll n3_47 n4_22 Sy1.
    (* We can see that in the original text, `Iχ` has been substituted into
    a concrete function. Our analogue here is generalizing over this "Predicate"
    whose body is currently an "admitted" definition to further substitute into
    a concrete definition, by applying n10_1 and n10_11 variants *)
    pose proof (n10_11_pred Iχ (fun p => 
      iota_f s φ p ↔ B = B)) as n10_11a.
    clear n3_47 n4_22.
    Syll Sy1 n10_11a Sy2.
    pose proof (n10_1_pred
      (fun p => iota_f s φ p ↔ B = B)
      (fun x => Iota s x = B)) as n10_1c.
    clear Sy1 n10_11a.
    now Syll Sy2 n10_1c S2.
  }
  assert (S3 : ((Iχ x <[- x -]> (x = B)) 
      ∧ (∀ ψ : Predicate 1, iota_f s φ ψ
        ↔ ψ B))
    → iota_f s φ (fun x => (Iota s x) = B)).
  {
    (* Similar as previous one, this application on n13_15 is somthing 
    out of the context. We should add a special rule for n13_15 in the 
    future *)
    pose proof n13_15 as n13_15.
    admit.
  }
  assert (S4 : (∃ χ : Predicate 1, (χ x <[- x -]> (x = B)))
    → ((∀ ψ : Predicate 1, iota_f s φ ψ ↔ ψ B)
      → iota_f s φ (fun x => x = B))).
  {
    pose proof (Exp3_3 (Iχ x <[- x -]> x = B)
      (∀ ψ : Predicate 1, iota_f s φ ψ ↔ ψ B)
      (iota_f s φ (λ x : Prop, Iota s x = B))) as Exp3_3.
    MP Exp3_3 S3.
    pose proof (n10_11_pred Iχ (fun p =>
      (p x <[- x -]> x = B)
      → (∀ ψ : Predicate 1, iota_f s φ ψ ↔ ψ B)
      → iota_f s φ (λ x : Prop, Iota s x = B))) as n10_11.
    MP n10_11 Exp3_3.
    now rewrite -> n10_23_pred in n10_11.
  }
  assert (S5 : ∃ χ : Predicate 1, χ x <[- x -]> (x = B)).
  {
    pose proof (n12_1 1 (fun x => x = B)) as n12_1.
    now setoid_rewrite -> n4_21 in n12_1.
  }
  assert (S6 : (∀ ψ : Predicate 1, 
      (iota_f s φ ψ) ↔ ψ B) 
    → iota_f s φ (fun x => (Iota s x) = B)).
  { now MP S4 S5. }
  assert (S7 : (iota_f s φ (fun x => (Iota s x) = B))
    ↔ (∀ ψ : Predicate 1, (iota_f s φ (fun x =>
      ψ (Iota s x)) ↔ ψ B))).
  {
    assert (C1 : (iota_f s φ (λ x, Iota s x = B)
        → ∀ ψ : Predicate 1, iota_f s φ ψ ↔ ψ B)
      ∧ ((∀ ψ : Predicate 1, iota_f s φ ψ ↔ ψ B)
        → iota_f s φ (λ x, Iota s x = B))).
    { clear S2 S3 S4 S5. now Conj S1 S6 C1. }
    now Equiv C1.
  }
  exact S7.
Admitted.

Theorem n14_171 (B : Prop) (s : string) (φ : Prop → Prop) : 
  (iota_f s φ (fun x => (Iota s x) = B))
  ↔
  (∀ ψ : Predicate 1, ψ B → iota_f s φ ψ).
Proof.
  assert (S1 : (iota_f s φ (fun x => (Iota s x) = B))
    → (∀ ψ : Predicate 1, ψ B → iota_f s φ ψ)).
  { apply n14_17. }
  assert (S2 : (∀ ψ : Predicate 1, ψ B → iota_f s φ ψ)
    → ((B = B) → iota_f s φ (fun x => (Iota s x) = B))).
  {
    (* *12.1 ignored - I don't know if we need this or how is
    it being used actually. This might be something important *)
    pose proof (n10_1_pred
      (fun p => p B → iota_f s φ p) 
      (fun x => x = B)) as n10_1.
    exact n10_1.
  }
  assert (S3 : (∀ ψ : Predicate 1, ψ B → iota_f s φ ψ)
    → iota_f s φ (fun x => (Iota s x) = B)).
  {
    (* as always... *)
    pose proof n13_15 as n13_15.
    admit.
  }
  assert (S4 : (iota_f s φ (fun x => (Iota s x) = B))
    ↔ (∀ ψ : Predicate 1, ψ B → iota_f s φ ψ)).
  {
    clear S2.
    Conj S1 S3 C1.
    now Equiv C1.
  }
  exact S4.
Admitted.

Theorem n14_18 (s : string) (φ ψ : Prop → Prop) :
  iota_E φ → ((∀ x, ψ x) → iota_f s φ (fun x =>
    ψ (Iota s x))).
Proof.
  (* TOOLS *)
  set (B := Individual "b").
  (* ******** *)
  assert (S1 : (∀ x, ψ x) → ψ B).
  { apply n10_1. }
  assert (S2 : ((φ x <[- x -]> (x = B)) ∧ (∀ x, ψ x))
    → ((φ x <[- x -]> (x = B)) ∧ ψ B)).
  {
    pose proof (Fact3_45 (∀ x, ψ x)
      (ψ B) ((φ x <[- x -]> (x = B)))) as Fact3_45.
    MP Fact3_45 S1.
    rewrite -> n4_3 in Fact3_45.
    now setoid_rewrite -> n4_3 in Fact3_45 at 2.
  }
  assert (S3 : ((∃ b, (φ x <[- x -]> (x = b)) ∧ ∀ x, ψ x))
    → (∃ b, (φ x <[- x -]> (x = b)) ∧ ψ b)).
  {
    pose proof (n10_11 B (fun b =>
      ((φ x <[- x -]> (x = b)) ∧ (∀ x, ψ x))
      → ((φ x <[- x -]> (x = b)) ∧ ψ b))) as n10_11.
    MP n10_11 S2.
    pose proof (n10_28
      (fun b => (φ x <[- x -]> (x = b)) ∧ (∀ x, ψ x))
      (fun b => (φ x <[- x -]> (x = b)) ∧ ψ b)) as n10_28.
    now MP n10_28 n10_11.
  }
  assert (S4 : ((∃ b, (φ x <[- x -]> (x = b))) ∧ ∀ x, ψ x)
    → (∃ b, (φ x <[- x -]> (x = b)) ∧ ψ b)).
  {
    setoid_rewrite n4_3 in S3 at 1.
    rewrite -> n10_35 in S3.
    now rewrite -> n4_3 in S3 at 1.
  }
  assert (S5 : (iota_E φ ∧ ∀ x, ψ x) → iota_f s φ (fun x =>
    ψ (Iota s x))).
  {
    rewrite <- (n14_1 s) in S4.
    now rewrite <- n14_11 in S4.
  }
  assert (S6 : iota_E φ → ((∀ x, ψ x) → iota_f s φ (fun x =>
    ψ (Iota s x)))).
  {
    pose proof (Exp3_3 (iota_E φ) (∀ x, ψ x)
      (iota_f s φ (fun x => ψ (Iota s x)))) as Exp3_3.
    now MP Exp3_3 S5.
  }
  exact S6.
Qed.

Theorem n14_2 (A : Prop) (s : string) : 
  iota_f s (fun x => x = A) (fun y => (Iota s y) = A).
Proof.
  (* TOOLS *)
  set (X := Individual "x").
  (* ******** *)
  assert (S1 : (iota_f s (fun x => x = A) (fun y => (Iota s y) = A))
    <-> (∃ b, ((x = A) <[- x -]> (x = b)) /\ (b = A))).
  { apply n14_101. }
  assert (S2 : (iota_f s (fun x => x = A) (fun y => (Iota s y) = A))
    <-> ((x = A) <[- x -]> (x = A))).
  {
    setoid_rewrite -> n4_3 in S1 at 2.
    now rewrite -> (n13_195 A) in S1.
  }
  assert (S3 : iota_f s (fun x => x = A) (fun y => (Iota s y) = A)).
  {
    (* I think Id2_08 is unclear to use, so we use another way
    to do this instead... *)
    pose proof (n4_2 (X = A)) as n4_2.
    pose proof (n10_11 X (fun x => x = A ↔ x = A)) as n10_11.
    MP n10_11 n4_2.
    now rewrite <- S2 in n10_11.
  }
  exact S3.
Qed.

Theorem n14_201 (φ : Prop → Prop) : iota_E φ → ∃ x, φ x. 
Proof.
  (* TOOLS *)
  set (X := Individual "x").
  set (B := Individual "b").
  (* ******** *)
  assert (S1 : iota_E φ -> ∃ b, (φ x <[- x -]> (x = b))).
  { apply n14_11. }
  assert (S2 : iota_E φ -> ∃ b, (φ b <-> (b = b))).
  {
    intro Hp.
    pose proof (S1 Hp) as S1.
    pose proof (n10_1 (fun x => φ x <-> (x = B)) B) as n10_1.
    (* Note that we're having quantifiers in the function body *)
    pose proof (n10_11 B (fun b => (φ x <[- x -]> x = b) 
      -> (φ b <-> (b = b)))) as n10_11.
    MP n10_11 n10_1.
    pose proof (n10_28
      (fun b => φ x <[- x -]> x = b)
      (fun b => φ b ↔ b = b)) as n10_28.
    MP n10_28 n10_11.
    now MP n10_28 S1.
  }
  assert (S3 : iota_E φ -> ∃ x, φ x).
  {
    (* Same issue *)
    pose proof n13_15 as n13_15.
    admit.
  }
  exact S3.
Admitted.

Theorem n14_202 (B : Prop) (s : string) (φ : Prop → Prop) : 
  ((φ x <[- x -]> x = B) ↔ (iota_f s φ (fun x => (Iota s x) = B)))
  ∧
  ((iota_f s φ (fun x => (Iota s x) = B)) ↔ (φ x <[- x -]> B = x))
  ∧
  ((φ x <[- x -]> B = x) ↔ (iota_f s φ (fun x => B = (Iota s x)))).
Proof.
  assert (S1 : (iota_f s φ (fun x => (Iota s x) = B))
    <-> (∃ c, (φ x <[- x -]> (x = c)) /\ (c = B))).
  { apply n14_1. }
  assert (S2 : (iota_f s φ (fun x => (Iota s x) = B))
    <-> (φ x <[- x -]> (x = B))).
  {
    setoid_rewrite -> n4_3 in S1 at 2.
    now rewrite -> n13_195 in S1.
  }
  assert (S3 : ((φ x <[- x -]> x = B) ↔ (iota_f s φ (fun x => (Iota s x) = B)))
    ∧ ((iota_f s φ (fun x => (Iota s x) = B)) ↔ (φ x <[- x -]> B = x))
    ∧ ((φ x <[- x -]> B = x) ↔ (iota_f s φ (fun x => B = (Iota s x))))).
  {
    assert (S3_1 : ((φ x <[- x -]> x = B) ↔ (iota_f s φ (fun x => (Iota s x) = B)))).
    { now rewrite -> n4_21 in S2. }
    assert (S3_2 : ((iota_f s φ (fun x => (Iota s x) = B)) ↔ (φ x <[- x -]> B = x))).
    { now setoid_rewrite -> n13_16 in S2 at 2. }
    assert (S3_3 : ((φ x <[- x -]> B = x) ↔ (iota_f s φ (fun x => B = (Iota s x))))).
    {
      assert (S3_3 : (iota_f s φ (fun x => B = (Iota s x)))
        <-> (∃ c, (φ x <[- x -]> (x = c)) /\ (B = c))).
      { apply n14_1. }
      setoid_rewrite -> n4_3 in S3_3 at 2.
      setoid_rewrite -> n13_16 in S3_3 at 2.
      rewrite -> n13_195 in S3_3.
      rewrite -> n4_21 in S3_3.
      now setoid_rewrite -> n13_16 in S3_3 at 1.
    }
    assert (C1 : (iota_f s φ (λ x, Iota s x = B) ↔ φ x <[- x -]> B = x)
      /\ (φ x <[- x -]> B = x  ↔ iota_f s φ (λ x, B = Iota s x))).
    { clear S3_1. now Conj S3_2 S3_3 C1. }
    clear S2 S3_2 S3_3.
    now Conj S3_1 C1 S3.
  }
  exact S3.
Qed.

Theorem n14_203 (φ : Prop → Prop) : iota_E φ 
  ↔ ((∃ x, φ x) ∧ ((φ x ∧ φ y)) -[ x y ]> (x = y)).
Proof.
  (* TOOLS *)
  set (B := Individual "b").
  set (X := Individual "x").
  (* ******** *)
  assert (S1 : iota_E φ -> ((∃ x, φ x) 
    /\ (φ x /\ φ y) -[ x y ]> (x = y))).
  {
    pose proof (n14_201 φ) as n14_201.
    pose proof (n14_12 φ) as n14_12.
    Conj n14_201 n14_12 C1.
    now rewrite -> n4_76 in C1.
  }
  assert (S2 : (φ B /\ ((φ x /\ φ y) -[ x y ]> (x = y)))
    -> (φ B /\ ((φ x /\ φ B) -[ x ]> (x = B)))).
  {
    pose proof (n10_1 (fun y => 
      (φ x ∧ φ y) -[ x ]> x = y) B) as n10_1.
    simpl in n10_1. (* This cannot be deleted *)
    setoid_rewrite -> n13_16 in n10_1 at 1.
    pose proof (Fact3_45
      ((φ x0 ∧ φ x) -[ x x0 ]> x = x0)
      ((φ x ∧ φ B) -[ x ]> x = B)
      (φ B)) as Fact3_45.
    MP Fact3_45 n10_1.
    rewrite -> n4_3 in Fact3_45.
    setoid_rewrite -> n4_3 in Fact3_45 at 2.
    now setoid_rewrite -> n4_3 in Fact3_45 at 3.
  }
  assert (S3 : (φ B /\ ((φ x /\ φ y) -[ x y ]> (x = y)))
    -> (φ B /\ (φ x -[ x ]> (x = B)))).
  {
    pose proof (n10_1 (fun x => ((φ x /\ φ B) -> (x = B)) ∧ φ B) X) as n10_1.
    rewrite -> n10_33 in n10_1.
    rewrite -> n4_3 in n10_1.
    Syll S2 n10_1 Sy1.
    setoid_rewrite -> n4_3 in Sy1 at 3.
    setoid_rewrite -> n4_3 in Sy1 at 4.
    setoid_rewrite <- n5_33 in Sy1.
    pose proof (n10_11 X (fun x => φ x → x = B)) as n10_11.
    pose proof (Fact3_45 (φ X → X = B)
      (φ x -[ x ]> x = B) (φ B)) as Fact3_45.
    MP Fact3_45 n10_11.
    rewrite -> n4_3 in Fact3_45.
    setoid_rewrite -> n4_3 in Fact3_45 at 2.
    now Syll Sy1 Fact3_45 S3.
  }
  assert (S4 : (φ B /\ ((φ x /\ φ y) -[ x y ]> (x = y)))
    -> (((x = B) -[ x ]> φ x) /\ (φ x -[ x ]> (x = B)))).
  {
    pose proof (n13_191 B φ) as n13_191.
    now rewrite <- n13_191 in S3 at 2.
  }
  assert (S5 : (φ B /\ ((φ x /\ φ y) -[ x y ]> (x = y)))
    -> (φ x <[- x -]> (x = B))).
  {
    (* Simplifications... *)
    intro Hp.
    pose proof (S4 Hp) as S4.
    rewrite <- n10_22 in S4.
    pose proof n10_22 as n10_22.
    replace (∀ x, (x = B → φ x) ∧ (φ x → x = B))
      with (∀ x, x = B <-> φ x) in S4 by reflexivity.
    now setoid_rewrite -> n4_3 in S4.
  }
  assert (S6 : (∃ b, φ b /\ ((φ x /\ φ y) -[ x y ]> (x = y)))
    -> (∃ b, φ x <[- x -]> (x = b))).
  {
    (* *10.1 ignored - I think its the wrong one *)
    pose proof (n10_11 B (fun b => φ b ∧
        ((φ x ∧ φ y) -[ x y ]> x = y)
      → (φ x <[- x -]> x = b))) as n10_11.
    (* simpl in n10_1. *)
    MP n10_11 S5.
    pose proof (n10_28
      (fun b => φ b ∧ ((φ x ∧ φ y) -[ x y ]> x = y))
      (fun b => (φ x <[- x -]> x = b))) as n10_28.
    now MP n10_28 n10_11.
  }
  assert (S7 : (∃ b, φ b) /\ ((φ x /\ φ y) -[ x y ]> (x = y))
    -> (∃ b, φ x <[- x -]> (x = b))).
  {
    setoid_rewrite -> n4_3 in S6 at 1.
    rewrite -> n10_35 in S6.
    now setoid_rewrite -> n4_3 in S6 at 1.
  }
  assert (S8 : (∃ b, φ b) /\ ((φ x /\ φ y) -[ x y ]> (x = y))
    -> iota_E φ).
  {
    now rewrite <- n14_11 in S7.
  }
  assert (S9 : iota_E φ 
    ↔ ((∃ x, φ x) ∧ ((φ x ∧ φ y)) -[ x y ]> (x = y))).
  {
    clear S2 S3 S4 S5 S6 S7.
    Conj S1 S8 S9.
    now Equiv S9.
  }
  exact S9.
Qed.

Theorem n14_204 (B : Prop) (s : string) (φ : Prop → Prop) : iota_E φ 
  ↔ ∃ b, (iota_f s φ (fun x => (Iota s x) = b)).
Proof.
  (* TOOLS *)
  (* ******** *)
  (* Notice that the following proposition involves 2 quantifiers already, 
    so it might have a higher type..? *)
  assert (S1 : ∀ b, (φ x <[- x -]> (x = b))
    <-> iota_f s φ (fun x => (Iota s x) = b)).
  {
    pose proof (n14_202 B s φ) as n14_202.
    (* simplifictaions *)
    destruct n14_202 as [n14_202l _].
    pose proof (n10_11 B (fun b => (φ x <[- x -]> x = b) <->
      iota_f s φ (λ x, Iota s x = b))) as n10_11.
    now MP n10_11 n14_202l.
  }
  assert (S2 : (∃ b, (φ x <[- x -]> (x = b)))
    <-> (∃ b, iota_f s φ (λ x, Iota s x = b))).
  {
    pose proof (n10_281 (fun b => φ x <[- x -]> x = b)
      (fun b => iota_f s φ (λ x, Iota s x = b))) as n10_281.
    now MP n10_281 S1.
  }
  assert (S3 : iota_E φ ↔ ∃ b, (iota_f s φ (fun x => 
    (Iota s x) = b))).
  { now rewrite <- n14_11 in S2. }
  exact S3.
Qed.

Theorem n14_205 (s : string) (φ ψ : Prop → Prop) : (iota_f s φ ψ)
  ↔ ∃ b, (iota_f s φ (fun x => b = (Iota s x))) ∧ ψ b.
Proof.
  set (B := Individual "b").
  pose proof (n14_202 B s φ) as n14_202.
  destruct n14_202 as [_ n14_202r].
  destruct n14_202r as [_ n14_202rr].
  pose proof (n4_36 (φ x <[- x -]> B = x) (iota_f s φ (λ x, B = Iota s x))
    (ψ B)) as n4_36.
  MP n4_36 n14_202rr.
  pose proof (n10_11 B (fun b => (φ x <[- x -]> b = x ) ∧ ψ b 
    ↔ iota_f s φ (λ x, b = Iota s x) ∧ ψ b)) as n10_11.
  MP n10_11 n4_36.
  pose proof (n10_281 (fun b => (φ x <[- x -]> b = x ) ∧ ψ b)
    (fun b => iota_f s φ (λ x, b = Iota s x) ∧ ψ b)) as n10_281.
  MP n10_281 n10_11.
  setoid_rewrite -> n13_16 in n10_281 at 1.
  now rewrite <- (n14_1 s) in n10_281.
Qed.

Theorem n14_21 (s : string) (φ ψ : Prop → Prop) : (iota_f s φ ψ) → iota_E φ.
Proof.
  assert (S1 : iota_f s φ ψ -> ∃ b, 
    (φ x <[- x -]> (x = b)) /\ ψ b).
  { apply n14_1. }
  assert (S2 : iota_f s φ ψ -> ∃ b, 
    (φ x <[- x -]> (x = b))).
  {
    (* simplifications *)
    intros Hp.
    pose proof (S1 Hp) as S1.
    pose proof (n10_5
      (fun b => φ x <[- x -]> (x = b)) ψ) as n10_5.
    MP n10_5 S1.
    now destruct n10_5.
  }
  assert (S3 : iota_f s φ ψ -> iota_E φ).
  { now rewrite <- n14_11 in S2. }
  exact S3.
Qed.

Theorem n14_22 (s : string) (φ : Prop → Prop) : iota_E φ ↔ iota_f s φ φ.
Proof.
  (* TOOLS *)
  set (B := Individual "b").
  (* ******** *)
  assert (S1 : (φ x <[- x -]> (x = B)) -> φ B).
  { apply n14_122. }
  assert (S2 : (φ x <[- x -]> (x = B)) 
    <-> ((φ x <[- x -]> (x = B)) /\ φ B)).
  { now rewrite -> n4_71 in S1. }
  assert (S3 : (∃ b, (φ x <[- x -]> (x = b))) 
    <-> (∃ b, (φ x <[- x -]> (x = b)) /\ φ b)).
  { 
    pose proof (n10_11 B (fun b => φ x <[- x -]> x = b
      ↔ (φ x <[- x -]> x = b) ∧ φ b)) as n10_11.
    MP n10_11 S2.
    pose proof (n10_281 (fun b => φ x <[- x -]> x = b)
      (fun b => (φ x <[- x -]> x = b) ∧ φ b)) as n10_281.
    now MP n10_281 n10_11.
  }
  assert (S4 : iota_E φ ↔ iota_f s φ φ).
  { now rewrite <- n14_11, <- (n14_101 s) in S3. }
  exact S4.
Qed.

(* This is a proposition where iotas are more than just a function. 
  Correspondingly we set up some ad hoc and very simple rules for its
  string representatives. *)
Theorem n14_23 (s1 s2 : string) (φ ψ : Prop → Prop) : iota_E (fun x => φ x ∧ ψ x) 
  ↔ iota_f (s1 ++ "/\" ++ s2) (fun x => φ x ∧ ψ x) φ.
Proof.
  (* TOOLS *)
  Open Scope string.
  set (s := s1 ++ "/\" ++ s2).
  Close Scope string.
  (* ******** *)
  assert (S1 : iota_E (fun x => φ x ∧ ψ x)
    <-> iota_f s (fun x => φ x /\ ψ x)
      (fun x => φ (Iota s x) /\ ψ (Iota s x))).
  { apply n14_22. }
  assert (S2 : iota_E (fun x => φ x ∧ ψ x) -> iota_f s 
    (fun x => φ x /\ ψ x) φ).
  {
    destruct S1 as [S1_l _].
    (* simplifications *)
    intro Hp.
    pose proof (S1_l Hp) as S1_l.
    rewrite -> n14_01 in S1_l.
    setoid_rewrite <- n4_32 in S1_l.
    pose proof (n10_5
      (fun b => ((φ x ∧ ψ x) <[- x -]> x = b) 
        ∧ φ (Iota s b))
      (fun b => ψ (Iota s b))) as n10_5a.
    MP n10_5a S1_l.
    (* Note that we have to use mere `x` manually here instead
    of `Iota s x` to perform rewrite for n14_01 *)
    pose proof (Simp3_26
      (∃ x, ((φ x0 ∧ ψ x0) <[- x0 -]> x0 = x) ∧ φ x)
        (* ∧ φ (Iota s x)) *)
      (∃ x, ψ (Iota s x))) as Simp3_26.
    MP Simp3_26 n10_5a.
    now rewrite <- (n14_01 s (fun x => φ x ∧ ψ x) φ) in Simp3_26.
  }
  assert (S3 : iota_f s (fun x => φ x /\ ψ x) φ
    -> iota_E (fun x => φ x /\ ψ x)).
  { apply n14_21. }
  assert (S4 : iota_E (fun x => φ x ∧ ψ x) 
    ↔ iota_f (s1 ++ "/\" ++ s2) (fun x => φ x ∧ ψ x) φ).
  {
    clear S1. 
    now Syll S2 S3 S4.
  }
  exact S4.
Qed.

Theorem n14_24 (s : string) (φ : Prop → Prop) : iota_E φ 
  ↔ iota_f s φ (fun x => φ y <[- y -]> y = (Iota s x)).
Proof.
  assert (S1 : iota_f s φ (fun x => φ y <[- y -]> y = (Iota s x))
    <-> ∃ b, (φ y <[- y -]> (y = b)) 
      /\ (φ y <[- y -]> (y = b))).
  { apply n14_1. }
  assert (S2 : iota_f s φ (fun x => φ y <[- y -]> y = (Iota s x))
    <-> ∃ b, (φ y <[- y -]> (y = b))).
  {
    (* n10_281 ignored *)
    now setoid_rewrite <- n4_24 in S1.
  }
  assert (S3 : iota_f s φ (fun x => φ y <[- y -]> y = (Iota s x))
    <-> iota_E φ).
  { now rewrite <- n14_11 in S2. }
  assert (S4 : iota_E φ 
    ↔ iota_f s φ (fun x => φ y <[- y -]> y = (Iota s x))).
  { now rewrite -> n4_21 in S3. }
  exact S4.
Qed.

Theorem n14_241 (s : string) (φ : Prop → Prop) : iota_E φ
  → (φ y <[- y -]> iota_f s φ (fun x => y = (Iota s x))).
Proof.
  (* TOOLS *)
  set (X := Individual "x").
  set (Y := Individual "y").
  set (λ P0 Q0 : Prop, eq_to_equiv (P0 ↔ Q0) ((P0 → Q0) ∧ (Q0 → P0)) 
    (Equiv4_01 P0 Q0))
  as Equiv4_01a.
  (* ******** *)
  assert (S1 : iota_E φ -> ((φ Y /\ φ X) -> (Y = X))).
  {
    pose proof (n14_203 φ) as n14_203.
    destruct n14_203 as [n14_203l _].
    (* simplifications... TODO: this can be removed easily in the future *)
    intro Hp.
    pose proof (n14_203l Hp) as n14_203l.
    pose proof (Simp3_27 (∃ x, φ x) ((φ x ∧ φ y) -[ x y ]> x = y)) 
      as Simp3_27.
    MP Simp3_27 n14_203l.
    (* I doubt if this is allowed in the system... *)
    pose proof (n10_1 (fun x => (φ x ∧ φ y) -[ y ]> x = y) X) 
      as n10_1a.
    MP n10_1a Simp3_27.
    pose proof (n10_1 (fun y => (φ X ∧ φ y) -> X = y) Y)
      as n10_1b.
    MP n10_1b n10_1a.
    now rewrite -> n13_16, -> n4_3 in n10_1b.
  }
  assert (S2 : iota_E φ -> (φ Y -> (φ X -> (Y = X)))).
  {
    intro Hp.
    pose proof (S1 Hp) as S1.
    pose proof (Exp3_3 (φ Y) (φ X) (Y = X)) as Exp3_3.
    now MP Exp3_3 S1.
  }
  assert (S3 : iota_E φ -> (φ Y -> (φ x -[ x ]> (Y = x)))).
  {
    intro Hp.
    pose proof (S2 Hp) as S2.
    pose proof (n10_11 X (fun x => φ Y -> (φ x -> Y = x))) as n10_11.
    clear S1.
    MP n10_11 S2.
    now rewrite -> n10_21 in n10_11.
  }
  assert (S4 : iota_E φ -> (φ Y <-> φ Y /\ (φ x -[ x ]> (Y = x)))).
  { now setoid_rewrite -> n4_71 in S3 at 2. }
  assert (S5 : iota_E φ -> (φ Y <-> ((Y = x) -[ x ]> φ x) 
    /\ (φ x -[ x ]> (Y = x)))).
  {
    rewrite <- (n13_191 Y) in S4 at 2.
    now setoid_rewrite -> n13_16 in S4 at 1.
  }
  assert (S6 : iota_E φ -> (φ Y <-> (φ x <[- x -]> (Y = x)))).
  {
    intro Hp.
    pose proof (S5 Hp) as S5.
    rewrite <- n10_22 in S5.
    setoid_rewrite <- Equiv4_01a in S5.
    now setoid_rewrite -> n4_21 in S5 at 2.
  }
  assert (S7 : iota_E φ -> (φ Y <-> iota_f s φ 
    (fun x => Y = (Iota s x)))).
  {
    pose proof (n14_202 Y s φ) as n14_202.
    destruct n14_202 as [_ n14_202r].
    destruct n14_202r as [_ n14_202rr].
    now rewrite -> n14_202rr in S6.
  }
  assert (S8 : iota_E φ → (φ y <[- y -]> iota_f s φ 
    (fun x => y = (Iota s x)))).
  {
    intro Hp.
    pose proof (S7 Hp) as S7.
    pose proof (n10_11 Y (fun y => φ y ↔ iota_f s φ 
      (λ x, y = Iota s x))) as n10_11.
    clear S1 S2 S3 S4 S5 S6.
    now MP n10_11 S7.
  }
  exact S8.
Qed.

Theorem n14_242 (B : Prop) (s : string) (φ ψ : Prop → Prop) : (φ x <[- x -]> x = B)
  → (ψ B ↔ iota_f s φ ψ).
Proof.
  pose proof (n14_202 B s φ) as n14_202.
  destruct n14_202 as [n14_202l _].
  destruct n14_202l as [n14_202ll _].
  pose proof (n14_15 B s φ ψ) as n14_15.
  Syll n14_202ll n14_15 S1.
  now rewrite -> n4_21 in S1.
Qed.

Theorem n14_25 (s : string) (φ ψ : Prop → Prop) : iota_E φ 
  → ((φ x -[ x ]> ψ x) ↔ iota_f s φ ψ).
Proof.
  (* TOOLS *)
  set (B := Individual "b").
  set (X := Individual "x").
  (* ******** *)
  assert (S1 : (φ x <[- x -]> (x = B)) -> ((φ x -[ x ]> ψ x)
    <-> ((x = B) -[ x ]> ψ x))).
  {
    pose proof (n4_84 (φ X) (X = B) (ψ X)) as n4_84.
    pose proof (n10_11 X (fun x =>
      (φ x ↔ x = B) -> ((φ x → ψ x) <-> (x = B → ψ x))))
      as n10_11.
    MP n10_11 n4_84.
    pose proof (n10_27 (fun x => φ x ↔ x = B)
      (fun x => (φ x → ψ x) ↔ (x = B → ψ x))) as n10_27.
    MP n10_27 n10_11.
    pose proof (n10_271 (fun z => φ z → ψ z)
      (fun z => z = B → ψ z)) as n10_271.
    now Syll n10_27 n10_271 S1.
  }
  assert (S2 : (φ x <[- x -]> (x = B)) -> ((φ x -[ x ]> ψ x)
    <-> ψ B)).
  { now rewrite -> n13_191 in S1. }
  assert (S3 : (φ x <[- x -]> (x = B)) -> ((φ x -[ x ]> ψ x)
    <-> iota_f s φ ψ)).
  {
    (* simplifications *)
    intro Hp.
    pose proof (S2 Hp) as S2.
    pose proof (n14_242 B s φ ψ) as n14_242.
    MP n14_242 Hp.
    now rewrite -> n14_242 in S2.
  }
  assert (S4 : (∃ b, φ x <[- x -]> (x = b)) 
    -> ((φ x -[ x ]> ψ x) <-> iota_f s φ ψ)).
  {
    pose proof (n10_11 B (fun b => (φ x <[- x -]> (x = b)) 
      -> ((φ x -[ x ]> ψ x) <-> iota_f s φ ψ))) as n10_11.
    MP n10_11 S3.
    now rewrite -> n10_23 in n10_11.
  }
  assert (S5 : iota_E φ → ((φ x -[ x ]> ψ x) 
    ↔ iota_f s φ ψ)).
  { now rewrite <- n14_11 in S4. }
  exact S5.
Qed.

Theorem n14_26 (s : string) (φ ψ : Prop → Prop) : iota_E φ 
  → ((∃ x, φ x ∧ ψ x) ↔ iota_f s φ ψ)
    ∧ ((iota_f s φ ψ) ↔ (φ x -[ x ]> ψ x)).
Proof.
  (* TOOLS *)
  set (B := Individual "b").
  (* ******** *)
  assert (S1 : iota_E φ -> ∃ b, φ x <[- x -]> (x = b)).
  { apply n14_11. }
  assert (S2 : (φ x <[- x -]> (x = B))
    -> ((φ x /\ ψ x) <[- x -]> ((x = B) /\ ψ x))).
  { apply n10_311. }
  assert (S3 : (φ x <[- x -]> (x = B))
    -> ((∃ x, φ x /\ ψ x) <-> (∃ x, (x = B) /\ ψ x))).
  {
    pose proof (n10_281 (fun x => φ x /\ ψ x)
      (fun x => (x = B) /\ ψ x)) as n10_281.
    now Syll S2 n10_281 S3.
  }
  assert (S4 : (φ x <[- x -]> (x = B))
    -> ((∃ x, φ x /\ ψ x) <-> ψ B)).
  { now rewrite -> n13_195 in S3. }
  assert (S5 : (φ x <[- x -]> (x = B))
    -> ((∃ x, φ x /\ ψ x) <-> iota_f s φ ψ)).
  { 
    (* simplifications *)
    intro Hp.
    pose proof (S4 Hp) as S4.
    pose proof (n14_242 B s φ ψ) as n14_242.
    MP n14_242 Hp.
    now rewrite -> n14_242 in S4.
  }
  assert (S6 : (∃ b, φ x <[- x -]> (x = b))
    -> ((∃ x, φ x /\ ψ x) <-> iota_f s φ ψ)).
  {
    pose proof (n10_11 B (fun b => (φ x <[- x -]> (x = b))
      -> ((∃ x, φ x /\ ψ x) <-> iota_f s φ ψ))) 
      as n10_11.
    MP n10_11 S5.
    now rewrite -> n10_23 in n10_11.
  }
  assert (S7 : iota_E φ 
    → ((∃ x, φ x ∧ ψ x) ↔ iota_f s φ ψ)
      ∧ ((iota_f s φ ψ) ↔ (φ x -[ x ]> ψ x))).
  {
    (* simplifications *)
    intro Hp.
    clear S2 S3 S4 S5.
    pose proof (S1 Hp) as S1.
    MP S6 S1.
    pose proof (n14_25 s φ ψ) as n14_25.
    MP n14_25 Hp.
    rewrite -> n4_21 in n14_25.
    now Conj S1 n14_25 S7.
  }
  exact S7.
Qed.

Theorem n14_27 (s1 s2 : string) (φ ψ : Prop → Prop) : iota_E φ 
  → ((φ x <[- x -]> ψ x) ↔ iota_f s1 φ (fun x => 
    iota_f s2 ψ (fun y => (Iota s1 x) = (Iota s2 y)))).
Proof.
  (* TOOLS *)
  set (B := Individual "b").
  set (X := Individual "x").
  (* ******** *)
  assert (S1 : (φ X <-> (X = B)) 
    -> ((φ X <-> ψ X) <-> (ψ X <-> (X = B)))).
  { 
    pose proof (n4_86 (φ X) (X = B) (ψ X)) as n4_86.
     (*simplification  *)
    intro Hp.
    MP n4_86 Hp.
    now setoid_rewrite -> n4_21 in n4_86 at 3.
  }
  assert (S2 : (φ x <[- x -]> (x = B)) 
    -> (∀ x, (φ x <-> ψ x) <-> (ψ x <-> (x = B)))).
  {
    pose proof (n10_11 X (fun x =>
      (φ x <-> (x = B)) -> ((φ x <-> ψ x) 
        <-> (ψ x <-> (x = B))))) as n10_11.
    MP n10_11 S1.
    pose proof (n10_27 (fun x => φ x <-> (x = B))
      (fun x => (φ x <-> ψ x) <-> (ψ x <-> (x = B)))) as n10_27.
    now MP n10_27 n10_11.
  }
  assert (S3 : (φ x <[- x -]> (x = B))
    -> ((φ x <[- x -]> ψ x) <-> (ψ x <[- x -]> (x = B)))).
  {
    pose proof (n10_271 (fun x => φ x <-> ψ x)
      (fun x => ψ x <-> (x = B))) as n10_271.
    now Syll S2 n10_271 S3.
  }
  assert (S4 : (φ x <[- x -]> (x = B))
    -> ((φ x <[- x -]> ψ x) <-> iota_f s2 ψ (fun x =>
      (B = (Iota s2 x))))).
  {
    pose proof (n14_202 B s2 ψ) as n14_202.
    destruct n14_202 as [_ n14_202r].
    destruct n14_202r as [_ n14_202rr].
    setoid_rewrite -> n13_16 in S3 at 2.
    now rewrite -> n14_202rr in S3.
  }
  assert (S5 : (φ x <[- x -]> (x = B))
    -> ((φ x <[- x -]> ψ x) <-> iota_f s1 φ (fun x => iota_f s2 ψ 
      (fun y => (Iota s1 x) = (Iota s2 y))))).
  {
    (* simplifications *)
    intro Hp.
    pose proof (S4 Hp) as S4.
    pose proof (n14_242 B s1 φ (fun x => iota_f s2 ψ 
      (λ y, Iota s1 x = Iota s2 y))) as n14_242.
    MP n14_242 Hp.
    now rewrite -> n14_242 in S4.
  }
  assert (S6 : iota_E φ → ((φ x <[- x -]> ψ x) 
    ↔ iota_f s1 φ (fun x => iota_f s2 ψ (fun y => 
      (Iota s1 x) = (Iota s2 y))))).
  {
    pose proof (n10_11 B (fun b => (φ x <[- x -]> (x = b))
      -> ((φ x <[- x -]> ψ x) <-> iota_f s1 φ (fun x => iota_f s2 ψ 
      (fun y => (Iota s1 x) = (Iota s2 y)))))) 
      as n10_11.
    MP n10_11 S5.
    rewrite -> n10_23 in n10_11.
    pose proof (n14_11 φ) as n14_11.
    destruct n14_11 as [n14_11l _].
    now Syll n14_11l n10_11 S6.
  }
  exact S6.
Qed.

Theorem n14_271 (φ ψ : Prop → Prop) : (φ x <[- x -]> ψ x)
  → ((iota_E φ) ↔ (iota_E ψ)).
Proof.
  (* TOOLS *)
  set (B := Individual "b").
  set (X := Individual "x").
  (* ******** *)
  assert (S1 : (φ X <-> ψ X) -> ((φ X <-> (X = B)) 
    <-> (ψ X <-> (X = B)))).
  { apply n4_86. }
  assert (S2 : (φ x <[- x -]> ψ x) -> (∀ x, (φ x <-> (x = B)) 
    <-> (ψ x <-> (x = B)))).
  {
    pose proof (n10_11 X (fun x => ((φ x <-> ψ x) -> (φ x <-> (x = B)) 
      <-> (ψ x <-> (x = B))))) as n10_11.
    MP n10_11 S1.
    pose proof (n10_27 (fun x => φ x <-> ψ x)
      (fun x => (φ x <-> (x = B)) <-> (ψ x <-> (x = B)))) as n10_27.
    now MP n10_27 n10_11.
  }
  assert (S3 : (φ x <[- x -]> ψ x) -> ((∀ x, φ x <-> (x = B)) 
    <-> (∀ x, ψ x <-> (x = B)))).
  {
    intro Hp.
    pose proof (S2 Hp) as S2.
    pose proof (n10_271 (fun x => φ x <-> (x = B))
      (fun x => ψ x <-> (x = B))) as n10_271.
    clear S1.
    now MP n10_271 S2.
  }
  assert (S4 : (φ x <[- x -]> ψ x) -> ∀ b, (∀ x, φ x <-> (x = b)) 
    <-> (∀ x, ψ x <-> (x = b))).
  {
    pose proof (n10_11 B (fun b => φ x <[- x -]> ψ x 
      -> (φ x <[- x -]> x = b ↔ ψ x <[- x -]> x = b))) as n10_11.
    MP n10_11 S3.
    now rewrite -> n10_21 in n10_11.
  }
  assert (S5 : (φ x <[- x -]> ψ x) -> ((∃ b, φ x <[- x -]> (x = b))
    <-> (∃ b, ψ x <[- x -]> (x = b)))).
  {
    pose proof (n10_281 (fun b => φ x <[- x -]> (x = b))
      (fun b => ψ x <[- x -]> (x = b))) as n10_281.
    now Syll n10_281 S4 S5.
  }
  assert (S6 : (φ x <[- x -]> ψ x) → ((iota_E φ) ↔ (iota_E ψ))).
  { now repeat rewrite <- n14_02 in S5. }
  exact S6.
Qed.

Theorem n14_272 (s1 s2 : string) (φ ψ χ : Prop → Prop) : (φ x <[- x -]> ψ x)
  → iota_f s1 φ χ <-> iota_f s2 ψ χ.
Proof.
  (* TOOLS *)
  set (B := Individual "b").
  set (X := Individual "x").
  (* ******** *)
  assert (S1 : (φ X <-> ψ X) -> ((φ X <-> (X = B)) <-> (ψ X <-> (X = B)))).
  { apply n4_86. }
  assert (S2 : (φ x <[- x -]> ψ x) -> ((φ x <[- x -]> (x = B))
    <-> (ψ x <[- x -]> (x = B)))).
  {
    (* From this single direction theorem *5.1, I hightly think this step is unprovable *)
    pose proof n5_1 as _n5_1.
    pose proof (n10_11 X (fun x => (φ x <-> ψ x) -> ((φ x <-> (x = B)) 
      <-> (ψ x <-> (x = B))))) as n10_11.
    MP n10_11 S1.
    pose proof (n10_27 (fun x => φ x ↔ ψ x)
      (fun x => (φ x ↔ x = B) ↔ (ψ x ↔ x = B))) as n10_27.
    MP n10_27 n10_11.
    intro Hp.
    MP n10_27 Hp.
    pose proof n10_414 as _n10_414.
    admit.
  }
  assert (S3 : (φ x <[- x -]> ψ x) 
    -> (((φ x <[- x -]> (x = B)) /\ χ B) 
      <-> ((ψ x <[- x -]> (x = B)) /\ χ B))).
  {
    intro Hp.
    pose proof (S2 Hp) as S2.
    (* simplifications *)
    destruct S2 as [S2l S2r].
    pose proof (Fact3_45 (φ x <[- x -]> x = B) 
      (ψ x <[- x -]> x = B) (χ B)) as Fact3_45a.
    MP Fact3_45a S2l.
    pose proof (Fact3_45 (ψ x <[- x -]> x = B) 
      (φ x <[- x -]> x = B) (χ B)) as Fact3_45b.
    MP Fact3_45b S2r.
    clear S1 S2l S2r Hp.
    Conj Fact3_45a Fact3_45b S3.
    now Equiv S3.
  }
  assert (S4 : (φ x <[- x -]> ψ x) 
    -> (∀ b, ((φ x <[- x -]> (x = b)) /\ χ b) 
      <-> ((ψ x <[- x -]> (x = b)) /\ χ b))).
  {
    pose proof (n10_11 B (fun b => (φ x <[- x -]> ψ x) 
      -> (((φ x <[- x -]> (x = b)) /\ χ b) 
        <-> ((ψ x <[- x -]> (x = b)) /\ χ b)))) as n10_11.
    MP n10_11 S3.
    now rewrite -> n10_21 in n10_11.
  }
  assert (S5 : (φ x <[- x -]> ψ x)
    -> ((∃ b, (φ x <[- x -]> (x = b)) /\ χ b) 
      <-> (∃ b, (ψ x <[- x -]> (x = b)) /\ χ b))).
  {
    pose proof (n10_281 (fun b => (φ x <[- x -]> x = b) ∧ χ b)
      (fun b => (ψ x <[- x -]> x = b) ∧ χ b)) as n10_281.
    now Syll S4 n10_281 S5.
  }
  assert (S6 : (φ x <[- x -]> ψ x)
    → iota_f s1 φ χ <-> iota_f s2 ψ χ).
  { now rewrite <- (n14_101 s1 φ), <- (n14_101 s2 ψ) in S5. }
  exact S6.
Admitted.

(* As the substitution on `B` in the proof substitutes on both side
of the `=`, our treatment on iota here varies again: we should write

`iota_f s φ (fun x => iota_f s φ (fun y => Iota s x = Iota s y))`

if it has been a fixed interpretation. However if we are following the 
proof, now we will see what is going on...
 *)
Theorem n14_28 (s : string) (φ : Prop → Prop) : iota_E φ
  ↔ iota_f s φ (fun x => Iota s x = Iota s x).
Proof.
  (* TOOLS *)
  set (B := Individual "b").
  (* ******** *)
  assert (S1 : (φ x <[- x -]> (x = B)) <-> ((φ x <[- x -]> (x = B))
    /\ (B = B))).
  {
    (* Here it comes again: the n13_15... being used correctly though *)
    pose proof (n13_15 B) as n13_15.
    pose proof (n4_73 (φ x <[- x -]> (x = B)) (B = B)) as n4_73.
    now MP n4_73 n13_15.
  }
  assert (S2 : (∃ b, φ x <[- x -]> (x = b)) <-> (∃ b, 
    (φ x <[- x -]> (x = b)) /\ (b = b))).
  {
    pose proof (n10_11 B (fun b => (φ x <[- x -]> (x = b)) 
      <-> ((φ x <[- x -]> (x = b)) /\ (b = b)))) as n10_11.
    MP n10_11 S1.
    pose proof (n10_281 (fun b => φ x <[- x -]> (x = b))
      (fun b => (φ x <[- x -]> (x = b)) /\ (b = b))) as n10_281.
    now MP n10_281 n10_11.
  }
  assert (S3 : iota_E φ ↔ iota_f s φ (fun x => 
    Iota s x = Iota s x)).
  {
    rewrite <- n14_11 in S2.
    now rewrite <- (n14_1 s φ) in S2.
  }
  exact S3.
Qed.

(* What a terrible looking theorem to prove *)
Theorem n14_3 (s : string) (φ χ f : Prop → Prop) : 
  (((p ↔ q) -[ p q ]> (f p ↔ f q)) ∧ iota_E φ)
  →
  ((f (iota_f s φ χ)) ↔ iota_f s φ (fun x =>
    f (χ (Iota s x)))).
Proof.
  (* TOOLS *)
  set (B := Individual "b").
  (* ******** *)
  assert (S1 : (φ x <[- x -]> (x = B))
    -> (iota_f s φ χ <-> χ B)).
  { 
    pose proof (n14_242 B s φ χ) as n14_242.
    now rewrite -> n4_21 in n14_242.
  }
  assert (S2 : (((p <-> q) -[ p q ]> (f p <-> f q))
      /\ (φ x <[- x -]> (x = B)))
    -> f (iota_f s φ χ) <-> f (χ B)).
  {
    (* This is a very special one: it doesn't cite any theorems at all
    and I think this specific step might be ill-formed *)
    (* Simplifications - we might investigate later to determine if there is
    actually a normal way to form the proof, i.e. every step comes with
    a cited theorem *)
    intro Hp.
    destruct Hp as [Hp1 Hp2].
    MP S1 Hp2.
    pose proof (Hp1 (iota_f s φ χ) (χ B)) as Hp1.
    now MP Hp1 S1.
  }
  assert (S3 : (φ x <[- x -]> (x = B))
    -> ((iota_f s φ (fun x => f (χ x))) <-> f (χ B))).
  {
    pose proof (n14_242 B s φ (fun x => f (χ x))) as n14_242.
    now rewrite -> n4_21 in n14_242.
  }
  assert (S4 : (((p <-> q) -[ p q ]> (f p <-> f q))
      /\ (φ x <[- x -]> (x = B)))
    -> (f (iota_f s φ χ) <-> iota_f s φ (fun x => f (χ x)))).
  {
    (* simplification *)
    intro Hp.
    pose proof (S2 Hp) as S2.
    destruct Hp as [Hp1 Hp2].
    MP S3 Hp2.
    now rewrite <- S3 in S2.
  }
  assert (S5 : (((p ↔ q) -[ p q ]> (f p ↔ f q)) ∧ iota_E φ)
    → ((f (iota_f s φ χ)) ↔ iota_f s φ (fun x =>
      f (χ (Iota s x))))).
  {
    pose proof (n10_11 B (fun b =>
      ((p ↔ q) -[ p q ]> (f p ↔ f q)) ∧ (∀ x, φ x ↔ x = b)
      → f (iota_f s φ χ) ↔ iota_f s φ (λ x, f (χ x)))) 
      as n10_11.
    MP n10_11 S4.
    rewrite -> n10_23 in n10_11.
    rewrite -> n10_35 in n10_11.
    rewrite <- n14_11 in n10_11.
    now replace (λ x, f (χ x)) with (λ x, f (χ (Iota s x)))
      in n10_11 by reflexivity.
  }
  exact S5.
Qed.

(* NOTE: original text mentioned here something about the axiom of reducibility *)
Theorem n14_31 (P : Prop) (s : string) (φ χ : Prop → Prop) : iota_E φ
  → ((iota_f s φ (fun x => P ∨ χ (Iota s x)))
    ↔ P ∨ (iota_f s φ χ)).
Proof.
  (* TOOLS *)
  set (B := Individual "b").
  (* ******** *)
  assert (S1 : (φ x <[- x -]> (x = B))
    -> (iota_f s φ (fun x => P \/ χ (Iota s x)) <-> (P \/ χ B))).
  {
    pose proof (n14_242 B s φ (fun x => P \/ χ x)) as n14_242.
    now rewrite -> n4_21 in n14_242.
  }
  assert (S2 : (φ x <[- x -]> (x = B)) -> ((iota_f s φ χ) 
    <-> χ B)).
  {
    pose proof (n14_242 B s φ χ) as n14_242.
    now rewrite -> n4_21 in n14_242.
  }
  assert (S3 : (φ x <[- x -]> (x = B)) 
    -> ((P \/ iota_f s φ χ) <-> (P \/ χ B))).
  {
    pose proof (n4_37 (iota_f s φ χ) (χ B) P) as n4_37.
    Syll S2 n4_37 S3.
    setoid_rewrite -> n4_31 in S3 at 1.
    now setoid_rewrite -> n4_31 in S3 at 2.
  }
  assert (S4 : (φ x <[- x -]> (x = B))
    -> (iota_f s φ (fun x => P \/ χ (Iota s x)) 
      <-> (P \/ iota_f s φ χ))).
  {
    (* simplification *)
    clear S2.
    intro Hp.
    pose proof (S1 Hp) as S1.
    pose proof (S3 Hp) as S3.
    now rewrite <- S3 in S1.
  }
  assert (S5 : iota_E φ → ((iota_f s φ (fun x => P ∨ χ (Iota s x)))
    ↔ P ∨ (iota_f s φ χ))).
  {
    pose proof (n10_11 B (fun b => (φ x <[- x -]> (x = b))
      -> (iota_f s φ (fun x => P \/ χ (Iota s x)) 
        <-> (P \/ iota_f s φ χ)))) as n10_11.
    MP n10_11 S4.
    rewrite -> n10_23 in n10_11.
    now rewrite <- n14_11 in n10_11.
  }
  exact S5.
Qed.

Theorem n14_32 (s : string) (φ χ : Prop → Prop) : iota_E φ
  ↔ ((iota_f s φ (fun x => ~ χ (Iota s x)))
    ↔ ~ (iota_f s φ χ)).
Proof.
  (* TOOLS *)
  set (B := Individual "b").
  (* ******** *)
  assert (S1 : (φ x <[- x -]> (x = B))
    -> (iota_f s φ (fun x => ~ χ (Iota s x)) <-> ~ χ B)).
  {
    pose proof (n14_242 B s φ (fun x => ~ χ x)) as n14_242.
    now rewrite -> n4_21 in n14_242.
  }
  assert (S2 : (φ x <[- x -]> (x = B)) -> ((iota_f s φ χ) 
    <-> χ B)).
  {
    pose proof (n14_242 B s φ χ) as n14_242.
    now rewrite -> n4_21 in n14_242.
  }
  assert (S3 : (φ x <[- x -]> (x = B)) 
    -> ((~ iota_f s φ χ) <-> ~ χ B)).
  { now rewrite -> Transp4_11 in S2. }
  assert (S4 : (φ x <[- x -]> (x = B))
    -> (iota_f s φ (fun x => ~ χ (Iota s x)) 
      <-> ~ iota_f s φ χ)).
  {
    (* simplification *)
    clear S2.
    intro Hp.
    pose proof (S1 Hp) as S1.
    pose proof (S3 Hp) as S3.
    now rewrite <- S3 in S1.
  }
  assert (S5 : iota_E φ -> ((iota_f s φ (fun x => ~ χ (Iota s x)))
    ↔ ~ (iota_f s φ χ))).
  {
    pose proof (n10_11 B (fun b => (φ x <[- x -]> (x = b))
      -> (iota_f s φ (fun x => ~ χ (Iota s x)) 
        <-> ~ iota_f s φ χ))) as n10_11.
    MP n10_11 S4.
    rewrite -> n10_23 in n10_11.
    now rewrite <- n14_11 in n10_11.
  }
  assert (S6 : ((iota_f s φ (fun x => ~ χ (Iota s x)))
    ↔ ~ (iota_f s φ χ)) -> iota_E φ).
  {
    (* NOTE: Doubt this step is provable, because the different meaning in 
    notation here could make a crucial difference *)
    pose proof n14_1 as _n14_1.
    admit.
  }
  assert (S7 : iota_E φ ↔ ((iota_f s φ (fun x => ~ χ (Iota s x)))
    ↔ ~ (iota_f s φ χ))).
  {
    clear S1 S2 S3 S4.
    Conj S5 S6 S7.
    now Equiv S7.
  }
  exact S7.
Admitted.

(* In original text, we can see straightforward that the citations are not
completely in the same order *)
Theorem n14_33 (P : Prop) (s : string) (φ χ : Prop → Prop) : iota_E φ
  → ((iota_f s φ (fun x => P → χ (Iota s x)))
    ↔ (P → iota_f s φ χ)).
Proof.
  (* TOOLS *)
  set (B := Individual "b").
  (* ******** *)
  assert (S1 : (φ x <[- x -]> (x = B))
    -> (iota_f s φ (fun x => P -> χ (Iota s x)) <-> (P -> χ B))).
  {
    pose proof (n14_242 B s φ (fun x => P -> χ x)) as n14_242.
    now rewrite -> n4_21 in n14_242.
  }
  assert (S2 : (φ x <[- x -]> (x = B)) -> ((iota_f s φ χ) 
    <-> χ B)).
  {
    pose proof (n14_242 B s φ χ) as n14_242.
    now rewrite -> n4_21 in n14_242.
  }
  assert (S3 : (φ x <[- x -]> (x = B)) 
    -> ((P -> iota_f s φ χ) <-> (P -> χ B))).
  { 
    (* simplification *)
    intro Hp.
    pose proof (S2 Hp) as S2.
    pose proof (n4_85 (iota_f s φ χ) (χ B) P) as n4_85.
    clear S1.
    now MP n4_85 S2.
  }
  assert (S4 : (φ x <[- x -]> (x = B))
    -> (iota_f s φ (fun x => P -> χ (Iota s x)) 
      <-> (P -> iota_f s φ χ))).
  {
    (* simplification *)
    clear S2.
    intro Hp.
    pose proof (S1 Hp) as S1.
    pose proof (S3 Hp) as S3.
    now rewrite <- S3 in S1.
  }
  assert (S5 : iota_E φ -> ((iota_f s φ (fun x => P -> χ (Iota s x)))
    ↔ (P -> (iota_f s φ χ)))).
  {
    pose proof (n10_11 B (fun b => (φ x <[- x -]> (x = b))
      -> (iota_f s φ (fun x => P -> χ (Iota s x)) 
        <-> (P -> iota_f s φ χ)))) as n10_11.
    MP n10_11 S4.
    rewrite -> n10_23 in n10_11.
    now rewrite <- n14_11 in n10_11.
  }
  exact S5.
Qed.

Theorem n14_331 (P : Prop) (s : string) (φ χ : Prop → Prop) : iota_E φ
  → ((iota_f s φ χ → P) ↔ (iota_f s φ (fun x => 
    χ (Iota s x) → P))).
Proof.
  (* TOOLS *)
  set (B := Individual "b").
  (* ******** *)
  assert (S1 : (φ x <[- x -]> (x = B))
    -> (iota_f s φ (fun x => χ (Iota s x) -> P) <-> (χ B -> P))).
  {
    pose proof (n14_242 B s φ (fun x => χ x -> P)) as n14_242.
    now rewrite -> n4_21 in n14_242.
  }
  assert (S2 : (φ x <[- x -]> (x = B)) -> ((iota_f s φ χ) 
    <-> χ B)).
  {
    pose proof (n14_242 B s φ χ) as n14_242.
    now rewrite -> n4_21 in n14_242.
  }
  assert (S3 : (φ x <[- x -]> (x = B)) 
    -> (((iota_f s φ χ) -> P) <-> (χ B -> P))).
  { 
    (* simplification *)
    intro Hp.
    pose proof (S2 Hp) as S2.
    pose proof (n4_84 (iota_f s φ χ) (χ B) P) as n4_85.
    clear S1.
    now MP n4_85 S2.
  }
  assert (S4 : (φ x <[- x -]> (x = B))
    -> (iota_f s φ (fun x => χ (Iota s x) -> P)
      <-> ((iota_f s φ χ) -> P))).
  {
    (* simplification *)
    clear S2.
    intro Hp.
    pose proof (S1 Hp) as S1.
    pose proof (S3 Hp) as S3.
    now rewrite <- S3 in S1.
  }
  assert (S5 : iota_E φ -> ((iota_f s φ (fun x => χ (Iota s x) -> P))
    ↔ (iota_f s φ χ -> P))).
  {
    pose proof (n10_11 B (fun b => (φ x <[- x -]> (x = b))
      -> (iota_f s φ (fun x => χ (Iota s x) -> P) 
        <-> (iota_f s φ χ -> P)))) as n10_11.
    MP n10_11 S4.
    rewrite -> n10_23 in n10_11.
    now rewrite <- n14_11 in n10_11.
  }
  (* What a lovely reversion, it has been so unorganized *)
  assert (S6 : iota_E φ → ((iota_f s φ χ → P) 
    ↔ (iota_f s φ (fun x => χ (Iota s x) → P)))).
  { now rewrite -> n4_21 in S5. }
  exact S6.
Qed.

Theorem n14_332 (P : Prop) (s : string) (φ χ : Prop → Prop) : iota_E φ
  → ((iota_f s φ (fun x => P ↔ χ (Iota s x)))
    ↔ (P ↔ (iota_f s φ χ))).
Proof.
  (* TOOLS *)
  set (B := Individual "b").
  (* ******** *)
  assert (S1 : (φ x <[- x -]> (x = B))
    -> (iota_f s φ (fun x => P <-> χ (Iota s x)) <-> (P <-> χ B))).
  {
    pose proof (n14_242 B s φ (fun x => P <-> χ x)) as n14_242.
    now rewrite -> n4_21 in n14_242.
  }
  assert (S2 : (φ x <[- x -]> (x = B)) -> ((iota_f s φ χ) 
    <-> χ B)).
  {
    pose proof (n14_242 B s φ χ) as n14_242.
    now rewrite -> n4_21 in n14_242.
  }
  assert (S3 : (φ x <[- x -]> (x = B)) 
    -> ((P <-> iota_f s φ χ) <-> (P <-> χ B))).
  { 
    (* simplification *)
    intro Hp.
    pose proof (S2 Hp) as S2.
    pose proof (n4_86 (iota_f s φ χ) (χ B) P) as n4_86.
    clear S1.
    setoid_rewrite -> n4_21 in n4_86 at 3.
    setoid_rewrite -> n4_21 in n4_86 at 4.
    now MP n4_86 S2.
  }
  assert (S4 : (φ x <[- x -]> (x = B))
    -> (iota_f s φ (fun x => P <-> χ (Iota s x)) 
      <-> (P <-> iota_f s φ χ))).
  {
    (* simplification *)
    clear S2.
    intro Hp.
    pose proof (S1 Hp) as S1.
    pose proof (S3 Hp) as S3.
    now rewrite <- S3 in S1.
  }
  assert (S5 : iota_E φ -> ((iota_f s φ (fun x => P <-> χ (Iota s x)))
    ↔ (P <-> (iota_f s φ χ)))).
  {
    pose proof (n10_11 B (fun b => (φ x <[- x -]> (x = b))
      -> (iota_f s φ (fun x => P <-> χ (Iota s x)) 
        <-> (P <-> iota_f s φ χ)))) as n10_11.
    MP n10_11 S4.
    rewrite -> n10_23 in n10_11.
    now rewrite <- n14_11 in n10_11.
  }
  exact S5.
Qed.

Theorem n14_34 (P : Prop) (s : string) (φ χ : Prop → Prop) : 
  (P ∧ iota_f s φ χ) ↔ iota_f s φ (fun x =>
    P ∧ χ (Iota s x)).
Proof.
  assert (S1 : (P ∧ iota_f s φ χ) <-> (P /\ (∃ b, 
    (φ x <[- x -]> (x = b)) /\ χ b))).
  { 
    pose proof (n14_1 s φ χ) as n14_1.
    pose proof (n4_36 (iota_f s φ χ) (∃ b, (φ x <[- x -]> x = b) ∧ χ b)
      P) as n4_36.
    MP n4_36 n14_1.
    rewrite -> n4_3 in n4_36.
    now setoid_rewrite -> n4_3 in n4_36 at 3.
  }
  assert (S2 : (P ∧ iota_f s φ χ) <-> (∃ b, 
    P /\ ((φ x <[- x -]> (x = b)) /\ χ b))).
  { now rewrite <- n10_35 in S1. }
  assert (S3 : (P ∧ iota_f s φ χ) ↔ iota_f s φ (fun x =>
    P ∧ χ (Iota s x))).
  {
    setoid_rewrite -> n4_3 in S2 at 4.
    setoid_rewrite <- n4_32 in S2.
    setoid_rewrite -> n4_3 in S2 at 3.
    now rewrite <- (n14_1 s) in S2.
  }
  exact S3.
Qed.

Close Scope single_app_equiv.
Close Scope single_app_impl.
Close Scope double_app_equiv.
Close Scope double_app_impl.