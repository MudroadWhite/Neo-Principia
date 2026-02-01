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
- fix all the `replace`s and `admit`s 
- fill in missing proofs
*)

(* 
The decription, or I would personally call it the iota operator, designs a special kind of 
parameter for functions. They will be passed into propositional functions normally, but unlike 
normal parameters that only calculates everything within themselves, they will rewrite on the 
whole propositional function, and on other terms that are not within them.

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
but it can correctly express what should a iota do and limit its scope as in the text.

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

Definition n14_01 (s : string) (Phi Psi : Prop → Prop) : 
  (iota_f s Phi Psi) = ∃ b, (Phi x <[- x -]> (x = b)) ∧ Psi b. 
Admitted.

Definition n14_02 (Phi : Prop → Prop) :
  (iota_E Phi) = ∃ b, (Phi x <[- x -]> (x = b)). 
Admitted.

(* Although `iota_f2` has been defined, expressions that involves 2 functions often
  comes up with the default interpretations as two `iota_f` rather than one `iota_f2`.
  While this doen't affect significantly how the definition organizes, it still affects
  how we should write down a theorem *)
Definition n14_03 (s1 s2 : string) (Phi Psi : Prop → Prop) (f : Prop → Prop → Prop) :
  (iota_f2 s1 s2 Phi Psi f) = 
    iota_f s1 Phi (fun b => iota_f s2 Psi 
      (fun c => f (Iota s1 b) (Iota s2 c))).
Admitted.

Definition n14_04 (s1 s2 : string) (Phi Psi : Prop → Prop) (f : Prop → Prop → Prop) : 
  (iota_f2_rev s2 s1 Psi Phi f) = iota_f2 s2 s1 Psi Phi (fun x y => f y x).
Admitted.

Theorem n14_1 (s : string) (Phi Psi : Prop → Prop) : (iota_f s Phi Psi) ↔ 
  ∃ b, (Phi x <[- x -]> (x = b)) ∧ Psi b.
Proof.
  pose proof (n4_2 (iota_f s Phi Psi)) as n4_2.
  now rewrite -> n14_01 in n4_2 at 2.
Qed.

(* The equivalent with n14_1, with scope notation in its original 
  representation omitted. With our definition, we might just make 
  another definition copying `iota_f` to indicate it is getting 
  scope notation in the text... *)
Theorem n14_101 (s : string) (Phi Psi : Prop → Prop) : (iota_f s Phi Psi) ↔ 
  ∃ b, (Phi x <[- x -]> (x = b)) ∧ Psi b.
Proof. exact (n14_1 s Phi Psi). Qed.

Theorem n14_11  (Phi : Prop → Prop) : (iota_E Phi) 
  ↔ (∃ b, Phi x <[- x -]> (x = b)).
Proof.
  pose proof (n4_2 (iota_E Phi)) as n4_2.
  now rewrite -> n14_02 in n4_2 at 2.
Qed.

Theorem n14_111 (s1 s2 : string) (Phi Psi : Prop → Prop) 
  (f : Prop → Prop → Prop) :
  (iota_f2_rev s2 s1 Psi Phi f) ↔ (∃ b c, 
    (Phi x <[- x -]> (x = b)) ∧ (Psi x <[- x -]> (x = c)) ∧ (f b c)).
Proof.
  assert (S1 : iota_f2_rev s2 s1 Psi Phi f ↔ 
    iota_f s2 Psi (fun c => iota_f s1 Phi 
      (fun b => f (Iota s1 b) (Iota s2 c)))).
  {
    pose proof (n4_2 (iota_f2_rev s2 s1 Psi Phi f)) as n4_2.
    rewrite -> n14_04 in n4_2 at 2.
    now rewrite -> (n14_03 s2 s1) in n4_2.
  }
  assert (S2 : iota_f2_rev s2 s1 Psi Phi f ↔ 
    (iota_f s2 Psi (fun c =>
      ∃ b, (Phi x <[- x -]> (x = b)) ∧ f b c))).
  {
    replace (λ c, iota_f s1 Phi (λ b, f (Iota s1 b) (Iota s2 c)))
      with (λ c, iota_f s1 Phi (λ b, f b c)) in S1 by reflexivity.
    (* Simplification: this place needs functional extentionality for our designed 
    notation of iota. Seems like the only way to survive *)
    assert (S1_1 : (λ c, iota_f s1 Phi (λ b, f b c))
      = (λ c, (∃ b, (Phi x <[- x -]> (x = b)) ∧ f b c))).
    {
      extensionality c. (* function extentionality *)
      pose proof (n14_1 s1 Phi (fun b => f b c)) as n14_1.
      now apply propositional_extensionality.
    }
    now rewrite -> S1_1 in S1.
  }
  assert (S3 : iota_f2_rev s2 s1 Psi Phi f ↔ 
    (∃ c, (Psi x <[- x -]> (x = c)) 
    ∧ ∃ b, (Phi x <[- x -]> (x = b)) ∧ f b c)).
  { now rewrite -> n14_1 in S2. }
  assert (S4 : iota_f2_rev s2 s1 Psi Phi f ↔ 
    (∃ b c, (Phi x <[- x -]> (x = b)) ∧ (Psi x <[- x -]> (x = c))
      ∧ f b c)).
  {
    pose proof (n11_55
      (fun c => (Psi x <[- x -]> (x = c)))
      (fun c b => ( Phi x<[- x -]> (x = b)) ∧ f b c)
    ) as n11_55.
    rewrite <- n11_55 in S3.
    (* We can see that there are some (non?)trivial steps that still need to be
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

Theorem n14_112 (s1 s2 : string) (Phi Psi : Prop → Prop) 
  (f : Prop → Prop → Prop) : 
  (iota_f2 s1 s2 Phi Psi f) ↔ ∃ b c, 
    (Phi x <[- x -]> x = b) ∧ (Psi x <[- x -]> x = c) ∧ f b c.
Proof.
  assert (S1 : (iota_f2 s1 s2 Phi Psi f) ↔ (iota_f s1 Phi 
    (fun b => iota_f s2 Psi (fun c => f (Iota s1 b) (Iota s2 c))))).
  {
    pose proof (n4_2 (iota_f2 s1 s2 Phi Psi f)) as n4_2.
    now rewrite -> n14_03 in n4_2 at 2.
  }
  assert (S2 : (iota_f2 s1 s2 Phi Psi f) ↔ (iota_f s1 Phi (fun b => 
    ∃ c, (Psi x <[- x -]> (x = c)) ∧ f b c))).
  {
    replace ((λ b, iota_f s2 Psi (λ c, f (Iota s1 b) (Iota s2 c))))
      with (λ b, iota_f s2 Psi (λ c, f b c)) in S1 
      by reflexivity.
    assert (S1_1 : (λ b, iota_f s2 Psi (λ c : Prop, f b c))
      = (λ b, ∃ c, (Psi x <[- x -]> (x = c)) ∧ f b c)).
    {
      extensionality b.
      pose proof (n14_1 s2 Psi (fun c => f b c)) as n14_1. 
      now apply propositional_extensionality.
    }
    now rewrite -> S1_1 in S1.
  }
  assert (S3 : (iota_f2 s1 s2 Phi Psi f) ↔ ∃ b, 
    (Phi x <[- x -]> x = b) ∧ (∃ c, (Psi x <[- x -]> x = c) ∧ f b c)).
  { now rewrite -> n14_1 in S2. } 
  assert (S4 : (iota_f2 s1 s2 Phi Psi f) ↔ ∃ b c, 
    (Phi x <[- x -]> x = b) ∧ (Psi x <[- x -]> x = c) ∧ f b c).
  { admit. }
Admitted.

Theorem n14_113 (s1 s2 : string) (Phi Psi : Prop → Prop) 
  (f : Prop → Prop → Prop) : 
  iota_f2 s2 s1 Psi Phi (fun y x => f x y) ↔ iota_f2 s1 s2 Phi Psi f. 
Proof.
  pose proof (n14_111 s1 s2 Phi Psi f) as n14_111.
  rewrite <- (n14_112 s1 s2) in n14_111.
  now rewrite -> n14_04 in n14_111.
Qed.

Open Scope double_app_equiv.
Open Scope double_app_impl.

Theorem n14_12 (Phi : Prop → Prop) : 
  iota_E Phi → ((Phi x ∧ Phi y) -[ x y ]> (x = y)).
Proof.
  (* TOOLS *)
  set (B := Individual "b").
  set (X := Individual "x").
  (* ******** *)
  assert (S1 : iota_E Phi → ∃ b, Phi x <[- x -]> x = b).
  {
    pose proof (n14_11 Phi) as n14_11.
    (* simplification: we use `Simp` if necessary *)
    now destruct n14_11.
  }
  assert (S2 : (Phi x <[- x -]> x = B) 
    → ((Phi x ∧ Phi y) <[- x y -]> (x = B ∧ y = B))).
  {
    (* NOTE: this place shows that we cannot assign a instance 
    automatically: in this complicated situation we are having 
    candidates being not unique. Might be interesting to check 
    in the future... *)
    pose proof (n4_38
      (Phi X) (Phi X) (X = B) (X = B)) as n4_38.
    rewrite <- n4_24 in n4_38.
    pose proof (n10_1 (fun x => (Phi x ↔ x = B)) X) as n10_1.
    Syll n10_1 n4_38 Sa.
    pose proof (n11_11 X X (fun z w => 
      (∀ x : Prop, Phi x ↔ x = B) →
      (Phi z ∧ Phi w ↔ z = B ∧ w = B))) as n11_11.
    MP n11_11 Sa.
    now rewrite <- n11_3 in n11_11.
  }
  assert (S3 : (Phi x <[- x -]> x = B) 
  → ((Phi x ∧ Phi y) -[ x y ]> (x = y))).
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
  assert (S4 : (∃ b, (Phi x <[- x -]> (x = b)))
    → ((Phi x ∧ Phi y) -[ x y ]> (x = y))).
  {
    pose proof (n10_11 B (fun b =>
      Phi x <[- x -]> x = b  →  (Phi x ∧ Phi y) -[ x y ]> (x = y)
      )) as n10_11.
    MP n10_11 S3.
    now rewrite -> n10_23 in n10_11.
  }
  assert (S5 : iota_E Phi → ((Phi x ∧ Phi y) -[ x y ]> (x = y))).
  { now Syll S1 S4 S5. }
  exact S5.
Qed.

Close Scope double_app_equiv.

Theorem n14_121 (B C : Prop) (Phi : Prop → Prop) : 
  ((Phi x <[- x -]> x = B) ∧ (Phi x <[- x -]> x = C))
  → B = C. 
Proof.
  assert (S1 : ((Phi x <[- x -]> x = B) ∧ (Phi x <[- x -]> x = C))
    → ((Phi B ↔ (B = B)) ∧ (Phi B ↔ (B = C)))).
  {
    pose proof (n10_1 (fun x => Phi x ↔ (x = B)) B) as n10_1a.
    pose proof (n10_1 (fun x => Phi x ↔ (x = C)) B) as n10_1b.
    Conj n10_1a n10_1b C1.
    pose proof (n3_47
      (Phi x<[-x-]>x = B) (Phi x<[-x-]>x = C)
      (Phi B ↔ (B = B)) (Phi B ↔ (B = C))
    ) as n3_47.
    now MP n3_47 C1.
  }
  assert (S2 : ((Phi x <[- x -]> x = B) ∧ (Phi x <[- x -]> x = C))
    → (Phi B ∧ (Phi B ↔ (B = C)))).
  {
    (* TODO: Design a special rule for *13.15. This is something unusual
      for the rewriting system *)
    pose proof n13_15.
    admit.
  }
  assert (S3 : ((Phi x <[- x -]> x = B) ∧ (Phi x <[- x -]> x = C))
    → (B = C)).
  {
    (* Simplifications... *)
    intro Hp.
    pose proof (S2 Hp) as S2.
    destruct S2 as [A1 A2].
    destruct A2 as [A2l _].
    assert (S2_1 : Phi B ∧ (Phi B → B = C)).
    { 
      clear S1.
      now Conj A1 A2l S2_1. 
    }
    pose proof (Ass3_35 (Phi B) (B = C)) as Ass3_35.
    now MP Ass3_35 S2_1.
  }
  exact S3.
Admitted.

Open Scope single_app_impl.

Theorem n14_122 (B : Prop) (Phi : Prop → Prop) :
  ((Phi x <[- x -]> (x = B)) ↔ ((Phi x -[ x ]> (x = B)) ∧ Phi B))
  ∧
  (((Phi x -[ x ]> (x = B)) ∧ Phi B) ↔ ((Phi x -[ x ]> (x = B)) ∧ ∃ x, Phi x)). 
Proof.
  (* TOOLS *)
  set (X := Individual "x").
  (* ******** *)
  assert (S1 : (Phi x <[- x -]> (x = B)) 
    ↔ ((Phi x -[ x ]> (x = B)) ∧ ((x = B) -[ x ]> Phi x))).
  { apply  n10_22. }
  assert (S2 : (Phi x <[- x -]> (x = B)) 
    ↔ ((Phi x -[ x ]> (x = B)) ∧ Phi B)).
  {
    pose proof (n13_191 B Phi) as n13_191.
    now rewrite -> n13_191 in S1.
  }
  assert (S3 : (Phi X → (X = B))
    → (Phi X ↔ (Phi X ∧ (X = B)))).
  {
    pose proof (n4_71 (Phi X) (X = B)) as n4_71.
    now destruct n4_71.
  }
  assert (S4 : (Phi x -[ x ]> (x = B))
    → (Phi x <[- x -]> (Phi x ∧ (x = B)))).
  {
    pose proof (n10_11 X (fun x =>
      (Phi x → (x = B)) → (Phi x 
        ↔ (Phi x ∧ (x = B))))) as n10_11.
    MP n10_11 S3.
    pose proof (n10_27 (fun x => Phi x → (x = B))
      (fun x => Phi x ↔ (Phi x ∧ (x = B)))) 
      as n10_27.
    now MP n10_27 n10_11.
  }
  assert (S5 : (Phi x -[ x ]> (x = B))
    → ((∃ x, Phi x) ↔ (∃ x, Phi x ∧ (x = B)))).
  {
    pose proof (n10_281 Phi (fun x => Phi x ∧ x = B)) 
      as n10_281.
    now Syll S4 n10_281 S5.
  }
  assert (S6 : (Phi x -[ x ]> (x = B)) → ((∃ x, 
    Phi x) ↔ Phi B)).
  {
    setoid_rewrite -> n4_3 in S5 at 2.
    now rewrite -> n13_195 in S5.
  }
  assert (S7 : ((Phi x -[ x ]> (x = B)) ∧ (∃ x, Phi x))
    ↔ ((Phi x -[ x ]> (x = B)) ∧ Phi B)).
  { now rewrite -> n5_32 in S6. }
  assert (S8 : ((Phi x <[- x -]> (x = B)) ↔ ((Phi x -[ x ]> (x = B)) ∧ Phi B))
    ∧ (((Phi x -[ x ]> (x = B)) ∧ Phi B) 
      ↔ ((Phi x -[ x ]> (x = B)) ∧ ∃ x, Phi x))).
  {
    clear S1 S3 S4 S5 S6.
    now Conj S2 S7 S8.
  }
  exact S8.
Qed.

Open Scope double_app_equiv.
Open Scope double_app_impl.

Theorem n14_123 (X Y : Prop) (Phi : Prop → Prop → Prop) : 
  ((Phi z w <[- z w -]> (z = X ∧ w = Y)) 
    ↔ ((Phi z w -[ z w ]> (z = X ∧ w = Y)) ∧ Phi X Y))
  ∧
  (((Phi z w -[ z w ]> (z = X ∧ w = Y)) ∧ Phi X Y)
    ↔ ((Phi z w -[ z w ]> (z = X ∧ w = Y)) ∧ ∃ z w, Phi z w)).
Proof.
  (* TOOLS *)
  set (Z := Individual "z").
  set (W := Individual "w").
  (* ******** *)
  assert (S1 : (Phi z w <[- z w -]> (z = X ∧ w = Y)) 
    ↔ ((Phi z w -[ z w ]> (z = X ∧ w = Y)) 
      ∧ (((z = X ∧ w = Y) -[ z w ]> Phi z w)))).
  {
    pose proof (n11_31 
      (fun z w => Phi z w → (z = X ∧ w = Y))
      (fun z w => ((z = X ∧ w = Y) → Phi z w))) as n11_31a.
    symmetry in n11_31a.
    (* TODO: unify the ∀s into one ∀ and perform equiv in it *)
    (* rewrite <- Equiv4_01 in n11_31a. *)
    admit.
  }
  assert (S2 : (Phi z w <[- z w -]> (z = X ∧ w = Y)) 
    ↔ ((Phi z w -[ z w ]> (z = X ∧ w = Y)) ∧ Phi X Y)).
  { now rewrite -> n13_21 in S1. }
  assert (S3 : (Phi Z W → ((Z = X) ∧ (W = Y)))
    → (Phi Z W ↔ (Phi Z W ∧ (Z = X) ∧ (W = Y)))).
  {
    pose proof (n4_71 (Phi Z W) ((Z = X) ∧ (W = Y))) as n4_71.
    now destruct n4_71.
  } 
  assert (S4 : (Phi z w -[ z w ]> ((z = X) ∧ (w = Y)))
    → (Phi z w <[- z w -]> (Phi z w ∧ (z = X) ∧ (w = Y)))).
  {
    pose proof (n11_11 Z W (fun z w =>
      (Phi z w → ((z = X) ∧ (w = Y)))
        → (Phi z w ↔ (Phi z w 
          ∧ (z = X) ∧ (w = Y))))) as n11_11.
    MP n11_11 S4.
    pose proof (n11_32 (fun z w => Phi z w → ((z = X) ∧ (w = Y)))
      (fun z w => Phi z w ↔ (Phi z w 
        ∧ (z = X) ∧ (w = Y)))) as n11_32.
    now MP n11_32 n11_11.
  }
  assert (S5 : (Phi z w -[ z w ]> ((z = X) ∧ (w = Y)))
    → ((∃ z w, Phi z w) ↔ (∃ z w, 
      Phi z w ∧ (z = X) ∧ (w = Y)))).
  {
    pose proof (n11_341 Phi (fun z w => 
      Phi z w ∧ (z = X) ∧ (w = Y))) as n11_341.
    now Syll n11_341 S4 S5.
  }
  assert (S6 : (Phi z w -[ z w ]> ((z = X) ∧ (w = Y)))
    → ((∃ z w, Phi z w) ↔ Phi X Y)).
  {
    setoid_rewrite -> n4_3 in S5 at 3.
    setoid_rewrite -> n4_32 in S5.
    now rewrite -> n13_22 in S5.
  }
  assert (S7 : ((Phi z w -[ z w ]> ((z = X) ∧ (w = Y)))
      ∧ (∃ z w, Phi z w)
    ↔ ((Phi z w -[ z w ]> (z = X ∧ w = Y)) ∧ Phi X Y))).
  { now rewrite -> n5_32 in S6. }
  assert (S8 : ((Phi z w <[- z w -]> (z = X ∧ w = Y)) 
      ↔ ((Phi z w -[ z w ]> (z = X ∧ w = Y)) ∧ Phi X Y))
    ∧ (((Phi z w -[ z w ]> (z = X ∧ w = Y)) ∧ Phi X Y)
      ↔ ((Phi z w -[ z w ]> (z = X ∧ w = Y)) ∧ ∃ z w, Phi z w))).
  {
    clear S1 S3 S4 S5 S6.
    now Conj S2 S7 S8.
  }
  exact S8.
Admitted.

(* TODO: 4-var impl notation will be supported in the future *)
Theorem n14_124 (Phi : Prop → Prop → Prop) : 
  (∃ x y, (Phi z w <[- z w -]> (z = x ∧ w = y)))
  ↔ ((∃ x y, Phi x y) 
    ∧ ∀ z w u v, (Phi z w ∧ Phi u v) → (z = u ∧ w = v)). 
Proof.
  (* TOOLS *)
  set (X := Individual "x").
  set (Y := Individual "y").
  set (Z := Individual "z").
  set (W := Individual "w").
  set (U := Individual "u").
  set (V := Individual "v").
  (* ******** *)
  assert (S1 : (∃ x y, (Phi z w <[- z w -]> (z = x ∧ w = y)))
    → ∃ x y, Phi x y).
  { 
    (* TODO: this can be done as in some previous chapter, but I 
    don't want to fill out at the moment *)
    pose proof n14_123 as n14_123.
    pose proof Simp3_27 as Simp3_27.
    admit.
  }
  assert (S2 : (Phi z w <[- z w -]> ((z = X) ∧ (w = Y)))
    → (((Phi Z W) ∧ (Phi U V))
      → (Z = X ∧ W = Y ∧ U = X ∧ V = Y))).
  {
    pose proof (n11_1 Z W (fun z w =>
      (Phi z w) ↔ ((z = X) ∧ (w = Y)))) as n11_1a.
    pose proof (n11_1 U V (fun z w =>
      (Phi z w) ↔ ((z = X) ∧ (w = Y)))) as n11_1b.
    pose proof (n3_47 ) as n3_47.
    (* Involves some very complicated treatments on destructing
    and recombining the ↔s. We might want to abstract such 
    procedure into a new theorem *)
    admit.
  }
  assert (S3 : (Phi z w <[- z w -]> ((z = X) ∧ (w = Y)))
    → (((Phi Z W) ∧ (Phi U V)) → ((Z = U) ∧ (W = V)))).
  {
    (* simplification: tedious reordering... *)
    assert (S2_1 : (Z = X ∧ W = Y ∧ U = X ∧ V = Y)
      ↔ ((Z = X ∧ U = X) ∧ (W = Y ∧ V = Y))).
    {
      (* TODO: we need theorem for commutativity for ∧ *)
      admit. 
    }
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
    intros Hp.
    pose proof (S2 Hp) as S2.
    now Syll S2 n3_47 S3.
  }
  assert (S4 : (∃ x y, Phi z w <[- z w -]> ((z = x) ∧ (w = y)))
    → (((Phi Z W) ∧ (Phi U V)) → ((Z = U) ∧ (W = V)))).
  {
    pose proof (n11_11 X Y (fun x y =>
      (Phi z w <[- z w -]> ((z = x) ∧ (w = y)))
        → (((Phi Z W) ∧ (Phi U V)) → ((Z = U) ∧ (W = V))))) 
      as n11_11.
    MP n11_11 S3.
    now rewrite -> n11_35 in n11_11.
  }
  assert (S5 : (∃ x y, Phi z w <[- z w -]> ((z = x) ∧ (w = y)))
    → (∀ z w u v, (Phi z w ∧ Phi u v) → ((z = u) ∧ (w = v)))).
  {
    (* For 4 variables, the generalization has applied twice! *)
    pose proof (n11_11 U V (fun u v =>
      (∃ x y, Phi z w <[- z w -]> ((z = x) ∧ (w = y)))
      → (((Phi Z W) ∧ (Phi u v)) → ((Z = u) ∧ (W = v))))) 
      as n11_11a.
    MP n11_11a S4.
    rewrite <- n11_3 in n11_11a.
    pose proof (n11_11 Z W (fun z w =>
    (∃ x y, Phi z w <[- z w -]> ((z = x) ∧ (w = y)))
      → (∀ u v, ((Phi z w) ∧ (Phi u v)) → ((z = u) ∧ (w = v)))
      )) as n11_11b.
    MP n11_11b n11_11a.
    now rewrite <- n11_3 in n11_11b.
  }
  assert (S6 : ((Phi X Y) ∧ (∀ z w u v, 
    ((Phi z w) ∧ (Phi u v)) → ((z = u) ∧ (w = v)))
      → (Phi X Y ∧ ((Phi z w ∧ Phi X Y) -[ z w ]> ((z = X) ∧ (w = Y)))))).
  {
    (* The ordering here is annoying... *)
    pose proof (n11_1 X Y (fun u v =>
      (∀ z w, Phi z w ∧ Phi u v → z = u ∧ w = v))) as n11_1.
    assert (A1 : (∀ x y z w : Prop, Phi z w ∧ Phi x y → z = x ∧ w = y)
      ↔ (∀ z w x y : Prop, Phi z w ∧ Phi x y → z = x ∧ w = y)).
    { admit. }
    rewrite -> A1 in n11_1.
    pose proof (Fact3_45
      (∀ z w x y : Prop, Phi z w ∧ Phi x y → z = x ∧ w = y)
      ((Phi z w ∧ Phi X Y)-[ z w ]> z = X ∧ w = Y)
      (Phi X Y)) as Fact3_45.
    MP Fact3_45 n11_1.
    rewrite -> n4_3 in Fact3_45.
    now setoid_rewrite -> n4_3 in Fact3_45 at 4.
  }
  assert (S7 : ((Phi X Y) ∧ (∀ z w u v, 
    ((Phi z w) ∧ (Phi u v)) → ((z = u) ∧ (w = v))))
    → (Phi X Y ∧ (Phi z w -[ z w ]> ((z = X) ∧ (w = Y))))).
  {
    (* TODO: design the n5_33 on a quantified version to procceed *)
    pose proof n5_33 as n5_33.
    (* rewrite <- n5_33 in S6. *)
    admit.
  }
  assert (S8 : ((Phi X Y) ∧ (∀ z w u v, 
    ((Phi z w) ∧ (Phi u v)) → ((z = u) ∧ (w = v))))
    → (Phi z w <[- z w -]> ((z = X) ∧ (w = Y)))).
  {
    pose proof (n14_123 X Y Phi) as n14_123.
    destruct n14_123 as [n14_123l _].
    setoid_rewrite -> n4_3 in S7 at 4.
    now rewrite <- n14_123l in S7.
  }
  assert (S9 : ((∃ x y, Phi x y) ∧ (∀ z w u v,
      (Phi z w ∧ Phi u v) → ((z = u) ∧ (w = v)))
    → (∃ x y, Phi z w <[- z w -]> ((z = x) ∧ (w = y))))).
  {
    pose proof n11_45 as _n11_45.
    pose proof (n11_11 X Y (fun x y =>
      ((Phi x y) ∧ (∀ z w u v, 
        ((Phi z w) ∧ (Phi u v)) → ((z = u) ∧ (w = v))))
        → (Phi z w <[- z w -]> ((z = x) ∧ (w = y))))) as n11_11.
    MP n11_11 S8.
    pose proof (n11_34
      (fun x y => Phi x y ∧ (∀ z w u v,
        (Phi z w ∧ Phi u v) → ((z = u) ∧ (w = v))))
      (fun x y => (Phi z w <[- z w -]> ((z = x) ∧ (w = y))))) 
      as n11_34.
    MP n11_34 n11_11.
    setoid_rewrite -> n4_3 in n11_34 at 1.
    rewrite -> n11_45 in n11_34.
    now rewrite -> n4_3 in n11_34 at 1.
  }
  assert (S10 : (∃ x y,  Phi z w<[- z w -]>z = x ∧ w = y )
    ↔ (∃ x y, Phi x y) 
      ∧ ∀ z w u v, Phi z w ∧ Phi u v → z = u ∧ w = v).
  {
    clear S2 S3 S4 S6 S7 S8.
    assert (C1 : ((∃ x y,  Phi z w <[- z w -]> z = x ∧ w = y ) → ∃ x y : Prop, Phi x y)
      ∧ ((∃ x y,  Phi z w <[- z w -]> z = x ∧ w = y )
        → ∀ z w u v, Phi z w ∧ Phi u v → z = u ∧ w = v)).
    { clear S9. now Conj S1 S5 C1. }
    pose proof (Comp3_43
      (∃ x y, Phi z w <[- z w -]> z = x ∧ w = y)
      (∃ x y, Phi x y)
      (∀ z w u v, Phi z w ∧ Phi u v → z = u ∧ w = v)) 
      as Comp3_43.
    MP Comp3_43 C1.
    clear S1 S5 C1.
    move S9 after Comp3_43.
    Conj Comp3_43 S9 S10.
    now Equiv S10.
  }
  exact S10.
Admitted.

Theorem n14_13 (A : Prop) (s : string) (Phi : Prop → Prop) : 
  (iota_f s Phi (fun x => A = (Iota s x)))
  ↔ (iota_f s Phi (fun x => (Iota s x) = A)). 
Proof.
  (* TOOLS *)
  set (B := Individual "b").
  (* ******** *)
  assert (S1 : (iota_f s Phi (fun x => A = (Iota s x)))
    ↔ (∃ b, (Phi x <[- x -]> (x = b)) ∧ A = b)).
  { apply n14_1. }
  assert (S2 : ((Phi x <[- x -]> (x = B)) ∧ (A = B))
    ↔ ((Phi x <[- x -]> (x = B)) ∧ (B = A))).
  {
    pose proof (n13_16 A B) as n13_16.
    pose proof (n4_36 (A = B) (B = A) (Phi x <[- x -]> (x = B))) as n4_36.
    MP n4_36 n13_16.
    rewrite -> n4_3 in n4_36.
    now setoid_rewrite -> n4_3 in n4_36 at 2.
  }
  assert (S3 : (∃ b, (Phi x <[- x -]> x = b) ∧ (A = b))
    ↔ (∃ b, (Phi x <[- x -]> x = b) ∧ (b = A))).
  {
    pose proof (n10_11 B (fun b => 
        ((Phi x <[- x -]> (x = b)) ∧ (A = b))
      ↔ ((Phi x <[- x -]> (x = b)) ∧ (b = A)))) as n10_11.
    MP n10_11 S2.
    pose proof (n10_281 
      (fun b => (Phi x <[- x -]> (x = b)) ∧ (A = b))
      (fun b => (Phi x <[- x -]> (x = b)) ∧ (b = A))) as n10_281.
    now MP n10_281 n10_11.
  }
  assert (S4 : (∃ b, (Phi x <[- x -]> x = b) ∧ (A = b))
    ↔ (iota_f s Phi (fun x => (Iota s x) = A))).
  { now rewrite <- (n14_1 s Phi  (fun b => b = A)) in S3. }
  assert (S5 : (iota_f s Phi (fun x => A = (Iota s x)))
    ↔ (iota_f s Phi (fun x => (Iota s x) = A))).
  { now rewrite -> S4 in S1. }
  exact S5.
Qed.

(* There are 2 ways to intrepret the iotas in this proposition. Original text
has also given both ways to interpre them correspondingly. It seems that
we will take the one-at-a-time as the usual way *)
Theorem n14_131 (s1 s2 : string) (Phi Psi : Prop → Prop) : 
  iota_f s1 Phi (fun x => iota_f s1 Psi (fun y =>
    (Iota s1 x) = (Iota s1 y)))
  ↔
  iota_f s1 Psi (fun y => iota_f s1 Phi (fun x =>
    (Iota s1 y) = (Iota s1 x))).
Proof.
  assert (S1 : iota_f s1 Phi (fun x => iota_f s1 Psi (fun y =>
      (Iota s1 x) = (Iota s1 y)))
    ↔ (∃ b, (Phi x <[- x -]> (x = b)) 
      ∧ iota_f s1 Psi (fun y => b = (Iota s1 y)))).
  { apply n14_1. }
  assert (S2 : iota_f s1 Phi (fun x => iota_f s1 Psi (fun y =>
      (Iota s1 x) = (Iota s1 y)))
    ↔ (∃ b, (Phi x <[- x -]> (x = b)) 
      ∧ (∃ c, (Psi x <[- x -]> (x = c)) ∧ (b = c)))).
  { now setoid_rewrite -> n14_1 in S1 at 3. }
  assert (S3 : iota_f s1 Phi (fun x => iota_f s1 Psi (fun y =>
      (Iota s1 x) = (Iota s1 y)))
    ↔ (∃ c, (Psi x <[- x -]> (x = c))
      ∧ (∃ b, (Phi x <[- x -]> (x = b)) ∧ (b = c)))).
  {
    setoid_rewrite -> n4_3 in S2 at 2.
    setoid_rewrite -> n4_3 in S2 at 3.
    rewrite -> n11_6 in S2.
    setoid_rewrite <- n4_3 in S2 at 3.
    now setoid_rewrite <- n4_3 in S2 at 2.
  }
  assert (S4 : iota_f s1 Phi (fun x => iota_f s1 Psi (fun y =>
      (Iota s1 x) = (Iota s1 y)))
    ↔ (∃ c, (Psi x <[- x -]> (x = c)) 
      ∧ iota_f s1 Phi (fun x => (Iota s1 x) = c))).
  { now setoid_rewrite <- (n14_1 s1) in S3 at 2. }
  assert (S5 : iota_f s1 Phi (fun x => iota_f s1 Psi (fun y =>
      (Iota s1 x) = (Iota s1 y)))
    ↔ (∃ c, (Psi x <[- x -]> (x = c)) 
      ∧ iota_f s1 Phi (fun x => c = (Iota s1 x)))).
  { now setoid_rewrite <- n14_13 in S4. }
  assert (S6 : iota_f s1 Phi (fun x => iota_f s1 Psi 
      (fun y => (Iota s1 x) = (Iota s1 y)))
    ↔ iota_f s1 Psi (fun y => iota_f s1 Phi (fun x =>
      (Iota s1 y) = (Iota s1 x)))).
  { now rewrite <- (n14_1 s1) in S5. }
  exact S6.
Qed.

Theorem n14_131_alt (s1 s2 : string) (Phi Psi : Prop → Prop) : 
  iota_f2 s1 s2 Phi Psi (fun x y => (Iota s1 x) = (Iota s2 y))
  ↔
  iota_f2 s2 s1 Psi Phi (fun x y => (Iota s2 y) = (Iota s1 x)). 
Proof.
  assert (S1 : iota_f2 s1 s2 Phi Psi (fun x y => (Iota s1 x) = (Iota s2 y))
    ↔ ∃ b c, (Phi x <[- x -]> (x = b)) 
      ∧ (Psi x <[- x -]> (x = c)) ∧ (b = c)).
  {
    (* We use the definition of iota_f2 instead, for the obvious reason.
     *14.111 ignored *)
    apply n14_112.
  }
  assert (S2 : iota_f2 s1 s2 Phi Psi (fun x y => (Iota s1 x) = (Iota s2 y))
    ↔ ∃ b c, (Psi x <[- x -]> (x = c)) 
      ∧ (Phi x <[- x -]> (x = b)) ∧ (c = b)).
  {
    (* *11.11, *11.341 ignored *)
    setoid_rewrite -> n13_16 in S1 at 4.
    setoid_rewrite -> n4_3 in S1 at 2.
    setoid_rewrite -> n4_32 in S1.
    now setoid_rewrite -> n4_3 in S1 at 4.
  }
  assert (S3 : iota_f2 s1 s2 Phi Psi (fun x y => 
      (Iota s1 x) = (Iota s2 y))
    ↔ iota_f2 s2 s1 Psi Phi (fun x y => (Iota s2 y) = (Iota s1 x))).
  {
    (* much of the citations are wrong... *)
    rewrite -> n11_23 in S2.
    pose proof (n14_112 s2 s1 Psi Phi
      (fun x y => Iota s2 y = Iota s1 x)) as n14_112.
    setoid_rewrite -> n13_16 in S2 at 4.
    now rewrite <- n14_112 in S2.
  }
  exact S3.
Qed.

Theorem n14_14 (A B : Prop) (s : string) (Phi : Prop → Prop) :
  ((A = B) ∧ (iota_f s Phi (fun x => B = (Iota s x))))
  → (iota_f s Phi (fun x => A = (Iota s x))).
Proof.
  rewrite -> n4_3.
  rewrite -> n13_16.
  exact (n13_13 B A (fun a => 
      (iota_f s Phi (fun x => a = (Iota s x))))).
Qed.

Theorem n14_142 (A : Prop) (s1 s2 : string) (Phi Psi : Prop → Prop) :
  iota_f s1 Phi (fun x => A = Iota s1 x)
    ∧ iota_f s1 Phi (fun x => iota_f s2 Psi 
      (fun y => Iota s1 x = Iota s2 y))
  → iota_f s2 Psi (fun x => A = Iota s2 x).
Proof.
  assert (S1 : (iota_f s1 Phi (fun x => A = Iota s1 x)
      ∧ iota_f s1 Phi (fun x => iota_f s2 Psi 
        (fun y => Iota s1 x = Iota s2 y)))
    → ((∃ b, (Phi x <[- x -]> (x = b)) ∧ (A = b)) 
      ∧ (∃ c, (Phi x <[- x -]> (x = c)) ∧ iota_f s2 Psi 
        (fun x => c = (Iota s2 x))))).
  {
    pose proof (n14_1 s1 Phi (fun b => A = Iota s1 b)) 
      as n14_1a.
    destruct n14_1a as [n14_1al _].
    pose proof (n14_1 s1 Phi (fun c =>
      iota_f s2 Psi (fun y => c = Iota s2 y))) as n14_1b.
    destruct n14_1b as [n14_1bl _].
    Conj n14_1al n14_1bl C1.
    pose proof (n3_47
      (iota_f s1 Phi (λ b, A = Iota s1 b))
      (iota_f s1 Phi (λ c, iota_f s2 Psi (λ y, c = Iota s2 y)))
      (∃ b, (Phi x <[- x -]> x = b) ∧ A = Iota s1 b)
      (∃ b, (Phi x <[- x -]> x = b) ∧ iota_f s2 Psi (λ y, b = Iota s2 y))) 
      as n3_47.
    now MP n3_47 C1.
  }
  assert (S2 : (iota_f s1 Phi (fun x => A = Iota s1 x)
    ∧ iota_f s1 Phi (fun x => iota_f s2 Psi 
      (fun y => Iota s1 x = Iota s2 y)))
  → ((Phi x <[- x -]> (x = A))
    ∧ (∃ c, (Phi x <[- x -]> (x = c)) ∧ iota_f s2 Psi 
        (fun x => c = (Iota s2 x))))).
  {
    setoid_rewrite -> n4_3 in S1 at 3.
    setoid_rewrite -> n13_16 in S1 at 3.
    now rewrite -> n13_195 in S1.
  }
  assert (S3 : (iota_f s1 Phi (fun x => A = Iota s1 x)
    ∧ iota_f s1 Phi (fun x => iota_f s2 Psi 
      (fun y => Iota s1 x = Iota s2 y)))
  → ∃ c, (Phi x <[- x -]> (x = A)) ∧ (Phi x <[- x -]> (x = c)) 
      ∧ iota_f s2 Psi (fun x => c = (Iota s2 x))).
  { now rewrite <- n10_35 in S2. }
  assert (S4 : (iota_f s1 Phi (fun x => A = Iota s1 x)
    ∧ iota_f s1 Phi (fun x => iota_f s2 Psi 
      (fun y => Iota s1 x = Iota s2 y)))
  → ∃ c, (Phi x <[- x -]> (x = A)) ∧ (A = c)
      ∧ iota_f s2 Psi (fun x => c = (Iota s2 x))).
  {
    intros Hp.
    pose proof (S3 Hp) as S3.
    (* I don't think here is provable *)
    pose proof n14_121 as n14_121.
    admit.
  }
  assert (S5 : iota_f s1 Phi (fun x => A = Iota s1 x)
      ∧ iota_f s1 Phi (fun x => iota_f s2 Psi 
        (fun y => Iota s1 x = Iota s2 y))
    → iota_f s2 Psi (fun x => A = Iota s2 x)).
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

Theorem n14_144 (s1 s2 s3 : string) (Phi Psi Chi : Prop → Prop) : 
  (iota_f2 s1 s2 Phi Psi (fun x y => (Iota s1 x) = (Iota s2 y))
    ∧ iota_f2 s2 s3 Psi Chi (fun x y => (Iota s2 x) = (Iota s3 y)))
  → iota_f2 s1 s3 Phi Chi (fun x y => (Iota s1 x) = (Iota s3 y)).
Proof.
  (* TOOLS *)
  set (X := Individual "x").
  set (Y := Individual "y").
  (* ******** *)
  assert (S1 : (iota_f2 s1 s2 Phi Psi (fun x y => (Iota s1 x) = (Iota s2 y))
    ∧ iota_f2 s2 s3 Psi Chi (fun x y => (Iota s2 x) = (Iota s3 y)))
    → ((∃ a b, (Phi x <[- x -]> (x = a)) 
          ∧ (Psi x <[- x -]> (x = b)) ∧ (a = b)))
        ∧ (∃ c d, (Psi x <[- x -]> (x = c)) 
          ∧ (Chi x <[- x -]> (x = d)) ∧ (c = d))).
  {
    pose proof (n14_112 s1 s2 Phi Psi
      (fun x y => Iota s1 x = Iota s2 y)) as n14_112a.
    destruct n14_112a as [n14_112al _].
    pose proof (n14_112 s2 s3 Psi Chi
      (fun x y => Iota s2 x = Iota s3 y)) as n14_112b.
    destruct n14_112b as [n14_112bl _].
    assert (C1 : (iota_f2 s1 s2 Phi Psi (λ x y, x = y)
        → ∃ b c, (Phi x <[- x -]> x = b) 
          ∧ (Psi x <[- x -]> x = c) ∧ b = c)
      ∧ (iota_f2 s2 s3 Psi Chi (λ x y, x = y)
      → ∃ b c, (Psi x <[- x -]> x = b)
          ∧ (Chi x <[- x -]> x = c) ∧ b = c)).
    { now Conj n14_113al n14_113bl C1. }
    pose proof (n3_47
      (iota_f2 s1 s2 Phi Psi (fun x y => Iota s1 x = Iota s2 y))
      (iota_f2 s2 s3 Psi Chi (fun x y => Iota s2 x = Iota s3 y))
      (∃ b c, (Phi x <[- x -]> x = b) 
        ∧ (Psi x <[- x -]> x = c) ∧ b = c)
      (∃ b c, (Psi x <[- x -]> x = b)
        ∧ (Chi x <[- x -]> x = c) ∧ b = c)) as n3_47.
    now MP n3_47 C1.
  }
  assert (S2 : (iota_f2 s1 s2 Phi Psi (fun x y => (Iota s1 x) = (Iota s2 y))
      ∧ iota_f2 s2 s3 Psi Chi (fun x y => (Iota s2 x) = (Iota s3 y)))
    → ((∃ a, (Phi x <[- x -]> (x = a)) ∧ (Psi x <[- x -]> (x = a)))
      ∧ (∃ c, (Psi x <[- x -]> (x = c)) ∧ (Chi x <[- x -]> (x = c))))).
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
  assert (S3 : (iota_f2 s1 s2 Phi Psi (fun x y => (Iota s1 x) = (Iota s2 y))
      ∧ iota_f2 s2 s3 Psi Chi (fun x y => (Iota s2 x) = (Iota s3 y)))
    → ∃ a c, (Phi x <[- x -]> (x = a))
      ∧ (Psi x <[- x -]> (x = a)) ∧ (Psi x <[- x -]> (x = c))
      ∧ (Chi x <[- x -]> (x = c))).
  {
    rewrite <- n11_54 in S2.
    now setoid_rewrite -> n4_32 in S2.
  }
  assert (S4 : (iota_f2 s1 s2 Phi Psi (fun x y => (Iota s1 x) = (Iota s2 y))
      ∧ iota_f2 s2 s3 Psi Chi (fun x y => (Iota s2 x) = (Iota s3 y)))
    → ∃ a c, (Phi x <[- x -]> (x = a)) ∧ (Chi x <[- x -]> (x = c))
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
    pose proof (n14_121 X Y Psi) as n14_121.
    pose proof (Fact3_45
      ((Psi x <[- x -]> x = X) ∧ Psi x <[- x -]> x = Y)
      (X = Y)
      ((Phi x <[- x -]> x = X) ∧ Chi x <[- x -]> x = Y)) as Fact3_45.
    MP Fact3_45 n14_121.
    pose proof (n11_11 X Y (fun a c =>
        ((Psi x <[- x -]> x = a) ∧ Psi x <[- x -]> x = c)
        ∧ (Phi x <[- x -]> x = a) ∧ Chi x <[- x -]> x = c
      → a = c ∧ (Phi x <[- x -]> x = a) ∧ Chi x <[- x -]> x = c)) 
      as n11_11.
    MP n11_11 Fact3_45.
    pose proof (n11_34
      (fun x y =>
        (((Psi x0 <[- x0 -]> x0 = x) ∧ Psi x0 <[- x0 -]> x0 = y)
        ∧ (Phi x0 <[- x0 -]> x0 = x) ∧ Chi x0 <[- x0 -]> x0 = y))
      (fun x y => x = y
        ∧ (Phi x0 <[- x0 -]> x0 = x) ∧ Chi x0 <[- x0 -]> x0 = y)) 
      as n11_34.
    MP n11_34 n11_11.
    clear n4_32 n14_121 Fact3_45 n11_11.
    MP n11_34 S3.
    setoid_rewrite -> n4_3 in n11_34.
    now setoid_rewrite -> n4_32 in n11_34.
  }
  assert (S5 : (iota_f2 s1 s2 Phi Psi (fun x y => (Iota s1 x) = (Iota s2 y))
      ∧ iota_f2 s2 s3 Psi Chi (fun x y => (Iota s2 x) = (Iota s3 y)))
    → iota_f2 s1 s3 Phi Chi (fun x y => (Iota s1 x) = (Iota s3 y))).
  {
    pose proof (n14_112 s1 s3 Phi Chi (fun a c => (Iota s1 a) = (Iota s3 c))) 
      as n14_112.
    now rewrite <- n14_112 in S4.
  }
  exact S5.
Qed.

Theorem n14_145 (A : Prop) (s1 s2 : string) (Phi Psi : Prop → Prop) : 
  ((iota_f s1 Phi (fun x => A = (Iota s1 x))) 
    ∧ (iota_f s2 Psi (fun x => A = (Iota s2 x))))
  → (iota_f2 s1 s2 Phi Psi (fun x y => (Iota s1 x) = (Iota s2 y))).
Proof.
  assert (S1 : (iota_f s1 Phi (fun x => A = (Iota s1 x)))
    ↔ ∃ b, (Phi x <[- x -]> (x = b)) ∧ (A = b)).
  { apply n14_1. }
  assert (S2 : (iota_f s1 Phi (fun x => A = (Iota s1 x)))
    ↔ (Phi x <[- x -]> (x = A))).
  {
    setoid_rewrite -> n4_3 in S1 at 2.
    setoid_rewrite -> n13_16 in S1 at 2.
    now rewrite -> n13_195 in S1.
  }
  assert (S3 : ((iota_f s1 Phi (fun x => A = (Iota s1 x))) 
      ∧ (iota_f s2 Psi (fun x => A = (Iota s2 x))))
    ↔ ((Phi x <[- x -]> (x = A)) ∧ (∃ b,
      (Psi x <[- x -]> (x = b)) ∧ (A = b)))).
  {
    pose proof (n14_1 s2 Psi (fun x => A = (Iota s2 x))) 
      as n14_1.
      simpl in n14_1.
    assert (C1 : (iota_f s1 Phi (λ x, A = Iota s1 x) 
        ↔ Phi x <[- x -]> x = A)
      ∧ (iota_f s2 Psi (λ x, A = Iota s2 x)
        ↔ ∃ b, ( Psi x <[- x -]> x = b) ∧ A = Iota s2 b)).
    { clear S1. now Conj S2 n14_1 C1. }
    pose proof (n4_38
      (iota_f s1 Phi (fun x => A = (Iota s1 x)))
      (iota_f s2 Psi (λ x : Prop, A = Iota s2 x))
      (Phi x <[- x -]> (x = A))
      (∃ b, ( Psi x<[-x-]>x = b ) ∧ A = Iota s2 b)) 
      as n4_38.
    now MP n4_38 C1.
  }
  assert (S4 : ((iota_f s1 Phi (fun x => A = (Iota s1 x))) 
      ∧ (iota_f s2 Psi (fun x => A = (Iota s2 x))))
    ↔ (∃ b, (Phi x <[- x -]> (x = A))
      ∧ (Psi x <[- x -]> (x = b)) ∧ (A = b))).
  { now rewrite <- n10_35 in S3. }
  assert (S5 : ((iota_f s1 Phi (fun x => A = (Iota s1 x))) 
      ∧ (iota_f s2 Psi (fun x => A = (Iota s2 x))))
    → (iota_f2 s1 s2 Phi Psi (fun x y => (Iota s1 x) = (Iota s2 y)))).
  {
    destruct S4 as [S4 _].
    pose proof (n10_24 (fun a => ∃ b, (Phi x <[- x -]> x = a) 
      ∧ (Psi x <[- x -]> x = b) ∧ a = b) A) as n10_24.
    Syll n10_24 S4 S4_1.
    pose proof (n14_112 s1 s2 Phi Psi (fun a b => a = b)) as n14_112.
    now rewrite <- n14_112 in S4_1.
  }
  exact S5.
Qed.

Theorem n14_15 (B : Prop) (s : string) (Phi Psi : Prop → Prop) : 
  (iota_f s Phi (fun x => (Iota s x) = B))
  → (iota_f s Phi (fun x => Psi (Iota s x)) ↔ Psi B).
Proof.
  assert (S1 : (iota_f s Phi (fun x => (Iota s x) = B))
    → (∃ c, (Phi x <[- x -]> (x = c)) ∧ (c = B))).
  { apply n14_1. }
  assert (S2 : (iota_f s Phi (fun x => (Iota s x) = B))
    → (Phi x <[- x -]> (x = B))).
  {
    setoid_rewrite -> n4_3 in S1.
    now rewrite -> n13_195 in S1.
  }
  assert (S3 : (iota_f s Phi (fun x => (Iota s x) = B))
    → ((iota_f s Phi Psi) ↔ ∃ c, 
      ((x = B) <[- x -]> (x = c)) ∧ Psi c)).
  {
    (* Simplification: for this step to be performed, S2 has become the 
    one to rewrite on the others. Technically speaking this involves the 
    alternative form for `Syll` *)
    intro Hp.
    pose proof (S2 Hp) as S2.
    pose proof (n14_1 s Phi Psi) as n14_1.
    now setoid_rewrite -> S2 in n14_1.
  }
  assert (S4 : (iota_f s Phi (fun x => (Iota s x) = B))
    → (iota_f s Phi Psi ↔ Psi B)).
  { now rewrite -> n13_192 in S3. }
  exact S4.
Qed.

(* Predicative Variant *)
Definition n14_15_pred (B : Prop) (s : string) (Phi : Prop → Prop) 
  (Psi : Predicate 1) : 
  (iota_f s Phi (fun x => (Iota s x) = B))
  → (iota_f s Phi (fun x => Psi (Iota s x)) ↔ Psi B).
Admitted.

Theorem n14_16 (s1 s2 : string) (Phi Psi Chi : Prop → Prop) :
  iota_f s1 Phi (fun x => iota_f s2 Psi 
    (fun y => (Iota s1 x) = (Iota s2 y)))
  →
  (iota_f s1 Phi Chi ↔ iota_f s2 Psi Chi).
Proof.
  (* TOOLS *)
  set (B := Individual "b").
  (* ******** *)
  assert (S1 : iota_f s1 Phi (fun x => iota_f s2 Psi 
    (fun y => (Iota s1 x) = (Iota s2 y)))
    → ∃ b, (Phi x <[- x -]> (x = b)) ∧ 
      iota_f s2 Psi (fun y => b = Iota s2 y)).
  { apply n14_1. }
  assert (S2 : (Phi x <[- x -]> (x = B)) 
    → (iota_f s1 Phi Chi ↔ (∃ c, 
      ((x = B) <[- x -]> (x = c)) ∧ Chi c))).
  {
    (* simplification as the same as previous one
    we might need to use P → P in normal way *)
    intro Hp.
    pose proof (n14_1 s1 Phi Chi) as n14_1.
    now setoid_rewrite -> Hp in n14_1.
  }
  assert (S3 : (Phi x <[- x -]> (x = B)) → 
    (iota_f s1 Phi Chi ↔ Chi B)).
  { now rewrite -> n13_192 in S2. }
  assert (S4 : iota_f s2 Psi (fun y => B = (Iota s2 y))
    → (Chi B ↔ iota_f s2 Psi (fun y => Chi (Iota s2 y)))).
  {
    pose proof (n14_15 B s2 Psi Chi) as n14_15.
    rewrite <- n14_13 in n14_15.
    now rewrite <- n4_21 in n14_15.
  }
  assert (S5 : ((Phi x <[- x -]> (x = B)) ∧ 
      iota_f s2 Psi (fun y => B = (Iota s2 y)))
    → (iota_f s1 Phi Chi ↔ iota_f s2 Psi Chi)).
  {
    assert (C1 : ((∀ x : Prop, Phi x ↔ x = B) 
        → iota_f s1 Phi Chi ↔ Chi B)
      ∧ (iota_f s2 Psi (λ y : Prop, B = Iota s2 y)
        → Chi B ↔ iota_f s2 Psi (λ y : Prop, Chi (Iota s2 y)))).
    { clear S1 S2. now Conj S3 S4 C1. }
    pose proof (n3_47
      (Phi x <[- x -]> x = B)
      (iota_f s2 Psi (λ y, B = Iota s2 y))
      (iota_f s1 Phi Chi ↔ Chi B)
      (Chi B ↔ iota_f s2 Psi (λ y, Chi (Iota s2 y)))) as n3_47.
    MP n3_47 C1.
    pose proof (n4_22 (iota_f s1 Phi Chi) (Chi B)
      (iota_f s2 Psi (λ y : Prop, Chi (Iota s2 y)))) as n4_22.
    now Syll n3_47 n4_22 S5.
  }
  assert (S6 : iota_f s1 Phi (fun x => iota_f s2 Psi 
      (fun y => (Iota s1 x) = (Iota s2 y)))
    → iota_f s1 Phi Chi ↔ iota_f s2 Psi Chi).
  {
    (* *10.2 ignored -  it doesn't fit in *)
    pose proof n10_11 as _n10_11.
    pose proof (n10_11 B (fun b =>
      ((∀ x, Phi x ↔ x = b) ∧ iota_f s2 Psi (λ y, b = Iota s2 y))
      → (iota_f s1 Phi Chi ↔ iota_f s2 Psi Chi))) as n10_11.
    MP n10_11 S5.
    rewrite -> n10_23 in n10_11.
    now Syll S1 n10_11 S6.
  }
  exact S6.
Qed.

Theorem n14_17 (B : Prop) (s : string) (Phi : Prop → Prop) : 
  (iota_f s Phi (fun x => (Iota s x) = B))
  ↔
  (∀ Psi : Predicate 1, (iota_f s Phi (fun x =>
    Psi (Iota s x)) ↔ Psi B)).
Proof.
  (* TOOLS *)
  set (IChi := Intro_pred "Chi" 1).
  set (X := Individual "x").
  (* ******** *)
  assert (S1 : iota_f s Phi (fun x => (Iota s x) = B)
    → (∀ Psi : Predicate 1, (iota_f s Phi (fun x =>
      Psi (Iota s x)) ↔ Psi B))).
  {
    (* *10.11 ignored *)
    pose proof (n14_15_pred B s Phi) as n14_15.
    now rewrite -> n10_21_pred in n14_15.
  }
  (* The following step is a beautiful demonstration on how our iota works
    with predicates. During formalization, we find out that there are even
    shorter ways to finish the proof, *but* that is due to our lack in setting
    up correct abstraction. We prefer the most conservative way to procceed
    on this step. In this way, quantified propositions will not be passed as
    parameters into functions/predicates so that the types should still be
    correct *)
  assert (S2 : ((IChi x <[- x -]> (x = B)) 
      ∧ (∀ Psi : Predicate 1, iota_f s Phi Psi ↔ Psi B))
    → (iota_f s Phi (fun x => (Iota s x) = B) ↔ (B = B))).
  {
    (* left part of the ∧ *)
    pose proof (n10_1 (fun x => IChi x ↔ (x = B)) B) 
      as n10_1a.
    (* right part of the ∧ *)
    pose proof (n10_1_pred (fun x : Predicate 1 => 
      (iota_f s Phi x) ↔ x B) IChi) as n10_1b.
    assert (C1 : ((∀ x, IChi x ↔ x = B) → IChi B ↔ B = B)
      ∧ ((∀ x : Predicate 1, iota_f s Phi x ↔ x B) 
        → iota_f s Phi IChi ↔ IChi B)).
    { now Conj n10_1a n10_1b C1. }
    pose proof (n3_47
      (∀ x, IChi x ↔ x = B)
      (∀ x : Predicate 1, iota_f s Phi x ↔ x B)
      (IChi B ↔ B = B)
      (iota_f s Phi IChi ↔ IChi B)) as n3_47.
    MP n3_47 C1.
    pose proof (n4_22 (iota_f s Phi IChi) (IChi B)
      (B = B)) as n4_22.
    clear n10_1a n10_1b C1.
    rewrite -> n4_3 in n4_22.
    Syll n3_47 n4_22 Sy1.
    (* We can see that in the original text, `IChi` has been substituted into
    a concrete function. Our analogue here is generalizing over this "Predicate"
    whose body is currently an "admitted" definition to further substitute into
    a concrete definition, by applying n10_1 and n10_11 variants *)
    pose proof (n10_11_pred IChi (fun p => 
      iota_f s Phi p ↔ B = B)) as n10_11a.
    clear n3_47 n4_22.
    Syll Sy1 n10_11a Sy2.
    pose proof (n10_1_pred
      (fun p => iota_f s Phi p ↔ B = B)
      (fun x => Iota s x = B)) as n10_1c.
    clear Sy1 n10_11a.
    now Syll Sy2 n10_1c S2.
  }
  assert (S3 : ((IChi x <[- x -]> (x = B)) 
      ∧ (∀ Psi : Predicate 1, iota_f s Phi Psi
        ↔ Psi B))
    → iota_f s Phi (fun x => (Iota s x) = B)).
  {
    (* Similar as previous one, this application on n13_15 is somthing 
    out of the context. We should add a special rule for n13_15 in the 
    future *)
    pose proof n13_15 as n13_15.
    admit.
  }
  assert (S4 : (∃ Chi : Predicate 1, (Chi x <[- x -]> (x = B)))
    → ((∀ Psi : Predicate 1, iota_f s Phi Psi ↔ Psi B)
      → iota_f s Phi (fun x => x = B))).
  {
    pose proof (Exp3_3 (IChi x <[- x -]> x = B)
      (∀ Psi : Predicate 1, iota_f s Phi Psi ↔ Psi B)
      (iota_f s Phi (λ x : Prop, Iota s x = B))) as Exp3_3.
    MP Exp3_3 S3.
    pose proof (n10_11_pred IChi (fun p =>
      (p x <[- x -]> x = B)
      → (∀ Psi : Predicate 1, iota_f s Phi Psi ↔ Psi B)
      → iota_f s Phi (λ x : Prop, Iota s x = B))) as n10_11.
    MP n10_11 Exp3_3.
    now rewrite -> n10_23_pred in n10_11.
  }
  assert (S5 : ∃ Chi : Predicate 1, Chi x <[- x -]> (x = B)).
  {
    pose proof (n12_1 (fun x => x = B)) as n12_1.
    now setoid_rewrite -> n4_21 in n12_1.
  }
  assert (S6 : (∀ Psi : Predicate 1, 
      (iota_f s Phi Psi) ↔ Psi B) 
    → iota_f s Phi (fun x => (Iota s x) = B)).
  { now MP S4 S5. }
  assert (S7 : (iota_f s Phi (fun x => (Iota s x) = B))
    ↔ (∀ Psi : Predicate 1, (iota_f s Phi (fun x =>
      Psi (Iota s x)) ↔ Psi B))).
  {
    assert (C1 : (iota_f s Phi (λ x, Iota s x = B)
        → ∀ Psi : Predicate 1, iota_f s Phi Psi ↔ Psi B)
      ∧ ((∀ Psi : Predicate 1, iota_f s Phi Psi ↔ Psi B)
        → iota_f s Phi (λ x, Iota s x = B))).
    { clear S2 S3 S4 S5. now Conj S1 S6 C1. }
    now Equiv C1.
  }
  exact S7.
Admitted.

Theorem n14_171 (B : Prop) (s : string) (Phi : Prop → Prop) : 
  (iota_f s Phi (fun x => (Iota s x) = B))
  ↔
  (∀ Psi : Predicate 1, Psi B → iota_f s Phi Psi).
Proof.
  assert (S1 : (iota_f s Phi (fun x => (Iota s x) = B))
    → (∀ Psi : Predicate 1, Psi B → iota_f s Phi Psi)).
  { apply n14_17. }
  assert (S2 : (∀ Psi : Predicate 1, Psi B → iota_f s Phi Psi)
    → ((B = B) → iota_f s Phi (fun x => (Iota s x) = B))).
  {
    (* *12.1 ignored - I don't know if we need this or how is
    it being used actually. This might be something important *)
    pose proof (n10_1_pred
      (fun p => p B → iota_f s Phi p) 
      (fun x => x = B)) as n10_1.
    exact n10_1.
  }
  assert (S3 : (∀ Psi : Predicate 1, Psi B → iota_f s Phi Psi)
    → iota_f s Phi (fun x => (Iota s x) = B)).
  {
    (* as always... *)
    pose proof n13_15 as n13_15.
    admit.
  }
  assert (S4 : (iota_f s Phi (fun x => (Iota s x) = B))
    ↔ (∀ Psi : Predicate 1, Psi B → iota_f s Phi Psi)).
  {
    clear S2.
    Conj S1 S3 C1.
    now Equiv C1.
  }
  exact S4.
Admitted.

Theorem n14_18 (s : string) (Phi Psi : Prop → Prop) :
  iota_E Phi → ((∀ x, Psi x) → iota_f s Phi (fun x =>
    Psi (Iota s x))).
Proof.
  (* TOOLS *)
  set (B := Individual "b").
  (* ******** *)
  assert (S1 : (∀ x, Psi x) → Psi B).
  { apply n10_1. }
  assert (S2 : ((Phi x <[- x -]> (x = B)) ∧ (∀ x, Psi x))
    → ((Phi x <[- x -]> (x = B)) ∧ Psi B)).
  {
    pose proof (Fact3_45 (∀ x, Psi x)
      (Psi B) ((Phi x <[- x -]> (x = B)))) as Fact3_45.
    MP Fact3_45 S1.
    rewrite -> n4_3 in Fact3_45.
    now setoid_rewrite -> n4_3 in Fact3_45 at 2.
  }
  assert (S3 : ((∃ b, (Phi x <[- x -]> (x = b)) ∧ ∀ x, Psi x))
    → (∃ b, (Phi x <[- x -]> (x = b)) ∧ Psi b)).
  {
    pose proof (n10_11 B (fun b =>
      ((Phi x <[- x -]> (x = b)) ∧ (∀ x, Psi x))
      → ((Phi x <[- x -]> (x = b)) ∧ Psi b))) as n10_11.
    MP n10_11 S2.
    pose proof (n10_28
      (fun b => (Phi x <[- x -]> (x = b)) ∧ (∀ x, Psi x))
      (fun b => (Phi x <[- x -]> (x = b)) ∧ Psi b)) as n10_28.
    now MP n10_28 n10_11.
  }
  assert (S4 : ((∃ b, (Phi x <[- x -]> (x = b))) ∧ ∀ x, Psi x)
    → (∃ b, (Phi x <[- x -]> (x = b)) ∧ Psi b)).
  {
    setoid_rewrite n4_3 in S3 at 1.
    rewrite -> n10_35 in S3.
    now rewrite -> n4_3 in S3 at 1.
  }
  assert (S5 : (iota_E Phi ∧ ∀ x, Psi x) → iota_f s Phi (fun x =>
    Psi (Iota s x))).
  {
    rewrite <- (n14_1 s) in S4.
    now rewrite <- n14_11 in S4.
  }
  assert (S6 : iota_E Phi → ((∀ x, Psi x) → iota_f s Phi (fun x =>
    Psi (Iota s x)))).
  {
    pose proof (Exp3_3 (iota_E Phi) (∀ x, Psi x)
      (iota_f s Phi (fun x => Psi (Iota s x)))) as Exp3_3.
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
    <-> (exists b, ((x = A) <[- x -]> (x = b)) /\ (b = A))).
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

Theorem n14_201 (Phi : Prop → Prop) : iota_E Phi → ∃ x, Phi x. 
Proof.
  (* TOOLS *)
  set (X := Individual "x").
  set (B := Individual "b").
  (* ******** *)
  assert (S1 : iota_E Phi -> exists b, (Phi x <[- x -]> (x = b))).
  { apply n14_11. }
  assert (S2 : iota_E Phi -> exists b, (Phi b <-> (b = b))).
  {
    intro Hp.
    pose proof (S1 Hp) as S1.
    pose proof (n10_1 (fun x => Phi x <-> (x = B)) B) as n10_1.
    (* Note that we're having quantifiers in the function body *)
    pose proof (n10_11 B (fun b => (Phi x <[- x -]> x = b) 
      -> (Phi b <-> (b = b)))) as n10_11.
    MP n10_11 n10_1.
    pose proof (n10_28
      (fun b => Phi x <[- x -]> x = b)
      (fun b => Phi b ↔ b = b)) as n10_28.
    MP n10_28 n10_11.
    now MP n10_28 S1.
  }
  assert (S3 : iota_E Phi -> exists x, Phi x).
  {
    pose proof n13_15 as n13_15.
    admit.
  }
  exact S3.
Admitted.

Theorem n14_202 (B : Prop) (s : string) (Phi : Prop → Prop) : 
  ((Phi x <[- x -]> x = B) ↔ (iota_f s Phi (fun x => (Iota s x) = B)))
  ∧
  ((iota_f s Phi (fun x => (Iota s x) = B)) ↔ (Phi x <[- x -]> B = x))
  ∧
  ((Phi x <[- x -]> B = x) ↔ (iota_f s Phi (fun x => B = (Iota s x)))).
Proof.
  assert (S1 : (iota_f s Phi (fun x => (Iota s x) = B))
    <-> (exists c, (Phi x <[- x -]> (x = c)) /\ (c = B))).
  { apply n14_1. }
  assert (S2 : (iota_f s Phi (fun x => (Iota s x) = B))
    <-> (Phi x <[- x -]> (x = B))).
  {
    setoid_rewrite -> n4_3 in S1 at 2.
    now rewrite -> n13_195 in S1.
  }
  assert (S3 : ((Phi x <[- x -]> x = B) ↔ (iota_f s Phi (fun x => (Iota s x) = B)))
    ∧ ((iota_f s Phi (fun x => (Iota s x) = B)) ↔ (Phi x <[- x -]> B = x))
    ∧ ((Phi x <[- x -]> B = x) ↔ (iota_f s Phi (fun x => B = (Iota s x))))).
  {
    assert (S3_1 : ((Phi x <[- x -]> x = B) ↔ (iota_f s Phi (fun x => (Iota s x) = B)))).
    { now rewrite -> n4_21 in S2. }
    assert (S3_2 : ((iota_f s Phi (fun x => (Iota s x) = B)) ↔ (Phi x <[- x -]> B = x))).
    { now setoid_rewrite -> n13_16 in S2 at 2. }
    assert (S3_3 : ((Phi x <[- x -]> B = x) ↔ (iota_f s Phi (fun x => B = (Iota s x))))).
    {
      assert (S3_3 : (iota_f s Phi (fun x => B = (Iota s x)))
        <-> (exists c, (Phi x <[- x -]> (x = c)) /\ (B = c))).
      { apply n14_1. }
      setoid_rewrite -> n4_3 in S3_3 at 2.
      setoid_rewrite -> n13_16 in S3_3 at 2.
      rewrite -> n13_195 in S3_3.
      rewrite -> n4_21 in S3_3.
      now setoid_rewrite -> n13_16 in S3_3 at 1.
    }
    assert (C1 : (iota_f s Phi (λ x, Iota s x = B) ↔  Phi x <[- x -]> B = x)
      /\ (Phi x <[- x -]> B = x  ↔ iota_f s Phi (λ x, B = Iota s x))).
    { clear S3_1. now Conj S3_2 S3_3 C1. }
    clear S2 S3_2 S3_3.
    now Conj S3_1 C1 S3.
  }
  exact S3.
Qed.

Theorem n14_203 (Phi : Prop → Prop) : iota_E Phi 
  ↔ ((∃ x, Phi x) ∧ ((Phi x ∧ Phi y)) -[ x y ]> (x = y)).
Proof.
  (* TOOLS *)
  set (B := Individual "b").
  (* ******** *)
  assert (S1 : iota_E Phi -> ((exists x, Phi x) 
    /\ (Phi x /\ Phi y) -[ x y ]> (x = y))).
  {
    pose proof (n14_201 Phi) as n14_201.
    pose proof (n14_12 Phi) as n14_12.
    Conj n14_201 n14_12 C1.
    now rewrite -> n4_76 in C1.
  }
  assert (S2 : (Phi B /\ ((Phi x /\ Phi y) -[ x y ]> (x = y)))
    -> (Phi B /\ ((Phi x /\ Phi B) -[ x ]> (x = B)))).
  {
    pose proof (n10_1 (fun y => 
      (Phi x ∧ Phi y) -[ x ]> x = y) B) as n10_1.
    simpl in n10_1. (* This cannot be deleted *)
    setoid_rewrite -> n13_16 in n10_1 at 1.
    pose proof (Fact3_45
      ((Phi x0 ∧ Phi x) -[ x x0 ]> x = x0)
      ((Phi x ∧ Phi B) -[ x ]> x = B)
      (Phi B)) as Fact3_45.
    MP Fact3_45 n10_1.
    rewrite -> n4_3 in Fact3_45.
    setoid_rewrite -> n4_3 in Fact3_45 at 2.
    now setoid_rewrite -> n4_3 in Fact3_45 at 3.
  }
  assert (S3 : (Phi B /\ ((Phi x /\ Phi y) -[ x y ]> (x = y)))
    -> (Phi B /\ (Phi x -[ x ]> (x = B)))).
  {
    (* TODO: We can use an extra `X` to instantiate the 
      forall and obtain the result, but for now it is too tedious *)
    pose proof n5_33 as n5_33.
    admit.
  }
  assert (S4 : (Phi B /\ ((Phi x /\ Phi y) -[ x y ]> (x = y)))
    -> (((x = B) -[ x ]> Phi x) /\ (Phi x -[ x ]> (x = B)))).
  {
    pose proof (n13_191 B Phi) as n13_191.
    now rewrite <- n13_191 in S3 at 2.
  }
  assert (S5 : (Phi B /\ ((Phi x /\ Phi y) -[ x y ]> (x = y)))
    -> (Phi x <[- x -]> (x = B))).
  {
    (* Simplifications... *)
    intro Hp.
    pose proof (S4 Hp) as S4.
    rewrite <- n10_22 in S4.
    (* TODO: instantiate X and then generalize... or find another theorem
    to use *)
    admit.
  }
  assert (S6 : (exists b, Phi b /\ ((Phi x /\ Phi y) -[ x y ]> (x = y)))
    -> (exists b, Phi x <[- x -]> (x = b))).
  {
    (* *10.1 ignored - I think its the wrong one *)
    pose proof (n10_11 B (fun b => Phi b ∧ 
        ((Phi x ∧ Phi y) -[ x y ]> x = y)
      → (Phi x <[- x -]> x = b))) as n10_11.
    (* simpl in n10_1. *)
    MP n10_11 S5.
    pose proof (n10_28
      (fun b => Phi b ∧ ((Phi x ∧ Phi y) -[ x y ]> x = y))
      (fun b => (Phi x <[- x -]> x = b))) as n10_28.
    now MP n10_28 n10_11.
  }
  assert (S7 : (exists b, Phi b) /\ ((Phi x /\ Phi y) -[ x y ]> (x = y))
    -> (exists b, Phi x <[- x -]> (x = b))).
  {
    setoid_rewrite -> n4_3 in S6 at 1.
    rewrite -> n10_35 in S6.
    now setoid_rewrite -> n4_3 in S6 at 1.
  }
  assert (S8 : (exists b, Phi b) /\ ((Phi x /\ Phi y) -[ x y ]> (x = y))
    -> iota_E Phi).
  {
    now rewrite <- n14_11 in S7.
  }
  assert (S9 : iota_E Phi 
    ↔ ((∃ x, Phi x) ∧ ((Phi x ∧ Phi y)) -[ x y ]> (x = y))).
  {
    clear S2 S3 S4 S5 S6 S7.
    Conj S1 S8 S9.
    now Equiv S9.
  }
  exact S9.
Admitted.

Theorem n14_204 (B : Prop) (s : string) (Phi : Prop → Prop) : iota_E Phi 
  ↔ ∃ b, (iota_f s Phi (fun x => (Iota s x) = b)).
Proof.
  (* TOOLS *)
  (* ******** *)
  (* Notice that the following proposition involves 2 quantifiers already, 
    so it might have a higher type..? *)
  assert (S1 : forall b, (Phi x <[- x -]> (x = b))
    <-> iota_f s Phi (fun x => (Iota s x) = b)).
  {
    pose proof (n14_202 B s Phi) as n14_202.
    (* simplifictaions *)
    destruct n14_202 as [n14_202l _].
    pose proof (n10_11 B (fun b => (Phi x <[- x -]> x = b) <->
      iota_f s Phi (λ x, Iota s x = b))) as n10_11.
    now MP n10_11 n14_202l.
  }
  assert (S2 : (exists b, (Phi x <[- x -]> (x = b)))
    <-> (exists b, iota_f s Phi (λ x, Iota s x = b))).
  {
    pose proof (n10_281 (fun b => Phi x <[- x -]> x = b)
      (fun b => iota_f s Phi (λ x, Iota s x = b))) as n10_281.
    now MP n10_281 S1.
  }
  assert (S3 : iota_E Phi ↔ ∃ b, (iota_f s Phi (fun x => 
    (Iota s x) = b))).
  { now rewrite <- n14_11 in S2. }
  exact S3.
Qed.

Theorem n14_205 (s : string) (Phi Psi : Prop → Prop) : (iota_f s Phi Psi)
  ↔ ∃ b, (iota_f s Phi (fun x => b = (Iota s x))) ∧ Psi b.
Proof.
  set (B := Individual "b").
  pose proof n14_1 as _n14_1.
  pose proof (n14_202 B s Phi) as n14_202.
  destruct n14_202 as [_ n14_202r].
  destruct n14_202r as [_ n14_202rr].
  setoid_rewrite -> n13_16 in n14_202rr at 1.
  (* TODO: generalize n14_202rr with `exist` and finish the proof *)
Admitted.

Theorem n14_21 (s : string) (Phi Psi : Prop → Prop) : (iota_f s Phi Psi) → iota_E Phi.
Proof.
  assert (S1 : iota_f s Phi Psi -> exists b, 
    (Phi x <[- x -]> (x = b)) /\ Psi b).
  { apply n14_1. }
  assert (S2 : iota_f s Phi Psi -> exists b, 
    (Phi x <[- x -]> (x = b))).
  {
    (* simplifications *)
    intros Hp.
    pose proof (S1 Hp) as S1.
    pose proof (n10_5
      (fun b => Phi x <[- x -]> (x = b)) Psi) as n10_5.
    MP n10_5 S1.
    now destruct n10_5.
  }
  assert (S3 : iota_f s Phi Psi -> iota_E Phi).
  { now rewrite <- n14_11 in S2. }
  exact S3.
Qed.

Theorem n14_22 (s : string) (Phi : Prop → Prop) : iota_E Phi ↔ iota_f s Phi Phi.
Proof.
  (* TOOLS *)
  set (B := Individual "b").
  (* ******** *)
  assert (S1 : (Phi x <[- x -]> (x = B)) -> Phi B).
  { apply n14_122. }
  assert (S2 : (Phi x <[- x -]> (x = B)) 
    <-> ((Phi x <[- x -]> (x = B)) /\ Phi B)).
  { now rewrite -> n4_71 in S1. }
  assert (S3 : (exists b, (Phi x <[- x -]> (x = b))) 
    <-> (exists b, (Phi x <[- x -]> (x = b)) /\ Phi b)).
  { 
    pose proof (n10_11 B (fun b => Phi x <[- x -]> x = b
      ↔ (Phi x <[- x -]> x = b) ∧ Phi b)) as n10_11.
    MP n10_11 S2.
    pose proof (n10_281 (fun b => Phi x <[- x -]> x = b)
      (fun b => (Phi x <[- x -]> x = b) ∧ Phi b)) as n10_281.
    now MP n10_281 n10_11.
  }
  assert (S4 : iota_E Phi ↔ iota_f s Phi Phi).
  { now rewrite <- n14_11, <- (n14_101 s) in S3. }
  exact S4.
Qed.

(* This is a proposition where iotas are more than just a function. 
  Correspondingly we set up some ad hoc and very simple rules for its
  string representatives. *)
Theorem n14_23 (s1 s2 : string) (Phi Psi : Prop → Prop) : iota_E (fun x => Phi x ∧ Psi x) 
  ↔ iota_f (s1 ++ "/\" ++ s2) (fun x => Phi x ∧ Psi x) Phi.
Proof.
  (* TOOLS *)
  Open Scope string.
  set (s := s1 ++ "/\" ++ s2).
  Close Scope string.
  (* ******** *)
  assert (S1 : iota_E (fun x => Phi x ∧ Psi x)
    <-> iota_f s (fun x => Phi x /\ Psi x)
      (fun x => Phi (Iota s x) /\ Psi (Iota s x))).
  { apply n14_22. }
  assert (S2 : iota_E (fun x => Phi x ∧ Psi x) -> iota_f s 
    (fun x => Phi x /\ Psi x) Phi).
  {
    pose proof n10_5 as _n10_5.
    pose proof Simp3_26 as _Simp3_26.
    destruct S1 as [S1_l _].
    (* simplifications *)
    intro Hp.
    pose proof (S1_l Hp) as S1_l.
    rewrite -> n14_01 in S1_l.
    setoid_rewrite <- n4_32 in S1_l.
    pose proof (n10_5
      (fun b => ((Phi x ∧ Psi x) <[- x -]> x = b) 
        ∧ Phi (Iota s b))
      (fun b => Psi (Iota s b))) as n10_5a.
    MP n10_5a S1_l.
    (* Note that we have to use mere `x` manually here instead
    of `Iota s x` to perform rewrite for n14_01 *)
    pose proof (Simp3_26
      (∃ x, ((Phi x0 ∧ Psi x0) <[- x0 -]> x0 = x) ∧ Phi x)
        (* ∧ Phi (Iota s x)) *)
      (∃ x, Psi (Iota s x))) as Simp3_26.
    MP Simp3_26 n10_5a.
    now rewrite <- (n14_01 s (fun x => Phi x ∧ Psi x) Phi) in Simp3_26.
  }
  assert (S3 : iota_f s (fun x => Phi x /\ Psi x) Phi
    -> iota_E (fun x => Phi x /\ Psi x)).
  { apply n14_21. }
  assert (S4 : iota_E (fun x => Phi x ∧ Psi x) 
    ↔ iota_f (s1 ++ "/\" ++ s2) (fun x => Phi x ∧ Psi x) Phi).
  {
    clear S1. 
    now Syll S2 S3 S4.
  }
  exact S4.
Qed.

Theorem n14_24 (s : string) (Phi : Prop → Prop) : iota_E Phi 
  ↔ iota_f s Phi (fun x => Phi y <[- y -]> y = (Iota s x)).
Proof.
  assert (S1 : iota_f s Phi (fun x => Phi y <[- y -]> y = (Iota s x))
    <-> exists b, (Phi y <[- y -]> (y = b)) 
      /\ (Phi y <[- y -]> (y = b))).
  { apply n14_1. }
  assert (S2 : iota_f s Phi (fun x => Phi y <[- y -]> y = (Iota s x))
    <-> exists b, (Phi y <[- y -]> (y = b))).
  {
    (* n10_281 ignored *)
    now setoid_rewrite <- n4_24 in S1.
  }
  assert (S3 : iota_f s Phi (fun x => Phi y <[- y -]> y = (Iota s x))
    <-> iota_E Phi).
  { now rewrite <- n14_11 in S2. }
  assert (S4 : iota_E Phi 
    ↔ iota_f s Phi (fun x => Phi y <[- y -]> y = (Iota s x))).
  { now rewrite -> n4_21 in S3. }
  exact S4.
Qed.

Theorem n14_241 (s : string) (Phi : Prop → Prop) : iota_E Phi
  → (Phi y <[- y -]> iota_f s Phi (fun x => y = (Iota s x))).
Proof.
  (* TOOLS *)
  set (X := Individual "x").
  set (Y := Individual "y").
  set (λ P0 Q0 : Prop, eq_to_equiv (P0 ↔ Q0) ((P0 → Q0) ∧ (Q0 → P0)) 
    (Equiv4_01 P0 Q0))
  as Equiv4_01a.
  (* ******** *)
  assert (S1 : iota_E Phi -> ((Phi Y /\ Phi X) -> (Y = X))).
  {
    pose proof (n14_203 Phi) as n14_203.
    destruct n14_203 as [n14_203l _].
    (* simplifications... TODO: this can be removed easily in the future *)
    intro Hp.
    pose proof (n14_203l Hp) as n14_203l.
    pose proof (Simp3_27 (∃ x, Phi x) ((Phi x ∧ Phi y) -[ x y ]> x = y)) 
      as Simp3_27.
    MP Simp3_27 n14_203l.
    (* I doubt if this is allowed in the system... *)
    pose proof (n10_1 (fun x => (Phi x ∧ Phi y) -[ y ]> x = y) X) 
      as n10_1a.
    MP n10_1a Simp3_27.
    pose proof (n10_1 (fun y => (Phi X ∧ Phi y) -> X = y) Y)
      as n10_1b.
    MP n10_1b n10_1a.
    now rewrite -> n13_16, -> n4_3 in n10_1b.
  }
  assert (S2 : iota_E Phi -> (Phi Y -> (Phi X -> (Y = X)))).
  {
    intro Hp.
    pose proof (S1 Hp) as S1.
    pose proof (Exp3_3 (Phi Y) (Phi X) (Y = X)) as Exp3_3.
    now MP Exp3_3 S1.
  }
  assert (S3 : iota_E Phi -> (Phi Y -> (Phi x -[ x ]> (Y = x)))).
  {
    intro Hp.
    pose proof (S2 Hp) as S2.
    pose proof (n10_11 X (fun x => Phi Y -> (Phi x -> Y = x))) as n10_11.
    clear S1.
    MP n10_11 S2.
    now rewrite -> n10_21 in n10_11.
  }
  assert (S4 : iota_E Phi -> (Phi Y <-> Phi Y /\ (Phi x -[ x ]> (Y = x)))).
  { now setoid_rewrite -> n4_71 in S3 at 2. }
  assert (S5 : iota_E Phi -> (Phi Y <-> ((Y = x) -[ x ]> Phi x) 
    /\ (Phi x -[ x ]> (Y = x)))).
  {
    rewrite <- (n13_191 Y) in S4 at 2.
    now setoid_rewrite -> n13_16 in S4 at 1.
  }
  assert (S6 : iota_E Phi -> (Phi Y <-> (Phi x <[- x -]> (Y = x)))).
  {
    intro Hp.
    pose proof (S5 Hp) as S5.
    rewrite <- n10_22 in S5.
    setoid_rewrite <- Equiv4_01a in S5.
    now setoid_rewrite -> n4_21 in S5 at 2.
  }
  assert (S7 : iota_E Phi -> (Phi Y <-> iota_f s Phi 
    (fun x => Y = (Iota s x)))).
  {
    pose proof (n14_202 Y s Phi) as n14_202.
    destruct n14_202 as [_ n14_202r].
    destruct n14_202r as [_ n14_202rr].
    now rewrite -> n14_202rr in S6.
  }
  assert (S8 : iota_E Phi → (Phi y <[- y -]> iota_f s Phi 
    (fun x => y = (Iota s x)))).
  {
    intro Hp.
    pose proof (S7 Hp) as S7.
    pose proof (n10_11 Y (fun y => Phi y ↔ iota_f s Phi 
      (λ x, y = Iota s x))) as n10_11.
    clear S1 S2 S3 S4 S5 S6.
    now MP n10_11 S7.
  }
  exact S8.
Qed.

Theorem n14_242 (B : Prop) (s : string) (Phi Psi : Prop → Prop) : (Phi x <[- x -]> x = B)
  → (Psi B ↔ iota_f s Phi Psi).
Proof.
  pose proof (n14_202 B s Phi) as n14_202.
  destruct n14_202 as [n14_202l _].
  destruct n14_202l as [n14_202ll _].
  pose proof (n14_15 B s Phi Psi) as n14_15.
  Syll n14_202ll n14_15 S1.
  now rewrite -> n4_21 in S1.
Qed.

Theorem n14_25 (s : string) (Phi Psi : Prop → Prop) : iota_E Phi 
  → ((Phi x -[ x ]> Psi x) ↔ iota_f s Phi Psi).
Proof.
  (* TOOLS *)
  set (B := Individual "b").
  set (X := Individual "x").
  (* ******** *)
  assert (S1 : (Phi x <[- x -]> (x = B)) -> ((Phi x -[ x ]> Psi x)
    <-> ((x = B) -[ x ]> Psi x))).
  {
    pose proof (n4_84 (Phi X) (X = B) (Psi X)) as n4_84.
    pose proof (n10_11 X (fun x =>
      (Phi x ↔ x = B) -> ((Phi x → Psi x) <-> (x = B → Psi x))))
      as n10_11.
    MP n10_11 n4_84.
    pose proof (n10_27 (fun x => Phi x ↔ x = B)
      (fun x => (Phi x → Psi x) ↔ (x = B → Psi x))) as n10_27.
    MP n10_27 n10_11.
    pose proof (n10_271 (fun z => Phi z → Psi z)
      (fun z => z = B → Psi z)) as n10_271.
    now Syll n10_27 n10_271 S1.
  }
  assert (S2 : (Phi x <[- x -]> (x = B)) -> ((Phi x -[ x ]> Psi x)
    <-> Psi B)).
  { now rewrite -> n13_191 in S1. }
  assert (S3 : (Phi x <[- x -]> (x = B)) -> ((Phi x -[ x ]> Psi x)
    <-> iota_f s Phi Psi)).
  {
    (* simplifications *)
    intro Hp.
    pose proof (S2 Hp) as S2.
    pose proof (n14_242 B s Phi Psi) as n14_242.
    MP n14_242 Hp.
    now rewrite -> n14_242 in S2.
  }
  assert (S4 : (exists b, Phi x <[- x -]> (x = b)) 
    -> ((Phi x -[ x ]> Psi x) <-> iota_f s Phi Psi)).
  {
    pose proof (n10_11 B (fun b => (Phi x <[- x -]> (x = b)) 
      -> ((Phi x -[ x ]> Psi x) <-> iota_f s Phi Psi))) as n10_11.
    MP n10_11 S3.
    now rewrite -> n10_23 in n10_11.
  }
  assert (S5 : iota_E Phi → ((Phi x -[ x ]> Psi x) 
    ↔ iota_f s Phi Psi)).
  { now rewrite <- n14_11 in S4. }
  exact S5.
Qed.

Theorem n14_26 (s : string) (Phi Psi : Prop → Prop) : iota_E Phi 
  → ((∃ x, Phi x ∧ Psi x) ↔ iota_f s Phi Psi)
    ∧ ((iota_f s Phi Psi) ↔ (Phi x -[ x ]> Psi x)).
Proof.
  (* TOOLS *)
  set (B := Individual "b").
  (* ******** *)
  assert (S1 : iota_E Phi -> exists b, Phi x <[- x -]> (x = b)).
  { apply n14_11. }
  assert (S2 : (Phi x <[- x -]> (x = B))
    -> ((Phi x /\ Psi x) <[- x -]> ((x = B) /\ Psi x))).
  { apply n10_311. }
  assert (S3 : (Phi x <[- x -]> (x = B))
    -> ((exists x, Phi x /\ Psi x) <-> (exists x, (x = B) /\ Psi x))).
  {
    pose proof (n10_281 (fun x => Phi x /\ Psi x)
      (fun x => (x = B) /\ Psi x)) as n10_281.
    now Syll S2 n10_281 S3.
  }
  assert (S4 : (Phi x <[- x -]> (x = B))
    -> ((exists x, Phi x /\ Psi x) <-> Psi B)).
  { now rewrite -> n13_195 in S3. }
  assert (S5 : (Phi x <[- x -]> (x = B))
    -> ((exists x, Phi x /\ Psi x) <-> iota_f s Phi Psi)).
  { 
    (* simplifications *)
    intro Hp.
    pose proof (S4 Hp) as S4.
    pose proof (n14_242 B s Phi Psi) as n14_242.
    MP n14_242 Hp.
    now rewrite -> n14_242 in S4.
  }
  assert (S6 : (exists b, Phi x <[- x -]> (x = b))
    -> ((exists x, Phi x /\ Psi x) <-> iota_f s Phi Psi)).
  {
    pose proof (n10_11 B (fun b => (Phi x <[- x -]> (x = b))
      -> ((exists x, Phi x /\ Psi x) <-> iota_f s Phi Psi))) 
      as n10_11.
    MP n10_11 S5.
    now rewrite -> n10_23 in n10_11.
  }
  assert (S7 : iota_E Phi 
    → ((∃ x, Phi x ∧ Psi x) ↔ iota_f s Phi Psi)
      ∧ ((iota_f s Phi Psi) ↔ (Phi x -[ x ]> Psi x))).
  {
    (* simplifications *)
    intro Hp.
    clear S2 S3 S4 S5.
    pose proof (S1 Hp) as S1.
    MP S6 S1.
    pose proof (n14_25 s Phi Psi) as n14_25.
    MP n14_25 Hp.
    rewrite -> n4_21 in n14_25.
    now Conj S1 n14_25 S7.
  }
  exact S7.
Qed.

(* TODO: rewrite the iota_f2 as double iota_f *)
Theorem n14_27 (s1 s2 : string) (Phi Psi : Prop → Prop) : iota_E Phi 
  → ((Phi x <[- x -]> Psi x) 
    ↔ iota_f2 s1 s2 Phi Psi (fun x y =>
      (Iota s1 x) = (Iota s2 y))).
Proof.
  (* TOOLS *)
  set (B := Individual "b").
  set (X := Individual "x").
  (* ******** *)
  assert (S1 : (Phi X <-> (X = B)) 
    -> ((Phi X <-> Psi X) <-> (Psi X <-> (X = B)))).
  { 
    pose proof n4_86 as _n4_86.
    pose proof (n4_86 (Phi X) (X = B) (Psi X)) as n4_86.
     (*simplification  *)
    intro Hp.
    MP n4_86 Hp.
    now setoid_rewrite -> n4_21 in n4_86 at 3.
  }
  assert (S2 : (Phi x <[- x -]> (x = B)) 
    -> (forall x, (Phi x <-> Psi x) <-> (Psi x <-> (x = B)))).
  {
    pose proof (n10_11 X (fun x =>
      (Phi x <-> (x = B)) -> ((Phi x <-> Psi x) 
        <-> (Psi x <-> (x = B))))) as n10_11.
    MP n10_11 S1.
    pose proof (n10_27 (fun x => Phi x <-> (x = B))
      (fun x => (Phi x <-> Psi x) <-> (Psi x <-> (x = B)))) as n10_27.
    now MP n10_27 n10_11.
  }
  assert (S3 : (Phi x <[- x -]> (x = B))
    -> ((Phi x <[- x -]> Psi x) <-> (Psi x <[- x -]> (x = B)))).
  {
    pose proof (n10_271 (fun x => Phi x <-> Psi x)
      (fun x => Psi x <-> (x = B))) as n10_271.
    now Syll S2 n10_271 S3.
  }
  assert (S4 : (Phi x <[- x -]> (x = B))
    -> ((Phi x <[- x -]> Psi x) <-> iota_f s2 Psi (fun x =>
      (B = (Iota s2 x))))).
  {
    pose proof (n14_202 B s2 Psi) as n14_202.
    destruct n14_202 as [_ n14_202r].
    destruct n14_202r as [_ n14_202rr].
    setoid_rewrite -> n13_16 in S3 at 2.
    now rewrite -> n14_202rr in S3.
  }
  assert (S5 : (Phi x <[- x -]> (x = B))
    -> ((Phi x <[- x -]> Psi x) <-> iota_f s2 Psi (fun x =>
      iota_f2 s1 s2 Phi Psi (fun x y =>
        (Iota s1 x) = (Iota s2 y))))).
  {
    (* TODO: currently stuck: the proof interprets the 
      equation as double iota_f *)
    pose proof n14_242 as n14_242.
    admit.
  }
  admit.
Admitted.

Theorem n14_271 (Phi Psi : Prop → Prop) : (Phi x <[- x -]> Psi x)
  → ((iota_E Phi) ↔ (iota_E Psi)).
Proof.
Admitted.

(* TODO: similarly, check the iota_f2 as double iota_f *)
Theorem n14_272 (Phi Psi Chi : Prop → Prop) : (Phi x <[- x -]> Psi x)
  → (iota_f2 "Phi" "Psi" Phi Psi (fun x y =>
    Chi (Iota "Phi" x) ↔ Chi (Iota "Psi" y))).
Proof.
Admitted.

(* TODO: similarly, check the iota_f2 as double iota_f *)
Theorem n14_28 (Phi : Prop → Prop) : iota_E Phi
  ↔ (iota_f2 "Phi" "Phi" Phi Phi (fun x y =>
    (Iota "Phi" x) = (Iota "Phi" y))).
Proof.
Admitted.

Theorem n14_3 (Phi Chi f : Prop → Prop) : 
  (((p ↔ q) -[ p q ]> (f p ↔ f q)) ∧ iota_E Phi)
  →
  ((f (iota_f "Phi" Phi Chi)) ↔ iota_f "Phi" Phi (fun x =>
    f (Chi (Iota "Phi" x)))).
Proof.
Admitted.

Theorem n14_31 (P : Prop) (Phi Chi : Prop → Prop) : iota_E Phi
  → ((iota_f "Phi" Phi (fun x => P ∨ Chi (Iota "Phi" x)))
    ↔ P ∨ (iota_f "Phi" Phi Chi)).
Proof.
Admitted.

Theorem n14_32 (Phi Chi : Prop → Prop) : iota_E Phi
  ↔ ((iota_f "Phi" Phi (fun x => ~ Chi (Iota "Phi" x)))
    ↔ ~ (iota_f "Phi" Phi Chi)).
Proof.
Admitted.

Theorem n14_33 (P : Prop) (Phi Chi : Prop → Prop) : iota_E Phi
  → ((iota_f "Phi" Phi (fun x => P → Chi (Iota "Phi" x)))
    ↔ (P → iota_f "Phi" Phi Chi)).
Proof.
Admitted.

(* Is there a typo in this proposition? An identitical conclusion? *)
Theorem n14_331 (P : Prop) (Phi Chi : Prop → Prop) : iota_E Phi
  → ((iota_f "Phi" Phi (fun x => Chi (Iota "Phi" x) → P))
    ↔ (iota_f "Phi" Phi (fun x => Chi (Iota "Phi" x) → P))).
Proof.
Admitted.

Theorem n14_332 (P : Prop) (Phi Chi : Prop → Prop) : iota_E Phi
  → ((iota_f "Phi" Phi (fun x => P ↔ Chi (Iota "Phi" x)))
    ↔ (P ↔ (iota_f "Phi" Phi Chi))).
Proof.
Admitted.

Theorem n14_34 (P : Prop) (Phi Chi : Prop → Prop) : 
  (P ∧ iota_f "Phi" Phi Chi) ↔ iota_f "Phi" Phi (fun x =>
    P ∧ Chi (Iota "Phi" x)).
Proof.
Admitted.

Close Scope single_app_equiv.
Close Scope single_app_impl.
Close Scope double_app_equiv.
Close Scope double_app_impl.