Require Import PM.pm.lib.
Require Import PM.pm.ch1.
Require Import PM.pm.ch2.
Require Import PM.pm.ch3.
Require Import PM.pm.ch4.
Require Import PM.pm.ch5.
Require Import PM.pm.ch9.
Require Import PM.pm.ch10.

(* TODO: 
- Add a special rule: (∃ x, P x ∧ Q x) -> (∃ x, P x) ∧ (∃ x, Q x) or recheck 
  if this is related to scopes
*)

(* **************** *)
(* NOTATION DEFINITIONS *)
(* **************** *)
(* Ref: https://rocq-prover.org/doc/v9.0/stdlib/Stdlib.Unicode.Utf8_core.html# *)
Declare Scope formal_impl.
Declare Scope formal_equiv.

Open Scope formal_impl.
Open Scope formal_equiv.

Example example_formal_impl_testtest := ∀ x y z : Prop, (x = y ∧ y = z) -> (x = z).

Notation "A '-[' x .. y ']>' B" := (∀ x, .. (∀ y, A -> B) ..)
  (at level 80, x binder, y binder, B at level 100, right associativity,
  format "'[ ' A '/' '[ ' -[ x .. y ]> ']' '/' B ']'") : formal_impl.
Example example_formal_impl0 := (x = y) -[ (x y : Prop) ]> (x = y).

Notation "A '<[-' x .. y '-]>' B" := (∀ x, .. (∀ y, A ↔ B) ..)
  (at level 80, x binder, y binder, B at level 100, right associativity,
  format "'[ ' A '/' '[ ' <[- x .. y -]> ']' '/' B ']'") : formal_equiv.
Example example_formal_equiv0 := (x = y) <[- (x y : Prop) -]> (y = x).

(* ******** *)
Definition n11_01 (φ : Prop → Prop → Prop) : 
  (∀ x y, (φ x y)) = (∀ x, ∀ y, φ x y).
Admitted.

Definition n11_02 (φ : Prop → Prop → Prop → Prop) :
  (∀ x y z, φ x y z) 
  = (∀ x, ∀ y, ∀ z, φ x y z).
Admitted.

Definition n11_03 (φ : Prop → Prop → Prop) :
  (∃ x y, φ x y) = (∃ x, ∃ y, φ x y).
Admitted.

Definition n11_04 (φ : Prop → Prop → Prop → Prop) :
  (∃ x y z, φ x y z) = (∃ x, ∃ y, ∃ z, φ x y z).
Admitted.

Definition n11_05 (φ ψ : Prop → Prop → Prop) :
  (φ x y -[ x y ]> ψ x y) = (∀ x y, φ x y → ψ x y).
Admitted.

Definition n11_06 (φ ψ : Prop → Prop → Prop) :
  (φ x y <[- x y -]> ψ x y) = (∀ x y, (φ x y ↔ ψ x y)).
Admitted.

(* Pp *11.07: "Whatever possible argument `x` may be, `φ(x, y)` is true 
whatever possible argument `y` may be" implies that the corresponding 
statement with `x` and `y` interchanged except in "φ(x, y)". *)
Definition n11_07 (φ : Prop → Prop → Prop) :
  (∀ x y, φ x y) → (∀ y x, φ x y).
Admitted.

Theorem n11_1 (Z W : Prop) (φ : Prop → Prop → Prop) : 
  (∀ x y, φ x y) → φ Z W.
Proof.
  assert (S1 : (∀ x y, φ x y) → ∀ y, (φ Z y)).
  { exact (n10_1 (fun x => ∀ y, φ x y) Z). }
  assert (S2 : (∀ x y, φ x y) → φ Z W).
  { 
    pose proof (n10_1 (fun y => φ Z y) W) as n10_1.
    now Syll_as S1 n10_1 S2.
  }
  exact S2.
Qed.

(* Thm *11.11 : If `φ(z, w)` is true whatever possible arguments `z` and `w` 
  may be, then `∀ x y, φ x y` is true. *)
Theorem n11_11 (Z W : Prop) (φ : Prop → Prop → Prop) : 
  (φ Z W) → (∀ x y, φ x y).
Admitted.

Theorem n11_12 (P : Prop) (φ : Prop → Prop → Prop) : 
  (∀ x y, P ∨ φ x y) → (P ∨ ∀ x y, φ x y).
Proof.
  (* TOOLS *)
  set (X := Intro_individual "x").
  (* ******** *)
  assert (S1 : (∀ y, P ∨ φ X y) → (P ∨ ∀ y, φ X y)).
  { apply n10_12. }
  assert (S2 : (∀ x y, P ∨ φ x y) → (∀ x, P ∨ (∀ y, φ x y))).
  {
    pose proof (n10_11 X (fun x =>
      (∀ y, P ∨ φ x y) → (P ∨ ∀ y, φ x y))) as n10_11.
    MP n10_11 S1.
    pose proof (n10_27 (fun x => (∀ y, P ∨ φ x y))
      (fun x => (P ∨ ∀ y, φ x y))) as n10_27.
    now MP n10_27 n10_11.
  }
  assert (S3 : (∀ x y, P ∨ φ x y) → (P ∨ ∀ x y, φ x y)).
  {
    pose proof (n10_12 (fun x => ∀ y, φ x y) P) as n10_12.
    now Syll_as S2 n10_12 S3.
  }
  exact S3.
Qed.

(* Similar to *10.13 *)
(* Thm *11.13 : If `φ x^ y^`, `ψ x^ y^  take their first and second arguments respectively of the same type, and we have `|-φ(x, y)` and `|-ψ(x, y)`, we shall have `|-φ(x, y) ∧ ψ(x, y)`. *)

(* An alternative version of *11.13, but can only be used during formal 
  inference. Similar to *10.14 *)
Theorem n11_14 (Z W : Prop) (φ ψ : Prop → Prop → Prop) : 
  ((∀ x y, φ x y) ∧ (∀ x y, ψ x y))
  → (φ Z W ∧ ψ Z W).
Proof.
  assert (S1 : ((∀ x y, φ x y) ∧ (∀ x y, ψ x y)) 
    → ((∀ y, φ Z y) ∧ (∀ y, ψ Z y))).
  {
    exact (n10_14 (fun x => ∀ y, φ x y) 
      (fun x => ∀ y, ψ x y) Z).
  }
  assert (S2 : ((∀ x y, φ x y) ∧ (∀ x y, ψ x y)) → (φ Z W ∧ ψ Z W)).
  {
    pose proof (n10_14 (fun y => φ Z y) (fun y => ψ Z y) W) as n10_14.
    now Syll_as S1 n10_14 S2.
  }
  exact S2.
Qed.

Theorem n11_2 (φ : Prop → Prop → Prop) : 
  (∀ x y, φ x y) ↔ (∀ y x, φ x y).
Proof.
  (* TOOLS *)
  set (X := Intro_individual "x").
  set (Y := Intro_individual "y").
  set (W := Intro_individual "w").
  set (Z := Intro_individual "z").
  set (λ P0 Q0 : Prop, eq_to_equiv (P0 → Q0) (¬ P0 ∨ Q0) (Impl1_01 P0 Q0))
    as Impl1_01a.
  (* ******** *)
  assert (S1 : (∀ x y, φ x y) → (φ Z W)).
  { apply n11_1. }
  assert (S2 : ∀ w z, (∀ x y, φ x y) → φ z w).
  {
    pose proof (n11_11 Z W (fun z w => (∀ x y, φ x y) → φ z w))
      as n11_11.
    MP n11_11 S1.
    pose proof (n11_07 (fun z w => (∀ x y, φ x y) → φ z w)) as n11_07.
    now MP n11_07 n11_11.
  }
  assert (S3 : (∀ x y, φ x y) → (∀ w z, φ z w)).
  {
    pose proof (n11_12 (¬ ∀ x y, φ x y) (fun z w => φ w z)) as n11_12.
    setoid_rewrite <- Impl1_01a in n11_12.
    now MP n11_12 S2.
  }
  assert (S4 : (∀ w z, φ z w) → (∀ x y, φ x y)).
  {
    pose proof (n11_1 Y X (fun w z => φ z w)) as n11_1.
    pose proof (n11_11 X Y (fun x y => (∀ w z, φ z w) → φ x y)) 
      as n11_11.
    MP n11_11 n11_1.
    pose proof (n11_12 (¬ ∀ w z, φ z w) φ) as n11_12.
    setoid_rewrite <- Impl1_01a in n11_12.
    now MP n11_12 n11_11.
  }
  assert (S5 : (∀ x y, φ x y) ↔ (∀ y x, φ x y)).
  { Conj_as S3 S4 C1. now Equiv C1. }
  exact S5.
Qed.  

Theorem n11_21 (φ : Prop → Prop → Prop → Prop) :
  (∀ x y z, φ x y z) ↔ (∀ y z x, φ x y z).
Proof.
  (* TOOLS *)
  set (Y := Intro_individual "y").
  (* ******** *)
  (* We can see that Rocq really doesn't make a distinction here... *)
  assert (S1 : (∀ x y z, φ x y z) ↔
    (∀ x, ∀ y, ∀ z, φ x y z)).
  {
    (* n11_01 ignored *)
    (* TODO: check if this proof can be normalized? *)
    (* NOTE: It seems that here we're getting a `↔` relation directly 
    from a `=` definition, from original text.
    I'm assumning that the original routine is set up 
    (φ X Y Z → φ X Y Z), instantiate by repeatly applying n11_1,
    and finally arrive at conclusion. Here, we omit the routine
    *)
    pose proof (n11_02 φ) as n11_02.
    reflexivity.
  }
  assert (S2 : (∀ x y z, φ x y z) ↔
    (∀ y, ∀ x, ∀ z, φ x y z)).
  {
    pose proof (n11_2 (fun x y => ∀ z, φ x y z)) as n11_2.
    (* NOTE: Since Rocq doesn't make a difference, we omit all the
      `Syll`s... *)
    now rewrite -> n11_2 in S1 at 2.
  }
  assert (S3 : (∀ x y z, φ x y z) ↔
    (∀ y, ∀ z, ∀ x, φ x y z)).
  {
    pose proof (n11_2 (fun x z => φ x Y z)) as n11_2.
    pose proof (n10_11 Y (fun y => (∀ x z, φ x y z) ↔ ∀ z x, φ x y z)) 
      as n10_11.
    MP n10_11 n11_2.
    pose proof (n10_271 (fun y => ∀ x z, φ x y z)
      (fun y => (∀ z x, φ x y z))) as n10_271.
    now MP n10_271 n10_11.
  }
  assert (S4 : (∀ x y z, φ x y z) ↔ (∀ y z x, φ x y z)).
  {
    (* Since it only involves n11_01 and n11_02, we skip the routine *)
    exact S3.
  }
  exact S4.
Qed.

Theorem n11_22 (φ : Prop → Prop → Prop) :
  (∃ x y, φ x y) ↔ (¬ (∀ x y, ¬ φ x y)).
Proof.
  assert (S1 : (∃ x y, φ x y) ↔ (¬ ∀ x, ¬ ∃ y, φ x y)).
  {
    (* The `∃` are currently separated, i.e. in the form of 
      `∃ x, ∃ y` *)
    pose proof (n10_252 (fun x => ∃ y, φ x y)) as n10_252.
    (* TODO: check if it is elligible to use theorems in chapter 4 *)
    rewrite -> Transp4_11 in n10_252.
    rewrite <- n4_13 in n10_252.
    (* Now we use n11_03 to merge the ∃. Since it's pretty tedious, I
    want to ignore this in the future. We can see that Rocq doesn't even 
    allow such rewrite to perform. *)
    (* rewrite <- (n11_03 φ) in n10_252. *)
    exact n10_252.
  }
  assert (S2 : (∃ x y, φ x y) ↔ (¬ ∀ x, ∀ y, ¬ φ x y)).
  {
    (* n10_271 ignored as in ch10 *)
    now setoid_rewrite -> n10_252 in S1.
  }
  assert (S3 : (∃ x y, φ x y) ↔ (¬ (∀ x y, ¬ φ x y))).
  {
    (* n11_01 ignored for merging `∀`s *)
    exact S2.
  }
  exact S3.
Qed.

Theorem n11_23 (φ : Prop → Prop → Prop) :
  (∃ x y, φ x y) ↔ (∃ y x, φ x y).
Proof.
  assert (S1 : (∃ x y, φ x y) ↔ ¬ (∀ x y, ¬ φ x y)).
  { apply n11_22. }
  assert (S2 : (∃ x y, φ x y) ↔ ¬ (∀ y x, ¬ φ x y)).
  {
    pose proof (n11_2 (fun x y => ¬ φ x y)) as n11_2.
    (* TODO: investigate if this proposition is correctly used *)
    rewrite -> Transp4_11 in n11_2.
    now rewrite -> n11_2 in S1.
  }
  assert (S3 : (∃ x y, φ x y) ↔ (∃ y x, φ x y)).
  { now rewrite <- n11_22 in S2. }
  exact S3.
Qed.

Theorem n11_24 (φ : Prop → Prop → Prop → Prop) :
  (∃ x y z, φ x y z) ↔ (∃ y z x, φ x y z).
Proof.
  (* TOOLS *)
  set (Y := Intro_individual "y").
  (* ******** *)
  assert (S1 : (∃ x y z, φ x y z) ↔ (∃ x, ∃ y, ∃ z, φ x y z)).
  {
    (* *11.03, *11.04 ignored *)
    reflexivity.
  }
  assert (S2 : (∃ x y z, φ x y z) ↔ (∃ y, ∃ x, ∃ z, φ x y z)).
  { now rewrite -> n11_23 in S1 at 2. }
  assert (S3 : (∃ x y z, φ x y z) ↔ (∃ y, ∃ z, ∃ x, φ x y z)).
  {
    pose proof (n11_23 (fun x z => φ x Y z)) as n11_23.
    pose proof (n10_11 Y (fun y =>
      (∃ x z, φ x y z) ↔ (∃ z x, φ x y z))) as n10_11.
    MP n10_11 n11_23.
    pose proof (n10_281 (fun y => ∃ x z, φ x y z) (fun y => (∃ z x, φ x y z))) as n10_281.
    MP n10_281 n10_11.
    now rewrite -> n10_281 in S2.
  }
  assert (S4 : (∃ x y z, φ x y z) ↔ (∃ y z x, φ x y z)).
  {
    (* *11.03, *11.04 ignored *)
    exact S3.
  }
  exact S4.
Qed.

Theorem n11_25 (φ : Prop → Prop → Prop) :
  (¬ ∃ x y, φ x y) ↔ ∀ x y, ¬ φ x y.
Proof.
  pose proof (n11_22 φ) as n11_22.
  rewrite -> Transp4_11 in n11_22.
  now rewrite <- n4_13 in n11_22.
Qed.

Theorem n11_26 (φ : Prop → Prop → Prop) :
  (∃ x, ∀ y, φ x y) → (∀ y, ∃ x, φ x y).
Proof.
  (* TOOLS *)
  set (X := Intro_individual "x").
  set (Y := Intro_individual "y").
  (* ******** *)
  assert (S1 : (∃ x, ∀ y, φ x y) → (∃ x, φ x Y)).
  {
    pose proof (n10_1 (fun y => φ X y) Y) as n10_1.
    pose proof (n10_11 X (fun x => (∀ y, φ x y) → φ x Y))
      as n10_11.
    MP n10_11 n10_1.
    pose proof (n10_28 (fun x => ∀ y, φ x y)
      (fun x => φ x Y)) as n10_28.
    now MP n10_28 n10_11.
  }
  assert (S2 : (∃ x, ∀ y, φ x y) → (∀ y, ∃ x, φ x y)).
  {
    pose proof (n10_11 Y (fun y0 =>
        (∃ x, ∀ y, φ x y) → ∃ x, φ x y0)) as n10_11.
    MP n10_11 S1.
    pose proof n10_21 as n10_21.
    pose proof (n10_21 (fun y => ∃ x, φ x y)
      (∃ x, ∀ y, φ x y)) as n10_21.
    now rewrite -> n10_21 in n10_11.
  }
  exact S2.
Qed.

(* Here the format is slightly different from original text. Also, since 
we cannot split the quantifiers in Rocq, here we only try to simulate the 
proof procedure. *)
Theorem n11_27 (φ : Prop → Prop → Prop → Prop) :
  ((∃ x y, ∃ z, φ x y z) ↔ (∃ x, ∃ y z, φ x y z))
  ∧
  ((∃ x, ∃ y z, φ x y z) ↔ (∃ x y z, φ x y z)).
Proof.
  (* TOOLS *)
  set (X := Intro_individual "x").
  (* ******** *)
  assert (S1 : (∃ x y, ∃ z, φ x y z) 
    ↔ (∃ x, ∃ y, ∃ z, φ x y z)).
  {
    (* *11.03 ignored *)
    apply n4_2.
  }
  assert (S2 : (∃ y, ∃ z, φ X y z) ↔ (∃ y z, φ X y z)).
  {
    (* *11.03 ignored *)
    apply n4_2.
  }
  assert (S3 : (∃ x, ∃ y, ∃ z, φ x y z) 
    ↔ (∃ x, ∃ y z, φ x y z)).
  {
    pose proof (n10_11 X (fun x =>
      (∃ y, ∃ z, φ x y z) ↔ (∃ y z, φ x y z))) as n10_11.
    MP n10_11 S2.
    pose proof (n10_281
      (fun x => ∃ y, ∃ z, φ x y z)
      (fun x => ∃ y z, φ x y z)) as n10_281.
    now MP n10_281 n10_11.
  }
  assert (S4 : ((∃ x y, ∃ z, φ x y z) ↔ (∃ x, ∃ y z, φ x y z))
    ∧
    ((∃ x, ∃ y z, φ x y z) ↔ (∃ x y z, φ x y z))).
  {
    (* *11.04 ignored. It should be applied on the `∃ x, ∃ y, ∃ z`
    side of S1 and S3. *)
    now Conj_as S1 S3 S4.
  }
  exact S4.
Qed.

Theorem n11_3 (P : Prop) (φ : Prop → Prop → Prop) :
  (P → (∀ x y, φ x y)) ↔ (∀ x y, P → φ x y).
Proof.
  assert (S1 : (P → ∀ x y, φ x y) 
    ↔ (∀ x, P → ∀ y, φ x y)).
  {
    pose proof (n10_21 (fun x => ∀ y, φ x y) P) as n10_21.
    now rewrite -> n4_21 in n10_21. 
  }
  assert (S2 : (P → (∀ x y, φ x y)) ↔ (∀ x y, P → φ x y)).
  {
    (* *10.271 ignored *)
    now setoid_rewrite <- n10_21 in S1 at 2.
  }
  exact S2.
Qed.

Theorem n11_31 (φ ψ : Prop → Prop → Prop) :
  ((∀ x y, φ x y) ∧ (∀ x y, ψ x y))
  ↔ (∀ x y, φ x y ∧ ψ x y).
Proof.
  assert (S1 : ((∀ x y, φ x y) ∧ (∀ x y, ψ x y))
    ↔ (∀ x, (∀ y, φ x y) ∧ (∀ y, ψ x y))).
  {
    pose proof (n10_22 (fun x => ∀ y, φ x y)
      (fun x => ∀ y, ψ x y)) as n10_22.
    now rewrite -> n4_21 in n10_22.
  }
  assert (S2 : ((∀ x y, φ x y) ∧ (∀ x y, ψ x y))
    ↔
    (∀ x y, φ x y ∧ ψ x y)).
  {
    (* *10.271 ignored *)
    now setoid_rewrite <- n10_22 in S1 at 2.
  }
  exact S2.
Qed.

(* Thm *11.311: If `φ(x^, y^)`, `ψ(x^, y^)` take arguments of the same type, and we have `|- φ(x, y)` and `|- ψ(x, y)`, we shall have `|- φ(x, y) ∧ ψ(x, y)`. *)

Theorem n11_32 (φ ψ : Prop → Prop → Prop) :
  (∀ x y, φ x y → ψ x y) 
  → ((∀ x y, φ x y) → ∀ x y, ψ x y).
Proof.
  set (X := Intro_individual "x").
  pose proof (n10_27 (fun y => φ X y) (fun y => ψ X y)) 
    as n10_27a.
  pose proof (n10_27 (fun x => (∀ y, φ x y → ψ x y))
    (fun x => (∀ y, φ x y) → ∀ y, ψ x y)) as n10_27b.
  pose proof (n10_27 (fun x => ∀ y, φ x y)
    (fun x => ∀ y, ψ x y)) as n10_27c.
  pose proof (n10_11 X (fun x =>
    (∀ y, φ x y → ψ x y)
      → (∀ y, φ x y) → ∀ y, ψ x y)) as n10_11.
  MP n10_11 n10_27a.
  MP n10_27b n10_11.
  now Syll_as n10_27b n10_27c Sy1.
Qed.

Theorem n11_33 (φ ψ : Prop → Prop → Prop) :
  (∀ x y, φ x y ↔ ψ x y) 
  → ((∀ x y, φ x y) ↔ (∀ x y, ψ x y)).
Proof.
  set (X := Intro_individual "x").
  pose proof (n10_271 (fun y => φ X y) (fun y => ψ X y)) 
    as n10_271a.
  pose proof (n10_271 (fun x => ∀ y, φ x y)
    (fun x => ∀ y, ψ x y)) as n10_271b.
  pose proof (n10_11 X (fun x =>
    (∀ y, φ x y ↔ ψ x y)
      → ((∀ y, φ x y) ↔ ∀ y, ψ x y))) as n10_11.
  MP n10_11 n10_271a.
  pose proof (n10_27 (fun x => (∀ y, φ x y ↔ ψ x y))
    (fun x => (∀ y, φ x y) ↔ ∀ y, ψ x y)) as n10_27.
  MP n10_27 n10_11.
  now Syll_as n10_27 n10_271b S1.
Qed.

Theorem n11_34 (φ ψ : Prop → Prop → Prop) :
  (∀ x y, φ x y → ψ x y) 
  → ((∃ x y, φ x y) → (∃ x y, ψ x y)).
Proof.
  set (X := Intro_individual "x").
  pose proof (n10_28 (fun y => φ X y) (fun y => ψ X y)) 
    as n10_28a.
  pose proof (n10_11 X (fun x => 
    ((∀ y, φ x y → ψ x y)
    → (∃ y, φ x y) → ∃ y, ψ x y))) as n10_11.
  MP n10_11 n10_28a.
  pose proof (n10_27 (fun x => (∀ y, φ x y → ψ x y))
    (fun x => (∃ y, φ x y) → ∃ y, ψ x y)) as n10_27.
  MP n10_27 n10_11.
  pose proof (n10_28 (fun x => ∃ y, φ x y)
    (fun x => ∃ y, ψ x y)) as n10_28b.
  now Syll_as n10_27 n10_28b S1.
Qed.

Theorem n11_341 (φ ψ : Prop → Prop → Prop) :
  (∀ x y, φ x y ↔ ψ x y) 
  → ((∃ x y, φ x y) ↔ (∃ x y, ψ x y)).
Proof.
  set (X := Intro_individual "x").
  pose proof (n10_281 (fun y => φ X y) (fun y => ψ X y))
    as n10_281a.
  pose proof (n10_11 X (fun x =>
    (∀ y, φ x y ↔ ψ x y)
      → (∃ y, φ x y) ↔ ∃ y, ψ x y)) as n10_11.
  MP n10_11 n10_281a.
  pose proof (n10_27 (fun x => (∀ y, φ x y ↔ ψ x y))
    (fun x => (∃ y, φ x y) ↔ ∃ y, ψ x y)) as n10_271.
  MP n10_271 n10_11.
  pose proof (n10_281 (fun x => (∃ y, φ x y))
    (fun x => ∃ y, ψ x y)) as n10_281b.
  now Syll_as n10_271 n10_281b S1.
Qed.

Theorem n11_35 (P : Prop) (φ : Prop → Prop → Prop) :
  (∀ x y, φ x y → P) ↔ ((∃ x y, φ x y) → P).
Proof.
  set (X := Intro_individual "x").
  pose proof (n10_23 (fun y => φ X y) P) as n10_23a.
  pose proof (n10_11 X (fun x => (∀ y, φ x y → P)
    ↔ ((∃ y, φ x y) → P))) as n10_11.
  MP n10_11 n10_23a.
  pose proof (n10_271 (fun x => (∀ y, φ x y → P))
    (fun x => ((∃ y, φ x y) → P))) as n10_271.
  MP n10_271 n10_11.
  pose proof (n10_23 (fun x => (∃ y, φ x y)) P)
    as n10_23b.
  now rewrite -> n10_23b in n10_271.
Qed.

Theorem n11_36 (W Z : Prop) (φ : Prop → Prop → Prop) :
  (φ Z W) → ∃ x y, φ x y.
Proof.
  assert (S1 : (∀ x y, ¬ φ x y) → ¬ φ Z W).
  { exact (n11_1 Z W (fun x y => ¬ φ x y)). }
  assert (S2 : (φ Z W) → ∃ x y, φ x y).
  {
    pose proof (Transp2_03 (∀ x y, ¬ φ x y)
      (φ Z W)) as Transp2_03.
    MP Transp2_03 S1.
    now rewrite <- n11_22 in Transp2_03.
  }
  exact S2.
Qed.

Theorem n11_37 (φ ψ χ : Prop → Prop → Prop) :
  ((∀ x y, φ x y → ψ x y) ∧ (∀ x y, ψ x y → χ x y))
    → (∀ x y, φ x y → χ x y).
Proof.
  (* TOOLS *)
  set (X := Intro_individual "x").
  set (Y := Intro_individual "y").
  (* ******** *)
  assert (S1 : ((∀ x y, φ x y → ψ x y) ∧ (∀ x y, ψ x y → χ x y))
    → (∀ x y, (φ x y → ψ x y) ∧ (ψ x y → χ x y))).
  { apply n11_31. }
  assert (S2 : ∀ x y, (φ x y → ψ x y) ∧ (ψ x y → χ x y)
    → (φ x y → χ x y)).
  {
    pose proof (Syll3_33 (φ X Y) (ψ X Y) (χ X Y)) as Syll3_33.
    pose proof (n11_11 X Y 
      (fun x y =>
        (φ x y → ψ x y) ∧ (ψ x y → χ x y)
        → φ x y → χ x y)) as n11_11.
    now MP n11_11 Syll3_33.
  }
  assert (S3 : (∀ x y, (φ x y → ψ x y) ∧ (ψ x y → χ x y))
    → (∀ x y, (φ x y → χ x y))).
  {
    pose proof (n11_32
      (fun x y => (φ x y → ψ x y) ∧ (ψ x y → χ x y))
      (fun x y => (φ x y → χ x y))) as n11_32.
    now MP n11_32 S2.
  }
  assert (S4 : ((∀ x y, φ x y → ψ x y) ∧ (∀ x y, ψ x y → χ x y))
    → (∀ x y, φ x y → χ x y)).
  { now Syll_as S1 S3 S4. }
  exact S4.
Qed.

(* Analogue to *10.301. *10.301 uses *4.22, which is missing here, for which
 I think a typo occured. We directly use the routine exactly in *10.301
for this proof. *)
Theorem n11_371 (φ ψ χ : Prop → Prop → Prop) :
  ((∀ x y, φ x y ↔ ψ x y) ∧ (∀ x y, ψ x y ↔ χ x y))
  → (∀ x y, φ x y ↔ χ x y).
Proof.
  set (X := Intro_individual "x").
  set (Y := Intro_individual "y").
  pose proof (n4_22 (φ X Y) (ψ X Y) (χ X Y)) as n4_22.
  pose proof (n11_11 X Y (fun x y =>
    (φ x y ↔ ψ x y) ∧ (ψ x y ↔ χ x y) → φ x y ↔ χ x y)) as n11_11.
  MP n11_11 n4_22.
  pose proof (n11_32 (fun x y => (φ x y ↔ ψ x y) ∧ (ψ x y ↔ χ x y))
    (fun x y => φ x y ↔ χ x y)) as n11_32.
  MP n11_32 n11_11.
  pose proof (n11_31 (fun x y => φ x y ↔ ψ x y)
    (fun x y => ψ x y ↔ χ x y)) as n11_31.
  now rewrite <- n11_31 in n11_32.
Qed.

Theorem n11_38 (φ ψ χ : Prop → Prop → Prop) :
  (∀ x y, φ x y → ψ x y) →
  (∀ x y, (φ x y ∧ χ x y) → (ψ x y ∧ χ x y)).
Proof.
  set (X := Intro_individual "x").
  set (Y := Intro_individual "y").
  pose proof (Fact3_45 (φ X Y) (ψ X Y) (χ X Y)) as Fact3_45.
  pose proof (n11_11 X Y (fun x y =>
    (φ x y → ψ x y) → φ x y ∧ χ x y → ψ x y ∧ χ x y))
    as n11_11.
  MP n11_11 Fact3_45.
  pose proof (n11_32 (fun x y => (φ x y → ψ x y))
    (fun x y => φ x y ∧ χ x y → ψ x y ∧ χ x y)) as n11_32.
  now MP n11_32 n11_11.
Qed.

Theorem n11_39 (φ ψ χ θ : Prop → Prop → Prop) :
  ((∀ x y, φ x y → ψ x y) ∧ (∀ x y, χ x y → θ x y))
  → ((∀ x y, φ x y ∧ χ x y) → (∀ x y, ψ x y ∧ θ x y)).
Proof.
  set (X := Intro_individual "x").
  set (Y := Intro_individual "y").
  pose proof (n3_47 (φ X Y) (χ X Y) (ψ X Y) (θ X Y)) 
    as n3_47.
  pose proof (n11_11 X Y (fun x y => 
    (φ x y → ψ x y) ∧ (χ x y → θ x y)
    → φ x y ∧ χ x y → ψ x y ∧ θ x y)) as n11_11.
  MP n11_11 n3_47.
  pose proof (n11_32 (fun x y => (φ x y → ψ x y) ∧ (χ x y → θ x y))
    (fun x y => φ x y ∧ χ x y → ψ x y ∧ θ x y)) as n11_32a.
  MP n11_32a n11_11.
  pose proof (n11_32 (fun x y => φ x y ∧ χ x y) 
    (fun x y => ψ x y ∧ θ x y)) as n11_32b.
  Syll_as n11_32a n11_32b S1.
  now rewrite <- n11_31 in S1.
Qed.

Theorem n11_391 (φ ψ χ : Prop → Prop → Prop) :
  ((∀ x y, φ x y → ψ x y) ∧ (∀ x y, φ x y → χ x y))
  ↔ (∀ x y, φ x y → (ψ x y ∧ χ x y)).
Proof.
  (* TOOLS *)
  set (X := Intro_individual "x").
  set (Y := Intro_individual "y").
  (* ******** *)
  assert (S1 : ((φ X Y → ψ X Y) ∧ (φ X Y → χ X Y))
    ↔ (φ X Y → (ψ X Y ∧ χ X Y))).
  { apply n4_76. }
  assert (S2 : (∀ x y, ((φ x y → ψ x y) ∧ (φ x y → χ x y)))
    ↔ (∀ x y, φ x y → (ψ x y ∧ χ x y))).
  {
    pose proof (n11_11 X Y (fun x y => 
      ((φ x y → ψ x y) ∧ (φ x y → χ x y))
        ↔ (φ x y → (ψ x y ∧ χ x y)))) as n11_11.
    MP n11_11 S1.
    pose proof (n11_33 (fun x y => (φ x y → ψ x y) ∧ (φ x y → χ x y))
      (fun x y => (φ x y → ψ x y ∧ χ x y))) as n11_33.
    now MP n11_33 n11_11.
  }
  assert (S3 : ((∀ x y, φ x y → ψ x y) 
      ∧ (∀ x y, φ x y → χ x y))
    ↔ (∀ x y, φ x y → (ψ x y ∧ χ x y))).
  { now rewrite <- n11_31 in S2. }
  exact S3.
Qed.

Theorem n11_4 (φ ψ χ θ : Prop → Prop → Prop) :
  ((∀ x y, φ x y ↔ ψ x y) ∧ (∀ x y, χ x y ↔ θ x y))
  → (∀ x y, (φ x y ∧ χ x y) ↔ (ψ x y ∧ θ x y)).
Proof.
  (* TOOLS *)
  set (X := Intro_individual "x").
  set (Y := Intro_individual "y").
  (* ******** *)
  assert (S1 : ((∀ x y, φ x y ↔ ψ x y) ∧ (∀ x y, χ x y ↔ θ x y))
    → (∀ x y, (φ x y ↔ ψ x y) ∧ (χ x y ↔ θ x y))).
  { apply n11_31. }
  assert (S2 : ((∀ x y, φ x y ↔ ψ x y) ∧ (∀ x y, χ x y ↔ θ x y))
    → (∀ x y, (φ x y ∧ χ x y) ↔ (ψ x y ∧ θ x y))).
  {
    pose proof (n4_38 (φ X Y) (χ X Y) (ψ X Y) (θ X Y)) as n4_38.
    pose proof (n11_11 X Y (fun x y => 
      (φ x y ↔ ψ x y) ∧ (χ x y ↔ θ x y)
        → φ x y ∧ χ x y ↔ ψ x y ∧ θ x y)) as n11_11.
    MP n11_11 n4_38.
    pose proof (n11_32 (fun x y => (φ x y ↔ ψ x y) ∧ (χ x y ↔ θ x y))
      (fun x y => φ x y ∧ χ x y ↔ ψ x y ∧ θ x y)) as n11_32.
    MP n11_32 n11_11.
    now Syll_as S1 n11_32 S2.
  }
  exact S2.
Qed.

(* Here the `Id` doesn't seem to mean `Id2_08`. *)
Theorem n11_401 (φ ψ χ : Prop → Prop → Prop) :
  (∀ x y, φ x y ↔ ψ x y) 
  → (∀ x y, (φ x y ∧ χ x y) ↔ (ψ x y ∧ χ x y)).
Proof.
  set (X := Intro_individual "x").
  set (Y := Intro_individual "y").
  pose proof (n4_2 (χ X Y)) as n4_2.
  pose proof (n4_73 (φ X Y ↔ ψ X Y) 
    (χ X Y ↔ χ X Y)) as n4_73.
  MP n4_73 n4_2.
  pose proof (n11_11 X Y (fun x y => (φ x y ↔ ψ x y) 
    ↔ (φ x y ↔ ψ x y) ∧ (χ x y ↔ χ x y)))as n11_11.
  MP n11_11 n4_73.
  pose proof (n11_33 (fun x y => φ x y ↔ ψ x y)
    (fun x y => (φ x y ↔ ψ x y) ∧ (χ x y ↔ χ x y))) 
    as n11_33.
  MP n11_33 n11_11.
  rewrite <- n11_31 in n11_33.
  pose proof (n11_4 φ ψ χ χ) as n11_4.
  now rewrite <- n11_33 in n11_4.
Qed.

Theorem n11_41 (φ ψ : Prop → Prop → Prop) :
  ((∃ x y, φ x y) ∨ (∃ x y, ψ x y))
  ↔ (∃ x y, φ x y ∨ ψ x y).
Proof.
  set (X := Intro_individual "x").
  pose proof (n10_42 (fun y => φ X y) 
    (fun y => ψ X y)) as n10_42a.
  pose proof (n10_11 X (fun x => 
    (∃ y, φ x y) ∨ (∃ y, ψ x y) ↔ ∃ y, φ x y ∨ ψ x y)) 
    as n10_11.
  MP n10_11 n10_42a.
  pose proof (n10_281
    (fun x => (∃ y, φ x y) ∨ (∃ y, ψ x y))
    (fun x => ∃ y, φ x y ∨ ψ x y)) as n10_281.
  MP n10_281 n10_11.
  now rewrite <- n10_42 in n10_281.
Qed.

Theorem n11_42 (φ ψ : Prop → Prop → Prop) :
  (∃ x y, φ x y ∧ ψ x y) 
  → ((∃ x y, φ x y) ∧ (∃ x y, ψ x y)).
Proof.
  set (X := Intro_individual "x").
  pose proof (n10_5 (fun y => φ X y) 
    (fun y => ψ X y)) as n10_5a.
  pose proof (n10_11 X (fun x =>
    (∃ y, φ x y ∧ ψ x y)
      → (∃ y, φ x y) ∧ ∃ y, ψ x y)) as n10_11.
  MP n10_11 n10_5a.
  pose proof (n10_28
    (fun x => (∃ y, φ x y ∧ ψ x y))
    (fun x => (∃ y, φ x y) ∧ ∃ y, ψ x y)) as n10_28.
  MP n10_28 n10_11.
  pose proof (n10_5 (fun x => (∃ y, φ x y))
    (fun x => ∃ y, ψ x y)) as n10_5b.
  now Syll_as n10_28 n10_5b S1.
Qed.

Theorem n11_421 (φ ψ : Prop → Prop → Prop) :
  ((∀ x y, φ x y) ∨ (∀ x y, ψ x y))
  → (∀ x y, φ x y ∨ ψ x y).
Proof.
  pose proof (n11_42 (fun x y => ¬ φ x y) 
    (fun x y => ¬ ψ x y)) as n11_42.
  pose proof (Transp2_16 (∃ x y, ¬ φ x y ∧ ¬ ψ x y)
    ((∃ x y, ¬ φ x y) ∧ ∃ x y, ¬ ψ x y)) 
    as Transp2_16.
  MP Transp2_16 n11_42.
  setoid_rewrite -> n4_56 in Transp2_16.
  rewrite -> n4_51 in Transp2_16.
  repeat rewrite -> n11_25 in Transp2_16.
  now setoid_rewrite <- n4_13 in Transp2_16.
Qed.

Theorem n11_43 (P : Prop) (φ : Prop → Prop → Prop) :
  (∃ x y, φ x y → P) ↔ ((∀ x y, φ x y) → P).
Proof.
  set (X := Intro_individual "x").
  pose proof (n10_34 (fun y => φ X y) P) as n10_34a.
  pose proof (n10_11 X (fun x => (∃ y, φ x y → P)
    ↔ ((∀ y, φ x y) → P))) as n10_11.
  MP n10_11 n10_34a.
  pose proof (n10_281
    (fun x => (∃ y, φ x y → P))
    (fun x => (∀ y, φ x y) → P)) as n10_281.
  MP n10_281 n10_11.
  now rewrite -> n10_34 in n10_281.
Qed.

Theorem n11_44 (P : Prop) (φ : Prop → Prop → Prop) :
  (∀ x y, φ x y ∨ P) ↔ ((∀ x y, φ x y) ∨ P).
Proof.
  set (X := Intro_individual "x").
  pose proof (n10_2 (fun y => φ X y) P) as n10_2a.
  pose proof (n10_11 X (fun x => (∀ y, P ∨ φ x y) 
    ↔ P ∨ ∀ y, φ x y)) as n10_11.
  MP n10_11 n10_2a.
  pose proof (n10_271 (fun x => (∀ y, P ∨ φ x y))
    (fun x => P ∨ ∀ y, φ x y)) as n10_271.
  MP n10_271 n10_11.
  rewrite -> n10_2 in n10_271.
  now setoid_rewrite -> n4_31 in n10_271.
Qed.

Theorem n11_45 (P : Prop) (φ : Prop → Prop → Prop) :
  (∃ x y, P ∧ φ x y) ↔ (P ∧ ∃ x y, φ x y).
Proof.
  set (X := Intro_individual "x").
  pose proof (n10_35 (fun y => φ X y) P) as n10_35a.
  pose proof (n10_11 X (fun x =>
    (∃ y, P ∧ φ x y) ↔ P ∧ ∃ y, φ x y)) as n10_11.
  MP n10_11 n10_35a.
  pose proof (n10_281 (fun x => (∃ y, P ∧ φ x y))
    (fun x => P ∧ ∃ y, φ x y)) as n10_281.
  MP n10_281 n10_11.
  now rewrite -> n10_35 in n10_281.
Qed.

Theorem n11_46 (P : Prop) (φ : Prop → Prop → Prop) :
  (∃ x y, P → φ x y) ↔ (P → ∃ x y, φ x y).
Proof.
  set (X := Intro_individual "x").
  pose proof (n10_37 (fun y => φ X y) P) as n10_37a.
  pose proof (n10_11 X (fun x => (∃ y, P → φ x y) 
    ↔ (P → ∃ y, φ x y))) as n10_11.
  MP n10_11 n10_37a.
  pose proof (n10_281 (fun x => ∃ y, P → φ x y)
    (fun x => P → ∃ y, φ x y)) as n10_281.
  MP n10_281 n10_11.
  now rewrite -> n10_37 in n10_281.
Qed.

Theorem n11_47 (P : Prop) (φ : Prop → Prop → Prop) :
  (∀ x y, P ∧ φ x y) ↔ (P ∧ ∀ x y, φ x y).
Proof.
  set (X := Intro_individual "x").
  pose proof (n10_33 (fun y => φ X y) P) as n10_33a. 
  pose proof (n10_11 X (fun x =>
    (∀ y, φ x y ∧ P) ↔ (∀ y, φ x y) ∧ P)) as n10_11.
  MP n10_11 n10_33a.
  pose proof (n10_271 (fun x => ∀ y, φ x y ∧ P)
    (fun x => (∀ y, φ x y) ∧ P)) as n10_271.
  MP n10_271 n10_11.
  rewrite -> n10_33 in n10_271.
  setoid_rewrite -> n4_3 in n10_271 at 2.
  now setoid_rewrite -> n4_3 in n10_271 at 3.
Qed.

(* NOTE: Different format from original proof *)
Theorem n11_5 (φ : Prop → Prop → Prop) :
  ((∃ x, ¬ ∀ y, φ x y) ↔ ¬ (∀ x y, φ x y))
  ∧
  (¬ (∀ x y, φ x y) ↔ (∃ x y, ¬ φ x y)).
Proof.
  (* TOOLS *)
  set (X := Intro_individual "x").
  (* ******** *)
  assert (S1 : (∃ x, ¬ ∀ y, φ x y) ↔ ¬ (∀ x, ∀ y, φ x y)).
  {
    pose proof (n10_253_alt (fun x => ∀ y, φ x y))
       as n10_253_alt.
    now rewrite -> n4_21 in n10_253_alt.
  }
  assert (S2 : (∃ x, ¬ ∀ y, φ x y) ↔ ¬ (∀ x y, φ x y)).
  {
    (* *11.01 ignored *)
    exact S1.
  }
  assert (S3 : (¬ (∀ y, φ X y)) ↔ (∃ y, ¬ φ X y)).
  { apply n10_253_alt. }
  assert (S4 : (∃ x, ¬ ∀ y, φ x y) ↔ (∃ x, ∃ y, ¬ φ x y)).
  {
    pose proof (n10_11 X (fun x =>
      ¬ (∀ y, φ x y) ↔ ∃ y, ¬ φ x y)) as n10_11.
    MP n10_11 S3.
    pose proof (n10_281 (fun x => ¬ (∀ y, φ x y))
      (fun x => ∃ y, ¬ φ x y)) as n10_281.
    now MP n10_281 n10_11.
  }
  assert (S5 : (∃ x, ¬ ∀ y, φ x y) ↔ ∃ x y, ¬ φ x y).
  {
    (* *11.03 ignored *)
    exact S4.
  }
  assert (S6 : ((∃ x, ¬ ∀ y, φ x y) ↔ ¬ (∀ x y, φ x y))
    ∧ (¬ (∀ x y, φ x y) ↔ (∃ x y, ¬ φ x y))).
  {
    rewrite -> S2 in S5.
    now Conj_as S2 S5 S6.
  }
  exact S6.
Qed.

Theorem n11_51 (φ : Prop → Prop → Prop) :
  (∃ x, ∀ y, φ x y) ↔ (¬ (∀ x, ∃ y, ¬ φ x y)).
Proof.
  (* TOOLS *)
  set (X := Intro_individual "x").
  (* ******** *)
  assert (S1 : (∃ x, ∀ y, φ x y) ↔ (¬ ∀ x, ¬ ∀ y, φ x y)).
  {
    pose proof (n10_252 (fun x => ∀ y, φ x y)) as n10_252.
    rewrite -> Transp4_11 in n10_252.
    now rewrite <- n4_13 in n10_252.
  }
  assert (S2 : (¬ ∀ y, φ X y) ↔ ∃ y, ¬ φ X y).
  { apply n10_253_alt. }
  assert (S3 : (∀ x, (¬ ∀ y, φ x y))
    ↔ ∀ x, ∃ y, ¬ φ x y).
  {
    pose proof (n10_11 X (fun x =>
      (¬ (∀ y, φ x y) ↔ ∃ y, ¬ φ x y))) as n10_11.
    MP n10_11 S2.
    pose proof (n10_271 (fun x => ¬ (∀ y, φ x y))
      (fun x => ∃ y, ¬ φ x y)) as n10_271.
    now MP n10_271 n10_11.
  }
  assert (S4 : (¬ ∀ x, (¬ ∀ y, φ x y))
    ↔ (¬ ∀ x, ∃ y, ¬ φ x y)).
  { now rewrite -> Transp4_11 in S3. }
  assert (S5 : (∃ x, ∀ y, φ x y) ↔ (¬ (∀ x, ∃ y, ¬ φ x y))).
  { now rewrite -> S4 in S1. }
  exact S5.
Qed.

Theorem n11_52 (φ ψ : Prop → Prop → Prop) :
  (∃ x y, φ x y ∧ ψ x y) ↔
  (¬ ∀ x y, φ x y → ¬ ψ x y).
Proof.
  (* TOOLS *)
  set (X := Intro_individual "x").
  set (Y := Intro_individual "y").
  (* ******** *)
  assert (S1 : (¬ (φ X Y ∧ ψ X Y)) ↔ (φ X Y → ¬ ψ X Y)).
  {
    pose proof (n4_51 (φ X Y) (ψ X Y)) as n4_51.
    now rewrite <- n4_62 in n4_51.
  }
  assert (S2 : (∀ x y, ¬ (φ x y ∧ ψ x y)) ↔
    ((∀ x y, φ x y → ¬ ψ x y))).
  {
    pose proof (n11_11 X Y
      (fun x y => ¬ (φ x y ∧ ψ x y) ↔ (φ x y → ¬ ψ x y)))
      as n11_11.
    MP n11_11 S1.
    pose proof (n11_33 (fun x y => ¬ (φ x y ∧ ψ x y))
      (fun x y => φ x y → ¬ ψ x y)) as n11_33.
    now MP n11_33 n11_11.
  }
  assert (S3 : (∃ x y, φ x y ∧ ψ x y) ↔
    (¬ ∀ x y, φ x y → ¬ ψ x y)).
  {
    rewrite -> Transp4_11 in S2.
    now rewrite <- n11_22 in S2.
  }
  exact S3.
Qed.

Theorem n11_521 (φ ψ : Prop → Prop → Prop) :
  (¬ ∃ x y, φ x y ∧ (¬ ψ x y))
  ↔ (∀ x y, φ x y → ψ x y).
Proof.
  pose proof (n11_52 φ (fun x y => ¬ ψ x y)) as n11_52.
  rewrite -> Transp4_11 in n11_52.
  now repeat setoid_rewrite <- n4_13 in n11_52.
Qed.

Theorem n11_53 (φ ψ : Prop → Prop) :
  (∀ x y, φ x → ψ y) ↔ ((∃ x, φ x) → ∀ y, ψ y).
Proof.
  (* TOOLS *)
  set (X := Intro_individual "x").
  (* ******** *)
  assert (S1 : (∀ x y, φ x → ψ y) ↔ (∀ x, φ x → ∀ y, ψ y)).
  {
    pose proof n10_21 as n10_21.
    pose proof (n10_21 (fun y => ψ y) (φ X)) as n10_21a.
    pose proof (n10_11 X (fun x =>
      (∀ y, φ x → ψ y) ↔ (φ x → ∀ y, ψ y))) as n10_11.
    MP n10_11 n10_21a.
    pose proof (n10_271 (fun x => (∀ y, φ x → ψ y))
      (fun x => (φ x → ∀ y, ψ y))) as n10_271.
    now MP n10_271 n10_11.
  }
  assert (S2 : (∀ x y, φ x → ψ y) ↔ ((∃ x, φ x) → ∀ y, ψ y)).
  { now rewrite -> n10_23 in S1. }
  exact S2.
Qed.

Theorem n11_54 (φ ψ : Prop → Prop) :
  (∃ x y, φ x ∧ ψ y) 
  ↔ ((∃ x, φ x) ∧ (∃ y, ψ y)).
Proof.
  (* TOOLS *)
  set (X := Intro_individual "x").
  (* ******** *)
  assert (S1 : (∃ y, φ X ∧ ψ y) ↔ (φ X ∧ (∃ y, ψ y))).
  { apply n10_35. }
  assert (S2 : (∃ x y, φ x ∧ ψ y) ↔
    (∃ x, φ x ∧ ∃ y, ψ y)).
  {
    pose proof (n10_11 X 
      (fun x =>(∃ y, φ x ∧ ψ y) ↔ φ x ∧ ∃ y, ψ y)) 
      as n10_11.
    MP n10_11 S1.
    pose proof (n10_281 (fun x => (∃ y, φ x ∧ ψ y))
      (fun x => φ x ∧ ∃ y, ψ y)) as n10_281.
    now MP n10_281 n10_11.
  }
  assert (S3 : (∃ x y, φ x ∧ ψ y) ↔ ((∃ x, φ x) ∧ (∃ y, ψ y))).
  {
    setoid_rewrite n4_3 in S2 at 3.
    rewrite -> n10_35 in S2.
    now rewrite <- n4_3 in S2.
  }
  exact S3.
Qed.

Theorem n11_55 (φ : Prop → Prop) (ψ : Prop → Prop → Prop) :
  (∃ x y, φ x ∧ ψ x y) ↔ (∃ x, φ x ∧ (∃ y, ψ x y)).
Proof.
  (* TOOLS *)
  set (X := Intro_individual "x").
  (* ******** *)
  assert (S1 : (∃ y, φ X ∧ ψ X y) ↔ (φ X ∧ ∃ y, ψ X y)).
  { apply n10_35. }
  assert (S2 : ∀ x, (∃ y, φ x ∧ ψ x y) ↔ (φ x ∧ ∃ y, ψ x y)).
  {
    pose proof (n10_11 X (fun x => (∃ y, φ x ∧ ψ x y) 
      ↔ (φ x ∧ ∃ y, ψ x y))) as n10_11.
    now MP n10_11 S1.
  }
  assert (S3 : (∃ x y, φ x ∧ ψ x y) ↔ (∃ x, φ x ∧ (∃ y, ψ x y))).
  {
    pose proof (n10_281 (fun x => (∃ y, φ x ∧ ψ x y)) 
      (fun x => (φ x ∧ ∃ y, ψ x y))) as n10_281.
    now MP n10_281 S2.
  }
  exact S3.
Qed.

Theorem n11_56 (φ ψ : Prop → Prop) :
  ((∀ x, φ x) ∧ (∀ y, ψ y)) ↔ (∀ x y, φ x ∧ ψ y).
Proof.
  (* TOOLS *)
  set (X := Intro_individual "x").
  (* ******** *)
  assert (S1 : ((∀ x, φ x) ∧ (∀ y, ψ y)) ↔ (∀ x, φ x ∧ ∀ y, ψ y)).
  { 
    pose proof (n10_33 φ (∀ y, ψ y)) as n10_33.
    now rewrite -> n4_21 in n10_33.
  }
  assert (S2 : (φ X ∧ (∀ y, ψ y)) ↔ (∀ y, φ X ∧ ψ y)).
  {
    pose proof (n10_33 ψ (φ X)) as n10_33.
    rewrite -> n4_21 in n10_33.
    rewrite <- n4_3 in n10_33.
    now setoid_rewrite <- n4_3 in n10_33 at 3.
  }
  assert (S3 : ∀ x, (φ x ∧ (∀ y, ψ y)) ↔ (∀ y, φ x ∧ ψ y)).
  {
    pose proof (n10_11 X (fun x => (φ x ∧ (∀ y, ψ y)) 
      ↔ (∀ y, φ x ∧ ψ y))) as n10_11.
    now MP n10_11 S2.
  }
  assert (S4 : (∀ x, φ x ∧ (∀ y, ψ y)) ↔ (∀ x, ∀ y, φ x ∧ ψ y)).
  {
    pose proof (n10_271 (fun x => φ x ∧ (∀ y, ψ y)) 
      (fun x => ∀ y, φ x ∧ ψ y)) as n10_271.
    now MP n10_271 S3.
  }
  assert (S5 : (∀ x, φ x ∧ (∀ y, ψ y)) ↔ (∀ x y, φ x ∧ ψ y)).
  {
    (* *11.01 ignored *)
    exact S4.
  }
  assert (S6 : ((∀ x, φ x) ∧ (∀ y, ψ y)) ↔ (∀ x y, φ x ∧ ψ y)).
  { now rewrite -> S5 in S1. }
  exact S6.
Qed.

Theorem n11_57 (φ : Prop → Prop) :
  (∀ x, φ x) ↔ (∀ x y, φ x ∧ φ y).
Proof.
  pose proof (n11_56 φ φ) as n11_56.
  now rewrite <- n4_24 in n11_56.
Qed.

Theorem n11_58 (φ : Prop → Prop) :
  (∃ x, φ x) ↔ (∃ x y, φ x ∧ φ y).
Proof.
  pose proof (n11_54 φ φ) as n11_54.
  now rewrite <- n4_24 in n11_54.
Qed.

Theorem n11_59 (φ ψ : Prop → Prop) :
  (φ x -[ x ]> ψ x) ↔ ((φ x ∧ φ y) -[ x y ]> (ψ x ∧ ψ y)).
Proof.
  (* TOOLS *)
  set (X := Intro_individual "x").
  set (Y := Intro_individual "y").
  (* ******** *)
  assert (S1 : (φ x -[ x ]> ψ x) 
    ↔ (∀ x y, (φ x → ψ x) ∧ (φ y → ψ y))).
  { apply n11_57. }
  assert (S2 : (φ x -[ x ]> ψ x) 
    → (∀ x y, (φ x ∧ φ y) → (ψ x ∧ ψ y))).
  {
    pose proof (n3_47 (φ X) (φ Y) (ψ X) (ψ Y)) as n3_47.
    pose proof (n11_11 X Y (fun x y =>
      (φ x → ψ x) ∧ (φ y → ψ y) → φ x ∧ φ y → ψ x ∧ ψ y)) 
      as n11_11.
    MP n11_11 n3_47.
    pose proof (n11_32 (fun x y => (φ x → ψ x) ∧ (φ y → ψ y))
      (fun x y => φ x ∧ φ y → ψ x ∧ ψ y)) as n11_32.
    MP n11_32 n11_11.
    destruct S1 as [S1l _].
    now Syll_as S1l n11_32 S2.
  }
  assert (S3 : (∀ x y, (φ x ∧ φ y) → (ψ x ∧ ψ y)) 
    → ((φ X ∧ φ Y) → (ψ X ∧ ψ Y))).
  { 
    exact (n11_1 X Y (fun x y => 
      (φ x ∧ φ y) → (ψ x ∧ ψ y))).
  }
  (* NOTE: Currently, direct substitution on a step is unsupported.
  Even if we can use `replace X with Y`, I don't want to do it
  for the moment. The only way to do this is rewrite the proposition
  again. *)
  assert (S4 : (∀ x y, (φ x ∧ φ y) → (ψ x ∧ ψ y)) 
    → (φ X → ψ X)).
  {
    pose proof (n11_1 X X (fun x y => 
      (φ x ∧ φ y) → (ψ x ∧ ψ y))) as n11_1.
    (* NOTE: This cannot be deleted *)
    simpl in n11_1.
    now repeat rewrite <- n4_24 in n11_1.
  }
  assert (S5 : (∀ x y, (φ x ∧ φ y) → (ψ x ∧ ψ y)) 
    → (φ x -[ x ]> ψ x)).
  {
    pose proof (n10_11 X (fun x =>
      ((φ x ∧ φ y) -[ x y ]> ψ x ∧ ψ y)
      → (φ x → ψ x))) as n10_11.
    MP n10_11 S4.
    pose proof (n10_21 (fun x =>φ x → ψ x)
      (((φ x ∧ φ y) -[ x y ]> ψ x ∧ ψ y))) as n10_21.
    now rewrite -> n10_21 in n10_11.
  }
  assert (S6 : (φ x -[ x ]> ψ x) ↔
    ((φ x ∧ φ y) -[ x y ]> (ψ x ∧ ψ y))).
  {
    Conj_as S2 S5 S6.
    now Equiv S6.
  }
  exact S6.
Qed.

Theorem n11_6 (φ : Prop → Prop → Prop) (ψ χ : Prop → Prop) :
  (∃ x, (∃ y, φ x y ∧ ψ y) ∧ χ x) 
  ↔ (∃ y, (∃ x, φ x y ∧ χ x) ∧ ψ y).
Proof.
  (* TOOLS *)
  set (X := Intro_individual "x").
  (* ******** *)
  assert (S1 : ((∃ y, φ X y ∧ ψ y) ∧ χ X) 
    ↔ (∃ y, (φ X y ∧ ψ y) ∧ χ X)).
  {
    pose proof (n10_35 (fun y => φ X y ∧ ψ y) (χ X)) as n10_35.
    rewrite -> n4_3 in n10_35.
    now setoid_rewrite -> n4_3 in n10_35 at 2.
  }
  assert (S2 : (∃ x, (∃ y, φ x y ∧ ψ y) ∧ χ x) 
    ↔ (∃ x, (∃ y, (φ x y ∧ ψ y) ∧ χ x))).
  {
    pose proof (n10_11 X (fun x => ((∃ y, φ x y ∧ ψ y) ∧ χ x) 
      ↔ (∃ y, (φ x y ∧ ψ y) ∧ χ x))) as n10_11.
    MP n10_11 S1.
    pose proof (n10_281 (fun x => (∃ y, φ x y ∧ ψ y) ∧ χ x)
      (fun x => ∃ y, (φ x y ∧ ψ y) ∧ χ x)) as n10_281.
    now MP n10_281 n10_11.
  }
  assert (S3 : (∃ x, (∃ y, φ x y ∧ ψ y) ∧ χ x)
    ↔ (∃ y, (∃ x, (φ x y ∧ ψ y) ∧ χ x))).
  { now rewrite -> n11_23 in S2. }
  assert (S4 : (∃ x, (∃ y, φ x y ∧ ψ y) ∧ χ x)
    ↔ (∃ y, (∃ x, (φ x y ∧ χ x) ∧ ψ y))).
  {
    (* *11.341, *1.4 ignored - we use a easier way *)
    setoid_rewrite -> n4_32 in S3.
    setoid_rewrite -> n4_3 in S3 at 5.
    now setoid_rewrite <- n4_32 in S3.
  }
  assert (S5 : (∃ x, (∃ y, φ x y ∧ ψ y) ∧ χ x) 
    ↔ (∃ y, (∃ x, φ x y ∧ χ x) ∧ ψ y)).
  {
    (* *10.281 ignored
    NOTE: There should be a typo here making S5 and S4 exactly the same in original text.
    We use the easiest way *)
    pose proof n10_35 as n10_35.
    setoid_rewrite -> n4_3 in S4 at 4.
    setoid_rewrite -> n10_35 in S4.
    now setoid_rewrite <- n4_3 in S4 at 4.
  }
  exact S5.
Qed.

Theorem n11_61 (φ : Prop → Prop) (ψ : Prop → Prop → Prop) :
  (∃ y, (φ x -[ x ]> ψ x y)) → (φ x -[ x ]> ∃ y, ψ x y).
Proof.
  (* TOOLS *)
  set (X := Intro_individual "x").
  (* ******** *)
  assert (S1 : (∃ y, (φ x -[ x ]> ψ x y)) →
    (∀ x, ∃ y, φ x → ψ x y)).
  { apply n11_26. }
  assert (S2 : (∃ y, φ X → ψ X y) → (φ X → ∃ y, ψ X y)).
  { apply n10_37. }
  assert (S3 : (∀ x, ∃ y, φ x → ψ x y) 
    → (∀ x, φ x → ∃ y, ψ x y)).
  {
    pose proof (n10_11 X (fun x => (∃ y, φ x → ψ x y) 
      → (φ x → ∃ y, ψ x y))) as n10_11.
    MP n10_11 S2.
    pose proof (n10_27 (fun x => ∃ y, φ x → ψ x y)
      (fun x => φ x → ∃ y, ψ x y)) as n10_27.
    now MP n10_27 n10_11.
  }
  assert (S4 : (∃ y, (φ x -[ x ]> ψ x y)) → (φ x -[ x ]> ∃ y, ψ x y)).
  { now Syll_as S1 S3 S4. }
  exact S4.
Qed.

Theorem n11_62 (φ : Prop → Prop) (ψ χ : Prop → Prop → Prop) :
  ((φ x ∧ ψ x y) -[ x y ]> χ x y) ↔ (φ x -[ x ]> (ψ x y -[ y ]> χ x y)).
Proof.
  (* TOOLS *)
  set (X := Intro_individual "x").
  set (Y := Intro_individual "y").
  (* ******** *)
  assert (S1 : ((φ x ∧ ψ x y) -[ x y ]> χ x y) 
    ↔ (∀ x y, φ x → (ψ x y → χ x y))).
  {
    pose proof (n4_87 (φ X) (ψ X Y) (χ X Y)) as n4_87.
    destruct n4_87 as [n4_87l _].
    pose proof (n11_11 X Y (fun x y => 
      (φ x ∧ ψ x y → χ x y) ↔ (φ x → ψ x y → χ x y)))as n11_11.
    MP n11_11 n4_87l.
    pose proof (n11_33 (fun x y => φ x ∧ ψ x y → χ x y)
      (fun x y => φ x → ψ x y → χ x y)) as n11_33.
    now MP n11_33 n11_11.
  }
  assert (S2 : ((φ x ∧ ψ x y) -[ x y ]> χ x y) 
    ↔ (∀ x, φ x → (∀ y, ψ x y → χ x y))).
  {
    (* NOTE: This proof is a little different: it only instantiates at the
      conclusion part of `S1`, similar to use a `Hp`
      TODO: recheck this proof *)
    pose proof (n10_21 (fun y => ψ X y → χ X y) (φ X)) as n10_21.
    pose proof (n10_11 X (fun x => 
      (∀ y, φ x → ψ x y → χ x y)
      ↔ (φ x → ∀ y, ψ x y → χ x y))) as n10_11.
    MP n10_11 n10_21.
    pose proof (n10_271 (fun x => (∀ y, φ x → ψ x y → χ x y))
      (fun x => φ x → ∀ y, ψ x y → χ x y)) as n10_271.
    MP n10_271 n10_11.
    now rewrite -> n10_271 in S1.
  }
  exact S2.
Qed.

Theorem n11_63 (φ ψ : Prop → Prop → Prop) :
  (¬ ∃ x y, φ x y) → (φ x y -[ x y ]> ψ x y).
Proof.
  (* TOOLS *)
  set (X := Intro_individual "x").
  set (Y := Intro_individual "y").
  (* ******** *)
  assert (S1 : ∀ x y, (¬ φ x y) → (φ x y → ψ x y)).
  {
    pose proof (n2_21 (φ X Y) (ψ X Y)) as n2_21.
    pose proof (n11_11 X Y (fun x y =>
      (¬ φ x y) → (φ x y → ψ x y))) as n11_11.
    now MP n11_11 n2_21.
  }
  assert (S2 : (∀ x y, (¬ φ x y)) 
    → (∀ x y, φ x y → ψ x y)).
  {
    pose proof (n11_32 (fun x y => ¬ φ x y)
      (fun x y => φ x y → ψ x y)) as n11_32.
    now MP n11_32 S1.
  }
  assert (S3 : (¬ ∃ x y, φ x y) → (φ x y -[ x y ]> ψ x y)).
  { now rewrite <- n11_25 in S2. }
  exact S3.
Qed.

Theorem n11_7 (φ : Prop → Prop → Prop) :
  (∃ x y, φ x y ∨ φ y x) ↔ ∃ x y, φ x y.
Proof.
  assert (S1 : (∃ x y, φ x y ∨ φ y x) 
    ↔ ((∃ x y, φ x y) ∨ (∃ x y, φ y x))).
  { 
    pose proof (n11_41 φ) as n11_41.
    now setoid_rewrite -> n4_21 in n11_41.
  }
  assert (S2 : (∃ x y, φ x y ∨ φ y x) 
    ↔ ((∃ x y, φ x y) ∨ (∃ y x, φ y x))).
  { now setoid_rewrite -> n11_23 in S1 at 3. }
  assert (S3 : (∃ x y, φ x y ∨ φ y x) 
    ↔ (∃ x y, φ x y)).
  { now rewrite <- n4_25 in S2. }
  exact S3.
Qed.

Theorem n11_71 (φ ψ χ θ : Prop → Prop) :
  ((∃ z, φ z) ∧ (∃ w, χ w))
  → (((φ z -[ z ]> ψ z) ∧ (χ w -[ w ]> θ w))
      ↔ ((φ z ∧ χ w) -[ z w ]> (ψ z ∧ θ w))).
Proof.
  (* TOOLS *)
  set (Z := Intro_individual "z").
  set (W := Intro_individual "w").
  (* NOTE: this is a very exclusive `equiv` version of `Comm` that
    is not provided in Principia Mathematica *)
  assert (Comm_Equiv : ∀ P Q R : Prop, 
    (P → (Q → R)) ↔ (Q → (P → R))).
  { split; apply Comm2_04. }
  (* ******** *)
  assert (S1 : 
    ((φ z -[ z ]> ψ z) ∧ (χ w -[ w ]> θ w))
    → ((φ Z ∧ χ W) → ψ Z ∧ θ W)).
  {
    pose proof (n10_1 (fun z => φ z → ψ z) Z) as n10_1a.
    pose proof (n10_1 (fun w => χ w → θ w) W) as n10_1b.
    Conj_as n10_1a n10_1b C1.
    pose proof (n3_47
      (φ z -[ z ]> ψ z) (χ w -[ w ]> θ w)
      (φ Z → ψ Z) (χ W → θ W)) as n3_47a.
    MP n3_47a C1.
    pose proof (n3_47 (φ Z) (χ W) (ψ Z) (θ W)) as n3_47b.
    now Syll_as n3_47a n3_47b S1.
  }
  assert (S2 : ((φ z -[ z ]> ψ z) ∧ (χ w -[ w ]> θ w))
    → (∀ z w, (φ z ∧ χ w) → ψ z ∧ θ w)).
  {
    (* We directly use `Syll` here for simplicity. Note that
      this might be actually not allowed in original proof *)
    (* n11_3 ignored *)
    pose proof (n11_11 Z W (fun z w => (φ z ∧ χ w) 
      → ψ z ∧ θ w)) as n11_11.
    now Syll_as S1 n11_11 S2.
  }
  assert (S3 : (∀ z w, (φ z ∧ χ w) → ψ z ∧ θ w)
    → ((φ Z ∧ χ w) -[ w ]> (ψ Z ∧ θ w))).
  {
    exact (n10_1 
      (fun z => ∀ w, (φ z ∧ χ w) → ψ z ∧ θ w) Z).
  }
  assert (S4 : (∀ z w, (φ z ∧ χ w) → ψ z ∧ θ w)
    → ((∃ w, φ Z ∧ χ w) → (∃ w, ψ Z ∧ θ w))).
  {
    pose proof (n10_28 (fun w => φ Z ∧ χ w)
      (fun w => ψ Z ∧ θ w)) as n10_28.
    now Syll_as S3 n10_28 S4.
  }
  assert (S5 : (∀ z w, (φ z ∧ χ w) → ψ z ∧ θ w)
    → ((φ Z ∧ ∃ w, χ w) → (ψ Z ∧ ∃ w, θ w))).
  {
    rewrite -> n10_35 in S4.
    now setoid_rewrite -> n10_35 in S4.
  }
  (* This has been an extremely long proof, so I don't mind use more
  simplifications... *)
  assert (S6 : (∃ w, χ w) 
    → (((φ z ∧ χ w) -[ z w ]> (ψ z ∧ θ w))
      → (φ Z → ψ Z))).
  {
    (* First we use the `Simpl` to delete the backmost part *)
    assert (S5_1 : (∀ z w, φ z ∧ χ w → ψ z ∧ θ w)
      → φ Z ∧ (∃ w, χ w) → ψ Z).
    {
      assert (S5_1_1 : 
        (φ Z ∧ (∃ w, χ w) → ψ Z ∧ ∃ w, θ w)
        → (φ Z ∧ (∃ w, χ w) → ψ Z)).
      {
        intro Hp.
        pose proof (Simp3_26 (ψ Z) (∃ w, θ w)) as Simp3_26.
        now Syll_as Hp Simp3_26 S5_1_1.
      }
      now Syll_as S5 S5_1_1 S5_1.
    }
    rewrite -> Comm_Equiv in S5_1.
    pose proof (n4_87
      (φ Z)
      (∃ w, χ w)
      ((∀ z w, φ z ∧ χ w → ψ z ∧ θ w)
        → ψ Z)) as n4_87.
    destruct n4_87 as [n4_87 _].
    rewrite -> n4_87 in S5_1.
    rewrite -> Comm_Equiv in S5_1.
    pose proof (Comm2_04 
      (φ Z)
      (∀ z w, φ z ∧ χ w → ψ z ∧ θ w)
      (ψ Z)) as Comm2_04.
    now Syll_as S5_1 Comm2_04 S6.
  }
  assert (S7 : (∃ w, χ w) 
    → (((φ z ∧ χ w) -[ z w ]> (ψ z ∧ θ w))
      → (φ z -[ z ]> ψ z))).
  {
    pose proof (n10_11 Z (fun z0 =>
      (∃ w, χ w) → (∀ z w, φ z ∧ χ w → ψ z ∧ θ w) 
      → φ z0 → ψ z0)) as n10_11.
    MP n10_11 S6.
    rewrite -> n10_21 in n10_11.
    now setoid_rewrite -> n10_21 in n10_11.
  }
  assert (S8 : (∃ z, φ z) 
    → (((φ z ∧ χ w) -[ z w ]> (ψ z ∧ θ w))
      → (χ w -[ w ]> θ w))).
  {
    assert (S5_2 : (∀ z w, (φ z ∧ χ w) → ψ z ∧ θ w)
      → (χ W ∧ (∃ z, φ z) → (θ W ∧ ∃ z, ψ z))).
    {
      pose proof ((n10_1 
        (fun w => ∀ z, (φ z ∧ χ w) → ψ z ∧ θ w) W))
        as S3_1. 
      pose proof (n10_28 (fun z => φ z ∧ χ W)
        (fun z => ψ z ∧ θ W)) as n10_28.
      Syll_as S3_1 n10_28 S4_1.
      setoid_rewrite -> n4_3 in S4_1 at 3.
      setoid_rewrite -> n4_3 in S4_1 at 4.
      rewrite -> n10_35 in S4_1.
      setoid_rewrite -> n10_35 in S4_1.
      now rewrite -> n11_2 in S4_1.
    }
    assert (S5_3 : (∀ z w, φ z ∧ χ w → ψ z ∧ θ w)
      → χ W ∧ (∃ z, φ z) → θ W).
    {
      assert (S5_3_1 : 
        (χ W ∧ (∃ z, φ z) → (θ W ∧ ∃ z, ψ z))
        → (χ W ∧ (∃ z, φ z) → θ W)).
      {
        intro Hp.
        pose proof (Simp3_26 (θ W) (∃ z, ψ z)) as Simp3_26.
        now Syll_as Hp Simp3_26 S5_3_2.
      }
      now Syll_as S5_2 S5_3_1 S5_3.
    }
    rewrite -> Comm_Equiv in S5_3.
    pose proof (n4_87
      (χ W)
      (∃ z, φ z)
      ((∀ z w, φ z ∧ χ w → ψ z ∧ θ w)
        → θ W)) as n4_87.
    destruct n4_87 as [n4_87 _].
    rewrite -> n4_87 in S5_3.
    rewrite -> Comm_Equiv in S5_3.
    pose proof (Comm2_04 
      (χ W)
      (∀ z w, φ z ∧ χ w → ψ z ∧ θ w)
      (θ W)) as Comm2_04.
    Syll_as S5_3 Comm2_04 S6_1.
    pose proof (n10_11 W (fun w0 =>
      (∃ z, φ z) → (∀ z w, φ z ∧ χ w → ψ z ∧ θ w) 
        → χ w0 → θ w0)) as n10_11.
    MP n10_11 S6_1.
    rewrite -> n10_21 in n10_11.
    now setoid_rewrite -> n10_21 in n10_11.
  }
  assert (S9 : ((∃ z, φ z) ∧ (∃ w, χ w))
    →  
      ((φ z ∧ χ w) -[ z w ]> (ψ z ∧ θ w))
      →
      ((φ z -[ z ]> ψ z) ∧ (χ w -[ w ]> θ w))).
  {
    (* n3_47 ignored. Here we try to save the routine... *)
    intro Hp.
    destruct Hp as [HS8 HS7].
    pose proof (S7 HS7) as S7.
    pose proof (S8 HS8) as S8.
    Conj_as S7 S8 C1.
    pose proof (Comp3_43 
      (∀ z w, φ z ∧ χ w → ψ z ∧ θ w)
      (∀ z, φ z → ψ z)
      (∀ w, χ w → θ w)) as Comp3_43.
    now MP Comp3_43 C1.
  }
  assert (S10 : ((∃ z, φ z) ∧ (∃ w, χ w))
    → (((φ z -[ z ]> ψ z) ∧ (χ w -[ w ]> θ w))
      ↔ ((φ z ∧ χ w) -[ z w ]> (ψ z ∧ θ w)))).
  {
    (* Similarly, we save the rountine *)
    intro Hp.
    pose proof (S9 Hp) as S9.
    Conj_as S2 S9 C1.
    now Equiv C1.
  }
  exact S10.
Qed.

Close Scope formal_impl.
Close Scope formal_equiv.
