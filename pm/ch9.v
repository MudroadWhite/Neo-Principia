Require Import PM.pm.lib.
Require Import PM.pm.ch1.
Require Import PM.pm.ch2.
Require Import PM.pm.ch3.
Require Import PM.pm.ch4.
Require Import PM.pm.ch5.

(* ******** *)

(* Definitions involving `¬` on 1st order props. Our current simulation doesn't emphasize
  that it's the negation that we're trying to specify(a more obvious example can be how 
  a typeclasse works on different instances) *)
(* Pp n9_01 tries to say the situation of `¬` working on a `∀` proposition *)
Definition n9_01 (φ : Prop → Prop) :
  (¬ ∀ x, φ x) = ∃ x, ¬ φ x. Admitted.

Definition n9_02 (φ : Prop → Prop) :
  (¬ ∃ x, φ x) = ∀ x, ¬ φ x. Admitted.

Definition n9_011 (φ : Prop → Prop) : 
  (¬ ∀ x, φ x) = ¬ (∀ x, φ x). Admitted.

Definition n9_021 (φ : Prop → Prop) :
  (¬ ∃ x, φ x) = ¬ (∃ x, φ x). Admitted.
(* ******** *)

(* Definitions for `∨`. n9_03 shows the situation of `∨` working on a `∀` *)
Definition n9_03 (φ : Prop → Prop) (p : Prop) :
  ((∀ x, φ x) ∨ p) = (∀ x, φ x ∨ p). Admitted.

Definition n9_04 (φ : Prop → Prop) (p : Prop) :
  (p ∨ (∀ x, φ x)) = (∀ x, p ∨ φ x). Admitted.

Definition n9_05 (φ : Prop → Prop) (p : Prop) :
  ((∃ x, φ x) ∨ p) = (∃ x, φ x ∨ p). Admitted.

Definition n9_06 (φ : Prop → Prop) (p : Prop) : 
  (p ∨ (∃ x, φ x)) = ∃ x, p ∨ (φ x). Admitted.

Definition n9_07 (φ ψ : Prop → Prop) : 
  ((∀ x, φ x) ∨ (∃ y, ψ y)) = ∀ x, ∃ y, φ x ∨ ψ y. Admitted.

Definition n9_08 (φ ψ : Prop → Prop) :
  ((∃ y, ψ y) ∨ (∀ x, φ x)) = ∀ x, ∃ y, ψ y ∨ φ x. Admitted.
(* ******** *)

(* Primitive propositions for `∃`, deriving from elementary propositions *)
(* `∃ z, φ z` means that for a function `φ z^`, there's a value that makes it true *)
Definition n9_1 (φ : Prop → Prop) (X : Prop) : 
  φ X → ∃ z, φ z. Admitted.

(* An extra Pp to avoid dependency on *1.2, which is only limited to elementary 
  propositions *)
Definition n9_11 (φ : Prop → Prop) (X Y : Prop) : 
  (φ X ∨ φ Y) → ∃ z, φ z. Admitted.
(* ******** *)

(* Primitive propositions for inference, for 1st order propositions. *)
(* Pp *9_12 : What is implied by a true premise is true. Analogue to *1.1. 
  We will not distinguish between *9.12 and *1.1. For all kinds of modus ponens, we 
  only use the `MP` tactic. *)
Definition MP9_12 (P Q : Prop): (P → Q) → P → Q. Admitted.

(* Pp n9_13 : In any assersion containing a real variable, this real variable
may be turned into an apparent variable of which all possible values are asserted
to satisfy the function in question. *)
(* The proposition to instantiate a real variable into a first order proposition. 
  This is almost the only starting point to get a quantified proposition, and is
  supposed to be very commonly used.
  What it really means:
  - If `¬` and `∨` can be defined, then we can define a function `φ`
  - If φ (over elementary propositions) can be defined, and φY is always true
  - then we can construct a 1st order proposition made up from φ *)
Definition n9_13 (φ : Prop → Prop) (Y : Prop) : 
  φ Y → (∀ x , φ x). Admitted.
(* ******** *)

(* Primitive propositions for identifying propositions "of the same type". WARNING:
  this implementation is immature and won't fix *)
Definition is_individual (x : Prop) : Prop. Admitted.
(* NOTE: Currently we only assert efuncs that takes 1 argument. *)
Definition is_efunc (F : Prop → Prop) : Prop. Admitted.
Definition is_eprop (P : Prop) : Prop. Admitted.

Module IsSameType.
  Inductive t (U V : Prop) : Prop :=
    | Individual : (is_individual U) → (is_individual V) → t U V
    | EFuncs (φ ψ : Prop → Prop) (X Y : Prop) 
      : (is_efunc φ) → (is_efunc ψ) → t X Y 
        → (U = φ X) → (V = ψ Y)
        → t U V
    | NEFuncs (φ : Prop → Prop) (X : Prop) : (is_efunc φ) 
        → (U = φ X) → (V = ¬ φ X)
        → t U V
    | OrL (φ ψ : Prop → Prop) (X : Prop) : (is_efunc φ) → (is_efunc ψ)
        → (U = φ X) → (V = φ X ∨ ψ X)
        → t U V
    | OrR (φ ψ : Prop → Prop) (X : Prop) : (is_efunc φ) → (is_efunc ψ)
        → (U = ψ X) → (V = φ X ∨ ψ X)
        → t U V
    | All2 (φ ψ : Prop → Prop → Prop) (X : Prop) (Y0 : Prop) : 
        t (φ X Y0) (ψ X Y0)
        → (U = ∀ y, φ X y) → (V = ∀ z, ψ X z)
        → t U V
    | EProp : (is_eprop U) → (is_eprop V) → t U V
    | NProp : (V = ¬ U) → t U V
    | All (φ ψ : Prop → Prop) (X0 : Prop) : t (φ X0) (ψ X0)
        → (U = ∀ x, φ x) → (V = ∀ y, ψ y)
        → t U V
    .
End IsSameType.

Definition n9_131 := IsSameType.t.

(* Cf p.120, *10.121 *)
Definition n9_14 (A : Prop) (φ : Prop → Prop) (X : Prop) :
  φ X → (n9_131 X A ↔ φ A). Admitted.

(* Pp n9_15 : If for some `a` there is a proposition `φ a`, then there is a function
  `phi x^` and vice versa. *)
(* This proposition is intended to type a function by saying that "this function exists". *)
Definition n9_15 (A X : Prop) (φ : Prop → Prop) :
  (φ A) ↔ (X → φ X).
Admitted.
(* ******** *)

(* Theorems below in this chapter are supposed to prove that `∀` and `∃` deduce just like 
  elementary propositions. We begin with some theorems for setups *)
Theorem n9_2 (φ : Prop → Prop) (Y : Prop) : (∀ x , φ x) → φ Y.
Proof. 
  (** Step 1 **)
  pose proof (n2_1 (φ Y)) as n2_1.
  (** Step 2 **)
  (* TODO: we're passing in a function as parameter. Whether this is allowed should be 
  examined *)
  pose proof (n9_1 (fun x => ¬ φ x ∨ φ Y) Y) as n9_1.
  (* MP here is the version *1.11 *)
  MP n9_1 n2_1.
  (** Step 3 **)
  rewrite <- (n9_05 (fun x => ¬ φ x) (φ Y)) in n9_1.
  (** Step 4 **)
  rewrite <- (n9_01 φ) in n9_1.
  rewrite <- Impl1_01 in n9_1. 
  apply n9_1.
Qed.

Theorem n9_21 (φ ψ : Prop → Prop) :
  (∀ x, φ x → ψ x) → (∀ y, φ y) → ∀ z, ψ z.
Proof.
  (** Necessary tools to be used globally **)
  (* Manually set up a `↔` variant from `=` relation so that we can `setoid_rewrite`. 
  This enables substitution where `∀`s and `∃` are involved. *)
  set (λ P0 Q0 : Prop, eq_to_equiv (P0 → Q0) (¬ P0 ∨ Q0) (Impl1_01 P0 Q0))
    as Impl1_01a.
  set (λ (φ0 : Prop → Prop) (P0 : Prop), 
    eq_to_equiv 
      (P0 ∨ ∃ x, φ0 x) (∃ x, P0 ∨ φ0 x) 
      (n9_06 φ0 P0))
  as n9_06a.
  set (Z := Intro_individual "z").
  (* ******** *)
  assert (S1 : (φ Z → ψ Z) → φ Z → ψ Z).
  { exact (Id2_08 (φ Z → ψ Z)). }
  assert (S2 : ∃ y, (φ Z → ψ Z) → φ y → ψ Z).
  { 
    pose proof (n9_1 (fun x => (φ Z → ψ Z) → φ x → ψ Z) Z) as n9_1.
    now MP n9_1 S1.
  }
  assert (S3 : ∃ x y, (φ x → ψ x) → φ y → ψ Z).
  { 
    (* *1.11 ignored *)
    pose proof (n9_1 (fun x => (∃ z0, (φ x → ψ x) → φ z0 → ψ Z)) Z) as n9_1.
    now MP n9_1 S2.
  }
  assert (S4 : ∀ z, ∃ x y, (φ x → ψ x) → φ y → ψ z).
  {
    pose proof (n9_13 (fun z => 
      (∃ x y, (φ x → ψ x) → φ y → ψ z)) Z) as n9_13.
    now MP n9_13 S3.
  }
  assert (S5 : ∀ z, (∃ x, (φ x → ψ x) → (∃ y, φ y → ψ z))).
  {
    setoid_rewrite -> Impl1_01a in S4.
    setoid_rewrite <- n9_06a in S4.
    now setoid_rewrite <- Impl1_01a in S4.
  }
  assert (S6 : ((∃ x, ¬ (φ x → ψ x)) ∨ (∀ y, ∃ z, (¬ φ z) ∨ ψ y))).
  {
    setoid_rewrite -> Impl1_01a in S5.
    setoid_rewrite -> Impl1_01a in S5 at 3.
    now rewrite <- (n9_08 (fun z1 => (∃ y0, (¬ φ y0) ∨ ψ z1)) 
      (fun x1 => ¬ (φ x1 → ψ x1))) in S5.
  }
  assert (S7 : (∃ x, ¬ (φ x → ψ x)) ∨ ((∃ y, (¬ φ y)) ∨ (∀ z, ψ z))).
  { rewrite <- n9_08 in S6. exact S6. }
  assert (S8 : (∀ x, φ x → ψ x) → (∀ y, φ y) → ∀ z, ψ z).
  { now repeat rewrite <- n9_01, <- Impl1_01 in S7. }
  exact S8.
Qed.

Theorem n9_22 (φ ψ : Prop → Prop) :
  (∀ x, φ x → ψ x) → (∃ x, φ x) → (∃ x, ψ x).
Proof. 
  (* TOOLS *)
  set (λ P0 Q0 : Prop, eq_to_equiv (P0 → Q0) (¬ P0 ∨ Q0) (Impl1_01 P0 Q0))
    as Impl1_01a.
  set (λ (P0 : Prop) (φ0 : Prop → Prop),
    eq_to_equiv (P0 ∨ ∃ x, φ0 x) (∃ x, P0 ∨ φ0 x) 
    (n9_06 φ0 P0)) as n9_06a.
  set (λ φ0 ψ0 : (Prop → Prop), 
    eq_to_equiv 
      ((∃ y, ψ0 y) ∨ ∀ x, φ0 x) 
      (∀ x, ∃ y, ψ0 y ∨ φ0 x) 
      (n9_08 φ0 ψ0)) as n9_08a.
  set (λ φ0 ψ0 : (Prop → Prop), 
    eq_to_equiv 
      ((∀ x, φ0 x) ∨ (∃ y, ψ0 y))
      (∀ x, ∃ y, φ0 x ∨ ψ0 y)
      (n9_07 φ0 ψ0)) as n9_07a.
  set (Y := Intro_individual "Y").
  (* ******** *)
  assert (S1 : (φ Y → ψ Y) → φ Y → ψ Y).
  { exact (Id2_08 (φ Y → ψ Y)). }
  assert (S2 : ∃ z, (φ Y → ψ Y) → (φ Y → ψ z)).
  { 
    pose proof (n9_1 (fun z => (φ Y → ψ Y) → (φ Y → ψ z)) Y) as n9_1.
    now MP n9_1 S1.
  }
  assert (S3 : ∃ x, ∃ z, (φ x → ψ x) → (φ Y → ψ z)).
  { 
    pose proof (n9_1 (fun x => ∃ z, (φ x → ψ x) → (φ Y → ψ z)) Y) as n9_1.
    now MP n9_1 S2.
  }
  assert (S4 : ∀ y, ∃ x, ∃ z, (φ x → ψ x) → (φ y → ψ z)).
  {
    pose proof (n9_13 (fun y => (∃ x, ∃ z, 
      (φ x → ψ x) → (φ y → ψ z))) Y) as n9_13.
    now MP n9_13 S3.
  }
  assert (S5 : ∀ y, ∃ x, (φ x → ψ x) → (∃ z, (φ y → ψ z))).
  { 
    setoid_rewrite -> Impl1_01a in S4.
    setoid_rewrite <- n9_06a in S4.
    now setoid_rewrite <- Impl1_01a in S4.
  }
  assert (S6 : (∃ x, ¬ (φ x → ψ x)) ∨ ∀ y, (∃ z, (φ y → ψ z))).
  {
    setoid_rewrite -> Impl1_01a in S5.
    now setoid_rewrite <- n9_08a in S5.
  }
  assert (S7 : (∃ x, ¬ (φ x → ψ x)) ∨ (∀ y, ¬ (φ y)) ∨ ∃ z, ψ z).
  { 
    setoid_rewrite -> Impl1_01a in S6 at 3.
    now setoid_rewrite <- n9_07a in S6.
  }
  assert (S8 : (∀ x, φ x → ψ x) → (∃ x, φ x) → (∃ x, ψ x)).
  { 
    now rewrite <- n9_01, <- Impl1_01,
    (* TODO: by the text 1st order propositions shouldn't be allowed to appear
    as parameters. Reexamine the proof below *)
            -> (n4_13 (∀ y, ¬ φ y)),
            <- n9_02, <- Impl1_01,
            <- (n4_13 (∃ x, φ x)) in S7.
  }
  exact S8.
Qed.

Theorem n9_23 (φ : Prop → Prop) : (∀ x, φ x) → (∀ x, φ x).
(* NOTE: Original proof uses Id, 9.13, 9.21 to **turn away from the problem of mismatched 
  parameter types**. *)
Proof. 
  set (X := Intro_individual "x").
  pose proof (Id2_08) (φ X) as Id2_08.
  pose proof (n9_13 (fun x => φ x → φ x) X) as n9_13.
  MP n9_13 Id2_08.
  pose proof (n9_21 φ φ) as n9_21.
  now MP n9_21 n9_13.
Qed.

Theorem n9_24 (φ : Prop → Prop) : (∃ x, φ x) → (∃ x, φ x).
(* Original proof uses Id, 9.13, 9.22. Since it's similar as above, we omit the proof,
  but note that this is technically not allowed. *)
Proof. exact (Id2_08 (∃ x, φ x)). Qed.

Theorem n9_25 (P : Prop) (φ : Prop → Prop) : 
  (∀ x, P ∨ φ x) → P ∨ (∀ x, φ x).
Proof.
  pose proof (n9_23 (fun x => P ∨ φ x)) as n9_23.
  now rewrite <- (n9_04 φ P) in n9_23 at 2.
Qed.
(* ******** *)

(* After the setup, we're going to derive the analogues for *1.2 - *1.6. These analogues
  support variables to be replaced by `∀ x, φ x` and `∃ x, φ x` only.
  Should they be derived, we can use theorems in *2 - *5. *)
Theorem n9_3 (φ : Prop → Prop) : 
  (∀ x, φ x) ∨ (∀ x, φ x) → (∀ x, φ x).
Proof.
  (* TOOLS *)
  set (λ P0 Q0 : Prop, eq_to_equiv (P0 → Q0) (¬ P0 ∨ Q0) (Impl1_01 P0 Q0))
    as Impl1_01a.
  set (λ (φ0 : Prop → Prop), eq_to_equiv (¬ ∀ x, φ0 x) (∃ x, ¬ φ0 x)
    (n9_01 φ0)) as n9_01a.
  set (λ (φ0 : Prop → Prop) (P0 : Prop), eq_to_equiv 
    (P0 ∨ ∀ x, φ0 x) (∀ x, P0 ∨ φ0 x) (n9_04 φ0 P0))
    as n9_04a.
  set (λ (φ0 : Prop → Prop) (P0 : Prop), 
    eq_to_equiv ((∃ x, φ0 x) ∨ P0) (∃ x, φ0 x ∨ P0) (n9_05 φ0 P0))
    as n9_05a.
  set (X := Intro_individual "x").
  (* ******** *)
  assert (S1 : φ X ∨ φ X → φ X).
  { apply Taut1_2. }
  assert (S2 : ∃ y, (φ X ∨ φ y) → φ X).
  { 
    pose proof (n9_1 (fun y => (φ X ∨ φ y) → φ X) X) as n9_1.
    now MP n9_1 S1.
  }
  assert (S3 : ∀ x, ∃ y, (φ x ∨ φ y) → φ x).
  {
    pose proof (n9_13 (fun x => ∃ y, (φ x ∨ φ y) → φ x) X) as n9_13.
    now MP n9_13 S2.
  }
  assert (S4 : ∀ x, (φ x ∨ ∀ y, φ y) → φ x).
  {
    setoid_rewrite -> Impl1_01a in S3.
    setoid_rewrite <- n9_05a in S3.
    setoid_rewrite <- n9_01a in S3.
    setoid_rewrite <- n9_04a in S3.
    now setoid_rewrite <- Impl1_01a in S3.
  }
  assert (S5 : (∀ x, (φ x ∨ ∀ y, φ y)) → (∀ x, φ x)).
  { 
    pose proof (n9_21 (fun x => φ x ∨ (∀ y, φ y)) φ) as n9_21.
    now MP n9_21 S4.
  }
  assert (S6 : (∀ x, φ x) ∨ (∀ x, φ x) → (∀ x, φ x)).
  { now rewrite <- n9_03 in S5. }
  exact S6.
Qed.

Theorem n9_31 (φ : Prop → Prop) : ((∃ x, φ x) ∨ (∃ x, φ x)) → (∃ x, φ x).
Proof. 
  (* TOOLS *)
  set (λ P0 Q0 : Prop, eq_to_equiv (P0 → Q0) (¬ P0 ∨ Q0) (Impl1_01 P0 Q0))
    as Impl1_01a.
  set (λ (φ0 : Prop → Prop) (P0 : Prop), 
    eq_to_equiv ((∃ x, φ0 x) ∨ P0) (∃ x, φ0 x ∨ P0) (n9_05 φ0 P0))
    as n9_05a.
  set (X := Intro_individual "X").
  (* ******** *)
  assert (S1 : ∀ y, φ X ∨ φ y → ∃ z, φ z).
  {
    pose proof (n9_11 φ X X) as n9_11. 
    pose proof (n9_13 (fun y => (φ X ∨ φ y) → ∃ z, φ z) X) as n9_13.
    now MP n9_13 n9_11.
  }
  assert (S2 : (∃ y, φ X ∨ φ y) → (∃ z, φ z)).
  {
    setoid_rewrite -> Impl1_01a in S1.
    now rewrite <- n9_03, <- n9_02, <- Impl1_01 in S1.
  }
  assert (S3 : ∀ x, (∃ y, φ x ∨ φ y) → ∃ z, φ z).
  {
    pose proof (n9_13 (fun x => (∃ y, φ x ∨ φ y) → ∃ z, φ z) X) as n9_13.
    now MP n9_13 S2.
  }
  assert (S4 : (∃ x, (∃ y, φ x ∨ φ y)) → (∃ z, φ z)).
  {
    setoid_rewrite -> Impl1_01a in S3.
    now rewrite <- n9_03, <- n9_02, <- Impl1_01 in S3.
  }
  assert (S5 : ((∃ x, φ x) ∨ (∃ y, φ y)) → (∃ x, φ x)).
  {
    setoid_rewrite <- n4_31 in S4.
    setoid_rewrite <- n9_05a in S4.
    now setoid_rewrite <- n9_06 in S4.
  }
  exact S5.
Qed.

Theorem n9_32 (φ : Prop → Prop) (Q : Prop) : Q → (∀ x, φ x) ∨ Q.
Proof. 
  (* TOOLS *)
  set (λ P0 Q0 : Prop, eq_to_equiv (P0 → Q0) (¬ P0 ∨ Q0) (Impl1_01 P0 Q0))
    as Impl1_01a.
  set (λ (φ0 : Prop → Prop) (P0 : Prop), 
    eq_to_equiv ((∀ x, φ0 x) ∨ P0) (∀ x, φ0 x ∨ P0) (n9_03 φ0 P0))
    as n9_03a.
  set (X := Intro_individual "x").
  (* ******** *)
  assert (S1 : Q → φ X ∨ Q).
  { apply Add1_3. }
  assert (S2 : ∀ x, Q → (φ x) ∨ Q).
  {
    pose proof (n9_13 (fun x => Q → (φ x) ∨ Q) X) as n9_13.
    now MP n9_13 S1.
  }
  assert (S3 : Q → ∀ x, φ x ∨ Q).
  { 
    pose proof (n9_25 (¬ Q) (fun x => φ x ∨ Q)) as n9_25.
    setoid_rewrite -> Impl1_01a in S2.
    MP n9_25 S2.
    now rewrite <- Impl1_01 in n9_25.
  }
  assert (S4 : Q → (∀ x, φ x) ∨ Q).
  { now setoid_rewrite <- (n9_03a φ Q) in S3. }
  exact S4.
Qed.
  
Theorem n9_33 (φ : Prop → Prop) (Q : Prop) : Q → (∃ x, φ x) ∨ Q.
Proof. 
  (* TOOLS *)
  set (λ P0 Q0 : Prop, eq_to_equiv (P0 → Q0) (¬ P0 ∨ Q0) (Impl1_01 P0 Q0))
    as Impl1_01a.
  set (λ (φ0 : Prop → Prop) (P0 : Prop), 
    eq_to_equiv ((∀ x, φ0 x) ∨ P0) (∀ x, φ0 x ∨ P0) (n9_03 φ0 P0))
    as n9_03a.
  set (X := Intro_individual "x").
  (* ******** *)
  assert (S1 : Q → φ X ∨ Q).
  { apply Add1_3. }
  assert (S2 : ∃ x, Q → φ x ∨ Q).
  {
    pose proof (n9_1 (fun x => Q → φ x ∨ Q) X) as n9_1.
    now MP n9_1 S1.
  }
  assert (S3 : Q → ∃ x, φ x ∨ Q).
  { 
    setoid_rewrite -> Impl1_01a in S2.
    rewrite <- (n9_06 (fun x => φ x ∨ Q) (¬ Q)) in S2.
    now rewrite <- Impl1_01 in S2.
  }
  assert (S4 : Q → (∃ x, φ x) ∨ Q).
  { now rewrite <- n9_05 in S3. }
  exact S4.
Qed.

Theorem n9_34 (φ : Prop → Prop) (P : Prop) : (∀ x, φ x) → P ∨ (∀ x, φ x).
Proof. 
  (* TOOLS *)
  set (X := Intro_individual "x").
  (* ******** *)
  assert (S1 : φ X → P ∨ φ X).
  { apply Add1_3. }
  assert (S2 : ∀ x, φ x → P ∨ φ x).
  { 
    pose proof (n9_13 (fun x => φ x → P ∨ φ x) X) as n9_13.
    now MP n9_13 S1.
  }
  assert (S3 : (∀ x, φ x) → (∀ x, P ∨ φ x)).
  {
    pose proof (n9_21 φ (fun x => P ∨ φ x)) as n9_21.
    now MP n9_21 S2.
  }
  assert (S4 : (∀ x, φ x) → P ∨ (∀ x, φ x)).
  { now rewrite <- (n9_04 φ P) in S3. }
  exact S4.
Qed.

Theorem n9_35 (φ : Prop → Prop) (P : Prop) : 
  (∃ x, φ x) → P ∨ (∃ x, φ x).
Proof.
  (* TOOLS *)
  set (X := Intro_individual "x").
  (* ******** *)
  assert (S1 : φ X → P ∨ φ X).
  { apply Add1_3. }
  assert (S2 : ∀ x, φ x → P ∨ φ x).
  { 
    pose proof (n9_13 (fun x => φ x → P ∨ φ x) X) as n9_13.
    now MP n9_13 S1.
  }
  assert (S3 : (∃ x, φ x) → (∃ x, P ∨ φ x)).
  {
    pose proof (n9_22 (fun x => φ x) (fun x => P ∨ φ x)) as n9_22.
    now MP n9_22 S2.
  }
  assert (S6 : (∃ x, φ x) → P ∨ (∃ x, φ x)).
  { now rewrite -> Impl1_01, <- n9_06, <- Impl1_01 in S3. }
  exact S6.
Qed.

Theorem n9_36 (φ : Prop → Prop) (P : Prop) : P ∨ (∀ x, φ x) → (∀ x, φ x) ∨ P.
Proof. 
  (* TOOLS *)
  set (X := Intro_individual "x").
  (* ******** *)
  assert (S1 : P ∨ φ X → φ X ∨ P).
  { apply Perm1_4. }
  assert (S2 : (∀ x, (P ∨ φ x)) → ∀ x, (φ x ∨ P)).
  { 
    pose proof (n9_13 (fun x => P ∨ φ x → φ x ∨ P) X) as n9_13.
    MP n9_13 S1.
    pose proof (n9_21 (fun x => P ∨ φ x) (fun x => φ x ∨ P)) as n9_21.
    now MP n9_21 n9_13.
  }
  assert (S3 : P ∨ (∀ x, φ x) → (∀ x, φ x) ∨ P).
  { now rewrite <- (n9_04 φ P), <- (n9_03 φ P) in S2. }
  exact S3.
Qed.

Theorem n9_361 (φ : Prop → Prop) (P : Prop) : (∀ x, φ x) ∨ P → P ∨ (∀ x, φ x).
Proof. 
  (* TOOLS *)
  set (X := Intro_individual "x").
  (* ******** *)
  assert (S1 : φ X ∨ P → P ∨ φ X).
  { apply Perm1_4. }
  assert (S2 : (∀ x, φ x ∨ P) → ∀ x, P ∨ φ x).
  {
    pose proof (n9_13 (fun x => (φ x ∨ P) → (P ∨ φ x)) X) as n9_13.
    MP n9_13 S1.
    pose proof (n9_21 (fun x => φ x ∨ P) (fun x => P ∨ φ x)) as n9_21.
    now MP n9_21 n9_13.
  }
  assert (S3 : (∀ x, φ x) ∨ P → P ∨ (∀ x, φ x)).
  { now rewrite <- n9_03, <- n9_04 in S2. }
  exact S3.
Qed.

Theorem n9_37 (φ : Prop → Prop) (P : Prop) : P ∨ (∃ x, φ x) → (∃ x, φ x) ∨ P.
Proof.
  (* TOOLS *)
  set (X := Intro_individual "x").
  (* ******** *)
  assert (S1 : P ∨ φ X → φ X ∨ P).
  { apply Perm1_4. }
  assert (S2 : (∃ x, (P ∨ φ x)) → ∃ x, (φ x ∨ P)).
  {
    pose proof (n9_13 (fun x => P ∨ φ x → φ x ∨ P) X) as n9_13.
    MP n9_13 S1.
    pose proof (n9_22 (fun x => P ∨ φ x) (fun x => φ x ∨ P)) as n9_22.
    now MP n9_22 n9_13.
  }
  assert (S3 : P ∨ (∃ x, φ x) → (∃ x, φ x) ∨ P).
  { now rewrite <- n9_06, <- n9_05 in S2. }
  exact S3.
Qed.

Theorem n9_371 (φ : Prop → Prop) (P : Prop) : (∃ x, φ x) ∨ P → P ∨ (∃ x, φ x).
Proof. 
  (* TOOLS *)
  set (X := Intro_individual "x").
  (* ******** *)
  assert (S1 : φ X ∨ P → P ∨ φ X).
  { apply Perm1_4. }
  assert (S2 : (∃ x, φ x ∨ P) → ∃ x, P ∨ φ x).
  {
    pose proof (n9_13 (fun x => (φ x ∨ P) → (P ∨ φ x)) X) as n9_13.
    MP n9_13 S1.
    pose proof (n9_22 (fun x => φ x ∨ P) (fun x => P ∨ φ x)) as n9_22.
    now MP n9_22 n9_13.
  }
  assert (S3 : (∃ x, φ x) ∨ P → P ∨ (∃ x, φ x)).
  { now rewrite <- n9_06, <- n9_05 in S2. }
  exact S3.
Qed.

Theorem n9_4 (φ : Prop → Prop) (P Q : Prop) : 
  P ∨ Q ∨ (∀ x, φ x) → Q ∨ P ∨ (∀ x, φ x).
Proof. 
  (* TOOLS *)
  assert (Assoc_Equiv : ∀ P Q R, (P ∨ Q) ∨ R ↔ P ∨ Q ∨ R).
  {
    intros P1 Q1 R1.
    pose proof (n2_32 P1 Q1 R1) as n2_32.
    pose proof (n2_31 P1 Q1 R1) as n2_31.
    Conj_as n2_32 n2_31 C1.
    now Equiv C1.
  }
  set (X := Intro_individual "x").
  (* ******** *)
  assert (S1 : (∀ x, P ∨ (Q ∨ φ x)) → (∀ x, Q ∨ (P ∨ φ x))).
  {
    pose proof (Assoc1_5 P Q (φ X)) as Assoc1_5.
    pose proof (n9_13 (fun x => P ∨ Q ∨ φ x → Q ∨ P ∨ φ x) X) as n9_13.
    MP n9_13 Assoc1_5.
    pose proof (n9_21 (fun x => P ∨ Q ∨ φ x) (fun x => Q ∨ P ∨ φ x)) as n9_21.
    now MP n9_21 n9_13.
  }
  assert (S2 : P ∨ Q ∨ (∀ x, φ x) → Q ∨ P ∨ (∀ x, φ x)).
  {
    repeat setoid_rewrite <- Assoc_Equiv in S1.
    rewrite <- (n9_04 φ (P ∨ Q)), <- (n9_04 φ (Q ∨ P)) in S1.
    pose proof (n2_32 Q P (∀ x, φ x)) as n2_32.
    Syll_as S1 n2_32 S1_1.
    pose proof (n2_31 P Q (∀ x, φ x)) as n2_31.
    Syll_as n2_31 S1_1 S2.
    exact S2.
  }
  exact S2.
Qed.

Theorem n9_401 (φ : Prop → Prop) (P Q : Prop) : 
  P ∨ Q ∨ (∃ x, φ x) → Q ∨ P ∨ (∃ x, φ x).
Proof. 
  (* TOOLS *)
  set (X := Intro_individual "x").
  (* ******** *)
  assert (S1 : (∃ x, P ∨ (Q ∨ φ x)) → (∃ x, Q ∨ (P ∨ φ x))).
  {
    pose proof (Assoc1_5 P Q (φ X)) as Assoc1_5.
    pose proof (n9_13 (fun x => P ∨ Q ∨ φ x → Q ∨ P ∨ φ x) X) as n9_13.
    MP n9_13 Assoc1_5.
    pose proof (n9_22 (fun x => P ∨ Q ∨ φ x) (fun x => Q ∨ P ∨ φ x)) as n9_22.
    now MP n9_22 n9_13.
  }
  assert (S2 : P ∨ Q ∨ (∃ x, φ x) → Q ∨ P ∨ (∃ x, φ x)).
  { now repeat rewrite <- n9_06 in S1. }
  exact S2.
Qed.

Theorem n9_41 (φ : Prop → Prop) (P R : Prop) : 
  P ∨ (∀ x, φ x) ∨ R → (∀ x, φ x) ∨ P ∨ R.
Proof. 
  (* TOOLS *)
  set (X := Intro_individual "x").
  (* ******** *)
  assert (S1 : (∀ x, P ∨ (φ x ∨ R)) → ∀ x, φ x ∨ (P ∨ R)).
  {
    pose proof ((Assoc1_5 P (φ X) R)) as Assoc1_5.
    pose proof (n9_13 (fun x => P ∨ φ x ∨ R → φ x ∨ P ∨ R) X) as n9_13.
    MP n9_13 Assoc1_5.
    pose proof (n9_21 (fun x => P ∨ (φ x ∨ R)) (fun x => φ x ∨ (P ∨ R))) as n9_21.
    now MP n9_21 n9_13.
  }
  assert (S2 : P ∨ (∀ x, φ x) ∨ R → (∀ x, φ x) ∨ P ∨ R).
  {
    rewrite <- n9_04 in S1.
    now repeat rewrite <- n9_03 in S1.
  }
  exact S2.
Qed.

Theorem n9_411 (φ : Prop → Prop) (P R : Prop) : 
  P ∨ (∃ x, φ x) ∨ R → (∃ x, φ x) ∨ P ∨ R.
Proof. 
  (* TOOLS *)
  set (X := Intro_individual "x").
  (* ******** *)
  assert (S1 : (∃ x, P ∨ (φ x ∨ R)) → ∃ x, φ x ∨ (P ∨ R)).
  {
    pose proof (Assoc1_5 P (φ X) R) as Assoc1_5.
    pose proof (n9_13 (fun x => P ∨ φ x ∨ R → φ x ∨ P ∨ R) X) as n9_13.
    MP n9_13 Assoc1_5.
    pose proof (n9_22 (fun x => P ∨ (φ x ∨ R)) (fun x => φ x ∨ (P ∨ R))) as n9_22.
    now MP n9_22 n9_13.
  }
  assert (S2 : P ∨ (∃ x, φ x) ∨ R → (∃ x, φ x) ∨ P ∨ R).
  {
    rewrite <- n9_06 in S1.
    now repeat rewrite <- n9_05 in S1.
  }
  exact S2.
Qed.

Theorem n9_42 (φ : Prop → Prop) (Q R : Prop) : 
  (∀ x, φ x) ∨ Q ∨ R → Q ∨ (∀ x, φ x) ∨ R.
Proof. 
  (* TOOLS *)
  set (X := Intro_individual "x").
  (* ******** *)
  assert (S1 : (∀ x, φ x ∨ (Q ∨ R)) → ∀ x, Q ∨ (φ x ∨ R)).
  {
    pose proof (Assoc1_5 (φ X) Q R) as Assoc1_5.
    pose proof (n9_13 (fun x => φ x ∨ Q ∨ R → Q ∨ φ x ∨ R) X) as n9_13.
    MP n9_13 Assoc1_5.
    pose proof (n9_21 (fun x => φ x ∨ (Q ∨ R)) (fun x => Q ∨ (φ x ∨ R))) as n9_21.
    now MP n9_21 n9_13.
  }
  assert (S2 : (∀ x, φ x) ∨ Q ∨ R → Q ∨ (∀ x, φ x) ∨ R).
  {
    rewrite <- n9_04 in S1.
    now repeat rewrite <- n9_03 in S1.
  }
  exact S2.
Qed.

Theorem n9_421 (φ : Prop → Prop) (Q R : Prop) : 
  (∃ x, φ x) ∨ Q ∨ R → Q ∨ (∃ x, φ x) ∨ R.
Proof. 
  (* TOOLS *)
  set (X := Intro_individual "x").
  (* ******** *)
  assert (S1 : (∃ x, φ x ∨ (Q ∨ R)) → ∃ x, Q ∨ (φ x ∨ R)).
  {
    pose proof (Assoc1_5 (φ X) Q R) as Assoc1_5.
    pose proof (n9_13 (fun x => φ x ∨ Q ∨ R → Q ∨ φ x ∨ R) X) as n9_13.
    MP n9_13 Assoc1_5.
    pose proof (n9_22 (fun x => φ x ∨ (Q ∨ R)) (fun x => Q ∨ (φ x ∨ R))) as n9_22.
    now MP n9_22 n9_13.
  }
  assert (S2 : (∃ x, φ x) ∨ Q ∨ R → Q ∨ (∃ x, φ x) ∨ R).
  {
    rewrite <- n9_06 in S1.
    now repeat rewrite <- n9_05 in S1.
  }
  exact S2.
Qed.

Theorem n9_5 (φ : Prop → Prop) (P Q : Prop) : 
  (P → Q) → ((P ∨ ∀ x, φ x) → (Q ∨ ∀ x, φ x)).
Proof. 
  (* TOOLS *)
  set (λ P0 Q0 : Prop, eq_to_equiv (P0 → Q0) (¬ P0 ∨ Q0) (Impl1_01 P0 Q0))
    as Impl1_01a.
  set (Y := Intro_individual "y").
  (* ******** *)
  assert (S1 : (P → Q) → ((P ∨ φ Y) → (Q ∨ φ Y))).
  { 
    (* While this step is supposed to be `Syll`ed, we show how it can also 
      be done with a `rewrite` on a ↔` relation  *)
    pose proof (Sum1_6 (φ Y) P Q) as Sum1_6.
    now rewrite -> (n4_31 (φ Y) P), -> (n4_31 (φ Y) Q) in Sum1_6.
  }
  assert (S2 : (P → Q) → ∃ x, (P ∨ φ x) → (Q ∨ φ Y)).
  {
    pose proof (n9_1 (fun x => P ∨ φ x → Q ∨ φ Y) Y) as n9_1.
    now Syll_as S1 n9_1 S2.
  }
  assert (S3 : (P → Q) → ∀ y, ∃ x, (P ∨ φ x) → (Q ∨ φ y)).
  { 
    (* *9.04 ignored *)
    pose proof (n9_13 (fun y => ∃ x, P ∨ φ x → Q ∨ φ y) Y) as n9_13.
    now Syll_as S2 n9_13 S3.
  }
  assert (S4 : (P → Q) → (∃ x, ¬ (P ∨ φ x)) ∨ (∀ y, Q ∨ φ y)).
  { 
    setoid_rewrite -> Impl1_01a in S3 at 3.
    now rewrite <- (n9_08 (fun y => Q ∨ φ y) (fun x => ¬ (P ∨ φ x))) in S3.
  }
  assert (S5 : (P → Q) → (∀ x, (P ∨ φ x)) → (∀ y, Q ∨ φ y)).
  { now rewrite <- n9_01, <- Impl1_01 in S4. }
  assert (S6 : (P → Q) → ((P ∨ ∀ x, φ x) → (Q ∨ ∀ x, φ x))).
  { now rewrite <- (n9_04 φ P), <- (n9_04 φ Q) in S5. }
  exact S6.
Qed.

Theorem n9_501 (φ : Prop → Prop) (P Q : Prop) : 
  (P → Q) → (P ∨ ∃ x, φ x) → (Q ∨ ∃ x, φ x).
Proof. 
  (* TOOLS *)
  set (λ P0 Q0 : Prop, eq_to_equiv (P0 → Q0) (¬ P0 ∨ Q0) (Impl1_01 P0 Q0))
    as Impl1_01a.
  set (Y := Intro_individual "y").
  (* ******** *)
  assert (S1 : (P → Q) → ((P ∨ φ Y) → (Q ∨ φ Y))).
  { 
    pose proof (Sum1_6 (φ Y) P Q) as Sum1_6.
    now rewrite -> (n4_31 (φ Y) P), -> (n4_31 (φ Y) Q) in Sum1_6.
  }
  assert (S2 : (P → Q) → ∃ y, (P ∨ φ Y) → (Q ∨ φ y)).
  {
    pose proof (n9_1 (fun y => P ∨ φ Y → Q ∨ φ y) Y) as n9_1.
    now Syll_as S1 n9_1 S2.
  }
  assert (S3 : (P → Q) → ∀ x, ∃ y, (P ∨ φ x) → (Q ∨ φ y)).
  { 
    pose proof (n9_13 (fun x => ∃ y, P ∨ φ x → Q ∨ φ y) Y) as n9_13.
    now Syll_as S2 n9_13 S3.
  }
  assert (S4 : (P → Q) → (∀ x, ¬ (P ∨ φ x)) ∨ (∃ y, Q ∨ φ y)).
  {
    setoid_rewrite -> Impl1_01a in S3 at 3.
    now rewrite <- (n9_07 (fun x => ¬ (P ∨ φ x)) (fun y => Q ∨ φ y)) in S3.
  }
  assert (S5 : (P → Q) → (∃ x, P ∨ φ x) → (∃ y, Q ∨ φ y)).
  { 
    rewrite -> (n4_13 (∀ x, ¬ (P ∨ φ x))) in S4.
    setoid_rewrite <- Impl1_01a in S4.
    rewrite <- n9_02 in S4.
    now rewrite <- (n4_13 (∃ x, P ∨ φ x)) in S4.
  }
  assert (S6 : (P → Q) → (P ∨ ∃ x, φ x) → (Q ∨ ∃ y, φ y)).
  { now repeat rewrite <- n9_06 in S5. }
  exact S6.
Qed.

Theorem n9_51 (φ : Prop → Prop) (P R : Prop) : 
  (P → ∀ x, φ x) → P ∨ R → (∀ x, φ x) ∨ R.
Proof. 
  (* TOOLS *)
  set (λ P0 Q0 : Prop, eq_to_equiv (P0 → Q0) (¬ P0 ∨ Q0) (Impl1_01 P0 Q0))
    as Impl1_01a.
  set (X := Intro_individual "x").
  (* ******** *)
  assert (S1 : (P → φ X) → ((P ∨ R) → (φ X ∨ R))).
  { 
    pose proof (Sum1_6 R P (φ X)) as Sum1_6.
    now rewrite -> (n4_31 R P), -> (n4_31 R (φ X)) in Sum1_6.
  }
  assert (S2 : (∀ x, P → φ x) → (∀ x, (P ∨ R) → (φ x ∨ R))).
  { 
    pose proof (n9_13 (fun x => (P → φ x) → P ∨ R → φ x ∨ R) X) as n9_13.
    MP n9_13 S1.
    pose proof (n9_21 (fun x => (P → φ x)) (fun x => P ∨ R → φ x ∨ R))
      as n9_21.
    now MP n9_21 n9_13.
  }
  assert (S3 : (P → ∀ x, φ x) → P ∨ R → (∀ x, φ x) ∨ R).
  { 
    setoid_rewrite -> Impl1_01a in S2 at 2.
    rewrite <- (n9_04 φ (¬ P)) in S2.
    setoid_rewrite <- Impl1_01a in S2.
    setoid_rewrite -> Impl1_01a in S2 at 3.
    setoid_rewrite -> n4_31 in S2.
    rewrite <- (n9_03 (fun x => φ x ∨ R) (¬ (P ∨ R))),
            -> n4_31 in S2.
    setoid_rewrite <- Impl1_01a in S2.
    now rewrite <- (n9_03 φ R) in S2.
  }
  exact S3.
Qed.

Theorem n9_511 (φ : Prop → Prop) (P R : Prop) : 
  (P → ∃ x, φ x) → P ∨ R → (∃ x, φ x) ∨ R.
Proof. 
  (* TOOLS *)
  set (λ P0 Q0 : Prop, eq_to_equiv (P0 → Q0) (¬ P0 ∨ Q0) (Impl1_01 P0 Q0))
    as Impl1_01a.
  set (X := Intro_individual "x").
  (* ******** *)
  assert (S1 : (P → φ X) → ((P ∨ R) → (φ X ∨ R))).
  { 
    pose proof (Sum1_6 R P (φ X)) as Sum1_6.
    now rewrite -> (n4_31 R P), -> (n4_31 R (φ X)) in Sum1_6.
  }
  assert (S2 : (∃ x, P → φ x) → (∃ x, (P ∨ R) → (φ x ∨ R))).
  {
    pose proof (n9_1 (fun x => P ∨ R → φ x ∨ R) X) as n9_1.
    Syll_as S1 n9_1 Sy1.
    pose proof (n9_13 (fun y => (P → φ y) → (∃ x, (P ∨ R) → (φ x ∨ R))) X)
      as n9_13.
    MP n9_13 Sy1.
    setoid_rewrite -> Impl1_01a in n9_13.
    now rewrite <- n9_03, <- n9_02, <- Impl1_01 in n9_13.
  }
  assert (S3 : (P → ∃ x, φ x) → P ∨ R → (∃ x, φ x) ∨ R).
  {
    setoid_rewrite -> Impl1_01a in S2 at 2.
    setoid_rewrite -> Impl1_01a in S2 at 3.
    rewrite <- n9_06, <- n9_06, <- n9_05 in S2.
    now setoid_rewrite <- Impl1_01a in S2.
  }
  exact S3.
Qed.

Theorem n9_52 (φ : Prop → Prop) (Q R : Prop) :
  ((∀ x, φ x) → Q) → ((∀ x, φ x) ∨ R) → (Q ∨ R).
Proof.
  (* TOOLS *)
  set (λ P0 Q0 : Prop, eq_to_equiv (P0 → Q0) (¬ P0 ∨ Q0) (Impl1_01 P0 Q0))
    as Impl1_01a.
  set (X := Intro_individual "x").
  (* ******** *)
  assert (S1 : (φ X → Q) → ((φ X ∨ R) → (Q ∨ R))).
  { 
    pose proof (Sum1_6 R (φ X) Q) as Sum1_6.
    now rewrite -> (n4_31 R Q), -> (n4_31 R (φ X)) in Sum1_6.
  }
  assert (S2 : (∃ x, (φ x → Q)) → (∃ x, (φ x ∨ R) → (Q ∨ R))).
  { 
    pose proof (n9_13 (fun x => (φ x → Q) → ((φ x ∨ R) → (Q ∨ R))) X) as n9_13.
    MP n9_13 S1.
    pose proof (n9_22 (fun x => φ x → Q) (fun x => φ x ∨ R → Q ∨ R)) as n9_22.
    now MP n9_22 n9_13.
  }
  assert (S3 : ((∀ x, φ x) → Q) → (∀ x, φ x ∨ R) → (Q ∨ R)).
  { 
    setoid_rewrite -> Impl1_01a in S2 at 2.
    setoid_rewrite -> Impl1_01a in S2 at 3.
    now repeat rewrite <- n9_05, <- n9_01, <- Impl1_01 in S2.
  }
  assert (S4 : ((∀ x, φ x) → Q) → ((∀ x, φ x) ∨ R) → (Q ∨ R)).
  { now rewrite <- n9_03 in S3. }
  exact S4.
Qed.

Theorem n9_521 (φ : Prop → Prop) (Q R : Prop) :
  ((∃ x, φ x) → Q) → (∃ x, φ x) ∨ R → Q ∨ R.
Proof. 
  (* TOOLS *)
  set (λ P0 Q0 : Prop, eq_to_equiv (P0 → Q0) (¬ P0 ∨ Q0) (Impl1_01 P0 Q0))
    as Impl1_01a.
  set (X := Intro_individual "x").
  (* ******** *)
  assert (S1 : (φ X → Q) → ((φ X ∨ R) → (Q ∨ R))).
  { 
    pose proof (Sum1_6 R (φ X) Q) as Sum1_6.
    now rewrite -> (n4_31 R Q), ->(n4_31 R (φ X)) in Sum1_6.
  }
  assert (S2 : (∀ x, (φ x → Q)) → (∀ x, (φ x ∨ R) → (Q ∨ R))).
  { 
    pose proof (n9_13 (fun x => (φ x → Q) → ((φ x ∨ R) → (Q ∨ R))) X) as n9_13.
    MP n9_13 S1.
    pose proof (n9_21 (fun x => φ x → Q) (fun x => φ x ∨ R → Q ∨ R)) as n9_21.
    now MP n9_21 n9_13.
  }
  assert (S3 : ((∃ x, φ x) → Q) → (∃ x, φ x) ∨ R → Q ∨ R).
  {
    setoid_rewrite -> Impl1_01a in S2 at 2.
    setoid_rewrite -> Impl1_01a in S2 at 3.
    repeat rewrite <- n9_03 in S2.
    repeat rewrite <- n9_02 in S2.
    repeat rewrite <- Impl1_01 in S2.
    now rewrite <- n9_05 in S2.
  }
  exact S3.
Qed.

(* Thm 9.6: `∀ x, φ x`, `¬ (∀ x, φ x)`, `∃ x, φ x`, `¬ (∃ x, φ x)` are of the same type. From *9.131, (7) and (8) *)
Theorem n9_6 (φ : Prop → Prop) :
  IsSameType.t (∀ x, φ x) (¬ (∀ x, φ x))
  ∧ IsSameType.t (¬ (∀ x, φ x)) (∃ x, φ x)
  ∧ IsSameType.t (∃ x, φ x) (¬ (∃ x, φ x)).
Proof.
  repeat split.
  - now apply IsSameType.NProp.
  - admit. (* This should be done by some transitivity relations on IsSameType *)
  - now apply IsSameType.NProp.
Admitted.

(* Thm 9.61: If `φ x^` and `ψ x^` are elementary functions of the same type, there is a function `φ x^ ∨ ψ x^`. *)
Theorem n9_61 (φ ψ : Prop → Prop) `{is_efunc φ} `{is_efunc ψ} (X0 : Prop) : 
  IsSameType.t (φ X0) (ψ X0)
  → (φ X0 ∨ ψ X0).
Proof.
Admitted.

(* Thm 9.62 : If `φ(x^, y^)` and `ψ z^` are elementary functions, and the x-argument to `φ` is of the same type as the argument of `ψ`, there are functions `(∀ y, φ(x^, y)) ∨ ψ x^`, `(∃ y, φ (x^, y) ∨ φ x^)` *)
Theorem n9_62 (φ : Prop → Prop → Prop) (ψ : Prop → Prop) (X Z : Prop) :
  IsSameType.t X Z 
  → (((∀ y, φ X y) ∨ ψ Z) 
  (* The `∧` below actually stands for the extra proposition *)
  ∧ ((∃ y, φ X y) ∨ ψ Z)).
Proof.
Admitted.

(* This is a very rough simulation of the theorem in natural language *)
(* Thm 9.63 : If `φ(x^, y^)` and `ψ(x^, y^)` are elementary functions of the same type, there are functions `(∀ y, φ(x^, y) ∨ ∀ z, ψ(x^, z)), etc.` *)
(* We currently ignore the restriction that they are efuncs since is_efunc is bugged *)
Theorem n9_63 (φ ψ : Prop → Prop → Prop) (X0 Y0 : Prop) :
  IsSameType.t (φ X0 Y0) (ψ X0 Y0)
  → ((∀ y, φ X0 y) ∨ (∀ z, ψ X0 z)).
Proof.
Admitted.
