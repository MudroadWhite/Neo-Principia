Require Import PM.pm.lib.
Require Import PM.pm.ch1.
Require Import PM.pm.ch2.
Require Import PM.pm.ch3.
Require Import PM.pm.ch4.
Require Import PM.pm.ch5.
Require Import PM.pm.ch10.
Require Import PM.pm.ch11.
Require Import PM.pm.ch12.

(* 
TODO: 
- investigate a convenient `∧` construction
- replace ~= with the /= unicode symbol
- fill in missing proofs. I believe that all admitted places are actually provable
*)

(* Experimental: provide variated theorems to be used in this chapter
  In the future, we might want to change `Prop → Prop` into `A → Prop`
  for common theorems starting from ch1 *)
Definition n10_11_pred (Y : Predicate 1) (φ : Predicate 1 → Prop)
  : φ Y → ∀ x, φ x.
Admitted.

Definition n10_21_pred (φ : Predicate 1 → Prop) (P : Prop) :
  (∀ x : Predicate 1, P → φ x) ↔ (P → (∀ x : Predicate 1, φ x)).
Admitted.

Definition n10_22_pred (φ ψ : Predicate 1 → Prop) :
  (∀ x : Predicate 1, φ x ∧ ψ x)
  ↔ (∀ x : Predicate 1, φ x) ∧ ∀ x : Predicate 1, ψ x.
Admitted.

Definition n10_23_pred (φ : Predicate 1 → Prop) (P : Prop) :
  (∀ x : Predicate 1, φ x → P) ↔ ((∃ x : Predicate 1, φ x) → P).
Admitted.

Definition n10_3_pred (φ ψ χ : Predicate 1 → Prop) :
  (∀ x : Predicate 1, φ x → ψ x) ∧ (∀ x : Predicate 1, ψ x → χ x)
  → ∀ x : Predicate 1, φ x → χ x.
Admitted.

Definition n10_32_pred (φ ψ : Predicate 1 → Prop) :
  (∀ x : Predicate 1, φ x ↔ ψ x) ↔ ∀ x : Predicate 1, ψ x ↔ φ x.
Admitted.

(* 
p.165: `φ x^` without a `!` will be a function with order unspecified, and this kind of function is
forbidden to be a quantified variable
*)
Definition n13_01 (X Y : Prop) : 
  (X = Y) = (∀ φ : Predicate 1, (φ X) → (φ Y)).
Admitted.

Definition n13_02 (X Y : Prop) :
  (¬ (X = Y)) = ¬ (X = Y).
Admitted.

Definition n13_03 (X Y Z : Prop) :
  ((X = Y) ∧ (Y = Z)) = ((X = Y) ∧ (Y = Z)).
Admitted.

Open Scope single_app_impl.

Theorem n13_1 (X Y : Prop) : 
  (X = Y) ↔
    (∀ φ : Predicate 1, (φ X) → (φ Y)).
Proof.
  pose proof (n4_2 (X = Y)) as n4_2.
  now rewrite -> n13_01 in n4_2 at 2.
  (* n10_02 ignored: I think this is unrelated *)
Qed.

Theorem n13_101 (X Y : Prop) (ψ : Prop → Prop) :
  (X = Y) → (ψ X → ψ Y).
Proof.
  assert (S1 : (∃ φ : Predicate 1, (ψ X ↔ φ X) ∧ (ψ Y ↔ φ Y))).
  {
    (* TODO: This proposition is provable if we manually introduce a 
    predicative placeholder to instantiate n12_1 *)
    pose proof n12_1 as n12_1a.
    pose proof n12_1 as n12_1b.
    admit.
  }
  assert (S2 : (X = Y) → ∀ φ : Predicate 1, φ X → φ Y).
  {
    apply n13_1.
  }
  assert (S3 : (X = Y) → (∀ φ : Predicate 1, 
    ((ψ X ↔ φ X) ∧ (ψ Y ↔ φ Y)) → (ψ X → ψ Y))).
  {
    destruct S1 as [φ HS1].
    destruct HS1 as [HS1_1 HS1_2].
    pose proof (n4_84 (ψ X) (φ X) (φ Y)) as n4_84.
    MP n4_84 HS1_1.
    pose proof (n4_85 (ψ Y) (φ Y) (ψ X)) as n4_85.
    MP n4_84 HS1_2.
    rewrite -> n4_84 in n4_85.
    (* TODO: use varied generalizations correctly to finish the proof*)
    (* setoid_rewrite <- n4_85 in S2. *)
    admit.
  }
  assert (S4 : (X = Y) → (∃ φ : Predicate 1, 
    ((ψ X ↔ φ X) ∧ (ψ Y ↔ φ Y))) → (ψ X → ψ Y)).
  {
    now rewrite -> n10_23_pred in S3.
  }
  assert (S5 : (X = Y) → (ψ X → ψ Y)).
  {
    intro Hp.
    pose proof (S4 Hp) as S4.
    clear S2 S3.
    now MP S4 S1.
  }
  exact S5.
Admitted.

Open Scope single_app_equiv.

Theorem n13_11 (X Y : Prop) :
  (X = Y) ↔
    (∀ φ : Predicate 1, (φ X) ↔ (φ Y)).
Proof.
  (* TOOLS *)
  set (Iφ := Intro_pred "φ" 1).
  (* ******** *)
  assert (S1 : (∀ φ : Predicate 1, φ X ↔ φ Y)
    → (∀ φ : Predicate 1, φ X → φ Y)).
  {
    (* TODO: make a matrix and generalize it; eventually 
      apply n10_22 *)
    pose proof n10_22_pred as n10_22.
    admit.
  }
  assert (S2 : (∀ φ : Predicate 1, φ X ↔ φ Y)
    → (X = Y)).
  { now rewrite <- n13_1 in S1. }
  assert (S3 : (X = Y) → (Iφ X → Iφ Y)).
  { apply n13_101. }
  assert (S4 : (X = Y) → ((¬ Iφ X) → (¬ Iφ Y))).
  {
    (* n1_7 ignored *)
    admit.
  }
  assert (S5 : (X = Y) → (Iφ Y → Iφ X)).
  {
    pose proof (Transp2_17 (Iφ Y) (Iφ X)) as Transp2_17.
    now Syll S4 Transp2_17 S5.
  }
  assert (S6 : (X = Y) → (Iφ X ↔ Iφ Y)).
  {
    pose proof (Comp3_43 (X = Y) (Iφ X → Iφ Y) (Iφ Y → Iφ X))
      as Comp3_43.
    assert (C1 : (X = Y → Iφ X → Iφ Y) ∧ (X = Y → Iφ Y → Iφ X)).
    { 
      clear S1 S2 S4.
      now Conj S3 S5 C1.
    }
    MP Comp3_43 C1.
    now rewrite <-Equiv4_01 in Comp3_43.
  }
  assert (S7 : (X = Y) → (∀ φ : Predicate 1, φ X ↔ φ Y)).
  {
    pose proof (n10_11_pred Iφ (fun P =>
      X = Y → P X ↔ P Y)) as n10_11.
    MP n10_11 S6.
    pose proof (n10_21_pred (fun P =>
      P X ↔ P Y) (X = Y)) as n10_21.
    now rewrite -> n10_21 in n10_11.
  }
  assert (S8 : (X = Y) ↔ (∀ φ : Predicate 1, (φ X) ↔ (φ Y))).
  {
    clear S1 S3 S4 S5 S6. move S2 after S7.
    assert (C1 : (X = Y → ∀ φ : Predicate 1, φ X ↔ φ Y)
      ∧ ((∀ φ : Predicate 1, φ X ↔ φ Y) → X = Y)).
    { now Conj S7 S2 C1. }
    now Equiv C1.
  }
  exact S8.
Admitted.

Theorem n13_12 (X Y : Prop) (ψ : Prop → Prop) :
  (X = Y) → (ψ X ↔ ψ Y).
Proof.
  assert (S1 : (X = Y) → ((ψ X → ψ Y) ∧ ((¬ ψ X) → (¬ ψ Y)))).
  {
    pose proof n13_101 as n13_101.
    pose proof Comp3_43 as Comp3_43.
    (* Same as n13_11.S4, and this is currently under investigation *)
    admit.
  }
  assert (S2 : (X = Y) → (ψ X ↔ ψ Y)).
  {
    intro Hp.
    pose proof (S1 Hp) as S1.
    destruct S1 as [S1_1l S1_1r].
    pose proof (Transp2_17 (ψ Y) (ψ X)) as Transp2_17.
    MP Transp2_17 S1_1r.
    assert (C1 : (ψ X → ψ Y) ∧ (ψ Y → ψ X)).
    { now Conj S1_1l Transp2_17 C1. }
    now Equiv C1.
  }
  exact S2.
Admitted.

Theorem n13_13 (X Y : Prop) (ψ : Prop → Prop) :
  ((ψ X) ∧ (X = Y)) → ψ Y.
Proof.
  pose proof (n13_101 X Y ψ) as n13_101.
  pose proof (Comm2_04 (X = Y) (ψ X) (ψ Y)) as Comm2_04.
  MP Comm2_04 n13_101.
  pose proof (Imp3_31 (ψ X) (X = Y) (ψ Y)) as Imp3_31.
  now MP Imp3_31 Comm2_04.
Qed.

Theorem n13_14 (X Y : Prop) (ψ : Prop → Prop) :
  (ψ X) ∧ (¬ ψ Y) → (¬ (X = Y)).
Proof.
  pose proof (n13_13 X Y ψ) as n13_13.
  pose proof (n4_14 (ψ X) (X = Y) (ψ Y)) as n4_14.
  now rewrite -> n4_14 in n13_13.
Qed.

Theorem n13_15 (X : Prop) : X = X.
Proof.
  pose proof (Id2_08 X) as Id2_08.
  pose proof (n10_11_pred
    (fun x => x)
    (fun P => P X → P X)
  ) as n10_11.
  MP n10_11 Id2_08.
  pose proof (n13_1 X X) as n13_1.
  now rewrite <- n13_1 in n10_11.
Qed.

Theorem n13_16 (X Y : Prop) : (X = Y) ↔ (Y = X).
Proof.
  pose proof (n13_11 X Y) as n13_11a.
  rewrite -> n10_32_pred in n13_11a.
  now rewrite <- n13_11 in n13_11a.
Qed.

(* A theorem that is shown how the related propositions are 
being used explicitly in original text *)
Theorem n13_17 (X Y Z : Prop) :
  ((X = Y) ∧ (Y = Z)) → (X = Z).
Proof.
  assert (S1 : ((X = Y) ∧ (Y = Z)) 
    → ((∀ φ : Predicate 1, φ X → φ Y) 
      ∧ (∀ φ : Predicate 1, φ Y → φ Z))).
  {
    pose proof n13_1 as n13_1.
    (* We currently didn't allow `∧` yet *)
    admit.
  }
  assert (S2 : ((X = Y) ∧ (Y = Z)) 
    → (∀ φ : Predicate 1, φ X → φ Z)).
  {
    intros Hp.
    pose proof (S1 Hp) as S1.
    pose proof (n10_3_pred
      (fun P => P X) (fun P => P Y) (fun P => P Z)) as n10_3_pred.
    now MP n10_3_pred S1.
  }
  assert (S3 : ((X = Y) ∧ (Y = Z)) → (X = Z)).
  { now rewrite <- n13_01 in S2. }
  exact S3.
Admitted.

Theorem n13_171 (X Y Z : Prop) :
  ((X = Y) ∧ (X = Z)) → (Y = Z).
Proof.
  pose proof (n13_17 Y X Z) as n13_17.
  now rewrite -> n13_16 in n13_17 at 1.
Qed.

Theorem n13_172 (X Y Z : Prop) :
  ((Y = X) ∧ (Z = X)) → (Y = Z).
Proof.
  pose proof (n13_17 Y X Z) as n13_17.
  pose proof (n13_16 X Z) as n13_16.
  now rewrite -> n13_16 in n13_17.
Qed.

Theorem n13_18 (X Y Z : Prop) :
  ((X = Y) ∧ (¬ (X = Z))) → ¬ (Y = Z).
Proof.
  pose proof (n13_17 X Y Z) as n13_17.
  pose proof (n4_14 (X = Y) (Y = Z) (X = Z)) as n4_14.
  now rewrite -> n4_14 in n13_17.
Qed.

Theorem n13_181 (X Y Z : Prop) :
  ((X = Y) ∧ (¬ (Y = Z))) → ¬ (X = Z).
Proof.
  pose proof (n13_171 X Y Z) as n13_171.
  now rewrite -> n4_14 in n13_171.
Qed.

Theorem n13_182 (X Y Z : Prop) :
  (X = Y) → ((Z = X) ↔ (Z = Y)).
Proof.
  pose proof (n13_17 X Y Z) as n13_17.
  pose proof (n13_172 X Y Z) as n13_172.
  pose proof (n13_16 Y Z) as n13_16a.
  pose proof (n13_16 X Z) as n13_16b.
  pose proof (n13_16 Y X) as n13_16c.
  rewrite -> n13_16a, -> n13_16b in n13_17.
  rewrite -> n13_16a, -> n13_16c in n13_172.
  pose proof (Exp3_3 (X = Y) (Z = Y) (Z = X)) as Exp3_3a.
  MP Exp3_3a n13_17.
  pose proof (Exp3_3 (X = Y) (Z = X) (Z = Y)) as Exp3_3b.
  MP Exp3_3b n13_172.
  pose proof (Comp3_43
    (X = Y) (Z = X → Z = Y) (Z = Y → Z = X)
  ) as Comp3_43.
  assert (C1 : (X = Y → Z = X → Z = Y) ∧ (X = Y → Z = Y → Z = X)).
  {
    clear n13_17 n13_172 n13_16a n13_16b n13_16c.
    now Conj Exp3_3a Exp3_3b C1.
  }
  MP Comp3_43 C1.
  now rewrite <- Equiv4_01 in Comp3_43.
Qed.

Open Scope single_app_equiv.

Theorem n13_183 (X Y : Prop) :
  (X = Y) ↔ ((X = z) <[- z -]> (z = Y)).
Proof.
  (* TOOLS *)
  set (Z := Individual "z").
  (* ******** *)
  assert (S1 : (X = Y) → ((X = z) <[- z -]> (z = Y))).
  {
    pose proof (n13_182 X Y Z) as n13_182.
    pose proof (n13_16 X Z) as n13_16.
    rewrite <- n13_16 in n13_182.
    pose proof (n10_11 Z (fun z =>
      X = Y → X = z ↔ z = Y)) as n10_11.
    MP n10_11 n13_182.
    pose proof (n10_21 (fun z => X = z ↔ z = Y) (X = Y)) as n10_21.
    now rewrite -> n10_21 in n10_11.
  }
  assert (S2 : ((X = z) <[- z -]> (z = Y)) 
    → ((X = X) → (X = Y))).
  {
    pose proof (n10_1 (fun z => X = z ↔ z = Y) X) as n10_1.
    (* Simplification *)
    intro Hp.
    pose proof (n10_1 Hp) as n10_1.
    now destruct n10_1.
  }
  assert (S3 : ((X = z) <[- z -]> (z = Y))  → (X = Y)).
  {
    (* Simplification *)
    intro Hp.
    pose proof (S2 Hp) as S2.
    (* This seems to be a very exceptional use of *13_15 :
    it is being used as a term being applied not a theorem 
    to be applied *)
    pose proof (n13_15 X) as n13_15.
    now MP S2 n13_15.
  }
  assert (S4 : (X = Y) ↔ ((X = z) <[- z -]> (z = Y))).
  {
    assert (C1 : (X = Y → ∀ z : Prop, X = z ↔ z = Y)
      ∧ ((∀ z : Prop, X = z ↔ z = Y) → X = Y)).
    { clear S2. now Conj S1 S3 C1. }
    now Equiv C1.
  }
  exact S4.
Qed.

Theorem n13_19 (X : Prop) : ∃ y, y = X.
Proof.
  pose proof (n13_15 X) as n13_15.
  pose proof (n10_24 (fun y => y = X) X) as n10_24.
  now MP n10_24 n13_15.
Qed.

Theorem n13_191 (X : Prop) (φ : Prop → Prop) :
  ((y = X) -[ y ]> φ y) ↔ φ X.
Proof.
  (* TOOLS *)
  set (Y := Individual "y").
  (* ******** *)
  assert (S1 : ((y = X) -[ y ]> φ y) → ((X = X) → (φ X))).
  { exact (n10_1 (fun y => y = X → φ y) X). }
  assert (S2 : ((y = X) -[ y ]> φ y) → φ X).
  {
    pose proof (n13_15 X) as n13_15.
    (* Simplification *)
    intro Hp.
    pose proof (S1 Hp) as S1.
    now MP S1 n13_15.
  }
  assert (S3 : (Y = X) → (φ X → φ Y)).
  {
    pose proof (n13_12 X Y φ) as n13_12.
    pose proof (n13_16 X Y) as n13_16.
    rewrite -> n13_16 in n13_12.
    (* Simplification *)
    intro Hp.
    pose proof (n13_12 Hp) as n13_12.
    now destruct n13_12.
  }
  assert (S4 : φ X → ((Y = X) → φ Y)).
  {
    pose proof (Comm2_04 (Y = X) (φ X) (φ Y)) as Comm2_04.
    now MP Comm2_04 S3.
  }
  assert (S5 : φ X → ((y = X) -[ y ]> φ y)).
  {
    pose proof (n10_11 Y (fun y =>
      φ X → y = X → φ y)) as n10_11.
    MP n10_11 S4.
    now rewrite -> n10_21 in n10_11.
  }
  assert (S6 : ((y = X) -[ y ]> φ y) ↔ φ X).
  {
    clear S1 S3 S4.
    Conj S2 S5 C1.
    now Equiv C1.
  }
  exact S6.
Qed.

Theorem n13_192 (B : Prop) (ψ : Prop → Prop) :
  (∃ c, ((x = B) <[- x -]> (x = c)) ∧ ψ c) ↔ ψ B.
Proof.
  (* TOOLS *)
  set (X := Individual "x").
  set (C := Individual "c").
  (* ******** *)
  assert (S1 : ψ B → (((x = B) <[- x -]> (x = B)) ∧ (ψ B))).
  {
    pose proof (n4_2 (X = B)) as n4_2.
    pose proof (n10_11 X (fun x => x = B ↔ x = B)) as n10_11.
    MP n10_11 n4_2.
    pose proof (n3_2 (∀ x, x = B ↔ x = B) (ψ B)) as n3_2.
    now MP n3_2 n10_11.
  }
  assert (S2 : ψ B → (∃ c, ((x = B) <[- x -]> (x = c)) ∧ ψ c)).
  {
    pose proof (n10_24 (fun c =>
      ( x = B<[-x-]>x = c ) ∧ ψ c) B) as n10_24.
    now Syll S1 n10_24 S2.
  }
  assert (S3 : ((x = B <[-x-]> x = C) ∧ (ψ C)) 
    → (((B = B) ↔ (B = C)) ∧ ψ C)).
  {
    pose proof (n10_1 (fun x => (x = B) ↔ (x = C)) B) as n10_1.
    pose proof (Fact3_45 (∀ x : Prop, x = B ↔ x = C) (B = B ↔ B = C)
      (ψ C)) as Fact3_45.
    now MP Fact3_45 n10_1.
  }
  assert (S4 : ((x = B <[-x-]> x = C) ∧ (ψ C)) 
    → ((B = C) ∧ (ψ C))).
  {
    pose proof (n5_501 (B = B) (B = C)) as n5_501.
    pose proof (n13_15 B) as n13_15.
    MP n5_501 n13_15.
    now rewrite <- n5_501 in S3.
  }
  assert (S5 : ((x = B <[-x-]> x = C) ∧ (ψ C)) → ψ B).
  {
    pose proof (n13_13 C B ψ) as n13_13.
    pose proof (n13_16 B C) as n13_16.
    rewrite <- n13_16 in n13_13.
    rewrite -> n4_3 in n13_13.
    now Syll S4 n13_13 S5.
  }
  assert (S6 : (∃ c, ((x = B <[-x-]> x = c) ∧ ψ c)) → ψ B).
  {
    pose proof (n10_11 C (fun c =>
      (∀ x, x = B ↔ x = c) ∧ ψ c → ψ B)) 
      as n10_11.
    MP n10_11 S5.
    pose proof (n10_23 (fun x =>
      (∀ x0, x0 = B ↔ x0 = x) ∧ ψ x) (ψ B)) as n10_23.
    now rewrite -> n10_23 in n10_11.
  }
  assert (S7 : (∃ c, ((x = B) <[- x -]> (x = c)) ∧ ψ c) ↔ ψ B).
  {
    clear S1 S3 S4 S5.
    move S2 after S6.
    Conj S6 S2 C1.
    now Equiv C1.
  }
  exact S7.
Qed.

Theorem n13_193 (X Y : Prop) (φ : Prop → Prop) :
  (φ X ∧ (X = Y)) ↔ (φ Y ∧ (X = Y)).
Proof.
  assert (S1 : (φ X ∧ (X = Y) → (X = Y))).
  { apply Simp3_27. }
  assert (S2 : (φ X ∧ (X = Y) → φ Y)).
  { apply n13_13. }
  assert (S3 : (φ X ∧ (X = Y)) → (φ Y ∧ (X = Y))).
  {
    move S1 after S2.
    Conj S2 S1 C1.
    pose proof (Comp3_43 (φ X ∧ (X = Y)) (φ Y) (X = Y)) as Comp3_43.
    now MP Comp3_43 C1.
  }
  assert (S4 : (φ Y ∧ (X = Y)) → (φ Y ∧ (Y = X))).
  {
    pose proof (n13_16 X Y) as n13_16.
    destruct n13_16 as [n13_16l _].
    pose proof (Fact3_45 (X = Y) (Y = X) (φ Y)) as Fact3_45.
    MP Fact3_45 n13_16l.
    pose proof (n4_3 (φ Y) (X = Y)) as n4_3a.
    pose proof (n4_3 (φ Y) (Y = X)) as n4_3b.
    now rewrite <- n4_3a, <- n4_3b in Fact3_45.
  }
  assert (S5 : (φ Y ∧ (X = Y)) → (φ X ∧ (Y = X))).
  {
    (* For this kind of substitution we have to rely on some theorems... which
    is different from original treatment *)
    pose proof (n10_11 X (fun x => φ x ∧ x = Y → φ Y ∧ x = Y)) as n10_11a.
    MP n10_11a S3.
    (* This might not be technically allowed *)
    pose proof (n10_11 Y (fun y => ∀ x, φ x ∧ x = y → φ y ∧ x = y)) as n10_11b.
    MP n10_11b n10_11a.
    pose proof (n10_11b X Y) as n10_11c.
    pose proof (n13_16 X Y) as n13_16.
    now rewrite <- n13_16 in n10_11c at 1.
  }
  assert (S6 : (φ Y ∧ (X = Y)) → (φ X ∧ (X = Y))).
  {
    pose proof (n13_16 X Y) as n13_16.
    (* Fact ignored *)
    now rewrite <- n13_16 in S5.
  }
  assert (S7 : (φ X ∧ (X = Y)) ↔ (φ Y ∧ (X = Y))).
  {
    clear S1 S2 S4 S5.
    Conj S3 S6 C1.
    now Equiv C1.
  }
  exact S7.
Qed.

Theorem n13_194 (X Y : Prop) (φ : Prop → Prop) :
  (φ X ∧ (X = Y)) ↔ (φ X ∧ φ Y ∧ (X = Y)).
Proof.
  pose proof (n13_13 X Y φ) as n13_13.
  pose proof (n4_71 (φ X ∧ (X = Y)) (φ Y)) as n4_71.
  rewrite -> n4_71 in n13_13.
  rewrite -> n4_32 in n13_13.
  pose proof (n4_3 (X = Y) (φ Y)) as n4_3.
  now rewrite -> n4_3 in n13_13.
Qed.

Theorem n13_195 (X : Prop) (φ : Prop → Prop) : 
  (∃ y, (y = X) ∧ φ y) ↔ φ X.
Proof.
  assert (S1 : φ X → ((X = X) ∧ (φ X))).
  {
    pose proof (n3_2 (X = X) (φ X)) as n3_2.
    pose proof (n13_15 X) as n13_15.
    now MP n3_2 n13_15.
  }
  assert (S2 : φ X → (∃ y, (y = X) ∧ φ y)).
  {
    pose proof (n10_24 (fun y => y = X ∧ φ y) X) as n10_24.
    now Syll S1 n10_24 S2.
  }
  assert (S3 : ∀ y, ((y = X) ∧ φ y) → φ X).
  {
    pose proof (n13_13 X X φ) as n13_13.
    rewrite -> n4_3 in n13_13.
    pose proof (n10_11 X (fun y => y = X ∧ φ y → φ X)) as n10_11.
    now MP n10_11 n13_13.
  }
  assert (S4 : (∃ y, (y = X) ∧ φ y) → φ X).
  { now rewrite -> n10_23 in S3. }
  assert (S5 : (∃ y, (y = X) ∧ φ y) ↔ φ X).
  {
    clear S1 S3.
    move S2 after S4.
    Conj S4 S2 C1.
    now Equiv C1.
  }
  exact S5.
Qed.

Theorem n13_196 (X : Prop) (φ : Prop → Prop) : 
  (¬ φ X) ↔ (φ y -[ y ]> (¬ (y = X))).
Proof.
  pose proof (n13_195 X φ) as n13_195.
  rewrite -> Transp4_11 in n13_195.
  setoid_rewrite -> n4_3 in n13_195 at 2.
  rewrite -> n10_51 in n13_195.
  now symmetry in n13_195.
Qed.

Open Scope double_app_impl.

Theorem n13_21 (X Y : Prop) (φ : Prop → Prop → Prop) : 
  ((((z = X) ∧ (w = Y)) -[ z w ]> φ z w) ↔ φ X Y).
Proof.
  assert (S1 : (((z = X) ∧ (w = Y)) -[ z w ]> (φ z w))
    ↔ ((z = X) -[ z ]> ((w = Y) -[ w ]> (φ z w)))).
  { apply n11_62. }
  assert (S2 : (((z = X) ∧ (w = Y)) -[ z w ]> (φ z w))
    ↔ ((w = Y) -[ w ]> φ X w )).
  { now rewrite -> n13_191 in S1. }
  assert (S3 : (((z = X) ∧ (w = Y)) -[ z w ]> (φ z w)) ↔ (φ X Y)).
  { now rewrite -> n13_191 in S2. }
  exact S3.
Qed.

Theorem n13_22 (X Y : Prop) (φ : Prop → Prop → Prop) : 
  (∃ z w, (z = X) ∧ (w = Y) ∧ φ z w) ↔ φ X Y.
Proof.
  assert (S1 : (∃ z w, z = X ∧ w = Y ∧ φ z w)
    ↔ (∃ z, z = X ∧ (∃ w, w = Y ∧ φ z w))).
  { apply n11_55. }
  assert (S2 : (∃ z w, z = X ∧ w = Y ∧ φ z w)
    ↔ ∃ w, w = Y ∧ φ X w).
  { now rewrite -> n13_195 in S1. }
  assert (S3 : (∃ z w, z = X ∧ w = Y ∧ φ z w) ↔ φ X Y).
  { now rewrite -> n13_195 in S2. }
  exact S3.
Qed.

Theorem n13_3 (A X : Prop) (φ : Prop → Prop) : 
  (φ A ∨ (¬ φ A)) → ((φ X ∨ (¬ φ X)) ↔ ((X = A) ∨ (¬ (X = A)))).
Proof.
  assert (S1 : φ X ∨ ¬ φ X).
  { apply n2_11. }
  assert (S2 : (φ A ∨ ¬ φ A) → φ X ∨ ¬ φ X).
  { 
    pose proof (Simp2_02 (φ A ∨ ¬ φ A) (φ X ∨ ¬ φ X)) as Simp2_02.
    now MP Simp2_02 S1.
  }
  assert (S3 : X = A ∨ ¬ (X = A)).
  { apply n2_11. }
  assert (S4 : (φ A ∨ ¬ φ A) → (X = A ∨ ¬ (X = A))).
  {
    pose proof (Simp2_02 (φ A ∨ ¬ φ A) (X = A ∨ ¬ (X = A))) as Simp2_02.
    now MP Simp2_02 S3.
  }
  assert (S5 : (φ A ∨ ¬ φ A) → ((X = A) → (φ X ∨ ¬ φ X))).
  {
    pose proof n13_101 as _n13_101.
    pose proof (n13_101 X A (fun x => φ x ∨ ¬ φ x)) as n13_101.
    pose proof (Comm2_04 (X = A) (φ X ∨ ¬ φ X) (φ A ∨ ¬ φ A)) as Comm2_04.
    now MP Comm2_04 n13_101.
  }
  assert (S6 : ((φ A ∨ ¬ φ A) → (X = A ∨ ¬ (X = A)))
    ∧ ((φ A ∨ ¬ φ A) → ((X = A) → (φ X ∨ ¬ φ X)))).
  {
    (* n10_13 ignored - we directly use `Conj` instead. Is it legal? *)
    (* n10_221 ignored *)
    clear S1 S2 S3.
    now Conj S4 S5 C1.
  }
  assert (S7 : ((φ A ∨ ¬ φ A) → φ X ∨ ¬ φ X)
    ∧ ((φ A ∨ ¬ φ A) → (X = A ∨ ¬ (X = A)))
    ∧ ((φ A ∨ ¬ φ A) → ((X = A) → (φ X ∨ ¬ φ X)))).
  {
    clear S1 S3 S4 S5.
    now Conj S2 S6 C1.
  }
  assert (S8 : ((φ A ∨ ¬ φ A) → φ X ∨ ¬ φ X)
    ∧ ((φ A ∨ ¬ φ A) → (X = A ∨ ¬ (X = A)))).
  {
    rewrite <- n4_32 in S7.
    pose proof (Simp3_26
      (((φ A ∨ ¬ φ A) → φ X ∨ ¬ φ X)
        ∧ ((φ A ∨ ¬ φ A) → (X = A ∨ ¬ (X = A))))
      (φ A ∨ ¬ φ A → X = A → φ X ∨ ¬ φ X)) as Simp3_26.
    now MP Simp3_26 S7.
  }
  assert (S9 : (φ A ∨ ¬ φ A) → 
    ((φ X ∨ ¬ φ X) ↔ (X = A ∨ ¬ (X = A)))).
  {
    pose proof (n5_35 (φ A ∨ ¬ φ A) (φ X ∨ ¬ φ X)
      (X = A ∨ ¬ (X = A))) as n5_35.
    now MP n5_35 S8.
  }
  exact S9.
Qed.

Close Scope double_app_impl.
Close Scope single_app_equiv.
Close Scope single_app_impl.
