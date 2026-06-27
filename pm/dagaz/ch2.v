Require Import PM.pm.lib.
Require Import PM.pm.ch1.

Theorem Abs2_01 (P : Prop) :
  (P → ¬ P) → ¬ P.
Proof.
  assert (S1 : ¬ P ∨ ¬ P → ¬ P).
  { exact (Taut1_2 (¬ P)). }
  assert (S2 : (P → ¬ P) → ¬ P).
  { now rewrite <- Impl1_01 in S1. }
  exact S2.
Qed.

Theorem Simp2_02 (P Q : Prop) :
  Q → (P → Q).
Proof.
  assert (S1 : Q → ¬ P ∨ Q).
  { exact (Add1_3 (¬ P) Q). }
  assert (S2 : Q → (P → Q)).
  { now rewrite <- Impl1_01 in S1. }
  exact S2.
Qed.

Theorem Transp2_03 (P Q : Prop) :
  (P → ¬ Q) → (Q → ¬ P).
Proof.
  assert (S1 : ¬ P ∨ ¬ Q → ¬ Q ∨ ¬ P).
  { exact (Perm1_4 (¬ P) (¬ Q)). }
  assert (S2 : (P → ¬ Q) → (Q → ¬ P)).
  { now repeat rewrite <- Impl1_01 in S1. }
  exact S2.
Qed.

Theorem Comm2_04 (P Q R : Prop) :
  (P → (Q → R)) → (Q → (P → R)).
Proof.
  assert (S1 : ¬ P ∨ (¬ Q ∨ R) → ¬ Q ∨ (¬ P ∨ R)).
  { exact (Assoc1_5 (¬ P) (¬ Q) R). }
  assert (S2 : (P → (Q → R)) → (Q → (P → R))).
  { now repeat rewrite <- Impl1_01 in S1. }
  exact S2.
Qed.

Theorem Syll2_05 (P Q R : Prop) :
  (Q → R) → ((P → Q) → (P → R)).
Proof.
  assert (S1 : (Q → R) → (¬ P ∨ Q → ¬ P ∨ R)).
  { exact (Sum1_6 (¬ P) Q R). }
  assert (S2 : (Q → R) → ((P → Q) → (P → R))).
  { now repeat rewrite <- Impl1_01 in S1. }
  exact S2.
Qed.

Theorem Syll2_06 (P Q R : Prop) :
  (P → Q) → ((Q → R) → (P → R)).
Proof.
  assert (S1 : ((Q → R) → ((P → Q) → (P → R))) → ((P → Q) → ((Q → R) → (P → R)))).
  { exact (Comm2_04 (Q → R) (P → Q) (P → R)). }
  assert (S2 : (Q → R) → ((P → Q) → (P → R))).
  { exact (Syll2_05 P Q R). }
  assert (S3 : (P → Q) → ((Q → R) → (P → R))).
  { now MP S1 S2. }
  exact S3.
Qed.

Theorem n2_07 (P : Prop) :
  P → (P ∨ P).
Proof.
  exact (Add1_3 P P).
Qed.

Theorem Id2_08 (P : Prop) :
  P → P.
Proof.
  assert (S1 : (P ∨ P → P) 
  → ((P → P ∨ P) → (P → P))).
  { exact (Syll2_05 P (P ∨ P) P). }
  assert (S2 : P ∨ P → P).
  { exact (Taut1_2 P). }
  assert (S3 : (P → P ∨ P) → (P → P)).
  { now MP S1 S2. }
  assert (S4 : P → P ∨ P).
  { exact (n2_07 P). }
  assert (S5 : P → P).
  { now MP S3 S4. }
  exact S5.
Qed.

Theorem n2_1 (P : Prop) :
  (¬ P) ∨ P.
Proof.
  assert (S1 : P → P).
  { exact (Id2_08 P). }
  assert (S2 : (¬ P) ∨ P).
  { now rewrite Impl1_01 in S1. }
  exact S2.
Qed.

Theorem n2_11 (P : Prop) :
  P ∨ ¬ P.
Proof.
  assert (S1 : ¬ P ∨ P → P ∨ ¬ P).
  { exact (Perm1_4 (¬ P) P). }
  assert (S2 : ¬ P ∨ P).
  { exact (n2_1 P). }
  assert (S3 : P ∨ ¬ P).
  { now MP S1 S2. }
  exact S3.
Qed.

Theorem n2_12 (P : Prop) :
  P → ¬¬ P.
Proof.
  assert (S1 : ¬ P ∨ ¬¬ P).
  { exact (n2_11 (¬ P)). }
  assert (S2 : P → ¬¬ P).
  { now rewrite <- Impl1_01 in S1. }
  exact S2.
Qed.

Theorem n2_13 (P : Prop) :
  P ∨ ¬¬¬ P.
Proof.
  assert (S1 : (¬ P → ¬¬¬ P) → (P ∨ ¬ P → P ∨ ¬¬¬ P)).
  { exact (Sum1_6 P (¬ P) (¬¬¬ P)). }
  assert (S2 : ¬ P → ¬¬¬ P).
  { exact (n2_12 (¬ P)). }
  assert (S3 : P ∨ ¬ P → P ∨ ¬¬¬ P).
  { now MP S1 S2. }
  assert (S4 : P ∨ ¬ P).
  { exact (n2_11 P). }
  assert (S5 : P ∨ ¬¬¬ P).
  { now MP S3 S4. }
  exact S5.
Qed.

Theorem n2_14 (P : Prop) :
  ¬¬ P → P.
Proof.
  assert (S1 : P ∨ ¬¬¬ P → ¬¬¬ P ∨ P).
  { exact (Perm1_4 P (¬¬¬ P)). }
  assert (S2 : P ∨ ¬¬¬ P).
  { exact (n2_13 P). }
  assert (S3 : ¬¬¬ P ∨ P).
  { now MP S1 S2. }
  assert (S4 : ¬¬ P → P).
  { now rewrite <- Impl1_01 in S3. }
  exact S4.
Qed.

Theorem Transp2_15 (P Q : Prop) :
  (¬ P → Q) → (¬ Q → P).
Proof.
  assert (S1 : (Q → ¬ (¬ Q)) → ((¬ P → Q) → (¬ P → ¬ (¬ Q)))).
  { exact (Syll2_05 (¬ P) Q (¬ (¬ Q))). }
  assert (S2 : Q → ¬ (¬ Q)).
  { exact (n2_12 Q). }
  assert (S3 : (¬ P → Q) → (¬ P → ¬ (¬ Q))).
  { now MP S1 S2. }
  assert (S4 : (¬ P → ¬ (¬ Q)) → (¬ Q → ¬ (¬ P))).
  { exact (Transp2_03 (¬ P) (¬ Q)). }
  assert (S5 : (¬ (¬ P) → P) → ((¬ Q → ¬ (¬ P)) → (¬ Q → P))).
  { exact (Syll2_05 (¬ Q) (¬ (¬ P)) P). }
  assert (S6 : (¬ Q → ¬ (¬ P)) → (¬ Q → P)).
  {
    pose proof (n2_14 P) as H14.
    now MP S5 H14.
  }
  assert (S7 : ((¬ P → ¬ (¬ Q)) → (¬ Q → ¬ (¬ P))) → 
               (((¬ P → Q) → (¬ P → ¬ (¬ Q))) → ((¬ P → Q) → (¬ Q → ¬ (¬ P))))).
  { exact (Syll2_05 (¬ P → Q) (¬ P → ¬ (¬ Q)) (¬ Q → ¬ (¬ P))). }
  assert (S8 : ((¬ P → Q) → (¬ P → ¬ (¬ Q))) → ((¬ P → Q) → (¬ Q → ¬ (¬ P)))).
  { now MP S7 S4. }
  assert (S9 : (¬ P → Q) → (¬ Q → ¬ (¬ P))).
  { now MP S8 S3. }
  assert (S10 : ((¬ Q → ¬ (¬ P)) → (¬ Q → P)) → 
                (((¬ P → Q) → (¬ Q → ¬ (¬ P))) → ((¬ P → Q) → (¬ Q → P)))).
  { exact (Syll2_05 (¬ P → Q) (¬ Q → ¬ (¬ P)) (¬ Q → P)). }
  assert (S11 : ((¬ P → Q) → (¬ Q → ¬ (¬ P))) → ((¬ P → Q) → (¬ Q → P))).
  { now MP S10 S6. }
  assert (S12 : (¬ P → Q) → (¬ Q → P)).
  { now MP S11 S9. }
  exact S12.
Qed.

Ltac Syll H1 H2 :=
  let S := fresh in
  match goal with 
  | [ _H1 : ?P → ?Q, _H2 : ?Q → ?R |- _ ] =>
    constr_eq H1 _H1;
    constr_eq H2 _H2;
    assert (S : P → R) by (intros p; exact (H2 (H1 p)));
    pose proof S as H1;
    clear S
  end.

Ltac Syll_as H1 H2 S :=
  let S := fresh S in
    match goal with 
    | [ _H1 : ?P → ?Q, _H2 : ?Q → ?R |- _ ] =>
      constr_eq H1 _H1;
      constr_eq H2 _H2;
      assert (S : P → R) by (intros p; exact (H2 (H1 p)))
  end.

Theorem Transp2_16 (P Q : Prop) :
  (P → Q) → (¬ Q → ¬ P).
Proof.
  assert (S1 : Q → ¬¬ Q).
  { exact (n2_12 Q). }
  assert (S2 : (P → Q) → (P → ¬¬ Q)).
  {
    pose proof (Syll2_05 P Q (¬¬ Q)) as Syll2_05 .
    now MP Syll2_05 S1.
  }
  assert (S3 : (P → ¬¬ Q) → (¬ Q → ¬ P)).
  { exact (Transp2_03 P (¬ Q)). }
  assert (S4 : (P → Q) → (¬ Q → ¬ P)).
  { now Syll_as S2 S3 S4. }
  exact S4.
Qed.

Theorem Transp2_17 (P Q : Prop) :
  (¬ Q → ¬ P) → (P → Q).
Proof.
  assert (S1 : (¬ Q → ¬ P) → (P → ¬¬ Q)).
  { exact (Transp2_03 (¬ Q) P). }
  assert (S2 : ¬¬ Q → Q).
  { exact (n2_14 Q). }
  assert (S3 : (P → ¬¬ Q) → (P → Q)).
  {
    pose proof (Syll2_05 P (¬¬ Q) Q) as Syll2_05.
    now MP Syll2_05 S2.
  }
  assert (S4 : (¬ Q → ¬ P) → (P → Q)).
  { now Syll_as S1 S3 S4. }
  exact S4.
Qed.

Theorem n2_18 (P : Prop) :
  (¬ P → P) → P.
Proof.
  assert (S1 : P → ¬¬ P).
  { exact (n2_12 P). }
  assert (S2 : (¬ P → P) → (¬ P → ¬¬ P)).
  {
    pose proof (Syll2_05 (¬ P) P (¬¬ P)) as Syll2_05.
    now MP Syll2_05 S1.
  }
  assert (S3 : (¬ P → ¬¬ P) → ¬¬ P).
  { exact (Abs2_01 (¬ P)). }
  assert (S4 : (¬ P → P) → ¬¬ P).
  { now Syll_as S2 S3 S4. }
  assert (S5 : ¬¬ P → P).
  { exact (n2_14 P). }
  assert (S6 : (¬ P → P) → P).
  { now Syll_as S4 S5 S6. }
  exact S6.
Qed.

Theorem n2_2 (P Q : Prop) :
  P → (P ∨ Q).
Proof.
  assert (S1 : P → Q ∨ P).
  { exact (Add1_3 Q P). }
  assert (S2 : Q ∨ P → P ∨ Q).
  { exact (Perm1_4 Q P). }
  assert (S3 : P → P ∨ Q).
  { now Syll_as S1 S2 S3. }
  exact S3.
Qed.

Theorem n2_21 (P Q : Prop) :
  ¬ P → (P → Q).
Proof.
  assert (S1 : ¬ P → ¬ P ∨ Q).
  { exact (n2_2 (¬ P) Q). }
  assert (S2 : ¬ P → (P → Q)).
  { now repeat rewrite <- Impl1_01 in S1. }
  exact S2.
Qed.

Theorem n2_24 (P Q : Prop) :
  P → (¬ P → Q).
Proof.
  assert (S1 : ¬ P → (P → Q)).
  { exact (n2_21 P Q). }
  assert (S2 : (¬ P → (P → Q)) → (P → (¬ P → Q))).
  { exact (Comm2_04 (¬ P) P Q). }
  assert (S3 : P → (¬ P → Q)).
  { now MP S2 S1. }
  exact S3.
Qed.

Theorem n2_25 (P Q : Prop) :
  P ∨ ((P ∨ Q) → Q).
Proof.
  assert (S1 : ¬ (P ∨ Q) ∨ (P ∨ Q)).
  { exact (n2_1 (P ∨ Q)). }
  assert (S2 : ¬ (P ∨ Q) ∨ (P ∨ Q) → P ∨ ¬ (P ∨ Q) ∨ Q).
  { exact (Assoc1_5 (¬ (P ∨ Q)) P Q). }
  assert (S3 : P ∨ ¬ (P ∨ Q) ∨  Q).
  { now MP S2 S1. }
  assert (S4 : P ∨ ((P ∨ Q) → Q)).
  { now repeat rewrite <- Impl1_01 in S3. }
  exact S4.
Qed.

Theorem n2_26 (P Q : Prop) :
  ¬ P ∨ ((P → Q) → Q).
Proof.
  assert (S1 : ¬ P ∨ ((¬ P ∨ Q) → Q)).
  { exact (n2_25 (¬ P) Q). }

  set (λ P0 Q0 : Prop, eq_to_equiv (P0 → Q0) (¬ P0 ∨ Q0) (Impl1_01 P0 Q0))
    as Impl1_01a.
    
  assert (S2 : ¬ P ∨ ((P → Q) → Q)).
  { now rewrite <- (Impl1_01a P Q) in S1. }
  exact S2.
Qed.

Theorem n2_27 (P Q : Prop) :
  P → ((P → Q) → Q).
Proof.
  assert (S1 : ¬ P ∨ ((P → Q) → Q)).
  { exact (n2_26 P Q). }
  assert (S2 : P → ((P → Q) → Q)).
  { now repeat rewrite <- Impl1_01 in S1. }
  exact S2.
Qed.

Theorem n2_3 (P Q R : Prop) :
  (P ∨ (Q ∨ R)) → (P ∨ (R ∨ Q)).
Proof.
  assert (S1 : Q ∨ R → R ∨ Q).
  { exact (Perm1_4 Q R). }
  assert (S2 : (Q ∨ R → R ∨ Q) → (P ∨ (Q ∨ R) → P ∨ (R ∨ Q))).
  { exact (Sum1_6 P (Q ∨ R) (R ∨ Q)). }
  assert (S3 : P ∨ (Q ∨ R) → P ∨ (R ∨ Q)).
  { now MP S2 S1. }
  exact S3.
Qed.

Theorem n2_31 (P Q R : Prop) :
  (P ∨ (Q ∨ R)) → ((P ∨ Q) ∨ R).
Proof.
  assert (S1 : P ∨ (Q ∨ R) → P ∨ (R ∨ Q)).
  { exact (n2_3 P Q R). }
  assert (S2 : P ∨ (R ∨ Q) → R ∨ (P ∨ Q)).
  { exact (Assoc1_5 P R Q). }
  assert (S3 : R ∨ (P ∨ Q) → (P ∨ Q) ∨ R).
  { exact (Perm1_4 R (P ∨ Q)). }
  assert (S4 : P ∨ (R ∨ Q) → (P ∨ Q) ∨ R).
  { now Syll_as S2 S3 S4. }
  assert (S5 : P ∨ (Q ∨ R) → ((P ∨ Q) ∨ R)).
  { now Syll_as S1 S4 S5. }
  exact S5.
Qed.

Theorem n2_32 (P Q R : Prop) :
  ((P ∨ Q) ∨ R) → (P ∨ (Q ∨ R)).
Proof.
  assert (S1 : (P ∨ Q) ∨ R → R ∨ (P ∨ Q)).
  { exact (Perm1_4 (P ∨ Q) R). }
  assert (S2 : R ∨ (P ∨ Q) → P ∨ (R ∨ Q)).
  { exact (Assoc1_5 R P Q). }
  assert (S3 : P ∨ (R ∨ Q) → P ∨ (Q ∨ R)).
  { exact (n2_3 P R Q). }
  Syll_as S1 S2 S3_1.
  now Syll_as S3_1 S3 S3_2.
Qed.

Theorem Abb2_33 (P Q R : Prop) :
  (P ∨ Q ∨ R) = ((P ∨ Q) ∨ R).
Proof.
  Admitted.
Qed.

Theorem n2_36 (P Q R : Prop) :
  (Q → R) → ((P ∨ Q) → (R ∨ P)).
Proof.
  assert (S1 : P ∨ R → R ∨ P).
  { exact (Perm1_4 P R). }
  assert (S2 : (P ∨ R → R ∨ P) → ((P ∨ Q → P ∨ R) → (P ∨ Q → R ∨ P))).
  { exact (Syll2_05 (P ∨ Q) (P ∨ R) (R ∨ P)). }
  assert (S3 : (P ∨ Q → P ∨ R) → (P ∨ Q → R ∨ P)).
  { now MP S2 S1. }
  assert (S4 : (Q → R) → (P ∨ Q → P ∨ R)).
  { exact (Sum1_6 P Q R). }
  assert (S5 : (Q → R) → (P ∨ Q → R ∨ P)).
  { now Syll_as S4 S3 S5. }
  exact S5.
Qed.

Theorem n2_37 (P Q R : Prop) :
  (Q → R) → ((Q ∨ P) → (P ∨ R)).
Proof.
  assert (S1 : Q ∨ P → P ∨ Q).
  { exact (Perm1_4 Q P). }
  assert (S2 : (Q ∨ P → P ∨ Q) → ((P ∨ Q → P ∨ R) → (Q ∨ P → P ∨ R))).
  { exact (Syll2_06 (Q ∨ P) (P ∨ Q) (P ∨ R)). }
  assert (S3 : (P ∨ Q → P ∨ R) → (Q ∨ P → P ∨ R)).
  { now MP S2 S1. }
  assert (S4 : (Q → R) → (P ∨ Q → P ∨ R)).
  { exact (Sum1_6 P Q R). }
  assert (S5 : (Q → R) → (Q ∨ P → P ∨ R)).
  { now Syll_as S4 S3 S5. }
  exact S5.
Qed.

Theorem n2_38 (P Q R : Prop) :
  (Q → R) → ((Q ∨ P) → (R ∨ P)).
Proof.
  assert (S1 : P ∨ R → R ∨ P).
  { exact (Perm1_4 P R). }
  assert (S2 : (P ∨ R → R ∨ P) → ((Q ∨ P → P ∨ R) → (Q ∨ P → R ∨ P))).
  { exact (Syll2_05 (Q ∨ P) (P ∨ R) (R ∨ P)). }
  assert (S3 : (Q ∨ P → P ∨ R) → (Q ∨ P → R ∨ P)).
  { now MP S2 S1. }
  assert (S4 : Q ∨ P → P ∨ Q).
  { exact (Perm1_4 Q P). }
  assert (S5 : (Q ∨ P → P ∨ Q) → ((P ∨ Q → P ∨ R) → (Q ∨ P → P ∨ R))).
  { exact (Syll2_06 (Q ∨ P) (P ∨ Q) (P ∨ R)). }
  assert (S6 : (P ∨ Q → P ∨ R) → (Q ∨ P → P ∨ R)).
  { now MP S5 S4. }
  assert (S7 : (P ∨ Q → P ∨ R) → (Q ∨ P → R ∨ P)).
  { now Syll_as S6 S3 S7. }
  assert (S8 : (Q → R) → (P ∨ Q → P ∨ R)).
  { exact (Sum1_6 P Q R). }
  assert (S9 : (Q → R) → (Q ∨ P → R ∨ P)).
  { now Syll_as S8 S7 S9. }
  exact S9.
Qed.

Theorem n2_4 (P Q : Prop) :
  (P ∨ (P ∨ Q)) → (P ∨ Q).
Proof.
  assert (S1 : P ∨ (P ∨ Q) → (P ∨ P) ∨ Q).
  { exact (n2_31 P P Q). }
  assert (S2 : P ∨ P → P).
  { exact (Taut1_2 P). }
  assert (S3 : (P ∨ P → P) → ((P ∨ P) ∨ Q → P ∨ Q)).
  { exact (n2_38 Q (P ∨ P) P). }
  assert (S4 : (P ∨ P) ∨ Q → P ∨ Q).
  { now MP S3 S2. }
  assert (S5 : P ∨ (P ∨ Q) → P ∨ Q).
  { now Syll_as S1 S4 S5. }
  exact S5.
Qed.

Theorem n2_41 (P Q : Prop) :
  (Q ∨ (P ∨ Q)) → (P ∨ Q).
Proof.
  assert (S1 : Q ∨ (P ∨ Q) → P ∨ (Q ∨ Q)).
  { exact (Assoc1_5 Q P Q). }
  assert (S2 : Q ∨ Q → Q).
  { exact (Taut1_2 Q). }
  assert (S3 : (Q ∨ Q → Q) → (P ∨ (Q ∨ Q) → P ∨ Q)).
  { exact (Sum1_6 P (Q ∨ Q) Q). }
  assert (S4 : P ∨ (Q ∨ Q) → P ∨ Q).
  { now MP S3 S2. }
  assert (S5 : Q ∨ (P ∨ Q) → P ∨ Q).
  { now Syll_as S1 S4 S5. }
  exact S5.
Qed.

Theorem n2_42 (P Q : Prop) :
  (¬ P ∨ (P → Q)) → (P → Q).
Proof.
  assert (S1 : ¬ P ∨ (¬ P ∨ Q) → ¬ P ∨ Q).
  { exact (n2_4 (¬ P) Q). }
  assert (S2 : ¬ P ∨ (P → Q) → (P → Q)).
  { now repeat rewrite <- (Impl1_01 P Q) in S1. }
  exact S2.
Qed.

Theorem n2_43 (P Q : Prop) :
  (P → (P → Q)) → (P → Q).
Proof.
  assert (S1 : ¬ P ∨ (P → Q) → (P → Q)).
  { exact (n2_42 P Q). }
  assert (S2 : (P → (P → Q)) → (P → Q)).
  { now repeat rewrite <- Impl1_01 in S1. }
  exact S2.
Qed.

Theorem n2_45 (P Q : Prop) :
  ¬ (P ∨ Q) → ¬ P.
Proof.
  assert (S1 : P → P ∨ Q).
  { exact (n2_2 P Q). }
  assert (S2 : (P → P ∨ Q) → (¬ (P ∨ Q) → ¬ P)).
  { exact (Transp2_16 P (P ∨ Q)). }
  assert (S3 : ¬ (P ∨ Q) → ¬ P).
  { now MP S2 S1. }
  exact S3.
Qed.

Theorem n2_46 (P Q : Prop) :
  ¬ (P ∨ Q) → ¬ Q.
Proof.
  assert (S1 : Q → P ∨ Q).
  { exact (Add1_3 P Q). }
  assert (S2 : (Q → P ∨ Q) → (¬ (P ∨ Q) → ¬ Q)).
  { exact (Transp2_16 Q (P ∨ Q)). }
  assert (S3 : ¬ (P ∨ Q) → ¬ Q).
  { now MP S2 S1. }
  exact S3.
Qed.

Theorem n2_47 (P Q : Prop) :
  ¬ (P ∨ Q) → (¬ P ∨ Q).
Proof.
  assert (S1 : ¬ (P ∨ Q) → ¬ P).
  { exact (n2_45 P Q). }
  assert (S2 : ¬ P → ¬ P ∨ Q).
  { exact (n2_2 (¬ P) Q). }
  assert (S3 : ¬ (P ∨ Q) → ¬ P ∨ Q).
  { now Syll_as S1 S2 S3. }
  exact S3.
Qed.

Theorem n2_48 (P Q : Prop) :
  ¬ (P ∨ Q) → (P ∨ ¬ Q).
Proof.
  assert (S1 : ¬ (P ∨ Q) → ¬ Q).
  { exact (n2_46 P Q). }
  assert (S2 : ¬ Q → P ∨ ¬ Q).
  { exact (Add1_3 P (¬ Q)). }
  assert (S3 : ¬ (P ∨ Q) → P ∨ ¬ Q).
  { now Syll_as S1 S2 S3. }
  exact S3.
Qed.

Theorem n2_49 (P Q : Prop) :
  ¬ (P ∨ Q) → (¬ P ∨ ¬ Q).
Proof.
  assert (S1 : ¬ (P ∨ Q) → ¬ P).
  { exact (n2_45 P Q). }
  assert (S2 : ¬ P → ¬ P ∨ ¬ Q).
  { exact (n2_2 (¬ P) (¬ Q)). }
  assert (S3 : ¬ (P ∨ Q) → ¬ P ∨ ¬ Q).
  { now Syll_as S1 S2 S3. }
  exact S3.
Qed.

Theorem n2_5 (P Q : Prop) :
  ¬ (P → Q) → (¬ P → Q).
Proof.
  assert (S1 : ¬ (¬ P ∨ Q) → ¬ (¬ P) ∨ Q).
  { exact (n2_47 (¬ P) Q). }
  assert (S2 : ¬ (P → Q) → (¬ P → Q)).
  { now repeat rewrite <- Impl1_01 in S1. }
  exact S2.
Qed.

Theorem n2_51 (P Q : Prop) :
  ¬ (P → Q) → (P → ¬ Q).
Proof.
  assert (S1 : ¬ (¬ P ∨ Q) → ¬ P ∨ ¬ Q).
  { exact (n2_48 (¬ P) Q). }
  assert (S2 : ¬ (P → Q) → (P → ¬ Q)).
  { now repeat rewrite <- Impl1_01 in S1. }
  exact S2.
Qed.

Theorem n2_52 (P Q : Prop) :
  ¬ (P → Q) → (¬ P → ¬ Q).
Proof.
  assert (S1 : ¬ (¬ P ∨ Q) → ¬ (¬ P) ∨ ¬ Q).
  { exact (n2_49 (¬ P) Q). }
  assert (S2 : ¬ (P → Q) → (¬ P → ¬ Q)).
  { now repeat rewrite <- Impl1_01 in S1. }
  exact S2.
Qed.

Theorem n2_521 (P Q : Prop) :
  ¬ (P → Q) → (Q → P).
Proof.
  assert (S1 : ¬ (P → Q) → (¬ P → ¬ Q)).
  { exact (n2_52 P Q). }
  assert (S2 : (¬ P → ¬ Q) → (Q → P)).
  { exact (Transp2_17 Q P). }
  assert (S3 : ¬ (P → Q) → (Q → P)).
  { now Syll_as S1 S2 S3. }
  exact S3.
Qed.

Theorem n2_53 (P Q : Prop) :
  (P ∨ Q) → (¬ P → Q).
Proof.
  assert (S1 : P → ¬¬ P).
  { exact (n2_12 P). }
  assert (S2 : (P → ¬¬ P) → (P ∨ Q → ¬¬ P ∨ Q)).
  { exact (n2_38 Q P (¬¬ P)). }
  assert (S3 : P ∨ Q → ¬¬ P ∨ Q).
  { now MP S2 S1. }
  
  set (λ P0 Q0 : Prop, eq_to_equiv (P0 → Q0) (¬ P0 ∨ Q0) (Impl1_01 P0 Q0))
    as Impl1_01a.
  
  assert (S4 : P ∨ Q → (¬ P → Q)).
  { now rewrite <- (Impl1_01a (¬ P) Q) in S3. }
  exact S4.
Qed.

Theorem n2_54 (P Q : Prop) :
  (¬ P → Q) → (P ∨ Q).
Proof.
  assert (S1 : ¬¬ P → P).
  { exact (n2_14 P). }
  assert (S2 : (¬¬ P → P) → (¬¬ P ∨ Q → P ∨ Q)).
  { exact (n2_38 Q (¬¬ P) P). }
  assert (S3 : ¬¬ P ∨ Q → P ∨ Q).
  { now MP S2 S1. }
  
  set (λ P0 Q0 : Prop, eq_to_equiv (P0 → Q0) (¬ P0 ∨ Q0) (Impl1_01 P0 Q0))
    as Impl1_01a.
  
  assert (S4 : (¬ P → Q) → P ∨ Q).
  { now rewrite (Impl1_01a (¬ P) Q) in S3. }
  exact S4.
Qed.

Theorem n2_55 (P Q : Prop) :
  ¬ P → ((P ∨ Q) → Q).
Proof.
  assert (S1 : P ∨ Q → (¬ P → Q)).
  { exact (n2_53 P Q). }
  assert (S2 : (P ∨ Q → (¬ P → Q)) → (¬ P → (P ∨ Q → Q))).
  { exact (Comm2_04 (P ∨ Q) (¬ P) Q). }
  assert (S3 : ¬ P → (P ∨ Q → Q)).
  { now MP S2 S1. }
  exact S3.
Qed.

Theorem n2_56 (P Q : Prop) :
  ¬ Q → ((P ∨ Q) → P).
Proof.
  assert (S1 : ¬ Q → (Q ∨ P → P)).
  { exact (n2_55 Q P). }
  assert (S2 : P ∨ Q → Q ∨ P).
  { exact (Perm1_4 P Q). }
  assert (S3 : (P ∨ Q → Q ∨ P) → ((Q ∨ P → P) → (P ∨ Q → P))).
  { exact (Syll2_06 (P ∨ Q) (Q ∨ P) P). }
  assert (S4 : (Q ∨ P → P) → (P ∨ Q → P)).
  { now MP S3 S2. }
  Syll_as S1 S4 S5.
  exact S5.
Qed.

Theorem n2_6 (P Q : Prop) :
  (¬ P → Q) → ((P → Q) → Q).
Proof.
  assert (S1 : (¬ P → Q) → (¬ P ∨ Q → Q ∨ Q)).
  { exact (n2_38 Q (¬ P) Q). }
  assert (S2 : Q ∨ Q → Q).
  { exact (Taut1_2 Q). }
  assert (S3 : (Q ∨ Q → Q) → ((¬ P ∨ Q → Q ∨ Q) → (¬ P ∨ Q → Q))).
  { exact (Syll2_05 (¬ P ∨ Q) (Q ∨ Q) Q). }
  assert (S4 : (¬ P ∨ Q → Q ∨ Q) → (¬ P ∨ Q → Q)).
  { now MP S3 S2. }
  Syll_as S1 S4 S5.
  
  set (λ P0 Q0 : Prop, eq_to_equiv (P0 → Q0) (¬ P0 ∨ Q0) (Impl1_01 P0 Q0))
    as Impl1_01a.
  
  assert (S6 : (¬ P → Q) → ((P → Q) → Q)).
  { now rewrite <- (Impl1_01a P Q) in S5. }
  exact S6.
Qed.

Theorem n2_61 (P Q : Prop) :
  (P → Q) → ((¬ P → Q) → Q).
Proof.
  assert (S1 : (¬ P → Q) → ((P → Q) → Q)).
  { exact (n2_6 P Q). }
  assert (S2 : ((¬ P → Q) → ((P → Q) → Q)) → ((P → Q) → ((¬ P → Q) → Q))).
  { exact (Comm2_04 (¬ P → Q) (P → Q) Q). }
  assert (S3 : (P → Q) → ((¬ P → Q) → Q)).
  { now MP S2 S1. }
  exact S3.
Qed.

Theorem n2_62 (P Q : Prop) :
  (P ∨ Q) → ((P → Q) → Q).
Proof.
  assert (S1 : P ∨ Q → (¬ P → Q)).
  { exact (n2_53 P Q). }
  assert (S2 : (¬ P → Q) → ((P → Q) → Q)).
  { exact (n2_6 P Q). }
  Syll_as S1 S2 S3.
  exact S3.
Qed.

Theorem n2_621 (P Q : Prop) :
  (P → Q) → ((P ∨ Q) → Q).
Proof.
  assert (S1 : P ∨ Q → ((P → Q) → Q)).
  { exact (n2_62 P Q). }
  assert (S2 : (P ∨ Q → ((P → Q) → Q)) → ((P → Q) → (P ∨ Q → Q))).
  { exact (Comm2_04 (P ∨ Q) (P → Q) Q). }
  assert (S3 : (P → Q) → (P ∨ Q → Q)).
  { now MP S2 S1. }
  exact S3.
Qed.

Theorem n2_63 (P Q : Prop) :
  (P ∨ Q) → ((¬ P ∨ Q) → Q).
Proof.
  assert (S1 : P ∨ Q → ((P → Q) → Q)).
  { exact (n2_62 P Q). }
  
  set (λ P0 Q0 : Prop, eq_to_equiv (P0 → Q0) (¬ P0 ∨ Q0) (Impl1_01 P0 Q0))
    as Impl1_01a.
  
  assert (S2 : P ∨ Q → (¬ P ∨ Q → Q)).
  { now rewrite (Impl1_01a P Q) in S1. }
  exact S2.
Qed.


Theorem n2_64 (P Q : Prop) :
  (P ∨ Q) → ((P ∨ ¬ Q) → P).
Proof.
  assert (S1 : Q ∨ P → (¬ Q ∨ P → P)).
  { exact (n2_63 Q P). }
  assert (S2 : P ∨ Q → Q ∨ P).
  { exact (Perm1_4 P Q). }
  Syll_as S2 S1 S3.
  assert (S4 : P ∨ ¬ Q → ¬ Q ∨ P).
  { exact (Perm1_4 P (¬ Q)). }
  assert (S5 : (P ∨ ¬ Q → ¬ Q ∨ P) → ((¬ Q ∨ P → P) → (P ∨ ¬ Q → P))).
  { exact (Syll2_06 (P ∨ ¬ Q) (¬ Q ∨ P) P). }
  assert (S6 : (¬ Q ∨ P → P) → (P ∨ ¬ Q → P)).
  { now MP S5 S4. }
  Syll_as S3 S6 S7.
  exact S7.
Qed.

Theorem n2_65 (P Q : Prop) :
  (P → Q) → ((P → ¬ Q) → ¬ P).
Proof.
  assert (S1 : ¬ P ∨ Q → (¬ P ∨ ¬ Q → ¬ P)).
  { exact (n2_64 (¬ P) Q). }
  
  set (λ P0 Q0 : Prop, eq_to_equiv (P0 → Q0) (¬ P0 ∨ Q0) (Impl1_01 P0 Q0))
    as Impl1_01a.
  
  assert (S2 : (P → Q) → (P → ¬ Q) → ¬ P).
  { 
    rewrite <- (Impl1_01a P Q) in S1.
    now rewrite <- (Impl1_01a P (¬ Q)) in S1.
  }
  exact S2.
Qed.

Theorem n2_67 (P Q : Prop) :
  ((P ∨ Q) → Q) → (P → Q).
Proof.
  assert (S1 : (¬ P → Q) → P ∨ Q).
  { exact (n2_54 P Q). }
  assert (S2 : ((¬ P → Q) → P ∨ Q) → ((P ∨ Q → Q) → ((¬ P → Q) → Q))).
  { exact (Syll2_06 (¬ P → Q) (P ∨ Q) Q). }
  assert (S3 : (P ∨ Q → Q) → ((¬ P → Q) → Q)).
  { now MP S2 S1. }
  assert (S4 : P → (¬ P → Q)).
  { exact (n2_24 P Q). }
  assert (S5 : (P → (¬ P → Q)) → (((¬ P → Q) → Q) → (P → Q))).
  { exact (Syll2_06 P (¬ P → Q) Q). }
  assert (S6 : ((¬ P → Q) → Q) → (P → Q)).
  { now MP S5 S4. }
  Syll_as S3 S6 S7.
  exact S7.
Qed.


Theorem n2_68 (P Q : Prop) :
  ((P → Q) → Q) → (P ∨ Q).
Proof.
  assert (S1 : (¬ P ∨ Q → Q) → (¬ P → Q)).
  { exact (n2_67 (¬ P) Q). }
  
  set (λ P0 Q0 : Prop, eq_to_equiv (P0 → Q0) (¬ P0 ∨ Q0) (Impl1_01 P0 Q0))
    as Impl1_01a.
  
  assert (S2 : ((P → Q) → Q) → (¬ P → Q)).
  { now rewrite <- (Impl1_01a P Q) in S1. }
  assert (S3 : (¬ P → Q) → P ∨ Q).
  { exact (n2_54 P Q). }
  Syll_as S2 S3 S4.
  exact S4.
Qed.


Theorem n2_69 (P Q : Prop) :
  ((P → Q) → Q) → ((Q → P) → P).
Proof.
  assert (S1 : ((P → Q) → Q) → P ∨ Q).
  { exact (n2_68 P Q). }
  assert (S2 : P ∨ Q → Q ∨ P).
  { exact (Perm1_4 P Q). }
  Syll_as S1 S2 S3.
  assert (S4 : Q ∨ P → ((Q → P) → P)).
  { exact (n2_62 Q P). }
  Syll_as S3 S4 S5.
  exact S5.
Qed.

Theorem n2_73 (P Q R : Prop) :
  (P → Q) → (((P ∨ Q) ∨ R) → (Q ∨ R)).
Proof.
  assert (S1 : (P → Q) → (P ∨ Q → Q)).
  { exact (n2_621 P Q). }
  assert (S2 : (P ∨ Q → Q) → ((P ∨ Q) ∨ R → Q ∨ R)).
  { exact (n2_38 R (P ∨ Q) Q). }
  Syll_as S1 S2 S3.
  exact S3.
Qed.

Theorem n2_74 (P Q R : Prop) :
  (Q → P) → ((P ∨ Q) ∨ R) → (P ∨ R).
Proof.
  assert (S1 : (Q → P) → ((Q ∨ P) ∨ R → P ∨ R)).
  { exact (n2_73 Q P R). }
  assert (S2 : P ∨ (Q ∨ R) → Q ∨ (P ∨ R)).
  { exact (Assoc1_5 P Q R). }
  assert (S3 : Q ∨ (P ∨ R) → (Q ∨ P) ∨ R).
  { exact (n2_31 Q P R). }
  Syll_as S2 S3 S4.
  assert (S5 : (P ∨ Q) ∨ R → P ∨ (Q ∨ R)).
  { exact (n2_32 P Q R). }
  Syll_as S5 S4 S6.
  assert (S7 : ((P ∨ Q) ∨ R → (Q ∨ P) ∨ R) → (((Q ∨ P) ∨ R → P ∨ R) → ((P ∨ Q) ∨ R → P ∨ R))).
  { exact (Syll2_06 ((P ∨ Q) ∨ R) ((Q ∨ P) ∨ R) (P ∨ R)). }
  assert (S8 : ((Q ∨ P) ∨ R → P ∨ R) → ((P ∨ Q) ∨ R → P ∨ R)).
  { now MP S7 S6. }
  Syll_as S1 S8 S9.
  exact S9.
Qed.

Theorem n2_75 (P Q R : Prop) :
  (P ∨ Q) → ((P ∨ (Q → R)) → (P ∨ R)).
Proof.
  assert (S1 : (¬ Q → P) → ((P ∨ ¬ Q) ∨ R → P ∨ R)).
  { exact (n2_74 P (¬ Q) R). }
  assert (S2 : Q ∨ P → (¬ Q → P)).
  { exact (n2_53 Q P). }
  Syll_as S2 S1 S3.
  assert (S4 : P ∨ (¬ Q ∨ R) → (P ∨ ¬ Q) ∨ R).
  { exact (n2_31 P (¬ Q) R). }
  assert (S5 : (P ∨ (¬ Q ∨ R) → (P ∨ ¬ Q) ∨ R) → (((P ∨ ¬ Q) ∨ R → P ∨ R) → (P ∨ (¬ Q ∨ R) → P ∨ R))).
  { exact (Syll2_06 (P ∨ (¬ Q ∨ R)) ((P ∨ ¬ Q) ∨ R) (P ∨ R)). }
  assert (S6 : ((P ∨ ¬ Q) ∨ R → P ∨ R) → (P ∨ (¬ Q ∨ R) → P ∨ R)).
  { now MP S5 S4. }
  Syll_as S3 S6 S7.
  assert (S8 : P ∨ Q → Q ∨ P).
  { exact (Perm1_4 P Q). }
  Syll_as S8 S7 S9.
  
  set (λ P0 Q0 : Prop, eq_to_equiv (P0 → Q0) (¬ P0 ∨ Q0) (Impl1_01 P0 Q0))
    as Impl1_01a.
  
  assert (S10 : P ∨ Q → (P ∨ (Q → R) → P ∨ R)).
  { now rewrite <- (Impl1_01a Q R) in S9. }
  exact S10.
Qed.

Theorem n2_76 (P Q R : Prop) :
  (P ∨ (Q → R)) → ((P ∨ Q) → (P ∨ R)).
Proof.
  assert (S1 : P ∨ Q → (P ∨ (Q → R) → P ∨ R)).
  { exact (n2_75 P Q R). }
  assert (S2 : (P ∨ Q → (P ∨ (Q → R) → P ∨ R)) → (P ∨ (Q → R) → (P ∨ Q → P ∨ R))).
  { exact (Comm2_04 (P ∨ Q) (P ∨ (Q → R)) (P ∨ R)). }
  assert (S3 : P ∨ (Q → R) → (P ∨ Q → P ∨ R)).
  { now MP S2 S1. }
  exact S3.
Qed.

Theorem n2_77 (P Q R : Prop) :
  (P → (Q → R)) → ((P → Q) → (P → R)).
Proof.
  assert (S1 : ¬ P ∨ (Q → R) → (¬ P ∨ Q → ¬ P ∨ R)).
  { exact (n2_76 (¬ P) Q R). }
  
  set (λ P0 Q0 : Prop, eq_to_equiv (P0 → Q0) (¬ P0 ∨ Q0) (Impl1_01 P0 Q0))
    as Impl1_01a.
  
  assert (S2 : (P → Q → R) → (P → Q) → (P → R)).
  {
    rewrite <- (Impl1_01a P (Q → R)) in S1.
    rewrite <- (Impl1_01a P Q) in S1.
    now rewrite <- (Impl1_01a P R) in S1.
  }
  exact S2.
Qed.

Theorem n2_8 (Q R S : Prop) :
  (Q ∨ R) → ((¬ R ∨ S) → (Q ∨ S)).
Proof.
  assert (S1 : R ∨ Q → (¬ R → Q)).
  { exact (n2_53 R Q). }
  assert (S2 : Q ∨ R → R ∨ Q).
  { exact (Perm1_4 Q R). }
  Syll_as S2 S1 S3.
  assert (S4 : (¬ R → Q) → (¬ R ∨ S → Q ∨ S)).
  { exact (n2_38 S (¬ R) Q). }
  Syll_as S3 S4 S5.
  exact S5.
Qed.


Theorem n2_81 (P Q R S : Prop) :
  (Q → (R → S)) → ((P ∨ Q) → ((P ∨ R) → (P ∨ S))).
Proof.
  assert (S1 : (Q → (R → S)) → (P ∨ Q → P ∨ (R → S))).
  { exact (Sum1_6 P Q (R → S)). }
  assert (S2 : P ∨ (R → S) → (P ∨ R → P ∨ S)).
  { exact (n2_76 P R S). }
  assert (S3 : (P ∨ (R → S) → (P ∨ R → P ∨ S)) → ((P ∨ Q → P ∨ (R → S)) → (P ∨ Q → (P ∨ R → P ∨ S)))).
  { exact (Syll2_05 (P ∨ Q) (P ∨ (R → S)) (P ∨ R → P ∨ S)). }
  assert (S4 : (P ∨ Q → P ∨ (R → S)) → (P ∨ Q → (P ∨ R → P ∨ S))).
  { now MP S3 S2. }
  Syll_as S1 S4 S5.
  exact S5.
Qed.

Theorem n2_82 (P Q R S : Prop) :
  (P ∨ Q ∨ R) → ((P ∨ ¬ R ∨ S) → (P ∨ Q ∨ S)).
Proof.
  assert (S1 : Q ∨ R → (¬ R ∨ S → Q ∨ S)).
  { exact (n2_8 Q R S). }
  assert (S2 : (Q ∨ R → (¬ R ∨ S → Q ∨ S)) → (P ∨ (Q ∨ R) → (P ∨ (¬ R ∨ S) → P ∨ (Q ∨ S)))).
  { exact (n2_81 P (Q ∨ R) (¬ R ∨ S) (Q ∨ S)). }
  assert (S3 : P ∨ (Q ∨ R) → (P ∨ (¬ R ∨ S) → P ∨ (Q ∨ S))).
  { now MP S2 S1. }
  exact S3.
Qed.

Theorem n2_83 (P Q R S : Prop) :
  (P → (Q → R)) → ((P → (R → S)) → (P → (Q → S))).
Proof.
  assert (S1 : ¬ P ∨ (¬ Q ∨ R) → (¬ P ∨ (¬ R ∨ S) → ¬ P ∨ (¬ Q ∨ S))).
  { exact (n2_82 (¬ P) (¬ Q) R S). }
  
  set (λ P0 Q0 : Prop, eq_to_equiv (P0 → Q0) (¬ P0 ∨ Q0) (Impl1_01 P0 Q0))
    as Impl1_01a.
  
  assert (S2 : (P → Q → R) → (P → R → S) → (P → Q → S)).
  {
    rewrite <- (Impl1_01a Q R) in S1.
    rewrite <- (Impl1_01a P (Q → R)) in S1.
    rewrite <- (Impl1_01a R S) in S1.
    rewrite <- (Impl1_01a P (R → S)) in S1.
    rewrite <- (Impl1_01a Q S) in S1.
    now rewrite <- (Impl1_01a P (Q → S)) in S1.
  }
  exact S2.
Qed.

Theorem n2_85 (P Q R : Prop) :
  ((P ∨ Q) → (P ∨ R)) → (P ∨ (Q → R)).
Proof.
  assert (S1 : Q → P ∨ Q).
  { exact (Add1_3 P Q). }
  assert (S2 : (Q → P ∨ Q) → ((P ∨ Q → R) → (Q → R))).
  { exact (Syll2_06 Q (P ∨ Q) R). }
  assert (S3 : (P ∨ Q → R) → (Q → R)).
  { now MP S2 S1. }
  assert (S4 : ¬ P → (P ∨ R → R)).
  { exact (n2_55 P R). }
  assert (S5 : (P ∨ R → R) → ((P ∨ Q → P ∨ R) → (P ∨ Q → R))).
  { exact (Syll2_05 (P ∨ Q) (P ∨ R) R). }
  Syll_as S4 S5 S6.
  assert (S7 : (¬ P → ((P ∨ Q → P ∨ R) → (P ∨ Q → R))) → ((¬ P → ((P ∨ Q → R) → (Q → R))) → (¬ P → ((P ∨ Q → P ∨ R) → (Q → R))))). 
  { exact (n2_83 (¬ P) (P ∨ Q → P ∨ R) (P ∨ Q → R) (Q → R)). }
  assert (S8 : (¬ P → ((P ∨ Q → R) → (Q → R))) → (¬ P → ((P ∨ Q → P ∨ R) → (Q → R)))).
  { now MP S7 S6. }
  assert (S9 : (¬ P → ((P ∨ Q → P ∨ R) → (Q → R))) → ((P ∨ Q → P ∨ R) → (¬ P → (Q → R)))). 
  { exact (Comm2_04 (¬ P) (P ∨ Q → P ∨ R) (Q → R)). }
  Syll_as S8 S9 S10.
  assert (S11 : ((P ∨ Q → R) → (Q → R)) → (¬ P → ((P ∨ Q → R) → (Q → R)))).
  { exact (Simp2_02 (¬ P) ((P ∨ Q → R) → (Q → R))). }
  assert (S12 : ¬ P → ((P ∨ Q → R) → (Q → R))).
  { now MP S11 S3. }
  assert (S13 : (P ∨ Q → P ∨ R) → (¬ P → (Q → R))).
  { now MP S10 S12. }
  assert (S14 : (¬ P → (Q → R)) → P ∨ (Q → R)).
  { exact (n2_54 P (Q → R)). }
  Syll_as S13 S14 S15.
  exact S15.
Qed.
    
Theorem n2_86 (P Q R : Prop) :
  ((P → Q) → (P → R)) → (P → (Q → R)).
Proof.
  assert (S1 : (¬ P ∨ Q → ¬ P ∨ R) → ¬ P ∨ (Q → R)).
  { exact (n2_85 (¬ P) Q R). }
  
  set (λ P0 Q0 : Prop, eq_to_equiv (P0 → Q0) (¬ P0 ∨ Q0) (Impl1_01 P0 Q0))
    as Impl1_01a.
  
  assert (S2 : ((P → Q) → (P → R)) → (P → (Q → R))).
  {
    rewrite <- (Impl1_01a P Q) in S1.
    rewrite <- (Impl1_01a P R) in S1.
    now rewrite <- (Impl1_01a P (Q → R)) in S1.
  }
  exact S2.
Qed.
