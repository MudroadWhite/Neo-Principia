Require Import PM.pm.lib.
Require Import PM.pm.ch1.

Theorem Abs2_01 (P : Prop) :
  (P → ¬ P) → ¬ P.
Proof.
  assert (S1 : ¬ P ∨ ¬ P → ¬ P).
  { exact (Taut1_2 (¬ P)). }
  assert (S2 : (P → ¬ P) → ¬ P).
  {
    now rewrite <- Impl1_01 in S1. 
  }
  exact S2.
Qed.

Theorem Simp2_02 (P Q : Prop) :
  Q → (P → Q).
Proof.
  assert (S1 : Q → ¬ P ∨ Q).
  { exact (Add1_3 (¬ P) Q). }
  assert (S2 : Q → (P → Q)).
  { now rewrite <- Impl1_01 in S1.  }
  exact S2.
Qed.

Theorem Transp2_03 (P Q : Prop) :
  (P → ¬ Q) → (Q → ¬ P).
Proof.
  assert (S1 : ¬ P ∨ ¬ Q → ¬ Q ∨ ¬ P).
  { exact (Perm1_4 (¬ P) (¬ Q)). }
  assert (S2 : (P → ¬ Q) → (Q → ¬ P)).
  { repeat rewrite <- Impl1_01 in S1. exact S1. }
  exact S2.
Qed.

Theorem Comm2_04 (P Q R : Prop) :
  (P → (Q → R)) → (Q → (P → R)).
Proof.
  assert (S1 : ¬ P ∨ (¬ Q ∨ R) → ¬ Q ∨ (¬ P ∨ R)).
  { exact (Assoc1_5 (¬ P) (¬ Q) R). }
  assert (S2 : (P → (Q → R)) → (Q → (P → R))).
  { repeat rewrite <- Impl1_01 in S1. exact S1. }
  exact S2.
Qed.

Theorem Syll2_05 (P Q R : Prop) :
  (Q → R) → ((P → Q) → (P → R)).
Proof.
  assert (S1 : (Q → R) → (¬ P ∨ Q → ¬ P ∨ R)).
  { exact (Sum1_6 (¬ P) Q R). }
  assert (S2 : (Q → R) → ((P → Q) → (P → R))).
  { repeat rewrite <- Impl1_01 in S1. exact S1. }
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
  { pose proof S1 as S3. MP S3 S2. exact S3. }
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
  { pose proof S1 as S3. MP S3 S2. exact S3. }
  assert (S4 : P → P ∨ P).
  { exact (n2_07 P). }
  assert (S5 : P → P).
  { pose proof S3 as S5. MP S5 S4. exact S5. }
  exact S5.
Qed.

Theorem n2_1 (P : Prop) :
  (¬ P) ∨ P.
Proof.
  assert (S1 : P → P).
  { exact (Id2_08 P). }
  assert (S2 : (¬ P) ∨ P).
  { rewrite Impl1_01 in S1. exact S1. }
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
  { pose proof S1 as S3. MP S3 S2. exact S3. }
  exact S3.
Qed.

Theorem n2_12 (P : Prop) :
  P → ¬¬ P.
Proof.
  assert (S1 : ¬ P ∨ ¬¬ P).
  { exact (n2_11 (¬ P)). }
  assert (S2 : P → ¬¬ P).
  { rewrite <- Impl1_01 in S1. exact S1. }
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
  { pose proof S1 as S3. MP S3 S2. exact S3. }
  assert (S4 : P ∨ ¬ P).
  { exact (n2_11 P). }
  assert (S5 : P ∨ ¬¬¬ P).
  { pose proof S3 as S5. MP S5 S4. exact S5. }
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
  { pose proof S1 as S3. MP S3 S2. exact S3. }
  assert (S4 : ¬¬ P → P).
  { rewrite <- Impl1_01 in S3. exact S3. }
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
  { pose proof S1 as S3. MP S3 S2. exact S3. }
  assert (S4 : (¬ P → ¬ (¬ Q)) → (¬ Q → ¬ (¬ P))).
  { exact (Transp2_03 (¬ P) (¬ Q)). }
  assert (S5 : (¬ (¬ P) → P) → ((¬ Q → ¬ (¬ P)) → (¬ Q → P))).
  { exact (Syll2_05 (¬ Q) (¬ (¬ P)) P). }
  assert (S6 : (¬ Q → ¬ (¬ P)) → (¬ Q → P)).
  { pose proof S5 as S6. pose proof (n2_14 P) as H14. MP S6 H14. exact S6. }
  assert (S7 : ((¬ P → ¬ (¬ Q)) → (¬ Q → ¬ (¬ P))) → 
               (((¬ P → Q) → (¬ P → ¬ (¬ Q))) → ((¬ P → Q) → (¬ Q → ¬ (¬ P))))).
  { exact (Syll2_05 (¬ P → Q) (¬ P → ¬ (¬ Q)) (¬ Q → ¬ (¬ P))). }
  assert (S8 : ((¬ P → Q) → (¬ P → ¬ (¬ Q))) → ((¬ P → Q) → (¬ Q → ¬ (¬ P)))).
  { pose proof S7 as S8. MP S8 S4. exact S8. }
  assert (S9 : (¬ P → Q) → (¬ Q → ¬ (¬ P))).
  { pose proof S8 as S9. MP S9 S3. exact S9. }
  assert (S10 : ((¬ Q → ¬ (¬ P)) → (¬ Q → P)) → 
                (((¬ P → Q) → (¬ Q → ¬ (¬ P))) → ((¬ P → Q) → (¬ Q → P)))).
  { exact (Syll2_05 (¬ P → Q) (¬ Q → ¬ (¬ P)) (¬ Q → P)). }
  assert (S11 : ((¬ P → Q) → (¬ Q → ¬ (¬ P))) → ((¬ P → Q) → (¬ Q → P))).
  { pose proof S10 as S11. MP S11 S6. exact S11. }
  assert (S12 : (¬ P → Q) → (¬ Q → P)).
  { pose proof S11 as S12. MP S12 S9. exact S12. }
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
  { pose proof (Syll2_05 P Q (¬¬ Q)) as S2. MP S2 S1. exact S2. }
  assert (S3 : (P → ¬¬ Q) → (¬ Q → ¬ P)).
  { exact (Transp2_03 P (¬ Q)). }
  assert (S4 : (P → Q) → (¬ Q → ¬ P)).
  { Syll_as S2 S3 S4. exact S4. }
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
  { pose proof (Syll2_05 P (¬¬ Q) Q) as S3. MP S3 S2. exact S3. }
  assert (S4 : (¬ Q → ¬ P) → (P → Q)).
  { Syll_as S1 S3 S4. exact S4. }
  exact S4.
Qed.

Theorem n2_18 (P : Prop) :
  (¬ P → P) → P.
Proof.
  assert (S1 : P → ¬¬ P).
  { exact (n2_12 P). }
  assert (S2 : (¬ P → P) → (¬ P → ¬¬ P)).
  { pose proof (Syll2_05 (¬ P) P (¬¬ P)) as S2. MP S2 S1. exact S2. }
  assert (S3 : (¬ P → ¬¬ P) → ¬¬ P).
  { exact (Abs2_01 (¬ P)). }
  assert (S4 : (¬ P → P) → ¬¬ P).
  { Syll_as S2 S3 S4. exact S4. }
  assert (S5 : ¬¬ P → P).
  { exact (n2_14 P). }
  assert (S6 : (¬ P → P) → P).
  { Syll_as S4 S5 S6. exact S6. }
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
  { Syll_as S1 S2 S3. exact S3. }
  exact S3.
Qed.

Theorem n2_21 (P Q : Prop) :
  ¬ P → (P → Q).
Proof.
  assert (S1 : ¬ P → ¬ P ∨ Q).
  { exact (n2_2 (¬ P) Q). }
  assert (S2 : ¬ P → (P → Q)).
  { repeat rewrite <- Impl1_01 in S1. exact S1. }
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
  { pose proof S2 as S3. MP S3 S1. exact S3. }
  exact S3.
Qed.

Theorem n2_25 (P Q : Prop) :
  P ∨ ((P ∨ Q) → Q).
Proof.
  assert (S1 : ¬ (P ∨ Q) ∨ (P ∨ Q)).
  { exact (n2_1 (P ∨ Q)). }
  assert (S2 : ¬ (P ∨ Q) ∨ (P ∨ Q) → P ∨ ¬ (P ∨ Q) ∨ Q).
  { pose proof (Assoc1_5 (¬ (P ∨ Q)) P Q) as Assoc1_5a.
  exact Assoc1_5a. }
  assert (S3 : P ∨ ¬ (P ∨ Q) ∨  Q).
  { pose proof S2 as S3. MP S3 S1. exact S3. }
  assert (S4 : P ∨ ((P ∨ Q) → Q)).
  { repeat rewrite <- Impl1_01 in S3. exact S3. }
  exact S4.
Qed.

Theorem n2_26 (P Q : Prop) :
  ¬ P ∨ ((P → Q) → Q).
Proof.
  assert (S1 : ¬ P ∨ ((¬ P ∨ Q) → Q)).
  {pose proof (n2_25 (¬ P) Q) as n2_25a.
  exact n2_25a. }
  assert (S2 : ¬ P ∨ ((P → Q) → Q)).
  { replace (¬ P ∨ Q) with (P → Q) in S1
  by now rewrite Impl1_01.
  exact S1. }
  exact S2.
Qed.

Theorem n2_27 (P Q : Prop) :
  P → ((P → Q) → Q).
Proof.
  assert (S1 : ¬ P ∨ ((P → Q) → Q)).
  { exact (n2_26 P Q). }
  assert (S2 : P → ((P → Q) → Q)).
  { repeat rewrite <- Impl1_01 in S1. exact S1. }
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
  { pose proof S2 as S3. MP S3 S1. exact S3. }
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
  { Syll_as S2 S3 S4. exact S4. }
  assert (S5 : P ∨ (Q ∨ R) → ((P ∨ Q) ∨ R)).
  { Syll_as S1 S4 S5. exact S5. }
  exact S5.
Qed.

Theorem n2_32 (P Q R : Prop) :
  ((P ∨ Q) ∨ R) → (P ∨ (Q ∨ R)).
Proof.
  Theorem n2_32 (P Q R : Prop) :
  ((P ∨ Q) ∨ R) → (P ∨ (Q ∨ R)).
Proof.
  Theorem n2_32 (P Q R : Prop) :
  ((P ∨ Q) ∨ R) → (P ∨ (Q ∨ R)).
Proof.
  assert (S1 : (P ∨ Q) ∨ R → R ∨ (P ∨ Q)).
  { exact (Perm1_4 (P ∨ Q) R). }
  assert (S2 : R ∨ (P ∨ Q) → P ∨ (R ∨ Q)).
  { exact (Assoc1_5 R P Q). }
  assert (S3 : P ∨ (R ∨ Q) → P ∨ (Q ∨ R)).
  { exact (n2_3 P R Q). }
  Syll_as S1 S2 H1.
  Syll_as H1 S3 H2.
  exact H2.
Qed.

(* Theorem Abb2_33 : ∀ P Q R : Prop,
  (P ∨ Q ∨ R) = ((P ∨ Q) ∨ R).
Proof. intros P Q R. rewrite → n2_32. *)

Theorem Abb2_33 (P Q R : Prop) :
  (P ∨ Q ∨ R) = ((P ∨ Q) ∨ R).
Proof.
  apply propositional_extensionality.
  split.
  {
    pose proof (n2_31 P Q R) as n2_31.
    exact n2_31.
  }
  {
    pose proof (n2_32 P Q R) as n2_32.
    exact n2_32.
  }
Qed.

Theorem n2_36 (P Q R : Prop) :
  (Q → R) → ((P ∨ Q) → (R ∨ P)).
Proof.
  assert (S1 : P ∨ R → R ∨ P).
  { exact (Perm1_4 P R). }
  assert (S2 : (P ∨ R → R ∨ P) → ((P ∨ Q → P ∨ R) → (P ∨ Q → R ∨ P))).
  { exact (Syll2_05 (P ∨ Q) (P ∨ R) (R ∨ P)). }
  assert (S3 : (P ∨ Q → P ∨ R) → (P ∨ Q → R ∨ P)).
  { pose proof S2 as S3. MP S3 S1. exact S3. }
  assert (S4 : (Q → R) → (P ∨ Q → P ∨ R)).
  { exact (Sum1_6 P Q R). }
  assert (S5 : (Q → R) → (P ∨ Q → R ∨ P)).
  { Syll_as S4 S3 S5. exact S5. }
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
  { pose proof S2 as S3. MP S3 S1. exact S3. }
  assert (S4 : (Q → R) → (P ∨ Q → P ∨ R)).
  { exact (Sum1_6 P Q R). }
  assert (S5 : (Q → R) → (Q ∨ P → P ∨ R)).
  { Syll_as S4 S3 S5. exact S5. }
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
  { pose proof S2 as S3. MP S3 S1. exact S3. }
  assert (S4 : Q ∨ P → P ∨ Q).
  { exact (Perm1_4 Q P). }
  assert (S5 : (Q ∨ P → P ∨ Q) → ((P ∨ Q → P ∨ R) → (Q ∨ P → P ∨ R))).
  { exact (Syll2_06 (Q ∨ P) (P ∨ Q) (P ∨ R)). }
  assert (S6 : (P ∨ Q → P ∨ R) → (Q ∨ P → P ∨ R)).
  { pose proof S5 as S6. MP S6 S4. exact S6. }
  assert (S7 : (P ∨ Q → P ∨ R) → (Q ∨ P → R ∨ P)).
  { Syll_as S6 S3 S7. exact S7. }
  assert (S8 : (Q → R) → (P ∨ Q → P ∨ R)).
  { exact (Sum1_6 P Q R). }
  assert (S9 : (Q → R) → (Q ∨ P → R ∨ P)).
  { Syll_as S8 S7 S9. exact S9. }
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
  { exact (n2_38 Q (P ∨ P) P). } (* 注意这里的参数绑定可能需要查证你的 n2_38 *)
  assert (S4 : (P ∨ P) ∨ Q → P ∨ Q).
  { pose proof S3 as S4. MP S4 S2. exact S4. }
  assert (S5 : P ∨ (P ∨ Q) → P ∨ Q).
  { Syll_as S1 S4 S5. exact S5. }
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
  { pose proof S3 as S4. MP S4 S2. exact S4. }
  assert (S5 : Q ∨ (P ∨ Q) → P ∨ Q).
  { Syll_as S1 S4 S5. exact S5. }
  exact S5.
Qed.

Theorem n2_42 (P Q : Prop) :
  (¬ P ∨ (P → Q)) → (P → Q).
Proof.
  assert (S1 : ¬ P ∨ (¬ P ∨ Q) → ¬ P ∨ Q).
  { exact (n2_4 (¬ P) Q). }
  assert (S2 : ¬ P ∨ (P → Q) → (P → Q)).
  { repeat rewrite <- (Impl1_01 P Q) in S1. exact S1. }
  exact S2.
Qed.

Theorem n2_43 (P Q : Prop) :
  (P → (P → Q)) → (P → Q).
Proof.
  assert (S1 : ¬ P ∨ (P → Q) → (P → Q)).
  { exact (n2_42 P Q). }
  assert (S2 : (P → (P → Q)) → (P → Q)).
  { repeat rewrite <- Impl1_01 in S1. exact S1. }
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
  { pose proof S2 as S3. MP S3 S1. exact S3. }
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
  { pose proof S2 as S3. MP S3 S1. exact S3. }
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
  { Syll_as S1 S2 S3. exact S3. }
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
  { Syll_as S1 S2 S3. exact S3. }
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
  { Syll_as S1 S2 S3. exact S3. }
  exact S3.
Qed.

Theorem n2_5 (P Q : Prop) :
  ¬ (P → Q) → (¬ P → Q).
Proof.
  assert (S1 : ¬ (¬ P ∨ Q) → ¬ (¬ P) ∨ Q).
  { exact (n2_47 (¬ P) Q). }
  assert (S2 : ¬ (P → Q) → (¬ P → Q)).
  { repeat rewrite <- Impl1_01 in S1. exact S1. }
  exact S2.
Qed.

Theorem n2_51 (P Q : Prop) :
  ¬ (P → Q) → (P → ¬ Q).
Proof.
  assert (S1 : ¬ (¬ P ∨ Q) → ¬ P ∨ ¬ Q).
  { exact (n2_48 (¬ P) Q). }
  assert (S2 : ¬ (P → Q) → (P → ¬ Q)).
  { repeat rewrite <- Impl1_01 in S1. exact S1. }
  exact S2.
Qed.

Theorem n2_52 (P Q : Prop) :
  ¬ (P → Q) → (¬ P → ¬ Q).
Proof.
  assert (S1 : ¬ (¬ P ∨ Q) → ¬ (¬ P) ∨ ¬ Q).
  { exact (n2_49 (¬ P) Q). }
  assert (S2 : ¬ (P → Q) → (¬ P → ¬ Q)).
  { repeat rewrite <- Impl1_01 in S1. exact S1. }
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
  { Syll_as S1 S2 S3. exact S3. }
  exact S3.
Qed.

Theorem n2_53 (P Q : Prop) :
  (P ∨ Q) → (¬ P → Q).
Proof.
  pose proof (n2_12 P) as n2_12a.
  pose proof (n2_38 Q P (¬¬ P)) as n2_38a.
  MP n2_38a n2_12a.
  replace (¬¬ P ∨ Q) with (¬ P → Q) in n2_38a
    by now rewrite Impl1_01.
  exact n2_38a.
Qed.

Theorem n2_54 (P Q : Prop) :
  (¬ P → Q) → (P ∨ Q).
Proof.
  pose proof (n2_14 P) as n2_14a.
  pose proof (n2_38 Q (¬¬ P) P) as n2_38a.
  MP n2_38a n2_14a.
  replace (¬¬ P ∨ Q) with (¬ P → Q) in n2_38a
    by now rewrite Impl1_01.
  exact n2_38a.
Qed.

Theorem n2_55 (P Q : Prop) :
  ¬ P → ((P ∨ Q) → Q).
Proof.
  pose proof (n2_53 P Q) as n2_53a.
  pose proof (Comm2_04 (P ∨ Q) (¬ P) Q) as Comm2_04a.
  MP Comm2_04a n2_53a.
  exact Comm2_04a.
Qed.

Theorem n2_56 (P Q : Prop) :
  ¬ Q → ((P ∨ Q) → P).
Proof.
  pose proof (n2_55 Q P) as n2_55a.
  pose proof (Perm1_4 P Q) as Perm1_4a.
  pose proof (Syll2_06 (P ∨ Q) (Q ∨ P) P) as Syll2_06a.
  MP Syll2_06a Perm1_4a.
  Syll_as n2_55a Syll2_06a Sa.
  exact Sa.
Qed.

Theorem n2_6 (P Q : Prop) :
  (¬ P → Q) → ((P → Q) → Q).
Proof.
  pose proof (n2_38 Q (¬ P) Q) as n2_38a.
  pose proof (Taut1_2 Q) as Taut1_2a.
  pose proof (Syll2_05 (¬ P ∨ Q) (Q ∨ Q) Q) as Syll2_05a.
  MP Syll2_05a Taut1_2a.
  Syll_as n2_38a Syll2_05a S.
  replace (¬ P ∨ Q) with (P → Q) in S
    by now rewrite Impl1_01.
  exact S.
Qed.

Theorem n2_61 (P Q : Prop) :
  (P → Q) → ((¬ P → Q) → Q).
Proof.
  pose proof (n2_6 P Q) as n2_6a.
  pose proof (Comm2_04 (¬ P → Q) (P → Q) Q) as Comm2_04a.
  MP Comm2_04a n2_6a.
  exact Comm2_04a.
Qed.

Theorem n2_62 (P Q : Prop) :
  (P ∨ Q) → ((P → Q) → Q).
Proof.
  pose proof (n2_53 P Q) as n2_53a.
  pose proof (n2_6 P Q) as n2_6a.
  Syll_as n2_53a n2_6a S.
  exact S.
Qed.

Theorem n2_621 (P Q : Prop) :
  (P → Q) → ((P ∨ Q) → Q).
Proof.
  pose proof (n2_62 P Q) as n2_62a.
  pose proof (Comm2_04 (P ∨ Q) (P → Q) Q) as Comm2_04a.
  MP Comm2_04a n2_62a.
  exact Comm2_04a.
Qed.

Theorem n2_63 (P Q : Prop) :
  (P ∨ Q) → ((¬ P ∨ Q) → Q).
Proof.
  pose proof (n2_62 P Q) as n2_62a.
  replace (P → Q) with (¬ P ∨ Q) in n2_62a
    by now rewrite Impl1_01.
  exact n2_62a.
Qed.

Theorem n2_64 (P Q : Prop) :
  (P ∨ Q) → ((P ∨ ¬ Q) → P).
Proof.
  pose proof (n2_63 Q P) as n2_63a.
  pose proof (Perm1_4 P Q) as Perm1_4a.
  Syll_as Perm1_4a n2_63a Ha.
  pose proof (Syll2_06 (P ∨ ¬ Q) (¬ Q ∨ P) P) as Syll2_06a.
  pose proof (Perm1_4 P (¬ Q)) as Perm1_4b.
  MP Syll2_06a Perm1_4b.
  Syll_as Ha Syll2_06a S.
  exact S.
Qed.

Theorem n2_65 (P Q : Prop) :
  (P → Q) → ((P → ¬ Q) → ¬ P).
Proof.
  pose proof (n2_64 (¬ P) Q) as n2_64a.
  replace (¬ P ∨ Q) with (P → Q) in n2_64a.
  replace (¬ P ∨ ¬ Q) with (P → ¬ Q) in n2_64a.
  exact n2_64a.
  all: now rewrite Impl1_01.
Qed.

Theorem n2_67 (P Q : Prop) :
  ((P ∨ Q) → Q) → (P → Q).
Proof.
  pose proof (n2_54 P Q) as n2_54a.
  pose proof (Syll2_06 (¬ P → Q) (P ∨ Q) Q) as Syll2_06a.
  MP Syll2_06a n2_54a.
  pose proof (n2_24  P Q) as n2_24.
  pose proof (Syll2_06 P (¬ P → Q) Q) as Syll2_06b.
  MP Syll2_06b n2_24.
  Syll_as Syll2_06a Syll2_06b S.
  exact S.
Qed.

Theorem n2_68 (P Q : Prop) :
  ((P → Q) → Q) → (P ∨ Q).
Proof.
  pose proof (n2_67 (¬ P) Q) as n2_67a.
  replace (¬ P ∨ Q) with (P → Q) in n2_67a
    by now rewrite Impl1_01.
  pose proof (n2_54 P Q) as n2_54a.
  Syll_as n2_67a n2_54a S.
  exact S.
Qed.

Theorem n2_69 (P Q : Prop) :
  ((P → Q) → Q) → ((Q → P) → P).
Proof.
  pose proof (n2_68 P Q) as n2_68a.
  pose proof (Perm1_4 P Q) as Perm1_4a.
  Syll_as n2_68a Perm1_4a Sa.
  pose proof (n2_62 Q P) as n2_62a.
  Syll_as Sa n2_62a Sb.
  exact Sb.
Qed.

Theorem n2_73 (P Q R : Prop) :
  (P → Q) → (((P ∨ Q) ∨ R) → (Q ∨ R)).
Proof.
  pose proof (n2_621 P Q) as n2_621a.
  pose proof (n2_38 R (P ∨ Q) Q) as n2_38a.
  Syll_as n2_621a n2_38a S.
  exact S.
Qed.

Theorem n2_74 (P Q R : Prop) :
  (Q → P) → ((P ∨ Q) ∨ R) → (P ∨ R).
Proof.
  pose proof (n2_73 Q P R) as n2_73a.
  pose proof (Assoc1_5 P Q R) as Assoc1_5a.
  pose proof (n2_31 Q P R) as n2_31a. (*not cited*)
  Syll_as Assoc1_5a n2_31a Sa.
  pose proof (n2_32 P Q R) as n2_32a. (*not cited*)
  Syll_as n2_32a Sa Sb.
  pose proof (Syll2_06 ((P ∨ Q) ∨ R) ((Q ∨ P) ∨ R) (P ∨ R)) as Syll2_06a.
  MP Syll2_06a Sb.
  Syll_as n2_73a Syll2_06a H.
  exact H.
Qed.

Theorem n2_75 (P Q R : Prop) :
  (P ∨ Q) → ((P ∨ (Q → R)) → (P ∨ R)).
Proof.
  pose proof (n2_74 P (¬ Q) R) as n2_74a.
  pose proof (n2_53 Q P) as n2_53a.
  Syll_as n2_53a n2_74a Sa.
  pose proof (n2_31 P (¬ Q) R) as n2_31a.
  pose proof (Syll2_06 (P ∨ (¬ Q) ∨ R) ((P ∨ (¬ Q)) ∨ R) (P ∨ R)) as Syll2_06a.
  MP Syll2_06a n2_31a.
  Syll_as Sa Syll2_06a Sb.
  pose proof (Perm1_4 P Q) as Perm1_4a. (*not cited*)
  Syll_as Perm1_4a Sb Sc.
  replace (¬ Q ∨ R) with (Q → R) in Sc
    by now rewrite Impl1_01.
  exact Sc.
Qed.

Theorem n2_76 (P Q R : Prop) :
  (P ∨ (Q → R)) → ((P ∨ Q) → (P ∨ R)).
Proof.
  pose proof (n2_75 P Q R) as n2_75a.
  pose proof (Comm2_04 (P ∨ Q) (P ∨ (Q → R)) (P ∨ R)) as Comm2_04a.
  MP Comm2_04a n2_75a.
  exact Comm2_04a.
Qed.

Theorem n2_77 (P Q R : Prop) :
  (P → (Q → R)) → ((P → Q) → (P → R)).
Proof.
  pose proof (n2_76 (¬ P) Q R) as n2_76a.
  replace (¬ P ∨ (Q → R)) with (P → Q → R) in n2_76a.
  replace (¬ P ∨ Q) with (P → Q) in n2_76a.
  replace (¬ P ∨ R) with (P → R) in n2_76a.
  exact n2_76a.
  all: now rewrite Impl1_01.
Qed.

Theorem n2_8 (Q R S : Prop) :
  (Q ∨ R) → ((¬ R ∨ S) → (Q ∨ S)).
Proof.
  pose proof (n2_53 R Q) as n2_53a.
  pose proof (Perm1_4 Q R) as Perm1_4a.
  Syll_as Perm1_4a n2_53a Ha.
  pose proof (n2_38 S (¬ R) Q) as n2_38a.
  Syll_as Ha n2_38a Hb.
  exact Hb.
Qed.

Theorem n2_81 (P Q R S : Prop) :
  (Q → (R → S)) → ((P ∨ Q) → ((P ∨ R) → (P ∨ S))).
Proof.
  pose proof (Sum1_6 P Q (R → S)) as Sum1_6a.
  pose proof (n2_76 P R S) as n2_76a.
  pose proof (Syll2_05 (P ∨ Q) (P ∨ (R → S)) ((P ∨ R) → (P ∨ S))) as Syll2_05a.
  MP Syll2_05a n2_76a.
  Syll_as Sum1_6a Syll2_05a H.
  exact H.
Qed.

Theorem n2_82 (P Q R S : Prop) :
  (P ∨ Q ∨ R) → ((P ∨ ¬ R ∨ S) → (P ∨ Q ∨ S)).
Proof.
  pose proof (n2_8 Q R S) as n2_8a.
  pose proof (n2_81 P (Q ∨ R) (¬ R ∨ S) (Q ∨ S)) as n2_81a.
  MP n2_81a n2_8a.
  exact n2_81a.
Qed.

Theorem n2_83 (P Q R S : Prop) :
  (P → (Q → R)) → ((P → (R → S)) → (P → (Q → S))).
Proof.
  pose proof (n2_82 (¬ P) (¬ Q) R S) as n2_82a.
  replace (¬ Q ∨ R) with (Q → R) in n2_82a.
  replace (¬ P ∨ (Q → R)) with (P → Q → R) in n2_82a.
  replace (¬ R ∨ S) with (R → S) in n2_82a.
  replace (¬ P ∨ (R → S)) with (P → R → S) in n2_82a.
  replace (¬ Q ∨ S) with (Q → S) in n2_82a.
  replace (¬ P ∨ (Q → S)) with (P → Q → S) in n2_82a.
  exact n2_82a.
  all : now rewrite Impl1_01.
Qed.

Theorem n2_85 (P Q R : Prop) :
  ((P ∨ Q) → (P ∨ R)) → (P ∨ (Q → R)).
Proof.
  pose proof (Add1_3 P Q) as Add1_3a.
  pose proof (Syll2_06 Q (P ∨ Q) R) as Syll2_06a.
  MP Syll2_06a Add1_3a.
  pose proof (n2_55 P R) as n2_55a.
  pose proof (Syll2_05 (P ∨ Q) (P ∨ R) R) as Syll2_05a.
  Syll_as n2_55a Syll2_05a Ha.
  pose proof (n2_83 (¬ P) ((P ∨ Q) → (P ∨ R)) ((P ∨ Q) → R) (Q → R)) as n2_83a.
  MP n2_83a Ha.
  pose proof (Comm2_04 (¬ P) (P ∨ Q → P ∨ R) (Q → R)) as Comm2_04a.
  Syll_as n2_83a Comm2_04a Hb.
  pose proof (n2_54 P (Q → R)) as n2_54a.
  pose proof (Simp2_02 (¬ P) ((P ∨ Q → R) → (Q → R))) as Simp2_02a. (*Not cited*)
  (*Greg's suggestion per the BRS list on June 25, 2017.*)
  MP Simp2_02a Syll2_06a.
  MP Hb Simp2_02a.
  Syll_as Hb n2_54a Hc.
  exact Hc.
Qed.

Theorem n2_86 (P Q R : Prop) :
  ((P → Q) → (P → R)) → (P → (Q → R)).
Proof.
  pose proof (n2_85 (¬ P) Q R) as n2_85a.
  replace (¬ P ∨ Q) with (P → Q) in n2_85a.
  replace (¬ P ∨ R) with (P → R) in n2_85a.
  replace (¬ P ∨ (Q → R)) with (P → Q → R) in n2_85a.
  exact n2_85a.
  all: now rewrite Impl1_01.
Qed.
