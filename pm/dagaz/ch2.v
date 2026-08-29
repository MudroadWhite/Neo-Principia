Require Import PM.pm.lib.
Require Import PM.pm.ch1.

Theorem Abs2_01 (P : Prop) :
  (P → ¬ P) → ¬ P.
Proof.
  assert (S1 : ¬ P ∨ ¬ P → ¬ P).
  { exact (Taut1_2 (¬ P)). }
  assert (S2 : (P → ¬ P) → ¬ P).
  {
    pose proof S1 as S1a.
    rewrite <- Impl1_01 in S1a.
    exact S1a.
  }
  exact S2.
Qed.

Theorem Simp2_02 (P Q : Prop) :
  Q → (P → Q).
Proof.
  assert (S1 : Q → ¬ P ∨ Q).
  { exact (Add1_3 (¬ P) Q). }
  assert (S2 : Q → (P → Q)).
  {
    pose proof S1 as S1a.
    rewrite <- Impl1_01 in S1a.
    exact S1a.
  }
  exact S2.
Qed.

Theorem Transp2_03 (P Q : Prop) :
  (P → ¬ Q) → (Q → ¬ P).
Proof.
  assert (S1 : ¬ P ∨ ¬ Q → ¬ Q ∨ ¬ P).
  { exact (Perm1_4 (¬ P) (¬ Q)). }
  assert (S2 : (P → ¬ Q) → (Q → ¬ P)).
  {
    pose proof S1 as S1a.
    repeat rewrite <- Impl1_01 in S1a.
    exact S1a.
  }
  exact S2.
Qed.

Theorem Comm2_04 (P Q R : Prop) :
  (P → (Q → R)) → (Q → (P → R)).
Proof.
  assert (S1 : ¬ P ∨ (¬ Q ∨ R) → ¬ Q ∨ (¬ P ∨ R)).
  { exact (Assoc1_5 (¬ P) (¬ Q) R). }
  assert (S2 : (P → (Q → R)) → (Q → (P → R))).
  {
    pose proof S1 as S1a.
    repeat rewrite <- Impl1_01 in S1a.
    exact S1a.
  }
  exact S2.
Qed.

Theorem Syll2_05 (P Q R : Prop) :
  (Q → R) → ((P → Q) → (P → R)).
Proof.
  assert (S1 : (Q → R) → (¬ P ∨ Q → ¬ P ∨ R)).
  { exact (Sum1_6 (¬ P) Q R). }
  assert (S2 : (Q → R) → ((P → Q) → (P → R))).
  {
    pose proof S1 as S1a.
    repeat rewrite <- Impl1_01 in S1a.
    exact S1a.
  }
  exact S2.
Qed.

Theorem Syll2_06 (P Q R : Prop) :
  (P → Q) → ((Q → R) → (P → R)).
Proof.
  assert (S1 :
    ((Q → R) → ((P → Q) → (P → R)))
      → ((P → Q) → ((Q → R) → (P → R)))).
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
  assert (S1 : (P ∨ P → P) → ((P → P ∨ P) → (P → P))).
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
  (* TOOLS *)
  set (λ P0 Q0 : Prop, eq_to_equiv (P0 → Q0) (¬ P0 ∨ Q0) (Impl1_01 P0 Q0))
    as Impl1_01a.
  (* ******** *)
  pose proof (Id2_08 P) as Id2_08.
  rewrite -> (Impl1_01a P P) in Id2_08.
  exact Id2_08.
Qed.

Theorem n2_11 (P : Prop) :
  P ∨ ¬ P.
Proof.
  assert (S1 : ¬ P ∨ P → P ∨ ¬ P).
  { exact (Perm1_4 (¬ P) P). }
  assert (S2 : P ∨ ¬ P).
  {
    pose proof (n2_1 P) as n2_1.
    now MP S1 n2_1.
  }
  exact S2.
Qed.

Theorem n2_12 (P : Prop) :
  P → ¬¬ P.
Proof.
  assert (S1 : ¬ P ∨ ¬¬ P).
  { exact (n2_11 (¬ P)). }
  assert (S2 : P → ¬¬ P).
  {
    pose proof S1 as S1a.
    rewrite <- Impl1_01 in S1a.
    exact S1a.
  }
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
  assert (S4 : P ∨ ¬¬¬ P).
  {
    pose proof (n2_11 P) as n2_11.
    now MP S3 n2_11.
  }
  exact S4.
Qed.

Theorem n2_14 (P : Prop) :
  ¬¬ P → P.
Proof.
  assert (S1 : P ∨ ¬¬¬ P → ¬¬¬ P ∨ P).
  { exact (Perm1_4 P (¬¬¬ P)). }
  assert (S2 : ¬¬¬ P ∨ P).
  {
    pose proof (n2_13 P) as n2_13.
    now MP S1 n2_13.
  }
  assert (S3 : ¬¬ P → P).
  {
    pose proof S2 as S2a.
    rewrite <- Impl1_01 in S2a.
    exact S2a.
  }
  exact S3.
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
    pose proof (n2_14 P) as n2_14.
    now MP S5 n2_14.
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
    pose proof (Syll2_05 P Q (¬¬ Q)) as Syll2_05.
    now MP Syll2_05 S1.
  }
  assert (S3 : (P → ¬¬ Q) → (¬ Q → ¬ P)).
  { exact (Transp2_03 P (¬ Q)). }
  assert (S4 : (P → Q) → (¬ Q → ¬ P)).
  {
    Syll_as S2 S3 S4.
    exact S4.
  }
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
  {
    Syll_as S1 S3 S4.
    exact S4.
  }
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
  Syll_as S2 S3 S4.
  assert (S5 : ¬¬ P → P).
  { exact (n2_14 P). }
  Syll_as S4 S5 S6.
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
  {
    Syll_as S1 S2 S3.
    exact S3.
  }
  exact S3.
Qed.

Theorem n2_21 (P Q : Prop) :
  ¬ P → (P → Q).
Proof.
  (* TOOLS *)
  set (λ P0 Q0 : Prop, eq_to_equiv (P0 → Q0) (¬ P0 ∨ Q0) (Impl1_01 P0 Q0))
    as Impl1_01a.
  (* ******** *)
  pose proof (n2_2 (¬ P) Q) as n2_2.
  rewrite <- (Impl1_01a P Q) in n2_2.
  exact n2_2.
Qed.

Theorem n2_24 (P Q : Prop) :
  P → (¬ P → Q).
Proof.
  (* TOOLS *)
  set (λ P0 Q0 R0 : Prop, Comm2_04 P0 Q0 R0) as Comm2_04a.
  (* ******** *)
  pose proof (n2_21 P Q) as n2_21.
  pose proof (Comm2_04a (¬ P) P Q) as Comm2_04b.
  now MP Comm2_04b n2_21.
Qed.

Theorem n2_25 (P Q : Prop) :
  P ∨ ((P ∨ Q) → Q).
Proof.
  (* TOOLS *)
  set (λ P0 Q0 : Prop, eq_to_equiv (P0 → Q0) (¬ P0 ∨ Q0) (Impl1_01 P0 Q0))
    as Impl1_01a.
  (* ******** *)
  assert (S1 : ¬ (P ∨ Q) ∨ (P ∨ Q)).
  { exact (n2_1 (P ∨ Q)). }
  assert (S2 : P ∨ (¬ (P ∨ Q) ∨ Q)).
  {
    pose proof (Assoc1_5 (¬ (P ∨ Q)) P Q) as Assoc1_5.
    now MP Assoc1_5 S1.
  }
  assert (S3 : P ∨ ((P ∨ Q) → Q)).
  {
    pose proof S2 as S2a.
    rewrite <- (Impl1_01a (P ∨ Q) Q) in S2a.
    exact S2a.
  }
  exact S3.
Qed.

Theorem n2_26 (P Q : Prop) :
  ¬ P ∨ ((P → Q) → Q).
Proof.
  (* TOOLS *)
  set (λ P0 Q0 : Prop, eq_to_equiv (P0 → Q0) (¬ P0 ∨ Q0) (Impl1_01 P0 Q0))
    as Impl1_01a.
  (* ******** *)
  pose proof (n2_25 (¬ P) Q) as n2_25.
  rewrite <- (Impl1_01a P Q) in n2_25.
  exact n2_25.
Qed.

Theorem n2_27 (P Q : Prop) :
  P → ((P → Q) → Q).
Proof.
  (* TOOLS *)
  set (λ P0 Q0 : Prop, eq_to_equiv (P0 → Q0) (¬ P0 ∨ Q0) (Impl1_01 P0 Q0))
    as Impl1_01a.
  (* ******** *)
  pose proof (n2_26 P Q) as n2_26.
  rewrite <- (Impl1_01a P ((P → Q) → Q)) in n2_26.
  exact n2_26.
Qed.

Theorem n2_3 (P Q R : Prop) :
  (P ∨ (Q ∨ R)) → (P ∨ (R ∨ Q)).
Proof.
  assert (S1 : Q ∨ R → R ∨ Q).
  { exact (Perm1_4 Q R). }
  assert (S2 : P ∨ (Q ∨ R) → P ∨ (R ∨ Q)).
  {
    pose proof (Sum1_6 P (Q ∨ R) (R ∨ Q)) as Sum1_6.
    now MP Sum1_6 S1.
  }
  exact S2.
Qed.

Theorem n2_31 (P Q R : Prop) :
  (P ∨ (Q ∨ R)) → ((P ∨ Q) ∨ R).
Proof.
  assert (S1 : P ∨ (Q ∨ R) → P ∨ (R ∨ Q)).
  { exact (n2_3 P Q R). }
  assert (S2 : P ∨ (R ∨ Q) → R ∨ (P ∨ Q)).
  { exact (Assoc1_5 P R Q). }
  Syll_as S1 S2 S3.
  assert (S4 : R ∨ (P ∨ Q) → (P ∨ Q) ∨ R).
  { exact (Perm1_4 R (P ∨ Q)). }
  assert (S5 : P ∨ (Q ∨ R) → (P ∨ Q) ∨ R).
  {
    Syll_as S3 S4 S5.
    exact S5.
  }
  exact S5.
Qed.

Theorem n2_32 (P Q R : Prop) :
  ((P ∨ Q) ∨ R) → (P ∨ (Q ∨ R)).
Proof.
  assert (S1 : (P ∨ Q) ∨ R → R ∨ (P ∨ Q)).
  { exact (Perm1_4 (P ∨ Q) R). }
  assert (S2 : R ∨ (P ∨ Q) → P ∨ (R ∨ Q)).
  { exact (Assoc1_5 R P Q). }
  assert (S3 : (P ∨ Q) ∨ R → P ∨ (R ∨ Q)).
  {
    Syll_as S1 S2 S3.
    exact S3.
  }
  assert (S4 : P ∨ (R ∨ Q) → P ∨ (Q ∨ R)).
  { exact (n2_3 P R Q). }
  assert (S5 : (P ∨ Q) ∨ R → P ∨ (Q ∨ R)).
  {
    Syll_as S3 S4 S5.
    exact S5.
  }
  exact S5.
Qed.

Definition Abb2_33 (P Q R : Prop) :
  (P ∨ Q ∨ R) = ((P ∨ Q) ∨ R).
Admitted.

Theorem n2_36 (P Q R : Prop) :
  (Q → R) → ((P ∨ Q) → (R ∨ P)).
Proof.
  assert (S1 : (P ∨ Q → P ∨ R) → (P ∨ Q → R ∨ P)).
  {
    pose proof (Syll2_05 (P ∨ Q) (P ∨ R) (R ∨ P)) as Syll2_05.
    pose proof (Perm1_4 P R) as Perm1_4.
    now MP Syll2_05 Perm1_4.
  }
  assert (S2 : (Q → R) → (P ∨ Q → P ∨ R)).
  { exact (Sum1_6 P Q R). }
  assert (S3 : (Q → R) → (P ∨ Q → R ∨ P)).
  {
    Syll_as S2 S1 S3.
    exact S3.
  }
  exact S3.
Qed.

Theorem n2_37 (P Q R : Prop) :
  (Q → R) → ((Q ∨ P) → (P ∨ R)).
Proof.
  pose proof (Syll2_06 (Q ∨ P) (P ∨ Q) (P ∨ R)) as Syll2_06.
  pose proof (Perm1_4 Q P) as Perm1_4.
  MP Syll2_06 Perm1_4.
  pose proof (Sum1_6 P Q R) as Sum1_6.
  Syll_as Sum1_6 Syll2_06 n2_37.
  exact n2_37.
Qed.

Theorem n2_38 (P Q R : Prop) :
  (Q → R) → ((Q ∨ P) → (R ∨ P)).
Proof.
  assert (S1 : (Q → R) → (Q ∨ P → P ∨ R)).
  { exact (n2_37 P Q R). }
  assert (S2 : (Q ∨ P → P ∨ R) → (Q ∨ P → R ∨ P)).
  {
    pose proof (Syll2_05 (Q ∨ P) (P ∨ R) (R ∨ P)) as Syll2_05.
    pose proof (Perm1_4 P R) as Perm1_4.
    now MP Syll2_05 Perm1_4.
  }
  assert (S3 : (Q → R) → (Q ∨ P → R ∨ P)).
  {
    Syll_as S1 S2 S3.
    exact S3.
  }
  exact S3.
Qed.

Theorem n2_4 (P Q : Prop) :
  (P ∨ (P ∨ Q)) → (P ∨ Q).
Proof.
  assert (S1 : P ∨ (P ∨ Q) → (P ∨ P) ∨ Q).
  { exact (n2_31 P P Q). }
  assert (S2 : (P ∨ P) ∨ Q → P ∨ Q).
  {
    pose proof (n2_38 Q (P ∨ P) P) as n2_38.
    pose proof (Taut1_2 P) as Taut1_2.
    now MP n2_38 Taut1_2.
  }
  assert (S3 : P ∨ (P ∨ Q) → P ∨ Q).
  {
    Syll_as S1 S2 S3.
    exact S3.
  }
  exact S3.
Qed.

Theorem n2_41 (P Q : Prop) :
  (Q ∨ (P ∨ Q)) → (P ∨ Q).
Proof.
  assert (S1 : Q ∨ (P ∨ Q) → P ∨ (Q ∨ Q)).
  { exact (Assoc1_5 Q P Q). }
  assert (S2 : P ∨ (Q ∨ Q) → P ∨ Q).
  {
    pose proof (Sum1_6 P (Q ∨ Q) Q) as Sum1_6.
    pose proof (Taut1_2 Q) as Taut1_2.
    now MP Sum1_6 Taut1_2.
  }
  assert (S3 : Q ∨ (P ∨ Q) → P ∨ Q).
  {
    Syll_as S1 S2 S3.
    exact S3.
  }
  exact S3.
Qed.

Theorem n2_42 (P Q : Prop) :
  (¬ P ∨ (P → Q)) → (P → Q).
Proof.
  (* TOOLS *)
  set (λ P0 Q0 : Prop, eq_to_equiv (P0 → Q0) (¬ P0 ∨ Q0) (Impl1_01 P0 Q0))
    as Impl1_01a.
  (* ******** *)
  pose proof (n2_4 (¬ P) Q) as n2_4.
  repeat rewrite <- (Impl1_01a P Q) in n2_4.
  exact n2_4.
Qed.

Theorem n2_43 (P Q : Prop) :
  (P → (P → Q)) → (P → Q).
Proof.
  (* TOOLS *)
  set (λ P0 Q0 : Prop, eq_to_equiv (P0 → Q0) (¬ P0 ∨ Q0) (Impl1_01 P0 Q0))
    as Impl1_01a.
  (* ******** *)
  pose proof (n2_42 P Q) as n2_42.
  rewrite <- (Impl1_01a P (P → Q)) in n2_42.
  exact n2_42.
Qed.

Theorem n2_45 (P Q : Prop) :
  ¬ (P ∨ Q) → ¬ P.
Proof.
  pose proof (Transp2_16 P (P ∨ Q)) as Transp2_16.
  pose proof (n2_2 P Q) as n2_2.
  now MP Transp2_16 n2_2.
Qed.

Theorem n2_46 (P Q : Prop) :
  ¬ (P ∨ Q) → ¬ Q.
Proof.
  pose proof (Transp2_16 Q (P ∨ Q)) as Transp2_16.
  pose proof (Add1_3 P Q) as Add1_3.
  now MP Transp2_16 Add1_3.
Qed.

Theorem n2_47 (P Q : Prop) :
  ¬ (P ∨ Q) → (¬ P ∨ Q).
Proof.
  pose proof (n2_45 P Q) as n2_45.
  pose proof (n2_2 (¬ P) Q) as n2_2.
  Syll_as n2_45 n2_2 n2_47a.
  exact n2_47a.
Qed.

Theorem n2_48 (P Q : Prop) :
  ¬ (P ∨ Q) → (P ∨ ¬ Q).
Proof.
  pose proof (n2_46 P Q) as n2_46.
  pose proof (Add1_3 P (¬ Q)) as Add1_3.
  Syll_as n2_46 Add1_3 n2_48a.
  exact n2_48a.
Qed.

Theorem n2_49 (P Q : Prop) :
  ¬ (P ∨ Q) → (¬ P ∨ ¬ Q).
Proof.
  pose proof (n2_45 P Q) as n2_45.
  pose proof (n2_2 (¬ P) (¬ Q)) as n2_2.
  Syll_as n2_45 n2_2 n2_49a.
  exact n2_49a.
Qed.

Theorem n2_5 (P Q : Prop) :
  ¬ (P → Q) → (¬ P → Q).
Proof.
  (* TOOLS *)
  set (λ P0 Q0 : Prop, eq_to_equiv (P0 → Q0) (¬ P0 ∨ Q0) (Impl1_01 P0 Q0))
    as Impl1_01a.
  (* ******** *)
  pose proof (n2_47 (¬ P) Q) as n2_47.
  rewrite <- (Impl1_01a (¬ P) Q) in n2_47.
  rewrite <- (Impl1_01a P Q) in n2_47.
  exact n2_47.
Qed.

Theorem n2_51 (P Q : Prop) :
  ¬ (P → Q) → (P → ¬ Q).
Proof.
  (* TOOLS *)
  set (λ P0 Q0 : Prop, eq_to_equiv (P0 → Q0) (¬ P0 ∨ Q0) (Impl1_01 P0 Q0))
    as Impl1_01a.
  (* ******** *)
  pose proof (n2_48 (¬ P) Q) as n2_48.
  rewrite <- (Impl1_01a P (¬ Q)) in n2_48.
  rewrite <- (Impl1_01a P Q) in n2_48.
  exact n2_48.
Qed.

Theorem n2_52 (P Q : Prop) :
  ¬ (P → Q) → (¬ P → ¬ Q).
Proof.
  (* TOOLS *)
  set (λ P0 Q0 : Prop, eq_to_equiv (P0 → Q0) (¬ P0 ∨ Q0) (Impl1_01 P0 Q0))
    as Impl1_01a.
  (* ******** *)
  pose proof (n2_49 (¬ P) Q) as n2_49.
  rewrite <- (Impl1_01a (¬ P) (¬ Q)) in n2_49.
  rewrite <- (Impl1_01a P Q) in n2_49.
  exact n2_49.
Qed.

Theorem n2_521 (P Q : Prop) :
  ¬ (P → Q) → (Q → P).
Proof.
  pose proof (n2_52 P Q) as n2_52.
  pose proof (Transp2_17 Q P) as Transp2_17.
  Syll_as n2_52 Transp2_17 n2_521a.
  exact n2_521a.
Qed.

Theorem n2_53 (P Q : Prop) :
  (P ∨ Q) → (¬ P → Q).
Proof.
  (* TOOLS *)
  set (λ P0 Q0 : Prop, eq_to_equiv (P0 → Q0) (¬ P0 ∨ Q0) (Impl1_01 P0 Q0))
    as Impl1_01a.
  (* ******** *)
  assert (S1 : P ∨ Q → ¬¬ P ∨ Q).
  {
    pose proof (n2_38 Q P (¬¬ P)) as n2_38.
    pose proof (n2_12 P) as n2_12.
    now MP n2_38 n2_12.
  }
  assert (S2 : (P ∨ Q) → (¬ P → Q)).
  {
    pose proof S1 as S1a.
    rewrite <- (Impl1_01a (¬ P) Q) in S1a.
    exact S1a.
  }
  exact S2.
Qed.

Theorem n2_54 (P Q : Prop) :
  (¬ P → Q) → (P ∨ Q).
Proof.
  (* TOOLS *)
  set (λ P0 Q0 : Prop, eq_to_equiv (P0 → Q0) (¬ P0 ∨ Q0) (Impl1_01 P0 Q0))
    as Impl1_01a.
  (* ******** *)
  pose proof (n2_38 Q (¬¬ P) P) as n2_38.
  pose proof (n2_14 P) as n2_14.
  MP n2_38 n2_14.
  rewrite <- (Impl1_01a (¬ P) Q) in n2_38.
  exact n2_38.
Qed.

Theorem n2_55 (P Q : Prop) :
  ¬ P → ((P ∨ Q) → Q).
Proof.
  pose proof (Comm2_04 (P ∨ Q) (¬ P) Q) as Comm2_04.
  pose proof (n2_53 P Q) as n2_53.
  now MP Comm2_04 n2_53.
Qed.

Theorem n2_56 (P Q : Prop) :
  ¬ Q → ((P ∨ Q) → P).
Proof.
  assert (S1 : ¬ Q → (Q ∨ P → P)).
  { exact (n2_55 Q P). }
  assert (S2 : (Q ∨ P → P) → (P ∨ Q → P)).
  {
    pose proof (Syll2_06 (P ∨ Q) (Q ∨ P) P) as Syll2_06.
    pose proof (Perm1_4 P Q) as Perm1_4.
    now MP Syll2_06 Perm1_4.
  }
  assert (S3 : ¬ Q → ((P ∨ Q) → P)).
  {
    Syll_as S1 S2 S3.
    exact S3.
  }
  exact S3.
Qed.

Theorem n2_6 (P Q : Prop) :
  (¬ P → Q) → ((P → Q) → Q).
Proof.
  (* TOOLS *)
  set (λ P0 Q0 : Prop, eq_to_equiv (P0 → Q0) (¬ P0 ∨ Q0) (Impl1_01 P0 Q0))
    as Impl1_01a.
  (* ******** *)
  assert (S1 : (¬ P → Q) → (¬ P ∨ Q → Q ∨ Q)).
  { exact (n2_38 Q (¬ P) Q). }
  assert (S2 : (¬ P ∨ Q → Q ∨ Q) → (¬ P ∨ Q → Q)).
  {
    pose proof (Syll2_05 (¬ P ∨ Q) (Q ∨ Q) Q) as Syll2_05.
    pose proof (Taut1_2 Q) as Taut1_2.
    now MP Syll2_05 Taut1_2.
  }
  assert (S3 : (¬ P → Q) → (¬ P ∨ Q → Q)).
  {
    Syll_as S1 S2 S3.
    exact S3.
  }
  assert (S4 : (¬ P → Q) → ((P → Q) → Q)).
  {
    pose proof S3 as S3a.
    rewrite <- (Impl1_01a P Q) in S3a.
    exact S3a.
  }
  exact S4.
Qed.

Theorem n2_61 (P Q : Prop) :
  (P → Q) → ((¬ P → Q) → Q).
Proof.
  pose proof (Comm2_04 (¬ P → Q) (P → Q) Q) as Comm2_04.
  pose proof (n2_6 P Q) as n2_6.
  now MP Comm2_04 n2_6.
Qed.

Theorem n2_62 (P Q : Prop) :
  (P ∨ Q) → ((P → Q) → Q).
Proof.
  pose proof (n2_53 P Q) as n2_53.
  pose proof (n2_6 P Q) as n2_6.
  Syll_as n2_53 n2_6 n2_62a.
  exact n2_62a.
Qed.

Theorem n2_621 (P Q : Prop) :
  (P → Q) → ((P ∨ Q) → Q).
Proof.
  pose proof (Comm2_04 (P ∨ Q) (P → Q) Q) as Comm2_04.
  pose proof (n2_62 P Q) as n2_62.
  now MP Comm2_04 n2_62.
Qed.

Theorem n2_63 (P Q : Prop) :
  (P ∨ Q) → ((¬ P ∨ Q) → Q).
Proof.
  (* TOOLS *)
  set (λ P0 Q0 : Prop, eq_to_equiv (P0 → Q0) (¬ P0 ∨ Q0) (Impl1_01 P0 Q0))
    as Impl1_01a.
  (* ******** *)
  pose proof (n2_62 P Q) as n2_62.
  rewrite -> (Impl1_01a P Q) in n2_62.
  exact n2_62.
Qed.

Theorem n2_64 (P Q : Prop) :
  (P ∨ Q) → ((P ∨ ¬ Q) → P).
Proof.
  pose proof (Syll2_06 (P ∨ ¬ Q) (¬ Q ∨ P) P) as Syll2_06.
  pose proof (Perm1_4 P (¬ Q)) as Perm1_4a.
  MP Syll2_06 Perm1_4a.
  pose proof (n2_63 Q P) as n2_63.
  Syll_as n2_63 Syll2_06 Syll_as_a.
  pose proof (Perm1_4 P Q) as Perm1_4b.
  Syll_as Perm1_4b Syll_as_a Syll_as_b.
  exact Syll_as_b.
Qed.
Theorem n2_65 (P Q : Prop) :
  (P → Q) → ((P → ¬ Q) → ¬ P).
Proof.
  (* TOOLS *)
  set (λ P0 Q0 : Prop, eq_to_equiv (P0 → Q0) (¬ P0 ∨ Q0) (Impl1_01 P0 Q0))
    as Impl1_01a.
  (* ******** *)
  pose proof (n2_64 (¬ P) Q) as n2_64.
  rewrite <- (Impl1_01a P Q) in n2_64.
  rewrite <- (Impl1_01a P (¬ Q)) in n2_64.
  exact n2_64.
Qed.

Theorem n2_67 (P Q : Prop) :
  ((P ∨ Q) → Q) → (P → Q).
Proof.
  assert (S1 : ((P ∨ Q) → Q) → ((¬ P → Q) → Q)).
  {
    pose proof (Syll2_06 (¬ P → Q) (P ∨ Q) Q) as Syll2_06a.
    pose proof (n2_54 P Q) as n2_54.
    now MP Syll2_06a n2_54.
  }
  assert (S2 : ((¬ P → Q) → Q) → (P → Q)).
  {
    pose proof (Syll2_06 P (¬ P → Q) Q) as Syll2_06b.
    pose proof (n2_24 P Q) as n2_24.
    now MP Syll2_06b n2_24.
  }
  assert (S3 : ((P ∨ Q) → Q) → (P → Q)).
  {
    Syll_as S1 S2 S3.
    exact S3.
  }
  exact S3.
Qed.

Theorem n2_68 (P Q : Prop) :
  ((P → Q) → Q) → (P ∨ Q).
Proof.
  (* TOOLS *)
  set (λ P0 Q0 : Prop, eq_to_equiv (P0 → Q0) (¬ P0 ∨ Q0) (Impl1_01 P0 Q0))
    as Impl1_01a.
  (* ******** *)
  assert (S1 : ((¬ P ∨ Q) → Q) → (¬ P → Q)).
  { exact (n2_67 (¬ P) Q). }
  assert (S2 : ((P → Q) → Q) → (¬ P → Q)).
  {
    pose proof S1 as S1a.
    rewrite <- (Impl1_01a P Q) in S1a.
    exact S1a.
  }
  assert (S3 : (¬ P → Q) → (P ∨ Q)).
  { exact (n2_54 P Q). }
  assert (S4 : ((P → Q) → Q) → (P ∨ Q)).
  {
    Syll_as S2 S3 S4.
    exact S4.
  }
  exact S4.
Qed.

Theorem n2_69 (P Q : Prop) :
  ((P → Q) → Q) → ((Q → P) → P).
Proof.
  pose proof (Perm1_4 P Q) as Perm1_4.
  pose proof (n2_62 Q P) as n2_62.
  Syll_as Perm1_4 n2_62 Syll_as_a.
  pose proof (n2_68 P Q) as n2_68.
  Syll_as n2_68 Syll_as_a n2_69a.
  exact n2_69a.
Qed.

Theorem n2_73 (P Q R : Prop) :
  (P → Q) → (((P ∨ Q) ∨ R) → (Q ∨ R)).
Proof.
  pose proof (n2_621 P Q) as n2_621.
  pose proof (n2_38 R (P ∨ Q) Q) as n2_38.
  Syll_as n2_621 n2_38 n2_73a.
  exact n2_73a.
Qed.

Theorem n2_74 (P Q R : Prop) :
  (Q → P) → ((P ∨ Q) ∨ R) → (P ∨ R).
Proof.
  pose proof (n2_73 Q P R) as n2_73.
  pose proof (Assoc1_5 P Q R) as Assoc1_5.
  pose proof (n2_31 Q P R) as n2_31.
  Syll_as Assoc1_5 n2_31 Sa.
  pose proof (n2_32 P Q R) as n2_32.
  Syll_as n2_32 Sa Sb.
  pose proof (Syll2_06 ((P ∨ Q) ∨ R) ((Q ∨ P) ∨ R) (P ∨ R)) as Syll2_06.
  MP Syll2_06 Sb.
  now Syll_as n2_73 Syll2_06 n2_74.
Qed.

Theorem n2_75 (P Q R : Prop) :
  (P ∨ Q) → ((P ∨ (Q → R)) → (P ∨ R)).
Proof.
  (* TOOLS *)
  set (λ P0 Q0 : Prop, eq_to_equiv (P0 → Q0) (¬ P0 ∨ Q0) (Impl1_01 P0 Q0))
    as Impl1_01a.
  (* ******** *)
  pose proof (Perm1_4 P Q) as Perm1_4.
  pose proof (n2_53 Q P) as n2_53.
  Syll_as Perm1_4 n2_53 Syll_as_a.
  pose proof (n2_74 P (¬ Q) R) as n2_74.
  Syll_as Syll_as_a n2_74 Syll_as_b.
  pose proof (n2_31 P (¬ Q) R) as n2_31.
  pose proof (Syll2_06 (P ∨ (¬ Q ∨ R)) ((P ∨ ¬ Q) ∨ R) (P ∨ R))
    as Syll2_06.
  MP Syll2_06 n2_31.
  Syll_as Syll_as_b Syll2_06 Syll_as_c.
  now rewrite <- (Impl1_01a Q R) in Syll_as_c.
Qed.

Theorem n2_76 (P Q R : Prop) :
  (P ∨ (Q → R)) → ((P ∨ Q) → (P ∨ R)).
Proof.
  pose proof (Comm2_04 (P ∨ Q) (P ∨ (Q → R)) (P ∨ R)) as Comm2_04.
  pose proof (n2_75 P Q R) as n2_75.
  now MP Comm2_04 n2_75.
Qed.

Theorem n2_77 (P Q R : Prop) :
  (P → (Q → R)) → ((P → Q) → (P → R)).
Proof.
  (* TOOLS *)
  set (λ P0 Q0 : Prop, eq_to_equiv (P0 → Q0) (¬ P0 ∨ Q0) (Impl1_01 P0 Q0))
    as Impl1_01a.
  (* ******** *)
  pose proof (n2_76 (¬ P) Q R) as n2_76.
  rewrite <- (Impl1_01a P R) in n2_76.
  rewrite <- (Impl1_01a P Q) in n2_76.
  rewrite <- (Impl1_01a P (Q → R)) in n2_76.
  exact n2_76.
Qed.

Theorem n2_8 (Q R S : Prop) :
  (Q ∨ R) → ((¬ R ∨ S) → (Q ∨ S)).
Proof.
  assert (S1 : R ∨ Q → (¬ R → Q)).
  { exact (n2_53 R Q). }
  assert (S2 : Q ∨ R → R ∨ Q).
  { exact (Perm1_4 Q R). }
  assert (S3 : Q ∨ R → (¬ R → Q)).
  {
    Syll_as S2 S1 S3.
    exact S3.
  }
  assert (S4 : (¬ R → Q) → (¬ R ∨ S → Q ∨ S)).
  { exact (n2_38 S (¬ R) Q). }
  assert (S5 : Q ∨ R → (¬ R ∨ S → Q ∨ S)).
  {
    Syll_as S3 S4 S5.
    exact S5.
  }
  exact S5.
Qed.

Theorem n2_81 (P Q R S : Prop) :
  (Q → (R → S)) → ((P ∨ Q) → ((P ∨ R) → (P ∨ S))).
Proof.
  assert (S1 : (Q → (R → S)) → (P ∨ Q → P ∨ (R → S))).
  { exact (Sum1_6 P Q (R → S)). }
  assert (S2 : (P ∨ Q → P ∨ (R → S)) → (P ∨ Q → (P ∨ R → P ∨ S))).
  {
    pose proof (Syll2_05 (P ∨ Q) (P ∨ (R → S)) (P ∨ R → P ∨ S)) as Syll2_05.
    pose proof (n2_76 P R S) as n2_76.
    now MP Syll2_05 n2_76.
  }
  assert (S3 : (Q → (R → S)) → (P ∨ Q → (P ∨ R → P ∨ S))).
  {
    Syll_as S1 S2 S3.
    exact S3.
  }
  exact S3.
Qed.

Theorem n2_82 (P Q R S : Prop) :
  (P ∨ Q ∨ R) → ((P ∨ ¬ R ∨ S) → (P ∨ Q ∨ S)).
Proof.
  pose proof (n2_81 P (Q ∨ R) (¬ R ∨ S) (Q ∨ S)) as n2_81.
  pose proof (n2_8 Q R S) as n2_8.
  now MP n2_81 n2_8.
Qed.

Theorem n2_83 (P Q R S : Prop) :
  (P → (Q → R)) → ((P → (R → S)) → (P → (Q → S))).
Proof.
  (* TOOLS *)
  set (λ P0 Q0 : Prop, eq_to_equiv (P0 → Q0) (¬ P0 ∨ Q0) (Impl1_01 P0 Q0))
    as Impl1_01a.
  (* ******** *)
  pose proof (n2_82 (¬ P) (¬ Q) R S) as n2_82.
  rewrite <- (Impl1_01a P (¬ Q ∨ S)) in n2_82.
  rewrite <- (Impl1_01a P (¬ Q ∨ R)) in n2_82.
  rewrite <- (Impl1_01a P (¬ R ∨ S)) in n2_82.
  rewrite <- (Impl1_01a Q S) in n2_82.
  rewrite <- (Impl1_01a Q R) in n2_82.
  rewrite <- (Impl1_01a R S) in n2_82.
  exact n2_82.
Qed.

Theorem n2_85 (P Q R : Prop) :
  ((P ∨ Q) → (P ∨ R)) → (P ∨ (Q → R)).
Proof.
  assert (S1 : (P ∨ Q → R) → (Q → R)).
  {
    pose proof (Syll2_06 Q (P ∨ Q) R) as Syll2_06a.
    pose proof (Add1_3 P Q) as Add1_3.
    now MP Syll2_06a Add1_3.
  }
  assert (S2 : ¬ P → ((P ∨ Q → P ∨ R) → (Q → R))).
  {
    pose proof (Syll2_06 (¬ P) (P ∨ R → R)
      ((P ∨ Q → P ∨ R) → (P ∨ Q → R))) as Syll2_06.
    pose proof (n2_55 P R) as n2_55.
    assert (S2_2 :
      ((P ∨ R → R) → ((P ∨ Q → P ∨ R) → (P ∨ Q → R))) →
        (¬ P → ((P ∨ Q → P ∨ R) → (P ∨ Q → R)))).
    { now MP Syll2_06 n2_55. }
    pose proof (Syll2_05 (P ∨ Q) (P ∨ R) R) as Syll2_05.
    assert (S2_3 : ¬ P → ((P ∨ Q → P ∨ R) → (P ∨ Q → R))).
    { now MP S2_2 Syll2_05. }

    pose proof (Simp2_02 (¬ P) ((P ∨ Q → R) → (Q → R))) as Simp2_02.
    assert (S2_4 : ¬ P → ((P ∨ Q → R) → (Q → R))).
    { now MP Simp2_02 S1. }

    pose proof (n2_83
      (¬ P)
      (P ∨ Q → P ∨ R)
      (P ∨ Q → R)
      (Q → R)) as n2_83.
    MP n2_83 S2_3.
    now MP n2_83 S2_4.
  }
  assert (S3 : (P ∨ Q → P ∨ R) → (¬ P → (Q → R))).
  {
    pose proof (Comm2_04 (¬ P) (P ∨ Q → P ∨ R) (Q → R)) as Comm2_04.
    now MP Comm2_04 S2.
  }
  assert (S4 : (P ∨ Q → P ∨ R) → (P ∨ (Q → R))).
  {
    pose proof (n2_54 P (Q → R)) as n2_54.
    Syll_as S3 n2_54 S4_res.
    exact S4_res.
  }
  exact S4.
Qed.

Theorem n2_86 (P Q R : Prop) :
  ((P → Q) → (P → R)) → (P → (Q → R)).
Proof.
  (* TOOLS *)
  set (λ P0 Q0 : Prop, eq_to_equiv (P0 → Q0) (¬ P0 ∨ Q0) (Impl1_01 P0 Q0))
    as Impl1_01a.
  (* ******** *)
  pose proof (n2_85 (¬ P) Q R) as n2_85.
  rewrite <- (Impl1_01a P (Q → R)) in n2_85.
  rewrite <- (Impl1_01a P R) in n2_85.
  rewrite <- (Impl1_01a P Q) in n2_85.
  exact n2_85.
Qed.
