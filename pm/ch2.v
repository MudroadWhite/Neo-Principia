Require Import PM.pm.lib.
Require Import PM.pm.ch1.

(*We proceed to the deductions of of Principia.*)

Theorem Abs2_01 (P : Prop) :
  (P → ¬ P) → ¬ P.
Proof.
  pose proof (Taut1_2 (¬ P)) as Taut1_2.
  replace (¬ P ∨ ¬ P) with (P → ¬ P) in Taut1_2
    by now rewrite Impl1_01.
  exact Taut1_2.
Qed.

Theorem Simp2_02 (P Q : Prop) :
  Q → (P → Q).
Proof.
  pose proof (Add1_3 (¬ P) Q) as Add1_3.
  replace (¬ P ∨ Q) with (P → Q) in Add1_3
    by now rewrite Impl1_01.
  exact Add1_3.
Qed.

Theorem Transp2_03 (P Q : Prop) :
  (P → ¬ Q) → (Q → ¬ P).
Proof.
  pose proof (Perm1_4 (¬ P) (¬ Q)) as Perm1_4.
  replace (¬ P ∨ ¬ Q) with (P → ¬ Q) in Perm1_4.
  replace (¬ Q ∨ ¬ P) with (Q → ¬ P) in Perm1_4.
  exact Perm1_4.
  all : now rewrite Impl1_01.
Qed.

Theorem Comm2_04 (P Q R : Prop) :
  (P → (Q → R)) → (Q → (P → R)).
Proof.
  pose proof (Assoc1_5 (¬ P) (¬ Q) R) as Assoc1_5.
  replace (¬ Q ∨ R) with (Q → R) in Assoc1_5.
  replace (¬ P ∨ (Q → R)) with (P → (Q → R)) in Assoc1_5.
  replace (¬ P ∨ R) with (P → R) in Assoc1_5.
  replace (¬ Q ∨ (P → R)) with (Q → (P → R)) in Assoc1_5.
  exact Assoc1_5.
  all: now rewrite Impl1_01.
Qed.

Theorem Syll2_05 (P Q R : Prop) :
  (Q → R) → ((P → Q) → (P → R)).
Proof.
  pose proof (Sum1_6 (¬ P) Q R) as Sum1_6.
  replace (¬ P ∨ Q) with (P → Q) in Sum1_6.
  replace (¬ P ∨ R) with (P → R) in Sum1_6.
  exact Sum1_6.
  all: now rewrite Impl1_01.
Qed.

Theorem Syll2_06 (P Q R : Prop) :
  (P → Q) → ((Q → R) → (P → R)).
Proof.
  pose proof (Comm2_04 (Q → R) (P → Q) (P → R)) as Comm2_04.
  pose proof (Syll2_05 P Q R) as Syll2_05.
  MP Comm2_04 Syll2_05.
  exact Comm2_04.
Qed.

Theorem n2_07 (P : Prop) :
  P → (P ∨ P).
Proof.
  exact (Add1_3 P P).
Qed.

Theorem Id2_08 (P : Prop) :
  P → P.
Proof.
  pose proof (Syll2_05 P (P ∨ P) P) as Syll2_05.
  pose proof (Taut1_2 P) as Taut1_2.
  MP Syll2_05 Taut1_2.
  pose proof (n2_07 P) as n2_07.
  MP Syll2_05 n2_07.
  exact Syll2_05.
Qed.

Theorem n2_1 (P : Prop) :
  (¬ P) ∨ P.
Proof.
  pose proof (Id2_08 P) as Id2_08.
  replace (P → P) with (¬ P ∨ P) in Id2_08
    by now rewrite Impl1_01.
  exact Id2_08.
Qed.

Theorem n2_11 (P : Prop) :
  P ∨ ¬ P.
Proof.
  pose proof (Perm1_4 (¬ P) P) as Perm1_4.
  pose proof (n2_1 P) as n2_1.
  MP Perm1_4 n2_1.
  exact Perm1_4.
Qed.

Theorem n2_12 (P : Prop) :
  P → ¬¬ P.
Proof.
  pose proof (n2_11 (¬ P)) as n2_11.
  replace (¬ P ∨ ¬¬ P) with (P → ¬¬ P) in n2_11
    by now rewrite Impl1_01.
  exact n2_11.
Qed.

Theorem n2_13 (P : Prop) :
  P ∨ ¬¬¬ P.
Proof.
  pose proof (Sum1_6 P (¬ P) (¬¬¬ P)) as Sum1_6.
  pose proof (n2_12 (¬ P)) as n2_12.
  MP Sum1_6 n2_12.
  pose proof (n2_11 P) as n2_11.
  MP Sum1_6 n2_11.
  exact Sum1_6.
Qed.

Theorem n2_14 (P : Prop) :
  ¬¬ P → P.
Proof.
  pose proof (Perm1_4 P (¬¬¬ P)) as Perm1_4.
  pose proof (n2_13 P) as n2_13.
  MP Perm1_4 n2_13.
  replace (¬¬¬ P ∨ P) with (¬¬ P → P) in Perm1_4
    by now rewrite Impl1_01.
  exact Perm1_4.
Qed.

Theorem Transp2_15 (P Q : Prop) :
  (¬ P → Q) → (¬ Q → P).
Proof.
  pose proof (Syll2_05 (¬ P) Q (¬¬ Q)) as Syll2_05a.
  pose proof (n2_12 Q) as n2_12.
  MP Syll2_05a n2_12.
  pose proof (Transp2_03 (¬ P) (¬ Q)) as Transp2_03.
  pose proof (Syll2_05 (¬ Q) (¬¬ P) P) as Syll2_05b.
  pose proof (n2_14 P) as n2_14.
  MP Syll2_05b n2_14.
  pose proof (Syll2_05 (¬ P → Q) (¬ P → ¬¬ Q) (¬ Q → ¬¬ P)) as Syll2_05c.
  MP Syll2_05c Transp2_03.
  MP Syll2_05c Syll2_05a.
  pose proof (Syll2_05 (¬ P → Q) (¬ Q → ¬¬ P) (¬ Q → P)) as Syll2_05d.
  MP Syll2_05d Syll2_05b.
  MP Syll2_05d Syll2_05c.
  exact Syll2_05d.
Qed.

(* To be tested and used in the future: syllogism in-place*)
Ltac Syll H1 H2 :=
  let S := fresh in
  lazymatch goal with 
  | [ _H1 : ?P → ?Q, _H2 : ?Q → ?R |- _ ] =>
    constr_eq H1 _H1;
    constr_eq H2 _H2;
    assert (S : P → R) by (intros p; exact (H2 (H1 p)));
    pose proof S as H1;
    clear S
  end.

(* We won't use `Syll` theorem but just to perform it as efficient as possible,
  knowing that it has been already proven *)
Ltac Syll_as H1 H2 S :=
  let S := fresh S in
    lazymatch goal with 
    | [ _H1 : ?P → ?Q, _H2 : ?Q → ?R |- _ ] =>
      constr_eq H1 _H1;
      constr_eq H2 _H2;
      assert (S : P → R) by (intros p; exact (H2 (H1 p)))
  end.

Theorem Transp2_16 (P Q : Prop) :
  (P → Q) → (¬ Q → ¬ P).
Proof.
  pose proof (n2_12 Q) as n2_12a.
  pose proof (Syll2_05 P Q (¬¬ Q)) as Syll2_05a.
  pose proof (Transp2_03 P (¬ Q)) as Transp2_03a.
  MP Syll2_05a n2_12a.
  Syll_as Syll2_05a Transp2_03a S.
  exact S.
Qed.

Theorem Transp2_17 (P Q : Prop) :
  (¬ Q → ¬ P) → (P → Q).
Proof.
  pose proof (Transp2_03 (¬ Q) P) as Transp2_03a.
  pose proof (n2_14 Q) as n2_14a.
  pose proof (Syll2_05 P (¬¬ Q) Q) as Syll2_05a.
  MP Syll2_05a n2_14a.
  Syll_as Transp2_03a Syll2_05a S.
  exact S.
Qed.

Theorem n2_18 (P : Prop) :
  (¬ P → P) → P.
Proof.
  pose proof (n2_12 P) as n2_12a.
  pose proof (Syll2_05 (¬ P) P (¬¬ P)) as Syll2_05a.
  pose proof Syll2_05 as Syll2_05.
  MP Syll2_05a n2_12a.
  pose proof (Abs2_01 (¬ P)) as Abs2_01a.
  Syll_as Syll2_05a Abs2_01a Sa.
  pose proof (n2_14 P) as n2_14a.
  Syll_as Sa n2_14a Sb.
  exact Sb.
Qed.

Theorem n2_2 (P Q : Prop) :
  P → (P ∨ Q).
Proof.
  pose proof (Add1_3 Q P) as Add1_3a.
  pose proof (Perm1_4 Q P) as Perm1_4a.
  Syll_as Add1_3a Perm1_4a S.
  exact S.
Qed.

Theorem n2_21 (P Q : Prop) :
  ¬ P → (P → Q).
Proof.
  pose proof (n2_2 (¬ P) Q) as n2_2a.
  replace (¬ P ∨ Q) with (P → Q) in n2_2a
    by now rewrite Impl1_01.
  exact n2_2a.
Qed.

Theorem n2_24 (P Q : Prop) :
  P → (¬ P → Q).
Proof.
  pose proof (n2_21 P Q) as n2_21a.
  pose proof (Comm2_04 (¬ P) P Q) as Comm2_04a.
  MP Comm2_04a n2_21a.
  exact Comm2_04a.
Qed.

Theorem n2_25 (P Q : Prop) :
  P ∨ ((P ∨ Q) → Q).
Proof.
  pose proof (n2_1 (P ∨ Q)) as n2_1a.
  pose proof (Assoc1_5 (¬ (P ∨ Q)) P Q) as Assoc1_5a.
  MP Assoc1_5a n2_1a.
  replace (¬ (P ∨ Q) ∨ Q) with (P ∨ Q → Q) in Assoc1_5a
    by now rewrite Impl1_01.
  exact Assoc1_5a.
Qed.

Theorem n2_26 (P Q : Prop) :
  ¬ P ∨ ((P → Q) → Q).
Proof.
  pose proof (n2_25 (¬ P) Q) as n2_25a.
  replace (¬ P ∨ Q) with (P → Q) in n2_25a
    by now rewrite Impl1_01.
  exact n2_25a.
Qed.

Theorem n2_27 (P Q : Prop) :
  P → ((P → Q) → Q).
Proof.
  pose proof (n2_26 P Q) as n2_26a.
  replace (¬ P ∨ ((P → Q) → Q)) with (P → (P → Q) → Q) 
    in n2_26a by now rewrite Impl1_01.
  exact n2_26a.
Qed.

Theorem n2_3 (P Q R : Prop) :
  (P ∨ (Q ∨ R)) → (P ∨ (R ∨ Q)).
Proof.
  pose proof (Perm1_4 Q R) as Perm1_4a.
  pose proof (Sum1_6 P (Q ∨ R) (R ∨ Q)) as Sum1_6a.
  MP Sum1_6a Perm1_4a.
  exact Sum1_6a.
Qed.

Theorem n2_31 (P Q R : Prop) :
  (P ∨ (Q ∨ R)) → ((P ∨ Q) ∨ R).
Proof.
  pose proof (n2_3 P Q R) as n2_3a.
  pose proof (Assoc1_5 P R Q) as Assoc1_5a.
  pose proof (Perm1_4 R (P ∨ Q)) as Perm1_4a.
  Syll_as Assoc1_5a Perm1_4a Sa.
  Syll_as n2_3a Sa Sb.
  exact Sb.
Qed.

Theorem n2_32 (P Q R : Prop) :
  ((P ∨ Q) ∨ R) → (P ∨ (Q ∨ R)).
Proof.
  pose proof (Perm1_4 (P ∨ Q) R) as Perm1_4a.
  pose proof (Assoc1_5 R P Q) as Assoc1_5a.
  pose proof (n2_3 P R Q) as n2_3a.
  pose proof (Syll2_06 ((P ∨ Q) ∨ R) (R ∨ P ∨ Q) (P ∨ R ∨ Q)) as Syll2_06a.
  MP Syll2_06a Perm1_4a.
  MP Syll2_06a Assoc1_5a.
  pose proof (Syll2_06 ((P ∨ Q) ∨ R) (P ∨ R ∨ Q) (P ∨ Q ∨ R)) as Syll2_06b.
  MP Syll2_06b Syll2_06a.
  MP Syll2_06b n2_3a.
  exact Syll2_06b.
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

(*The default in Coq is right association.*)
Theorem n2_36 (P Q R : Prop) :
  (Q → R) → ((P ∨ Q) → (R ∨ P)).
Proof.
  pose proof (Perm1_4 P R) as Perm1_4a.
  pose proof (Syll2_05 (P ∨ Q) (P ∨ R) (R ∨ P)) as Syll2_05a.
  MP Syll2_05a Perm1_4a.
  pose proof (Sum1_6 P Q R) as Sum1_6a.
  Syll_as Sum1_6a Syll2_05a S.
  exact S.
Qed.

Theorem n2_37 (P Q R : Prop) :
  (Q → R) → ((Q ∨ P) → (P ∨ R)).
Proof.
  pose proof (Perm1_4 Q P) as Perm1_4a.
  pose proof (Syll2_06 (Q ∨ P) (P ∨ Q) (P ∨ R)) as Syll2_06a.
  MP Syll2_06a Perm1_4a.
  pose proof (Sum1_6 P Q R) as Sum1_6a.
  Syll_as Sum1_6a Syll2_06a S.
  exact S.
Qed.

Theorem n2_38 (P Q R : Prop) :
  (Q → R) → ((Q ∨ P) → (R ∨ P)).
Proof.
  pose proof (Perm1_4 P R) as Perm1_4a.
  pose proof (Syll2_05 (Q ∨ P) (P ∨ R) (R ∨ P)) as Syll2_05a.
  MP Syll2_05a Perm1_4a.
  pose proof (Perm1_4 Q P) as Perm1_4b.
  pose proof (Syll2_06 (Q ∨ P) (P ∨ Q) (P ∨ R)) as Syll2_06a.
  MP Syll2_06a Perm1_4b.
  Syll_as Syll2_06a Syll2_05a H.
  pose proof (Sum1_6 P Q R) as Sum1_6a.
  Syll_as Sum1_6a H S.
  exact S.
Qed.

Theorem n2_4 (P Q : Prop) :
  (P ∨ (P ∨ Q)) → (P ∨ Q).
Proof.
  pose proof (n2_31 P P Q) as n2_31a.
  pose proof (Taut1_2 P) as Taut1_2a.
  pose proof (n2_38 Q (P ∨ P) P) as n2_38a.
  MP n2_38a Taut1_2a.
  Syll_as n2_31a n2_38a S.
  exact S.
Qed.

Theorem n2_41 (P Q : Prop) :
  (Q ∨ (P ∨ Q)) → (P ∨ Q).
Proof.
  pose proof (Assoc1_5 Q P Q) as Assoc1_5a.
  pose proof (Taut1_2 Q) as Taut1_2a.
  pose proof (Sum1_6 P (Q ∨ Q) Q) as Sum1_6a.
  MP Sum1_6a Taut1_2a.
  Syll_as Assoc1_5a Sum1_6a S.
  exact S.
Qed.

Theorem n2_42 (P Q : Prop) :
  (¬ P ∨ (P → Q)) → (P → Q).
Proof.
  pose proof (n2_4 (¬ P) Q) as n2_4a.
  replace (¬ P ∨ Q) with (P → Q) in n2_4a
    by now rewrite Impl1_01.
  exact n2_4a.
Qed.

Theorem n2_43 (P Q : Prop) :
  (P → (P → Q)) → (P → Q).
Proof.
  pose proof (n2_42 P Q) as n2_42a.
  replace (¬ P ∨ (P → Q)) with (P → (P → Q)) 
    in n2_42a by now rewrite Impl1_01.
  exact n2_42a.
Qed.

Theorem n2_45 (P Q : Prop) :
  ¬ (P ∨ Q) → ¬ P.
Proof.
  pose proof (n2_2 P Q) as n2_2a.
  pose proof (Transp2_16 P (P ∨ Q)) as Transp2_16a.
  MP Transp2_16a n2_2a.
  exact Transp2_16a.
Qed.

Theorem n2_46 (P Q : Prop) :
  ¬ (P ∨ Q) → ¬ Q.
Proof.
  pose proof (Add1_3 P Q) as Add1_3a.
  pose proof (Transp2_16 Q (P ∨ Q)) as Transp2_16a.
  MP Transp2_16a Add1_3a.
  exact Transp2_16a.
Qed.

Theorem n2_47 (P Q : Prop) :
  ¬ (P ∨ Q) → (¬ P ∨ Q).
Proof.
  pose proof (n2_45 P Q) as n2_45a.
  pose proof (n2_2 (¬ P) Q) as n2_2a.
  Syll_as n2_45a n2_2a S.
  exact S.
Qed.

Theorem n2_48 (P Q : Prop) :
  ¬ (P ∨ Q) → (P ∨ ¬ Q).
Proof.
  pose proof (n2_46 P Q) as n2_46a.
  pose proof (Add1_3 P (¬ Q)) as Add1_3a.
  Syll_as n2_46a Add1_3a S.
  exact S.
Qed.

Theorem n2_49 (P Q : Prop) :
  ¬ (P ∨ Q) → (¬ P ∨ ¬ Q).
Proof.
  pose proof (n2_45 P Q) as n2_45a.
  pose proof (n2_2 (¬ P) (¬ Q)) as n2_2a.
  Syll_as n2_45a n2_2a S.
  exact S.
Qed.

Theorem n2_5 (P Q : Prop) :
  ¬ (P → Q) → (¬ P → Q).
Proof.
  pose proof (n2_47 (¬ P) Q) as n2_47a.
  replace (¬ P ∨ Q) with (P → Q) in n2_47a.
  replace (¬¬ P ∨ Q) with (¬ P → Q) in n2_47a.
  exact n2_47a.
  all: now rewrite Impl1_01.
Qed.

Theorem n2_51 (P Q : Prop) :
  ¬ (P → Q) → (P → ¬ Q).
Proof.
  pose proof (n2_48 (¬ P) Q) as n2_48a.
  replace (¬ P ∨ Q) with (P → Q) in n2_48a.
  replace (¬ P ∨ ¬ Q) with (P → ¬ Q) in n2_48a.
  exact n2_48a.
  all : now rewrite Impl1_01.
Qed.

Theorem n2_52 (P Q : Prop) :
  ¬ (P → Q) → (¬ P → ¬ Q).
Proof.
  pose proof (n2_49 (¬ P) Q) as n2_49a.
  replace (¬ P ∨ Q) with (P → Q) in n2_49a.
  replace (¬¬ P ∨ ¬ Q) with (¬ P → ¬ Q) in n2_49a.
  exact n2_49a.
  all : now rewrite Impl1_01.
Qed.

Theorem n2_521 (P Q : Prop) :
  ¬ (P → Q) → (Q → P).
Proof.
  pose proof (n2_52 P Q) as n2_52a.
  pose proof (Transp2_17 Q P) as Transp2_17a.
  Syll_as n2_52a Transp2_17a S.
  exact S.
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
