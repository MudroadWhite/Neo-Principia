Require Import PM.pm.lib.
Require Import PM.pm.ch1.
Require Import PM.pm.ch2.
Require Import PM.pm.ch3.

Theorem Equiv4_01 : ∀ P Q : Prop, 
  (P ↔ Q) = ((P → Q) ∧ (Q → P)).
Proof. intros. reflexivity. Qed.

(* Theorem Equiv4_01 () : P Q : Prop, 
(P ↔ Q) = ((P → Q) ∧ (Q → P)).
Proof.) as P Q.
apply propositional_extensionality.
pose proof (iff_to_and with P Q.
) as iff_to_and.
exact iff_to_and.
Qed.*)
(*This is a notational definition in Principia;
it is used to switch between " ↔ " and " → ∧ ←".*)

(*Axiom Abb4_02 () : P Q R : Prop,
(P ↔ Q ↔ R) = ((P ↔ Q) ∧ (Q ↔ R)).*)
(*Since Coq forbids ill-formed strings, or else 
automatically associates to the right, we leave 
this notational axiom commented out.*)

Ltac Equiv H1 :=
  match goal with 
    | [ _H1 : (?P → ?Q) ∧ (?Q → ?P) |- _ ] => 
      constr_eq H1 _H1;
      replace ((P → Q) ∧ (Q → P)) with (P ↔ Q) in H1
      by now rewrite Equiv4_01
  end.

Theorem Transp4_1 (P Q : Prop) :
  (P → Q) ↔ (¬ Q → ¬ P).
Proof.
  pose proof (Transp2_16 P Q) as Transp2_16a.
  pose proof (Transp2_17 P Q) as Transp2_17a.
  Conj_as Transp2_16a Transp2_17a C.
  Equiv C.
  exact C.
Qed.

Theorem Transp4_11 (P Q : Prop) :
  (P ↔ Q) ↔ (¬ P ↔ ¬ Q).
Proof.
  assert (Sa : (P → Q) ∧ (Q → P) → (¬ P → ¬ Q) ∧ (¬ Q → ¬ P)).
  {
    pose proof (Transp2_16 P Q) as Transp2_16a.
    pose proof (Transp2_16 Q P) as Transp2_16b.
    Conj_as Transp2_16a Transp2_16b Ca.
    pose proof (n3_47 (P → Q) (Q → P) (¬ Q → ¬ P) (¬ P → ¬ Q)) as n3_47a.
    MP n3_47a Ca.
    pose proof (n3_22 (¬ Q → ¬ P) (¬ P → ¬ Q)) as n3_22a.
    Syll_as n3_47a n3_22a Sa_1.
    exact Sa_1.
  }
  replace ((P → Q) ∧ (Q → P)) with (P ↔ Q) in Sa.
  replace ((¬ P → ¬ Q) ∧ (¬ Q → ¬ P)) with (¬ P ↔ ¬ Q) in Sa.
  assert (Sb : (¬ P → ¬ Q) ∧ (¬ Q → ¬ P) → (P → Q) ∧ (Q → P)).
  {
    pose proof (Transp2_17 Q P) as Transp2_17a.
    pose proof (Transp2_17 P Q) as Transp2_17b.
    Conj_as Transp2_17a Transp2_17b Cb.
    pose proof (n3_47 (¬ P → ¬ Q) (¬ Q → ¬ P) (Q → P) (P → Q)) as n3_47a.
    MP n3_47a Cb.
    pose proof (n3_22 (Q → P) (P → Q)) as n3_22a.
    Syll_as n3_47a n3_22a Sb_1.
    exact Sb_1.
  }
  replace ((P → Q) ∧ (Q → P)) with (P ↔ Q) in Sb.
  replace ((¬ P → ¬ Q) ∧ (¬ Q → ¬ P)) with (¬ P ↔ ¬ Q) in Sb.
  Conj_as Sa Sb Cc.
  Equiv Cc.
  exact Cc.
  all: now rewrite Equiv4_01.
Qed.

Theorem n4_12 (P Q : Prop) :
  (P ↔ ¬ Q) ↔ (Q ↔ ¬ P).
Proof.
  assert (Ca : ((P → ¬ Q) → Q → ¬ P) ∧ ((¬ Q → P) → ¬ P → Q)).
  {
    pose proof (Transp2_03 P Q) as Transp2_03a.
    pose proof (Transp2_15 Q P) as Transp2_15a.
    Conj_as Transp2_03a Transp2_15a Ca.
    exact Ca.
  }
  pose proof (n3_47 (P → ¬ Q) (¬ Q → P) (Q → ¬ P) (¬ P → Q)) as n3_47a.
  MP n3_47a Ca.
  assert (Cb : ((Q → ¬ P) → P → ¬ Q) ∧ ((¬ P → Q) → ¬ Q → P)).
  {
    pose proof (Transp2_03 Q P) as Transp2_03b.
    pose proof (Transp2_15 P Q) as Transp2_15b.
    Conj_as Transp2_03b Transp2_15b Cb.
    exact Cb.
  }
  pose proof (n3_47 (Q → ¬ P) (¬ P → Q) (P → ¬ Q) (¬ Q → P)) as n3_47b.
  MP n3_47b Cb.
  clear Ca Cb.
  Conj_as n3_47a n3_47b Cc.
  rewrite <- Equiv4_01 in Cc.
  rewrite <- Equiv4_01 in Cc.
  rewrite <- Equiv4_01 in Cc.
  exact Cc.
Qed.

Theorem n4_13 (P : Prop) :
  P ↔ ¬¬ P.
Proof.
  pose proof (n2_12 P) as n2_12a.
  pose proof (n2_14 P) as n2_14a.
  Conj_as n2_12a n2_14a C.
  Equiv C.
  exact C.
Qed.

Theorem n4_14 (P Q R : Prop) :
  ((P ∧ Q) → R) ↔ ((P ∧ ¬ R) → ¬ Q).
Proof.
  pose proof (Transp3_37 P Q R) as Transp3_37a.
  pose proof (Transp3_37 P (¬ R) (¬ Q)) as Transp3_37b.
  Conj_as Transp3_37a Transp3_37b C.
  pose proof (n4_13 Q) as n4_13a.
  apply propositional_extensionality in n4_13a.
  pose proof (n4_13 R) as n4_13b.
  apply propositional_extensionality in n4_13b.
  replace (¬¬ Q) with Q in C
  by now apply n4_13a.
  replace (¬¬ R) with R in C
  by now apply n4_13b.
  Equiv C.
  exact C.
Qed.

Theorem n4_15 (P Q R : Prop) :
  ((P ∧ Q) → ¬ R) ↔ ((Q ∧ R) → ¬ P).
Proof.
  pose proof (n3_22 Q P) as n3_22a.
  pose proof (Syll2_06 (Q ∧ P) (P ∧ Q) (¬ R)) as Syll2_06a.
  MP Syll2_06a n3_22a.
  assert (n4_14a : ((Q ∧ P → ¬ R) → Q ∧ R → ¬ P)
    ∧ ((Q ∧ R → ¬ P) → Q ∧ P → ¬ R)).
  {
    pose proof (n4_14 Q P (¬ R)) as n4_14a.
    pose proof (n4_13 R) as n4_13a.
    apply propositional_extensionality in n4_13a.
    replace (¬¬ R) with R in n4_14a
      by now apply n4_13a.
    rewrite Equiv4_01 in n4_14a.
    exact n4_14a.
  }
  assert (Sa : (P ∧ Q → ¬ R) → Q ∧ R → ¬ P).
  {
    pose proof (Simp3_26 ((Q ∧ P → ¬ R) → Q ∧ R → ¬ P) 
        ((Q ∧ R → ¬ P) → Q ∧ P → ¬ R)) as Simp3_26a.
    MP Simp3_26a n4_14a.
    Syll_as Syll2_06a Simp3_26a Sa.
    exact Sa.
  }
  assert (Sb : (Q ∧ R → ¬ P) → P ∧ Q → ¬ R).
  {
    pose proof (Simp3_27 ((Q ∧ P → ¬ R) → Q ∧ R → ¬ P) 
        ((Q ∧ R → ¬ P) → Q ∧ P → ¬ R)) as Simp3_27a.
    MP Simp3_27a n4_14a.
    pose proof (n3_22 P Q) as n3_22b.
    pose proof (Syll2_06 (P ∧ Q) (Q ∧ P) (¬ R)) as Syll2_06b.
    MP Syll2_06b n3_22b.
    Syll_as Simp3_27a Syll2_06b Sb.
    exact Sb.
  }
  Conj_as Sa Sb C.
  Equiv C.
  exact C.
Qed.

Theorem n4_2 (P : Prop) :
  P ↔ P.
Proof.
  pose proof (n3_2 (P → P) (P → P)) as n3_2a.
  pose proof (Id2_08 P) as Id2_08a.
  MP n3_2a Id2_08a.
  MP n3_2a Id2_08a.
  Equiv n3_2a.
  exact n3_2a.
Qed.

Theorem n4_21 (P Q : Prop) :
  (P ↔ Q) ↔ (Q ↔ P).
Proof.
  pose proof (n3_22 (P → Q) (Q → P)) as n3_22a.
  replace ((P → Q) ∧ (Q → P)) with (P ↔ Q) 
    in n3_22a.
  replace ((Q → P) ∧ (P → Q)) with (Q ↔ P)
    in n3_22a.
  pose proof (n3_22 (Q → P) (P → Q)) as n3_22b.
  replace ((P → Q) ∧ (Q → P)) with (P ↔ Q) 
    in n3_22b.
  replace ((Q → P) ∧ (P → Q)) with (Q ↔ P) 
    in n3_22b.
  Conj_as n3_22a n3_22b C.
  Equiv C.
  exact C.
  all: now rewrite Equiv4_01.
Qed.

Theorem n4_22 (P Q R : Prop) :
  ((P ↔ Q) ∧ (Q ↔ R)) → (P ↔ R).
Proof.
  assert (Sa : (P ↔ Q) ∧ (Q ↔ R) → P → Q). {
    pose proof (Simp3_26 (P ↔ Q) (Q ↔ R)) as Simp3_26a.
    pose proof (Simp3_26 (P → Q) (Q → P)) as Simp3_26b.
    replace ((P → Q) ∧ (Q → P)) with (P ↔ Q) 
      in Simp3_26b by now rewrite Equiv4_01.
    Syll_as Simp3_26a Simp3_26b Sa.
    exact Sa.
  }
  assert (Sb : (P ↔ Q) ∧ (Q ↔ R) → Q → R). {
    pose proof (Simp3_27 (P ↔ Q) (Q ↔ R)) as Simp3_27a.
    pose proof (Simp3_26 (Q → R) (R → Q)) as Simp3_26c.
    replace ((Q → R) ∧ (R → Q)) with (Q ↔ R) 
      in Simp3_26c by now rewrite Equiv4_01.
    Syll_as Simp3_27a Simp3_26c Sb.
    exact Sb.
  }
  pose proof (n2_83 ((P ↔ Q) ∧ (Q ↔ R)) P Q R) as n2_83a.
  MP n2_83a Sa.
  MP n2_83a Sb.
  assert (Sc : (P ↔ Q) ∧ (Q ↔ R) → R → Q). 
  {
    pose proof (Simp3_27 (P ↔ Q) (Q ↔ R)) as Simp3_27b.
    pose proof (Simp3_27 (Q → R) (R → Q)) as Simp3_27c.
    replace ((Q → R) ∧ (R → Q)) with (Q ↔ R) 
      in Simp3_27c by now rewrite Equiv4_01.
    Syll_as Simp3_27b Simp3_27c Sc.
    exact Sc.
  }
  assert (Sd : (P ↔ Q) ∧ (Q ↔ R) → Q → P).
  {
    pose proof (Simp3_26 (P ↔ Q) (Q ↔ R)) as Simp3_26d.
    pose proof (Simp3_27 (P → Q) (Q → P)) as Simp3_27d.
    replace ((P → Q) ∧ (Q → P)) with (P ↔ Q) 
      in Simp3_27d by now rewrite Equiv4_01.
    Syll_as Simp3_26d Simp3_27d Sd.
    exact Sd.
  }
  pose proof (n2_83 ((P ↔ Q) ∧ (Q ↔ R)) R Q P) as n2_83b.
  MP n2_83b Sc.
  MP n2_83b Sd.
  clear Sa Sb Sc Sd.
  Conj_as n2_83a n2_83b C.
  pose proof (Comp3_43 ((P ↔ Q) ∧ (Q ↔ R)) (P → R) (R → P)) as Comp3_43a.
  MP Comp3_43a C.
  replace ((P → R) ∧ (R → P)) with (P ↔ R) 
    in Comp3_43a by apply Equiv4_01.
  exact Comp3_43a.
Qed.

Theorem n4_24 (P : Prop) :
  P ↔ (P ∧ P).
Proof.
  pose proof (n3_2 P P) as n3_2a.
  pose proof (n2_43 P (P ∧ P)) as n2_43a.
  MP n2_43a n3_2a.
  pose proof (Simp3_26 P P) as Simp3_26a.
  Conj_as n2_43a Simp3_26a C.
  Equiv C.
  exact C.
Qed.

Theorem n4_25 (P : Prop) :
  P ↔ (P ∨ P).
Proof.
  pose proof (Add1_3 P P) as Add1_3a.
  pose proof (Taut1_2 P) as Taut1_2a.
  Conj_as Add1_3a Taut1_2a C.
  Equiv C.
  exact C.
Qed.

Theorem n4_3 (P Q : Prop) :
  (P ∧ Q) ↔ (Q ∧ P).
Proof.
  pose proof (n3_22 P Q) as n3_22a.
  pose proof (n3_22 Q P) as n3_22b.
  Conj_as n3_22a n3_22b C.
  Equiv C.
  exact C.
Qed.

Theorem n4_31 (P Q : Prop) :
  (P ∨ Q) ↔ (Q ∨ P).
Proof.
  pose proof (Perm1_4 P Q) as Perm1_4a.
  pose proof (Perm1_4 Q P) as Perm1_4b.
  Conj_as Perm1_4a Perm1_4b C.
  Equiv C.
  exact C.
Qed.

Theorem n4_32 (P Q R : Prop) :
  ((P ∧ Q) ∧ R) ↔ (P ∧ (Q ∧ R)).
Proof.
  pose proof (n4_15 P Q R) as n4_15a.
  pose proof (Transp4_1 P (¬ (Q ∧ R))) as Transp4_1a.
  apply propositional_extensionality in Transp4_1a.
  pose proof (n4_13 (Q ∧ R)) as n4_13a.
  apply propositional_extensionality in n4_13a.
  pose proof (n4_21 (¬ (P ∧ Q → ¬ R) ↔ ¬ (P → ¬ (Q ∧ R)))
    ((P ∧ Q → ¬ R) ↔ (P → ¬ (Q ∧ R)))) as n4_21a.
  apply propositional_extensionality in n4_21a.
  replace (¬¬ (Q ∧ R)) with (Q ∧ R) in Transp4_1a
    by now apply n4_13a.
  replace (Q ∧ R → ¬ P) with (P → ¬ (Q ∧ R)) in n4_15a
    by now apply Transp4_1a.
  pose proof (Transp4_11 (P ∧ Q → ¬ R) (P → ¬ (Q ∧ R))) as Transp4_11a.
  apply propositional_extensionality in Transp4_11a.
  symmetry in Transp4_11a.
  replace ((P ∧ Q → ¬ R) ↔ (P → ¬ (Q ∧ R))) with 
      (¬ (P ∧ Q → ¬ R) ↔ ¬ (P → ¬ (Q ∧ R))) in n4_15a
      by now apply Transp4_11a.
  replace (P ∧ Q → ¬ R) with 
      (¬ (P ∧ Q) ∨ ¬ R) in n4_15a
      by now rewrite Impl1_01.
  replace (P → ¬ (Q ∧ R)) with 
      (¬ P ∨ ¬ (Q ∧ R)) in n4_15a
      by now rewrite Impl1_01.
  replace (¬ (¬ (P ∧ Q) ∨ ¬ R)) with 
      ((P ∧ Q) ∧ R) in n4_15a
      by now rewrite Prod3_01.
  replace (¬ (¬ P ∨ ¬ (Q ∧ R))) with 
      (P ∧ (Q ∧ R)) in n4_15a
      by now rewrite Prod3_01.
  exact n4_15a.
Qed.
  (*Note that the actual proof uses n4_12, but 
      that transposition involves transforming a 
      biconditional into a conditional.This citation
      of the lemma may be a misprint.Using 
      Transp4_1 to transpose a conditional and 
      then applying n4_13 to double negate does 
      secure the desired formula.*)

Theorem n4_33 (P Q R : Prop) :
  (P ∨ (Q ∨ R)) ↔ ((P ∨ Q) ∨ R).
Proof.
  pose proof (n2_31 P Q R) as n2_31a.
  pose proof (n2_32 P Q R) as n2_32a.
  Conj_as n2_31a n2_32a C.
  Equiv C.
  exact C.
Qed.

Theorem Abb4_34 (P Q R : Prop) :
  (P ∧ Q ∧ R) = ((P ∧ Q) ∧ R).
Proof.
  apply propositional_extensionality.
  pose proof (n4_21 ((P ∧ Q) ∧ R) (P ∧ Q ∧ R)) as n4_21.
  replace (((P ∧ Q) ∧ R ↔ P ∧ Q ∧ R) ↔ (P ∧ Q ∧ R ↔ (P ∧ Q) ∧ R))
    with ((((P ∧ Q) ∧ R ↔ P ∧ Q ∧ R) → (P ∧ Q ∧ R ↔ (P ∧ Q) ∧ R)) 
    ∧ ((P ∧ Q ∧ R ↔ (P ∧ Q) ∧ R) → ((P ∧ Q) ∧ R ↔ P ∧ Q ∧ R))) 
    in n4_21 by now rewrite Equiv4_01.
  pose proof (Simp3_26 
    (((P ∧ Q) ∧ R ↔ P ∧ Q ∧ R) → (P ∧ Q ∧ R ↔ (P ∧ Q) ∧ R))
    ((P ∧ Q ∧ R ↔ (P ∧ Q) ∧ R) → ((P ∧ Q) ∧ R ↔ P ∧ Q ∧ R))) as Simp3_26.
  MP Simp3_26 n4_21.
  pose proof (n4_32 P Q R) as n4_32.
  MP Simp3_26 n4_32.
  exact Simp3_26.
Qed.

Theorem n4_36 (P Q R : Prop) :
  (P ↔ Q) → ((P ∧ R) ↔ (Q ∧ R)).
Proof.
  pose proof (Fact3_45 P Q R) as Fact3_45a.
  pose proof (Fact3_45 Q P R) as Fact3_45b.
  Conj_as Fact3_45a Fact3_45b C.
  pose proof (n3_47 (P → Q) (Q → P) 
      (P ∧ R → Q ∧ R) (Q ∧ R → P ∧ R)) as n3_47a.
  MP n3_47a C.
  replace  ((P → Q) ∧ (Q → P)) with (P ↔ Q) in n3_47a.
  replace ((P ∧ R → Q ∧ R) ∧ (Q ∧ R → P ∧ R)) with (P ∧ R ↔ Q ∧ R) in n3_47a.
  exact n3_47a.
  all : now rewrite Equiv4_01.
Qed.

Theorem n4_37 (P Q R : Prop) :
  (P ↔ Q) → ((P ∨ R) ↔ (Q ∨ R)).
Proof.
  pose proof (Sum1_6 R P Q) as Sum1_6a.
  pose proof (Sum1_6 R Q P) as Sum1_6b.
  Conj_as Sum1_6a Sum1_6b C.
  pose proof (n3_47 (P → Q) (Q → P) 
      (R ∨ P → R ∨ Q) (R ∨ Q → R ∨ P)) as n3_47a.
  MP n3_47a C.
  replace  ((P → Q) ∧ (Q → P)) with (P ↔ Q) in n3_47a.
  replace ((R ∨ P → R ∨ Q) ∧ (R ∨ Q → R ∨ P)) with (R ∨ P ↔ R ∨ Q) in n3_47a.
  pose proof (n4_31 Q R) as n4_31a.
  apply propositional_extensionality in n4_31a.
  pose proof (n4_31 P R) as n4_31b.
  apply propositional_extensionality in n4_31b.
  replace (R ∨ P) with (P ∨ R) in n3_47a
    by now apply n4_31b.
  replace (R ∨ Q) with (Q ∨ R) in n3_47a
    by now apply n4_31a.
  exact n3_47a.
  all: now rewrite Equiv4_01.
Qed.

Theorem n4_38 (P Q R S : Prop) :
  ((P ↔ R) ∧ (Q ↔ S)) → ((P ∧ Q) ↔ (R ∧ S)).
Proof.
  pose proof (n3_47 P Q R S) as n3_47a.
  pose proof (n3_47 R S P Q) as n3_47b.
  Conj_as n3_47a n3_47b Ca.
  pose proof (n3_47 ((P → R) ∧ (Q → S)) 
      ((R → P) ∧ (S → Q)) (P ∧ Q → R ∧ S) (R ∧ S → P ∧ Q)) as n3_47c.
  MP n3_47c Ca.
  pose proof (n4_32 (P → R) (Q → S) ((R → P) ∧ (S → Q))) as n4_32a.
  apply propositional_extensionality in n4_32a.
  symmetry in n4_32a.
  replace (((P → R) ∧ (Q → S)) ∧ (R → P) ∧ (S → Q)) with 
      ((P → R) ∧ (Q → S) ∧ (R → P) ∧ (S → Q)) in n3_47c
      by now apply n4_32a.
  pose proof (n4_32 (Q → S) (R → P) (S → Q)) as n4_32b.
  apply propositional_extensionality in n4_32b.
  replace ((Q → S) ∧ (R → P) ∧ (S → Q)) with 
      (((Q → S) ∧ (R → P)) ∧ (S → Q)) in n3_47c
      by now apply n4_32b.
  pose proof (n3_22 (Q → S) (R → P)) as n3_22a.
  pose proof (n3_22 (R → P) (Q → S)) as n3_22b.
  Conj_as n3_22a n3_22b Cb.
  Equiv Cb.
  pose proof (n4_3 (R → P) (Q → S)) as n4_3a.
  apply propositional_extensionality in n4_3a.
  replace ((Q → S) ∧ (R → P)) with 
      ((R → P) ∧ (Q → S)) in n3_47c
      by now apply n4_3a.
  pose proof (n4_32 (R → P) (Q → S) (S → Q)) as n4_32c.
  apply propositional_extensionality in n4_32c.
  symmetry in n4_32c.
  replace (((R → P) ∧ (Q → S)) ∧ (S → Q)) with 
      ((R → P) ∧ (Q → S) ∧ (S → Q)) in n3_47c
      by now apply n4_32c.
  pose proof (n4_32 (P → R) (R → P) ((Q → S) ∧ (S → Q))) as n4_32d.
  apply propositional_extensionality in n4_32d.
  replace ((P → R) ∧ (R → P) ∧ (Q → S) ∧ (S → Q)) with 
      (((P → R) ∧ (R → P)) ∧ (Q → S) ∧ (S → Q)) in n3_47c
      by now apply n4_32d.
  replace ((P → R) ∧ (R → P)) with (P ↔ R) in n3_47c.
  replace ((Q → S) ∧ (S → Q)) with (Q ↔ S) in n3_47c.
  replace ((P ∧ Q → R ∧ S) ∧ (R ∧ S → P ∧ Q)) with ((P ∧ Q) ↔ (R ∧ S)) in n3_47c.
  exact n3_47c.
  all : now rewrite Equiv4_01.
Qed.

Theorem n4_39 (P Q R S : Prop) :
  ((P ↔ R) ∧ (Q ↔ S)) → ((P ∨ Q) ↔ (R ∨ S)).
Proof.
  pose proof (n3_48 P Q R S) as n3_48a.
  pose proof (n3_48 R S P Q) as n3_48b.
  Conj_as n3_48a n3_48b Ca.
  pose proof (n3_47 ((P → R) ∧ (Q → S)) 
      ((R → P) ∧ (S → Q)) (P ∨ Q → R ∨ S) (R ∨ S → P ∨ Q)) as n3_47a.
  MP n3_47a Ca.
  replace ((P ∨ Q → R ∨ S) ∧ (R ∨ S → P ∨ Q)) with ((P ∨ Q) ↔ (R ∨ S)) in n3_47a.
  pose proof (n4_32 ((P → R) ∧ (Q → S)) (R → P) (S → Q)) as n4_32a.
  apply propositional_extensionality in n4_32a.
  replace (((P → R) ∧ (Q → S)) ∧ (R → P) ∧ (S → Q)) with 
      ((((P → R) ∧ (Q → S)) ∧ (R → P)) ∧ (S → Q)) in n3_47a
      by now apply n4_32a.
  pose proof (n4_32 (P → R) (Q → S) (R → P)) as n4_32b.
  apply propositional_extensionality in n4_32b.
  symmetry in n4_32b.
  replace (((P → R) ∧ (Q → S)) ∧ (R → P)) with 
      ((P → R) ∧ (Q → S) ∧ (R → P)) in n3_47a
      by now apply n4_32b.
  pose proof (n3_22 (Q → S) (R → P)) as n3_22a.
  pose proof (n3_22 (R → P) (Q → S)) as n3_22b.
  Conj_as  n3_22a n3_22b Cb.
  Equiv Cb.
  apply propositional_extensionality in Cb.
  symmetry in Cb.
  replace ((Q → S) ∧ (R → P)) with 
      ((R → P) ∧ (Q → S)) in n3_47a
      by now apply Cb.
  pose proof (n4_32 (P → R) (R → P) (Q → S)) as n4_32c.
  apply propositional_extensionality in n4_32c.
  replace ((P → R) ∧ (R → P) ∧ (Q → S)) with 
      (((P → R) ∧ (R → P)) ∧ (Q → S)) in n3_47a
      by now apply n4_32c.
  replace ((P → R) ∧ (R → P)) with (P ↔ R) in n3_47a.
  pose proof (n4_32 (P ↔ R) (Q → S) (S → Q)) as n4_32d.
  apply propositional_extensionality in n4_32d.
  symmetry in n4_32d.
  replace (((P ↔ R) ∧ (Q → S)) ∧ (S → Q)) with 
      ((P ↔ R) ∧ (Q → S) ∧ (S → Q)) in n3_47a
      by now apply n4_32d.
  replace ((Q → S) ∧ (S → Q)) with (Q ↔ S) in n3_47a.
  exact n3_47a.
  all: now rewrite Equiv4_01.
Qed.

Theorem n4_4 (P Q R : Prop) :
  (P ∧ (Q ∨ R)) ↔ ((P ∧ Q) ∨ (P ∧ R)).
Proof.
  assert (Ca: (P → Q → P ∧ Q) ∧ (P → R → P ∧ R)).
  {
    pose proof (n3_2 P Q) as n3_2a.
    pose proof (n3_2 P R) as n3_2b.
    Conj_as n3_2a n3_2b Ca.
    exact Ca.
  }
  pose proof (Comp3_43 P (Q → P ∧ Q) (R → P ∧ R)) as Comp3_43a.
  MP Comp3_43a Ca.
  pose proof (n3_48 Q R (P ∧ Q) (P ∧ R)) as n3_48a.
  Syll_as Comp3_43a n3_48a Sa.
  pose proof (Imp3_31 P (Q ∨ R) ((P ∧ Q) ∨ (P ∧ R))) as Imp3_31a.
  MP Imp3_31a Sa.
  assert (Cb: (P ∧ Q → P) ∧ (P ∧ R → P)).
  {
    pose proof (Simp3_26 P Q) as Simp3_26a.
    pose proof (Simp3_26 P R) as Simp3_26b.
    Conj_as Simp3_26a Simp3_26b Cb.
    exact Cb.
  }
  pose proof (n3_44 P (P ∧ Q) (P ∧ R)) as n3_44a.
  MP n3_44a Cb.
  assert (Cc: (P ∧ Q → Q) ∧ (P ∧ R → R)).
  {
    pose proof (Simp3_27 P Q) as Simp3_27a.
    pose proof (Simp3_27 P R) as Simp3_27b.
    Conj_as Simp3_27a Simp3_27b Cc.
    exact Cc.
  }
  pose proof (n3_48 (P ∧ Q) (P ∧ R) Q R) as n3_48b.
  MP n3_48b Cc.
  clear Ca Cb Cc Comp3_43a Sa.
  Conj_as n3_44a n3_48b Cdd. (*Cd is reserved*)
  pose proof (Comp3_43 (P ∧ Q ∨ P ∧ R) P (Q ∨ R)) as Comp3_43b.
  MP Comp3_43b Cdd.
  clear n3_48a n3_44a n3_48b Cdd.
  Conj_as Imp3_31a Comp3_43b Ce.
  Equiv Ce.
  exact Ce.
Qed.

Theorem n4_41 (P Q R : Prop) :
  (P ∨ (Q ∧ R)) ↔ ((P ∨ Q) ∧ (P ∨ R)).
Proof.
  assert (Sum1_6a: P ∨ Q ∧ R → P ∨ Q).
  {
    pose proof (Simp3_26 Q R) as Simp3_26a.
    pose proof (Sum1_6 P (Q ∧ R) Q) as Sum1_6a.
    MP Sum1_6a Simp3_26a.
    exact Sum1_6a.
  }
  assert (Sum1_6b: P ∨ Q ∧ R → P ∨ R).
  {
    pose proof (Simp3_27 Q R) as Simp3_27a.
    pose proof (Sum1_6 P (Q ∧ R) R) as Sum1_6b.
    MP Sum1_6b Simp3_27a.
    exact Sum1_6b.
  }
  (* ??? *)
  Conj_as Sum1_6a Sum1_6b Ca.
  pose proof (Comp3_43 (P ∨ Q ∧ R) (P ∨ Q) (P ∨ R)) as Comp3_43a.
  MP Comp3_43a Ca.
  pose proof (n2_53 P Q) as n2_53a.
  pose proof (n2_53 P R) as n2_53b.
  Conj_as n2_53a n2_53b Cb.
  pose proof (n3_47 (P ∨ Q) (P ∨ R) (¬ P → Q) (¬ P → R)) as n3_47a.
  MP n3_47a Cb.
  pose proof (Comp3_43 (¬ P) Q R) as Comp3_43b.
  Syll_as n3_47a Comp3_43b Sa.
  pose proof (n2_54 P (Q ∧ R)) as n2_54a.
  Syll_as Sa n2_54a Sb.
  clear Sum1_6a. clear Sum1_6b. clear Ca. clear n2_53a.
      clear n2_53b. clear Cb. clear n3_47a. clear Sa.
      clear Comp3_43b. clear n2_54a.
  Conj_as Comp3_43a Sb Cc.
  Equiv Cc.
  exact Cc.
Qed.

Theorem n4_42 (P Q : Prop) :
  P ↔ ((P ∧ Q) ∨ (P ∧ ¬ Q)).
Proof.
  pose proof (n3_21 P (Q ∨ ¬ Q)) as n3_21a.
  pose proof (n2_11 Q) as n2_11a.
  MP n3_21a n2_11a.
  pose proof (Simp3_26 P (Q ∨ ¬ Q)) as Simp3_26a. clear n2_11a.
  Conj_as n3_21a Simp3_26a C.
  Equiv C.
  pose proof (n4_4 P Q (¬ Q)) as n4_4a.
  apply propositional_extensionality in C.
  replace (P ∧ (Q ∨ ¬ Q)) with P in n4_4a
    by now apply C.
  exact n4_4a.
Qed.

Theorem n4_43 (P Q : Prop) :
  P ↔ ((P ∨ Q) ∧ (P ∨ ¬ Q)).
Proof.
  pose proof (n2_2 P Q) as n2_2a.
  pose proof (n2_2 P (¬ Q)) as n2_2b.
  Conj_as n2_2a n2_2b Ca.
  pose proof (Comp3_43 P (P ∨ Q) (P ∨ ¬ Q)) as Comp3_43a.
  MP Comp3_43a Ca.
  pose proof (n2_53 P Q) as n2_53a.
  pose proof (n2_53 P (¬ Q)) as n2_53b.
  Conj_as n2_53a n2_53b Cb.
  pose proof (n3_47 (P ∨ Q) (P ∨ ¬ Q) (¬ P → Q) (¬ P → ¬ Q)) as n3_47a.
  MP n3_47a Cb.
  pose proof (n2_65 (¬ P) Q) as n2_65a.
  pose proof (n4_13 P) as n4_13a.
  apply propositional_extensionality in n4_13a.
  replace (¬¬ P) with P in n2_65a by now apply n4_13a.
  pose proof (Imp3_31 (¬ P → Q) (¬ P → ¬ Q) (P)) as Imp3_31a.
  MP Imp3_31a n2_65a.
  Syll_as n3_47a Imp3_31a Sa.
  clear n2_2a. clear n2_2b. clear Ca. clear n2_53a.
    clear n2_53b. clear Cb. clear n2_65a.
    clear n3_47a. clear Imp3_31a. clear n4_13a.
  Conj_as Comp3_43a Sa Cc.
  Equiv Cc.
  exact Cc.
Qed.

Theorem n4_44 (P Q : Prop) :
  P ↔ (P ∨ (P ∧ Q)).
Proof.
  pose proof (n2_2 P (P ∧ Q)) as n2_2a.
  pose proof (Id2_08 P) as Id2_08a.
  pose proof (Simp3_26 P Q) as Simp3_26a.
  Conj_as Id2_08a Simp3_26a Ca.
  pose proof (n3_44 P P (P ∧ Q)) as n3_44a.
  MP n3_44a Ca.
  clear Ca. clear Id2_08a. clear Simp3_26a.
  Conj_as n2_2a n3_44a Cb.
  Equiv Cb.
  exact Cb.
Qed.

Theorem n4_45 (P Q : Prop) :
  P ↔ (P ∧ (P ∨ Q)).
Proof.
  pose proof (n2_2 (P ∧ P) (P ∧ Q)) as n2_2a.
  pose proof (n4_4 P P Q) as n4_4a.
  apply propositional_extensionality in n4_4a.
  replace (P ∧ P ∨ P ∧ Q) with (P ∧ (P ∨ Q)) in n2_2a
    by now apply n4_4a.
  pose proof (n4_24 P) as n4_24a.
  apply propositional_extensionality in n4_24a.
  replace (P ∧ P) with P in n2_2a 
    by now apply n4_24a.
  pose proof (Simp3_26 P (P ∨ Q)) as Simp3_26a.
  clear n4_4a. clear n4_24a.
  Conj_as n2_2a Simp3_26a C.
  Equiv C.
  exact C.
Qed.

Theorem n4_5 (P Q : Prop) :
  P ∧ Q ↔ ¬ (¬ P ∨ ¬ Q).
Proof.
  pose proof (n4_2 (P ∧ Q)) as n4_2a.
  replace ((P ∧ Q) ↔ (P ∧ Q)) with 
    ((P ∧ Q) ↔ ¬ (¬ P ∨ ¬ Q)) in n4_2a 
    by now rewrite Prod3_01.
  exact n4_2a.
Qed.

Theorem n4_51 (P Q : Prop) :
  ¬ (P ∧ Q) ↔ (¬ P ∨ ¬ Q).
Proof.
  pose proof (n4_5 P Q) as n4_5a.
  pose proof (n4_12 (P ∧ Q) (¬ P ∨ ¬ Q)) as n4_12a.
  pose proof (Simp3_26 
    ((P ∧ Q ↔ ¬ (¬ P ∨ ¬ Q)) → (¬ P ∨ ¬ Q ↔ ¬ (P ∧ Q)))
    ((¬ P ∨ ¬ Q ↔ ¬ (P ∧ Q)) → ((P ∧ Q ↔ ¬ (¬ P ∨ ¬ Q))))) as Simp3_26a.
  replace ((P ∧ Q ↔ ¬ (¬ P ∨ ¬ Q)) ↔ (¬ P ∨ ¬ Q ↔ ¬ (P ∧ Q)))
    with (((P ∧ Q ↔ ¬ (¬ P ∨ ¬ Q)) → (¬ P ∨ ¬ Q ↔ ¬ (P ∧ Q)))
    ∧ ((¬ P ∨ ¬ Q ↔ ¬ (P ∧ Q)) → ((P ∧ Q ↔ ¬ (¬ P ∨ ¬ Q)))))
    in n4_12a by now rewrite Equiv4_01.
  MP Simp3_26a n4_12a.
  MP Simp3_26a n4_5a.
  pose proof (n4_21 (¬ (P ∧ Q)) (¬ P ∨ ¬ Q)) as n4_21a.
  pose proof (Simp3_27 
  (((¬ (P ∧ Q) ↔ ¬ P ∨ ¬ Q)) → ((¬ P ∨ ¬ Q ↔ ¬ (P ∧ Q))))
  (((¬ P ∨ ¬ Q ↔ ¬ (P ∧ Q))) → ((¬ (P ∧ Q) ↔ ¬ P ∨ ¬ Q)))) as Simp3_27a.
  MP Simp3_27a n4_21a.
  MP Simp3_27a Simp3_26a.
  exact Simp3_27a.
Qed.

Theorem n4_52 (P Q : Prop) :
  (P ∧ ¬ Q) ↔ ¬ (¬ P ∨ Q).
Proof.
  pose proof (n4_5 P (¬ Q)) as n4_5a.
  pose proof (n4_13 Q) as n4_13a.
  apply propositional_extensionality in n4_13a.
  replace (¬¬ Q) with Q in n4_5a 
    by now apply n4_13a.
  exact n4_5a.
Qed.

Theorem n4_53 (P Q : Prop) :
  ¬ (P ∧ ¬ Q) ↔ (¬ P ∨ Q).
Proof.
  pose proof (n4_52 P Q) as n4_52a.
  pose proof (n4_12 (P ∧ ¬ Q) ((¬ P ∨ Q))) as n4_12a.
  replace ((P ∧ ¬ Q ↔ ¬ (¬ P ∨ Q)) ↔ (¬ P ∨ Q ↔ ¬ (P ∧ ¬ Q)))
    with (((P ∧ ¬ Q ↔ ¬ (¬ P ∨ Q)) → (¬ P ∨ Q ↔ ¬ (P ∧ ¬ Q)))
    ∧ ((¬ P ∨ Q ↔ ¬ (P ∧ ¬ Q)) → (P ∧ ¬ Q ↔ ¬ (¬ P ∨ Q))))
    in n4_12a by now rewrite Equiv4_01.
  pose proof (Simp3_26 
    ((P ∧ ¬ Q ↔ ¬ (¬ P ∨ Q)) → (¬ P ∨ Q ↔ ¬ (P ∧ ¬ Q)))
    ((¬ P ∨ Q ↔ ¬ (P ∧ ¬ Q)) → (P ∧ ¬ Q ↔ ¬ (¬ P ∨ Q)))) as Simp3_26a.
  MP Simp3_26a n4_12a.
  MP Simp3_26a n4_52a.
  pose proof (n4_21 (¬ (P ∧ ¬ Q)) (¬ P ∨ Q)) as n4_21a.
  replace ((¬ (P ∧ ¬ Q) ↔ ¬ P ∨ Q) ↔ (¬ P ∨ Q ↔ ¬ (P ∧ ¬ Q)))
    with (((¬ (P ∧ ¬ Q) ↔ ¬ P ∨ Q) → (¬ P ∨ Q ↔ ¬ (P ∧ ¬ Q)))
    ∧ ((¬ P ∨ Q ↔ ¬ (P ∧ ¬ Q)) → (¬ (P ∧ ¬ Q) ↔ ¬ P ∨ Q)))
    in n4_21a by now rewrite Equiv4_01.
  pose proof (Simp3_27 
    ((¬ (P ∧ ¬ Q) ↔ ¬ P ∨ Q) → (¬ P ∨ Q ↔ ¬ (P ∧ ¬ Q)))
    ((¬ P ∨ Q ↔ ¬ (P ∧ ¬ Q)) → (¬ (P ∧ ¬ Q) ↔ ¬ P ∨ Q))) as Simp3_27a.
  MP Simp3_27a n4_21a.
  MP Simp3_27a Simp3_26a.
  exact Simp3_27a.
Qed.

Theorem n4_54 (P Q : Prop) :
  (¬ P ∧ Q) ↔ ¬ (P ∨ ¬ Q).
Proof.
  pose proof (n4_5 (¬ P) Q) as n4_5a.
  pose proof (n4_13 P) as n4_13a.
  apply propositional_extensionality in n4_13a.
  replace (¬¬ P) with P in n4_5a
   by now apply n4_13a.
  exact n4_5a.
Qed.

Theorem n4_55 (P Q : Prop) :
  ¬ (¬ P ∧ Q) ↔ (P ∨ ¬ Q).
Proof.
  pose proof (n4_54 P Q) as n4_54a.
  pose proof (n4_12 (¬ P ∧ Q) (P ∨ ¬ Q)) as n4_12a.
  apply propositional_extensionality in n4_12a.
  symmetry in n4_12a.
  replace (¬ P ∧ Q ↔ ¬ (P ∨ ¬ Q)) with 
      (P ∨ ¬ Q ↔ ¬ (¬ P ∧ Q)) in n4_54a 
      by now apply n4_12a.
  pose proof (n4_21 (¬ (¬ P ∧ Q)) (P ∨ ¬ Q)) as n4_21a. (*Not cited*)
  apply propositional_extensionality in n4_21a.
  replace (P ∨ ¬ Q ↔ ¬ (¬ P ∧ Q)) with 
      (¬ (¬ P ∧ Q) ↔ (P ∨ ¬ Q)) in n4_54a
      by now apply n4_21a.
  exact n4_54a.
Qed.

Theorem n4_56 (P Q : Prop) :
  (¬ P ∧ ¬ Q) ↔ ¬ (P ∨ Q).
Proof.
  pose proof (n4_54 P (¬ Q)) as n4_54a.
  pose proof (n4_13 Q) as n4_13a.
  apply propositional_extensionality in n4_13a.
  replace (¬¬ Q) with Q in n4_54a 
    by now apply n4_13a.
  exact n4_54a.
Qed.

Theorem n4_57 (P Q : Prop) :
  ¬ (¬ P ∧ ¬ Q) ↔ (P ∨ Q).
Proof.
  pose proof (n4_56 P Q) as n4_56a.
  pose proof (n4_12 (¬ P ∧ ¬ Q) (P ∨ Q)) as n4_12a.
  apply propositional_extensionality in n4_12a.
  symmetry in n4_12a.
  replace (¬ P ∧ ¬ Q ↔ ¬ (P ∨ Q)) with 
      (P ∨ Q ↔ ¬ (¬ P ∧ ¬ Q)) in n4_56a
      by now apply n4_12a.
  pose proof (n4_21 (¬ (¬ P ∧ ¬ Q)) (P ∨ Q)) as n4_21a.
  apply propositional_extensionality in n4_21a.
  replace (P ∨ Q ↔ ¬ (¬ P ∧ ¬ Q)) with 
      (¬ (¬ P ∧ ¬ Q) ↔ P ∨ Q) in n4_56a
      by now apply n4_21a.
  exact n4_56a.
Qed.
  
Theorem n4_6 (P Q : Prop) :
  (P → Q) ↔ (¬ P ∨ Q).
Proof.
  pose proof (n4_2 (¬ P ∨ Q)) as n4_2a.
  rewrite Impl1_01.
  exact n4_2a.
Qed.

Theorem n4_61 (P Q : Prop) :
  ¬ (P → Q) ↔ (P ∧ ¬ Q).
Proof.
  pose proof (n4_6 P Q) as n4_6a.
  pose proof (Transp4_11 (P → Q) (¬ P ∨ Q)) as Transp4_11a.
  apply propositional_extensionality in Transp4_11a.
  symmetry in Transp4_11a.
  replace ((P → Q) ↔ ¬ P ∨ Q) with 
      (¬ (P → Q) ↔ ¬ (¬ P ∨ Q)) in n4_6a
      by now apply Transp4_11a.
  pose proof (n4_52 P Q) as n4_52a.
  apply propositional_extensionality in n4_52a.
  replace (¬ (¬ P ∨ Q)) with (P ∧ ¬ Q) in n4_6a
    by now apply n4_52a.
  exact n4_6a.
Qed.

Theorem n4_62 (P Q : Prop) :
  (P → ¬ Q) ↔ (¬ P ∨ ¬ Q).
Proof.
  pose proof (n4_6 P (¬ Q)) as n4_6a.
  exact n4_6a.
Qed.

Theorem n4_63 (P Q : Prop) :
  ¬ (P → ¬ Q) ↔ (P ∧ Q).
Proof.
  pose proof (n4_62 P Q) as n4_62a.
  pose proof (Transp4_11 (P → ¬ Q) (¬ P ∨ ¬ Q)) as Transp4_11a.
  pose proof (n4_5 P Q) as n4_5a.
  apply propositional_extensionality in n4_5a.
  replace (¬ (¬ P ∨ ¬ Q)) with (P ∧ Q) in Transp4_11a
    by now apply n4_5a.
  apply propositional_extensionality in Transp4_11a.
  symmetry in Transp4_11a.
  replace ((P → ¬ Q) ↔ ¬ P ∨ ¬ Q) with 
      ((¬ (P → ¬ Q) ↔ P ∧ Q)) in n4_62a
      by now apply Transp4_11a.
  exact n4_62a.
Qed.
(*One could use Prod3_01 in lieu of n4_5.*)

Theorem n4_64 (P Q : Prop) :
  (¬ P → Q) ↔ (P ∨ Q).
Proof.
  pose proof (n2_54 P Q) as n2_54a.
  pose proof (n2_53 P Q) as n2_53a.
  Conj_as n2_54a n2_53a C.
  Equiv C.
  exact C.
Qed.

Theorem n4_65 (P Q : Prop) :
  ¬ (¬ P → Q) ↔ (¬ P ∧ ¬ Q).
Proof.
  pose proof (n4_64 P Q) as n4_64a.
  pose proof (Transp4_11(¬ P → Q) (P ∨ Q)) as Transp4_11a.
  pose proof (n4_21 (¬ (¬ P → Q) ↔ ¬ (P ∨ Q))
      ((¬ P → Q) ↔ (P ∨ Q))) as n4_21a.
  apply propositional_extensionality in n4_21a.
  replace (((¬ P → Q) ↔ P ∨ Q) ↔ (¬ (¬ P → Q) ↔ ¬ (P ∨ Q))) with 
      ((¬ (¬ P → Q) ↔ ¬ (P ∨ Q)) ↔ ((¬ P → Q) ↔ P ∨ Q)) in Transp4_11a
      by now apply n4_21a.
  apply propositional_extensionality in Transp4_11a.
  replace ((¬ P → Q) ↔ P ∨ Q) with 
      (¬ (¬ P → Q) ↔ ¬ (P ∨ Q)) in n4_64a
      by now apply Transp4_11a.
  pose proof (n4_56 P Q) as n4_56a.
  apply propositional_extensionality in n4_56a.
  replace (¬ (P ∨ Q)) with (¬ P ∧ ¬ Q) in n4_64a
    by now apply n4_56a.
  exact n4_64a.
Qed.

Theorem n4_66 (P Q : Prop) :
  (¬ P → ¬ Q) ↔ (P ∨ ¬ Q).
Proof.
  pose proof (n4_64 P (¬ Q)) as n4_64a.
  exact n4_64a.
Qed.

Theorem n4_67 (P Q : Prop) :
  ¬ (¬ P → ¬ Q) ↔ (¬ P ∧ Q).
Proof.
  pose proof (n4_66 P Q) as n4_66a.
  pose proof (Transp4_11 (¬ P → ¬ Q) (P ∨ ¬ Q)) as Transp4_11a.
  apply propositional_extensionality in Transp4_11a.
  symmetry in Transp4_11a.
  replace ((¬ P → ¬ Q) ↔ P ∨ ¬ Q) with 
      (¬ (¬ P → ¬ Q) ↔ ¬ (P ∨ ¬ Q)) in n4_66a
      by now apply Transp4_11a.
  pose proof (n4_54 P Q) as n4_54a.
  apply propositional_extensionality in n4_54a.
  replace (¬ (P ∨ ¬ Q)) with (¬ P ∧ Q) in n4_66a
    by now apply n4_54a.
  exact n4_66a.
Qed.

Theorem n4_7 (P Q : Prop) :
  (P → Q) ↔ (P → (P ∧ Q)).
Proof.
  pose proof (Comp3_43 P P Q) as Comp3_43a.
  pose proof (Exp3_3 (P → P) (P → Q) (P → P ∧ Q)) as Exp3_3a.
  MP Exp3_3a Comp3_43a.
  pose proof (Id2_08 P) as Id2_08a.
  MP Exp3_3a Id2_08a.
  pose proof (Simp3_27 P Q) as Simp3_27a.
  pose proof (Syll2_05 P (P ∧ Q) Q) as Syll2_05a.
  MP Syll2_05a Simp3_27a.
  clear Id2_08a. clear Comp3_43a. clear Simp3_27a.
  Conj_as Syll2_05a Exp3_3a C.
  Equiv C.
  rewrite -> n4_21 in C.
  exact C.
Qed.

Theorem n4_71 (P Q : Prop) :
  (P → Q) ↔ (P ↔ (P ∧ Q)).
Proof.
  pose proof (n4_7 P Q) as n4_7a.
  pose proof (n3_21 (P → (P ∧ Q)) ((P ∧ Q) → P)) as n3_21a.
  replace ((P → P ∧ Q) ∧ (P ∧ Q → P)) with (P ↔ (P ∧ Q)) 
      in n3_21a by now rewrite Equiv4_01.
  pose proof (Simp3_26 P Q) as Simp3_26a.
  MP n3_21a Simp3_26a.
  pose proof (Simp3_26 (P → (P ∧ Q)) ((P ∧ Q) → P)) as Simp3_26b.
  replace ((P → P ∧ Q) ∧ (P ∧ Q → P)) with (P ↔ (P ∧ Q)) 
    in Simp3_26b by now rewrite Equiv4_01.
  clear Simp3_26a.
  Conj_as n3_21a Simp3_26b Ca.
  Equiv Ca.
  clear n3_21a. clear Simp3_26b.
  Conj_as n4_7a Ca Cb.
  pose proof (n4_22 (P → Q) (P → P ∧ Q) (P ↔ P ∧ Q)) as n4_22a.
  MP n4_22a Cb.
  exact n4_22a.
Qed.

Theorem n4_72 (P Q : Prop) :
  (P → Q) ↔ (Q ↔ (P ∨ Q)).
Proof.
  pose proof (Transp4_1 P Q) as Transp4_1a.
  pose proof (n4_71 (¬ Q) (¬ P)) as n4_71a.
  Conj_as Transp4_1a n4_71a Ca.
  pose proof (n4_22 (P → Q) (¬ Q → ¬ P) (¬ Q ↔ ¬ Q ∧ ¬ P)) as n4_22a.
  MP n4_22a Ca.
  pose proof (n4_21 (¬ Q) (¬ Q ∧ ¬ P)) as n4_21a.
  Conj_as n4_22a n4_21a Cb.
  pose proof (n4_22 (P → Q) (¬ Q ↔ ¬ Q ∧ ¬ P) 
    (¬ Q ∧ ¬ P ↔ ¬ Q)) as n4_22b.
  MP n4_22b Cb.
  pose proof (n4_12 (¬ Q ∧ ¬ P) (Q)) as n4_12a.
  Conj_as n4_22b n4_12a Cc.
  pose proof (n4_22 (P → Q) ((¬ Q ∧ ¬ P) ↔ ¬ Q) 
    (Q ↔ ¬ (¬ Q ∧ ¬ P))) as n4_22c.
  MP n4_22c Cc.
  pose proof (n4_57 Q P) as n4_57a.
  apply propositional_extensionality in n4_57a.
  symmetry in n4_57a.
  replace (¬ (¬ Q ∧ ¬ P)) with (Q ∨ P) in n4_22c
    by now apply n4_57a.
  pose proof (n4_31 P Q) as n4_31a.
  apply propositional_extensionality in n4_31a.
  replace (Q ∨ P) with (P ∨ Q) in n4_22c
    by now apply n4_31a.
  exact n4_22c.
Qed.
(*One could use Prod3_01 in lieu of n4_57.*)

Theorem n4_73 (P Q : Prop) :
  Q → (P ↔ (P ∧ Q)).
Proof.
  pose proof (Simp2_02 P Q) as Simp2_02a.
  pose proof (n4_71 P Q) as n4_71a.
  replace ((P → Q) ↔ (P ↔ P ∧ Q)) with 
      (((P → Q) → (P ↔ P ∧ Q)) ∧ ((P ↔ P ∧ Q) → (P → Q))) 
      in n4_71a by now rewrite Equiv4_01.
  pose proof (Simp3_26 ((P → Q) → P ↔ P ∧ Q) 
    (P ↔ P ∧ Q → P → Q)) as Simp3_26a.
  MP Simp3_26a n4_71a.
  Syll_as Simp2_02a Simp3_26a Sa.
  exact Sa.
Qed.

Theorem n4_74 (P Q : Prop) :
  ¬ P → (Q ↔ (P ∨ Q)).
Proof.
  pose proof (n2_21 P Q) as n2_21a.
  pose proof (n4_72 P Q) as n4_72a.
  apply propositional_extensionality in n4_72a.
  symmetry in n4_72a.
  replace (P → Q) with (Q ↔ P ∨ Q) in n2_21a
    by now apply n4_72a.
  exact n2_21a.
Qed.

Theorem n4_76 (P Q R : Prop) :
  ((P → Q) ∧ (P → R)) ↔ (P → (Q ∧ R)).
Proof.
  pose proof (n4_41 (¬ P) Q R) as n4_41a.
  replace (¬ P ∨ Q) with (P → Q) in n4_41a.
  replace (¬ P ∨ R) with (P → R) in n4_41a.
  replace (¬ P ∨ Q ∧ R) with (P → Q ∧ R) in n4_41a.
  pose proof (n4_21 ((P → Q) ∧ (P → R)) (P → Q ∧ R)) as n4_21a.
  apply propositional_extensionality in n4_21a.
  replace ((P → Q ∧ R) ↔ (P → Q) ∧ (P → R)) with 
      ((P → Q) ∧ (P → R) ↔ (P → Q ∧ R)) in n4_41a
      by now apply n4_21a.
  exact n4_41a.
  all: now rewrite Impl1_01.
Qed.

Theorem n4_77 (P Q R : Prop) :
  ((Q → P) ∧ (R → P)) ↔ ((Q ∨ R) → P).
Proof.
  pose proof (n3_44 P Q R) as n3_44a.
  pose proof (n2_2 Q R) as n2_2a.
  pose proof (Add1_3 Q R) as Add1_3a.
  pose proof (Syll2_06 Q (Q ∨ R) P) as Syll2_06a.
  MP Syll2_06a n2_2a.
  pose proof (Syll2_06 R (Q ∨ R) P) as Syll2_06b.
  MP Syll2_06b Add1_3a.
  Conj_as Syll2_06a Syll2_06b Ca.
  pose proof (Comp3_43  ((Q ∨ R) → P)
    (Q → P) (R → P)) as Comp3_43a.
  MP Comp3_43a Ca.
  clear n2_2a. clear Add1_3a. clear Ca.
    clear Syll2_06a. clear Syll2_06b.
  Conj_as n3_44a Comp3_43a Cb.
  Equiv Cb.
  exact Cb.
Qed.

Theorem n4_78 (P Q R : Prop) :
  ((P → Q) ∨ (P → R)) ↔ (P → (Q ∨ R)).
Proof.
  pose proof (n4_2 ((P → Q) ∨ (P → R))) as n4_2a.
  replace (((P → Q) ∨ (P → R)) ↔ ((P → Q) ∨ (P → R))) with 
      (((P → Q) ∨ (P → R)) ↔ ((P → Q) ∨ ¬ P ∨ R)) in n4_2a
      by now rewrite <- Impl1_01.
  replace (((P → Q) ∨ (P → R)) ↔ ((P → Q) ∨ ¬ P ∨ R)) with 
      (((P → Q) ∨ (P → R)) ↔ ((¬ P ∨ Q) ∨ ¬ P ∨ R)) in n4_2a
      by now rewrite <- Impl1_01.
  pose proof (n4_33 (¬ P) Q (¬ P ∨ R)) as n4_33a.
  apply propositional_extensionality in n4_33a.
  replace ((¬ P ∨ Q) ∨ ¬ P ∨ R) with 
      (¬ P ∨ Q ∨ ¬ P ∨ R) in n4_2a 
      by now apply n4_33a.
  pose proof (n4_33 Q (¬ P) R) as n4_33b.
  apply propositional_extensionality in n4_33b.
  symmetry in n4_33b.
  replace (Q ∨ ¬ P ∨ R) with 
      ((Q ∨ ¬ P) ∨ R) in n4_2a
      by now apply n4_33b.
  pose proof (n4_31 (¬ P) Q) as n4_31a.
  pose proof (n4_37 (¬ P ∨ Q) (Q ∨ ¬ P) R) as n4_37a.
  MP n4_37a n4_31a.
  apply propositional_extensionality in n4_37a.
  replace ((Q ∨ ¬ P) ∨ R) with 
      ((¬ P ∨ Q) ∨ R) in n4_2a
      by now apply n4_37a.
  pose proof (n4_33 (¬ P) (¬ P ∨ Q) R) as n4_33c.
  apply propositional_extensionality in n4_33c.
  symmetry in n4_33c.
  replace (¬ P ∨ (¬ P ∨ Q) ∨ R) with 
      ((¬ P ∨ (¬ P ∨ Q)) ∨ R) in n4_2a
      by now apply n4_33c.
  pose proof (n4_33 (¬ P) (¬ P) Q) as n4_33d.
  apply propositional_extensionality in n4_33d.
  symmetry in n4_33d.
  replace (¬ P ∨ ¬ P ∨ Q) with 
      ((¬ P ∨ ¬ P) ∨ Q) in n4_2a
      by now apply n4_33d.
  pose proof (n4_33 (¬ P ∨ ¬ P) Q R) as n4_33e.
  apply propositional_extensionality in n4_33e.
  replace (((¬ P ∨ ¬ P) ∨ Q) ∨ R) with 
      ((¬ P ∨ ¬ P) ∨ Q ∨ R) in n4_2a
      by now apply n4_33e.
  pose proof (n4_25 (¬ P)) as n4_25a.
  pose proof (n4_37 (¬ P) (¬ P ∨ ¬ P) (Q ∨ R)) as n4_37b.
  MP n4_37b n4_25a.
  apply propositional_extensionality in n4_25a.
  replace ((¬ P ∨ ¬ P) ∨ Q ∨ R) with 
      ((¬ P) ∨ (Q ∨ R)) in n4_2a
      by now rewrite <- n4_25a.
  replace (¬ P ∨ Q ∨ R) with 
      (P → (Q ∨ R)) in n4_2a
      by now rewrite Impl1_01.
  exact n4_2a.
Qed.

Theorem n4_79 (P Q R : Prop) :
  ((Q → P) ∨ (R → P)) ↔ ((Q ∧ R) → P).
Proof.
  pose proof (Transp4_1 Q P) as Transp4_1a.
  pose proof (Transp4_1 R P) as Transp4_1b.
  Conj_as Transp4_1a Transp4_1b Ca.
  pose proof (n4_39 
      (Q → P) (R → P) (¬ P → ¬ Q) (¬ P → ¬ R)) as n4_39a.
  MP n4_39a Ca.
  pose proof (n4_78 (¬ P) (¬ Q) (¬ R)) as n4_78a.
  rewrite Equiv4_01 in n4_78a.
  pose proof (Simp3_26 
    (((¬ P → ¬ Q) ∨ (¬ P → ¬ R)) → (¬ P → (¬ Q ∨ ¬ R)))
    ((¬ P → (¬ Q ∨ ¬ R)) → ((¬ P → ¬ Q) ∨ (¬ P → ¬ R)))) as Simp3_26a.
  MP Simp3_26a n4_78a.
  pose proof (Transp2_15 P (¬ Q ∨ ¬ R)) as Transp2_15a.
  pose proof (Simp3_27 
    (((¬ P → ¬ Q) ∨ (¬ P → ¬ R)) → (¬ P → (¬ Q ∨ ¬ R)))
    ((¬ P → (¬ Q ∨ ¬ R)) → ((¬ P → ¬ Q) ∨ (¬ P → ¬ R)))) as Simp3_27a.
  MP Simp3_27a n4_78a.
  pose proof (Transp2_15 (¬ Q ∨ ¬ R) P) as Transp2_15b.
  pose proof (Syll2_06 ((¬ P → ¬ Q) ∨ (¬ P → ¬ R))
    (¬ P → (¬ Q ∨ ¬ R)) (¬ (¬ Q ∨ ¬ R) → P)) as Syll2_06a.
  MP Syll2_06a Simp3_26a.
  MP Syll2_06a Transp2_15a.
  pose proof (Syll2_06 (¬ (¬ Q ∨ ¬ R) → P)
    (¬ P → (¬ Q ∨ ¬ R)) ((¬ P → ¬ Q) ∨ (¬ P → ¬ R))) as Syll2_06b.
  MP Syll2_06b Transp2_15b.
  MP Syll2_06b Simp3_27a.
  Conj_as Syll2_06a Syll2_06b Cb.
  Equiv Cb.
  clear Transp4_1a. clear Transp4_1b. clear Ca.
    clear Simp3_26a. clear Syll2_06b. clear n4_78a.
    clear Transp2_15a. clear Simp3_27a.
    clear Transp2_15b. clear Syll2_06a.
  Conj_as n4_39a Cb Cc.
  pose proof (n4_22 ((Q → P) ∨ (R → P))
    ((¬ P → ¬ Q) ∨ (¬ P → ¬ R)) (¬ (¬ Q ∨ ¬ R) → P)) as n4_22a.
  MP n4_22a Cc.
  pose proof (n4_2 (¬ (¬ Q ∨ ¬ R) → P)) as n4_2a.
  Conj_as n4_22a n4_2a Cdd.
  pose proof (n4_22 ((Q → P) ∨ (R → P))
  (¬ (¬ Q ∨ ¬ R) → P) (¬ (¬ Q ∨ ¬ R) → P)) as n4_22b.
  MP n4_22b Cdd.
  rewrite <- Prod3_01 in n4_22b.
  exact n4_22b.
Qed.

Theorem n_8 (P : Prop) :
  (P → ¬ P) ↔ ¬ P.
Proof.
  pose proof (Abs2_01 P) as Abs2_01a.
  pose proof (Simp2_02 P (¬ P)) as Simp2_02a.
  Conj_as Abs2_01a Simp2_02a C.
  Equiv C.
  exact C.
Qed.

Theorem n_81 (P : Prop) :
  (¬ P → P) ↔ P.
Proof.
  pose proof (n2_18 P) as n2_18a.
  pose proof (Simp2_02 (¬ P) P) as Simp2_02a.
  Conj_as n2_18a Simp2_02a C.
  Equiv C.
  exact C.
Qed.

Theorem n4_82 (P Q : Prop) :
  ((P → Q) ∧ (P → ¬ Q)) ↔ ¬ P.
Proof.
  pose proof (n2_65 P Q) as n2_65a.
  pose proof (Imp3_31 (P → Q) (P → ¬ Q) (¬ P)) as Imp3_31a.
  MP Imp3_31a n2_65a.
  pose proof (n2_21 P Q) as n2_21a.
  pose proof (n2_21 P (¬ Q)) as n2_21b.
  Conj_as n2_21a n2_21b Ca.
  pose proof (Comp3_43 (¬ P) (P → Q) (P → ¬ Q)) as Comp3_43a.
  MP Comp3_43a Ca.
  clear n2_65a. clear n2_21a.
    clear n2_21b. clear Ca.
  Conj_as Imp3_31a Comp3_43a Cb.
  Equiv Cb.
  exact Cb.
Qed.

Theorem n4_83 (P Q : Prop) :
  ((P → Q) ∧ (¬ P → Q)) ↔ Q.
Proof.
  pose proof (n2_61 P Q) as n2_61a.
  pose proof (Imp3_31 (P → Q) (¬ P → Q) (Q)) as Imp3_31a.
  MP Imp3_31a n2_61a.
  pose proof (Simp2_02 P Q) as Simp2_02a.
  pose proof (Simp2_02 (¬ P) Q) as Simp2_02b.
  Conj_as Simp2_02a Simp2_02b Ca.
  pose proof (Comp3_43 Q (P → Q) (¬ P → Q)) as Comp3_43a.
  MP Comp3_43a Ca.
  clear n2_61a. clear Simp2_02a.
  clear Simp2_02b. clear Ca.
  Conj_as Imp3_31a Comp3_43a Cb.
  Equiv Cb.
  exact Cb.
Qed.

Theorem n4_84 (P Q R : Prop) :
  (P ↔ Q) → ((P → R) ↔ (Q → R)).
Proof.
  pose proof (Syll2_06 P Q R) as Syll2_06a.
  pose proof (Syll2_06 Q P R) as Syll2_06b.
  Conj_as Syll2_06a Syll2_06b Ca.
  pose proof (n3_47 (P → Q) (Q → P) ((Q → R) → P → R) 
    ((P → R) → Q → R)) as n3_47a.
  MP n3_47a Ca.
  replace ((P → Q) ∧ (Q → P)) with (P ↔ Q) 
      in n3_47a by now rewrite Equiv4_01.
  replace (((Q → R) → P → R) ∧ ((P → R) → Q → R)) with 
    ((Q → R) ↔ (P → R)) in n3_47a by 
    now rewrite Equiv4_01.
  pose proof (n4_21 (P → R) (Q → R)) as n4_21a.
  apply propositional_extensionality in n4_21a.
  replace ((Q → R) ↔ (P → R)) with 
      ((P → R) ↔ (Q → R)) in n3_47a
      by now apply n4_21a.
  exact n3_47a.
Qed.

Theorem n4_85 (P Q R : Prop) :
  (P ↔ Q) → ((R → P) ↔ (R → Q)).
Proof.
  pose proof (Syll2_05 R P Q) as Syll2_05a.
  pose proof (Syll2_05 R Q P) as Syll2_05b.
  Conj_as Syll2_05a Syll2_05b Ca.
  pose proof (n3_47 (P → Q) (Q → P) ((R → P) → R → Q) 
    ((R → Q) → R → P)) as n3_47a.
  MP n3_47a Ca.
  replace ((P → Q) ∧ (Q → P)) with (P ↔ Q) in n3_47a.
  replace (((R → P) → R → Q) ∧ ((R → Q) → R → P)) with 
    ((R → P) ↔ (R → Q)) in n3_47a.
  exact n3_47a.
  all: now rewrite Equiv4_01.
Qed.

Theorem n4_86 (P Q R : Prop) :
  (P ↔ Q) → ((P ↔ R) ↔ (Q ↔ R)).
Proof.
  pose proof (n4_22  Q P R) as n4_22a.
  pose proof (Exp3_3 (Q ↔ P) (P ↔ R) (Q ↔ R)) as Exp3_3a. (*Not cited*)
  MP Exp3_3a n4_22a.
  pose proof (n4_22  P Q R) as n4_22b.
  pose proof (Exp3_3 (P ↔ Q) (Q ↔ R) (P ↔ R)) as Exp3_3b.
  MP Exp3_3b n4_22b.
  pose proof (n4_21 P Q) as n4_21a.
  apply propositional_extensionality in n4_21a.
  replace (Q ↔ P) with (P ↔ Q) in Exp3_3a
    by now apply n4_21a.
  clear n4_22a. clear n4_22b. clear n4_21a.
  Conj_as Exp3_3a Exp3_3b Ca.
  pose proof (Comp3_43 (P ↔ Q)
      ((P ↔ R) → (Q ↔ R)) ((Q ↔ R) → (P ↔ R))) as Comp3_43a. (*Not cited*)
  MP Comp3_43a Ca.
  replace (((P ↔ R) → (Q ↔ R)) ∧ ((Q ↔ R) → (P ↔ R)))
    with ((P ↔ R) ↔ (Q ↔ R)) in Comp3_43a 
    by now rewrite Equiv4_01.
  exact Comp3_43a.
Qed.

Theorem n4_87 (P Q R : Prop) :
  (((P ∧ Q) → R) ↔ (P → (Q → R)))
  ∧
  ((P → (Q → R)) ↔ (Q → (P → R)))
  ∧
  ((Q → (P → R)) ↔ ((Q ∧ P) → R)).
Proof.
  assert (S1 : ((P ∧ Q) → R) ↔ (P → (Q → R))).
  {
    pose proof (Exp3_3 P Q R) as Exp3_3.
    pose proof (Imp3_31 P Q R) as Imp3_31.
    Conj_as Exp3_3 Imp3_31 C1.
    now Equiv C1.
  }
  assert (S2 : (P → (Q → R)) ↔ (Q → (P → R))).
  {
    pose proof (Comm2_04 P Q R) as Comm2_04a.
    pose proof (Comm2_04 Q P R) as Comm2_04b.
    Conj_as Comm2_04a Comm2_04b C1.
    now Equiv C1.
  }
  assert (S3 : (Q → (P → R)) ↔ ((Q ∧ P) → R)).
  {
    pose proof (Imp3_31 Q P R) as Imp3_31.
    pose proof (Exp3_3 Q P R) as Exp3_3.
    Conj_as Imp3_31 Exp3_3 C1.
    now Equiv C1.
  }
  Conj_as S2 S3 C1.
  clear S2 S3.
  now Conj_as S1 C1 C2.
Qed.
