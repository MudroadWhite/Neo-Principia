Require Import PM.pm.lib.
Require Import PM.pm.ch1.
Require Import PM.pm.ch2.

Theorem Prod3_01 (P Q : Prop) :
  (P ∧ Q) = (¬(¬P ∨ ¬Q)).
Proof.
  apply propositional_extensionality.
  split.
  {
    pose proof (or_not_and P Q) as or_not_and.
    pose proof (Transp2_03 (¬P ∨ ¬Q) (P ∧ Q)) as Transp2_03.
    MP Transp2_03 or_not_and.
    exact Transp2_03.
  }
  {
    pose proof (not_and_or P Q) as not_and_or.
    pose proof (Transp2_15 (P ∧ Q) (¬P ∨ ¬Q)) as Transp2_15.
    MP Transp2_15 not_and_or.
    exact Transp2_15.
  }
Qed.
(*This is a notational definition in Principia;
  it is used to switch between "∧" and "¬∨¬".*)

(*Axiom Abb3_02 : ∀ P Q R : Prop, 
  (P → Q → R) = ((P → Q) ∧ (Q → R)).*)
  (*Since Coq forbids such strings as ill-formed, or
  else automatically associates to the right,
  we leave this notational axiom commented out.*)

Theorem Conj3_03 (P Q : Prop) : P → Q → (P∧Q).
Proof.
  pose proof (n2_11 (¬P∨¬Q)) as n2_11a.
  pose proof (n2_32 (¬P) (¬Q) (¬(¬P ∨ ¬Q))) as n2_32a.
  MP n2_32a n2_11a.
  replace (¬(¬P∨¬Q)) with (P∧Q) in n2_32a
    by now rewrite Prod3_01.
  replace (¬Q ∨ (P∧Q)) with (Q→(P∧Q)) in n2_32a.
  replace (¬P ∨ (Q → (P∧Q))) with (P→Q→(P∧Q)) in n2_32a.
  exact n2_32a.
  all: now rewrite Impl1_01.
Qed.
(*3.03 is permits the inference from the theoremhood 
    of P and that of Q to the theoremhood of P and Q.So:*)

(* NOTE:
Although this Ltac simplifies the proof a lot, there is only one safe way
to perform the `Conj`. We have to 
1. `assert` the final proposition being produced
2. `clear` all irrevalent hypotheses
3. `move` the only two hypotheses into right order, optionally
4. `Conj` them and `exact` the result
*)
Ltac Conj H1 H2 C :=
  let C := fresh C in lazymatch goal with 
    | [ H1 : ?P, H2 : ?Q |- _ ] =>  
      (pose proof (Conj3_03 P Q) as C; simpl in C;
      MP Conj3_03 P; MP Conj3_03 Q)
end.

Theorem n3_1 (P Q : Prop) :
  (P ∧ Q) → ¬(¬P ∨ ¬Q).
Proof.
  pose proof (Id2_08 (P∧Q)) as Id2_08a.
  replace ((P∧Q)→(P∧Q)) with ((P∧Q)→¬(¬P∨¬Q)) 
    in Id2_08a by now rewrite Prod3_01.
  exact Id2_08a.
Qed.

Theorem n3_11 (P Q : Prop) :
  ¬(¬P ∨ ¬Q) → (P ∧ Q).
Proof.
  pose proof (Id2_08 (P∧Q)) as Id2_08a.
  replace ((P∧Q)→(P∧Q)) with (¬(¬P∨¬Q)→(P∧Q)) 
    in Id2_08a by now rewrite Prod3_01.
  exact Id2_08a.
Qed.

Theorem n3_12 (P Q : Prop) :
  (¬P ∨ ¬Q) ∨ (P ∧ Q).
Proof.
  pose proof (n2_11 (¬P∨¬Q)) as n2_11a.
  replace (¬(¬P∨¬Q)) with (P∧Q) in n2_11a
    by now rewrite Prod3_01.
  exact n2_11a.
Qed.

Theorem n3_13 (P Q : Prop) :
  ¬(P ∧ Q) → (¬P ∨ ¬Q).
Proof.
  pose proof (n3_11 P Q) as n3_11a.
  pose proof (Transp2_15 (¬P∨¬Q) (P∧Q)) as Transp2_15a.
  MP Transp2_15a n3_11a.
  exact Transp2_15a.
Qed.

Theorem n3_14 (P Q : Prop) :
  (¬P ∨ ¬Q) → ¬(P ∧ Q).
Proof.
  pose proof (n3_1 P Q) as n3_1a.
  pose proof (Transp2_16 (P∧Q) (¬(¬P∨¬Q))) as Transp2_16a.
  MP Transp2_16a n3_1a.
  pose proof (n2_12 (¬P∨¬Q)) as n2_12a.
  Syll n2_12a Transp2_16a S.
  exact S.
Qed.

Theorem n3_2 (P Q : Prop) :
  P → Q → (P ∧ Q).
Proof.
  pose proof (n3_12 P Q) as n3_12a.
  pose proof (n2_32 (¬P) (¬Q) (P∧Q)) as n2_32a.
  MP n3_32a n3_12a.
  replace (¬Q ∨ P ∧ Q) with (Q→P∧Q) in n2_32a.
  replace (¬P ∨ (Q → P ∧ Q)) with (P→Q→P∧Q) in n2_32a.
  exact n2_32a.
  all: now rewrite Impl1_01.
Qed.

Theorem n3_21 (P Q : Prop) :
  Q → P → (P ∧ Q).
Proof.
  pose proof (n3_2 P Q) as n3_2a.
  pose proof (Comm2_04 P Q (P∧Q)) as Comm2_04a.
  MP Comm2_04a n3_2a.
  exact Comm2_04a.
Qed.

Theorem n3_22 (P Q : Prop) :
  (P ∧ Q) → (Q ∧ P).
Proof.
  pose proof (n3_13 Q P) as n3_13a.
  pose proof (Perm1_4 (¬Q) (¬P)) as Perm1_4a.
  Syll n3_13a Perm1_4a Ha.
  pose proof (n3_14  P Q) as n3_14a.
  Syll Ha n3_14a Hb.
  pose proof (Transp2_17 (P∧Q) (Q ∧ P)) as Transp2_17a.
  MP Transp2_17a Hb.
  exact Transp2_17a.
Qed.

Theorem n3_24 (P : Prop) :
  ¬(P ∧ ¬P).
Proof.
  pose proof (n2_11 (¬P)) as n2_11a.
  pose proof (n3_14 P (¬P)) as n3_14a.
  MP n3_14a n2_11a.
  exact n3_14a.
Qed.

Theorem Simp3_26 (P Q : Prop) :
  (P ∧ Q) → P.
Proof.
  pose proof (Simp2_02 Q P) as Simp2_02a.
  replace (P→(Q→P)) with (¬P∨(Q→P)) in Simp2_02a.
  replace (Q→P) with (¬Q∨P) in Simp2_02a.
  pose proof (n2_31 (¬P) (¬Q) P) as n2_31a.
  MP n2_31a Simp2_02a.
  pose proof (n2_53 (¬P∨¬Q) P) as n2_53a.
  MP n2_53a Simp2_02a.
  replace (¬(¬P∨¬Q)) with (P∧Q) in n2_53a
    by now rewrite Prod3_01.
  exact n2_53a.
  all: now rewrite <- Impl1_01.
Qed.

Theorem Simp3_27 (P Q : Prop) :
  (P ∧ Q) → Q.
Proof.
  pose proof (n3_22 P Q) as n3_22a.
  pose proof (Simp3_26 Q P) as Simp3_26a.
  Syll n3_22a Simp3_26a S.
  exact S.
Qed.

Theorem Exp3_3 (P Q R : Prop) :
  ((P ∧ Q) → R) → (P → (Q → R)).
Proof.
  pose proof (Id2_08 ((P∧Q)→R)) as Id2_08a. (*This theorem isn't needed.*)
  replace (((P ∧ Q) → R) → ((P ∧ Q) → R)) with 
    (((P ∧ Q) → R) → (¬(¬P ∨ ¬Q) → R)) in Id2_08a
    by now rewrite Prod3_01.
  pose proof (Transp2_15 (¬P∨¬Q) R) as Transp2_15a.
  Syll Id2_08a Transp2_15a Sa.
  pose proof (Id2_08 (¬R → (¬P ∨ ¬Q))) as Id2_08b. (*This theorem isn't needed.*)
  Syll Sa Id2_08b Sb.
  replace (¬P ∨ ¬Q) with (P → ¬Q) in Sb
    by now rewrite Impl1_01.
  pose proof (Comm2_04 (¬R) P (¬Q)) as Comm2_04a.
  Syll Sb Comm2_04a Sc.
  pose proof (Transp2_17 Q R) as Transp2_17a.
  pose proof (Syll2_05 P (¬R → ¬Q) (Q → R)) as Syll2_05a.
  MP Syll2_05a Transp2_17a.
  Syll Sa Syll2_05a Sd.
  exact Sd.
Qed.

Theorem Imp3_31 (P Q R : Prop) :
  (P → (Q → R)) → (P ∧ Q) → R.
Proof.
  pose proof (Id2_08 (P → (Q → R))) as Id2_08a.
  replace ((P → (Q → R))→(P → (Q → R))) with
    ((P → (Q → R))→(¬P ∨ (Q → R))) in Id2_08a
    by now rewrite <- Impl1_01.
  replace (¬P ∨ (Q → R)) with 
    (¬P ∨ (¬Q ∨ R)) in Id2_08a
    by now rewrite Impl1_01.
  pose proof (n2_31 (¬P) (¬Q) R) as n2_31a.
  Syll Id2_08a n2_31a Sa.
  pose proof (n2_53 (¬P∨¬Q) R) as n2_53a.
  replace (¬(¬P∨¬Q)) with (P∧Q) in n2_53a
    by now rewrite Prod3_01.
  Syll Sa n2_53a Sb.
  exact Sb.
Qed.

Theorem Syll3_33 (P Q R : Prop) :
  ((P → Q) ∧ (Q → R)) → (P → R).
Proof.
  pose proof (Syll2_06 P Q R) as Syll2_06a.
  pose proof (Imp3_31 (P→Q) (Q→R) (P→R)) as Imp3_31a.
  MP Imp3_31a Syll2_06a.
  exact Imp3_31a.
Qed.

Theorem Syll3_34 (P Q R : Prop) :
  ((Q → R) ∧ (P → Q)) → (P → R).
Proof.
  pose proof (Syll2_05 P Q R) as Syll2_05a.
  pose proof (Imp3_31 (Q→R) (P→Q) (P→R)) as Imp3_31a.
  MP Imp3_31a Syll2_05a.
  exact Imp3_31a.
Qed.

Theorem Ass3_35 (P Q : Prop) :
  (P ∧ (P → Q)) → Q.
Proof.
  pose proof (n2_27 P Q) as n2_27a.
  pose proof (Imp3_31 P (P→Q) Q) as Imp3_31a.
  MP Imp3_31a n2_27a.
  exact Imp3_31a.
Qed.

Theorem Transp3_37 (P Q R : Prop) :
  (P ∧ Q → R) → (P ∧ ¬R → ¬Q).
Proof.
  pose proof (Transp2_16 Q R) as Transp2_16a.
  pose proof (Syll2_05 P (Q→R) (¬R→¬Q)) as Syll2_05a.
  MP Syll2_05a Transp2_16a.
  pose proof (Exp3_3 P Q R) as Exp3_3a.
  Syll Exp3_3a Syll2_05a Sa.
  pose proof (Imp3_31 P (¬R) (¬Q)) as Imp3_31a.
  Syll Sa Imp3_31a Sb.
  exact Sb.
Qed.

Theorem n3_4 (P Q : Prop) :
  (P ∧ Q) → P → Q.
Proof.
  pose proof (n2_51 P Q) as n2_51a.
  pose proof (Transp2_15 (P→Q) (P→¬Q)) as Transp2_15a.
  MP Transp2_15a n2_51a.
  replace (P→¬Q) with (¬P∨¬Q) in Transp2_15a
    by now rewrite Impl1_01.
  replace (¬(¬P∨¬Q)) with (P∧Q) in Transp2_15a
    by now rewrite Prod3_01.
  exact Transp2_15a.
Qed.

Theorem n3_41 (P Q R : Prop) :
  (P → R) → (P ∧ Q → R).
Proof.
  pose proof (Simp3_26 P Q) as Simp3_26a.
  pose proof (Syll2_06 (P∧Q) P R) as Syll2_06a.
  MP Simp3_26a Syll2_06a.
  exact Syll2_06a.
Qed.

Theorem n3_42 (P Q R : Prop) :
  (Q → R) → (P ∧ Q → R).
Proof.
  pose proof (Simp3_27 P Q) as Simp3_27a.
  pose proof (Syll2_06 (P∧Q) Q R) as Syll2_06a.
  MP Syll2_06a Simp3_27a.
  exact Syll2_06a.
Qed.

Theorem Comp3_43 (P Q R : Prop) :
  (P → Q) ∧ (P → R) → (P → Q ∧ R).
Proof.
  pose proof (n3_2 Q R) as n3_2a.
  pose proof (Syll2_05 P Q (R→Q∧R)) as Syll2_05a.
  MP Syll2_05a n3_2a.
  pose proof (n2_77 P R (Q∧R)) as n2_77a.
  Syll Syll2_05a n2_77a Sa.
  pose proof (Imp3_31 (P→Q) (P→R) (P→Q∧R)) as Imp3_31a.
  MP Sa Imp3_31a.
  exact Imp3_31a.
Qed.

Theorem n3_44 (P Q R : Prop) :
  (Q → P) ∧ (R → P) → (Q ∨ R → P).
Proof.
  pose proof (Syll3_33 (¬Q) R P) as Syll3_33a.
  pose proof (n2_6 Q P) as n2_6a.
  Syll Syll3_33a n2_6a Sa.
  pose proof (Exp3_3 (¬Q→R) (R→P) ((Q→P)→P)) as Exp3_3a.
  MP Exp3_3a Sa.
  pose proof (Comm2_04 (R→P) (Q→P) P) as Comm2_04a.
  Syll Exp3_3a Comm2_04a Sb.
  pose proof (Imp3_31 (Q→P) (R→P) P) as Imp3_31a.
  Syll Sb Imp3_31a Sc.
  pose proof (Comm2_04 (¬Q→R) ((Q→P)∧(R→P)) P) as Comm2_04b.
  MP Comm2_04b Sc.
  pose proof (n2_53 Q R) as n2_53a.
  pose proof (Syll2_06 (Q∨R) (¬Q→R) P) as Syll2_06a.
  MP Syll2_06a n2_53a.
  Syll Comm2_04b Syll2_06a Sd.
  exact Sd.
Qed.

Theorem Fact3_45 (P Q R : Prop) :
  (P → Q) → (P ∧ R) → (Q ∧ R).
Proof.
  pose proof (Syll2_06 P Q (¬R)) as Syll2_06a.
  pose proof (Transp2_16 (Q→¬R) (P→¬R)) as Transp2_16a.
  Syll Syll2_06a Transp2_16a Sa.
  pose proof (Id2_08 (¬(P→R)→¬(Q→¬R))) as Id2_08a.
  Syll Sa Id2_08a Sb.
  replace (P→¬R) with (¬P∨¬R) in Sb
    by now rewrite Impl1_01.
  replace (Q→¬R) with (¬Q∨¬R) in Sb
    by now rewrite Impl1_01.
  replace (¬(¬P∨¬R)) with (P∧R) in Sb
    by now rewrite Prod3_01.
  replace (¬(¬Q∨¬R)) with (Q∧R) in Sb
    by now rewrite Prod3_01.
  exact Sb.
Qed.

Theorem n3_47 (P Q R S : Prop) :
  ((P → R) ∧ (Q → S)) → (P ∧ Q) → R ∧ S.
Proof.
  assert (Sa : (P → R) ∧ (Q → S) → P ∧ Q → R ∧ Q).
  {
    pose proof (Simp3_26 (P→R) (Q→S)) as Simp3_26a.
    pose proof (Fact3_45 P R Q) as Fact3_45a.
    Syll Simp3_26a Fact3_45a Sa_1.
    exact Sa_1.
  }
  assert (Sb : (P → R) ∧ (Q → S) → P ∧ Q → Q ∧ R).
  {
    pose proof (n3_22 R Q) as n3_22a.
    pose proof (Syll2_05 (P∧Q) (R∧Q) (Q∧R)) as Syll2_05a.
    MP Syll2_05a n3_22a.
    Syll Sa Syll2_05a Sb_1.
    exact Sb_1.
  }
  assert (Sc : (P → R) ∧ (Q → S) → Q ∧ R → S ∧ R).
  {
    pose proof (Simp3_27 (P→R) (Q→S)) as Simp3_27a.
    pose proof (Fact3_45 Q S R) as Fact3_45b.
    Syll Simp3_27a Fact3_45b Sc_1.
    exact Sc_1.
  }
  assert (Sd : (P → R) ∧ (Q → S) → Q ∧ R → R ∧ S).
  {
    pose proof (n3_22 S R) as n3_22b.
    pose proof (Syll2_05 (Q∧R) (S∧R) (R∧S)) as Syll2_05b.
    MP Syll2_05b n3_22b.
    Syll Sc Syll2_05b Sd_1.
    exact Sd_1.
  }
  clear Sa Sc.
  Conj Sb Sd C.
  pose proof (n2_83 ((P→R)∧(Q→S)) (P∧Q) (Q∧R) (R∧S)) as n2_83a. (*This with MP works, but it omits Conj3_03.*)
  pose proof (Imp3_31 (((P→R)∧(Q→S))→((P∧Q)→(Q∧R)))
    (((P→R)∧(Q→S))→((Q∧R)→(R∧S))) 
    (((P→R)∧(Q→S))→((P∧Q)→(R∧S)))) as Imp3_31a.
  MP Imp3_31a n2_83a.
  MP Imp3_31a C.
  exact Imp3_31a.
Qed.

Theorem n3_48 (P Q R S : Prop) :
  ((P → R) ∧ (Q → S)) → (P ∨ Q) → R ∨ S.
Proof.
  pose proof (Simp3_26 (P→R) (Q→S)) as Simp3_26a.
  pose proof (Sum1_6 Q P R) as Sum1_6a.
  Syll Simp3_26a Sum1_6a Sa.
  pose proof (Perm1_4 P Q) as Perm1_4a.
  pose proof (Syll2_06 (P∨Q) (Q∨P) (Q∨R)) as Syll2_06a.
  MP Syll2_06a Perm1_4a.
  Syll Sa Syll2_06a Sb.
  pose proof (Simp3_27 (P→R) (Q→S)) as Simp3_27a.
  pose proof (Sum1_6 R Q S) as Sum1_6b.
  Syll Simp3_27a Sum1_6b Sc.
  pose proof (Perm1_4 Q R) as Perm1_4b.
  pose proof (Syll2_06 (Q∨R) (R∨Q) (R∨S)) as Syll2_06b.
  MP Syll2_06b Perm1_4b.
  Syll Sc Syll2_06a Sd.
  pose proof (n2_83 ((P→R)∧(Q→S)) (P∨Q) (Q∨R) (R∨S)) as n2_83a.
  MP n2_83a Sb.
  MP n2_83a Sd.
  exact n2_83a.
Qed.
