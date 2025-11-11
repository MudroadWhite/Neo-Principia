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
TODO: investigate a convenient `/\` construction
*)

(* Experimental: provide variated theorems to be used in this chapter
  In the future, we might want to change `Prop -> Prop` into `A -> Prop`
  for common theorems starting from ch1 *)
Module Variants.
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
End Variants.

(* 
p.165: `Phi x^` without a `!` will be a function with order unspecified, and this kind of function is
forbidden to be a quantified variable
*)
Definition n13_01 (X Y : Prop) : 
  (X = Y) = (forall Phi : Predicate 1, (Phi X) -> (Phi Y)).
Admitted.

Definition n13_02 (X Y : Prop) :
  (~(X = Y)) = ~(X = Y).
Admitted.

Definition n13_03 (X Y Z : Prop) :
  ((X = Y) /\ (Y = Z)) = ((X = Y) /\ (Y = Z)).
Admitted.

Open Scope single_app_impl.

Theorem n13_1 (X Y : Prop) : 
  (X = Y) <-> 
    (forall Phi : Predicate 1, (Phi X) -> (Phi Y)).
Proof.
  pose proof (n4_2 (X = Y)) as n4_2.
  now rewrite -> n13_01 in n4_2 at 2.
  (* n10_02 ignored: I think this is unrelated *)
Qed.

Theorem n13_101 (X Y : Prop) (Psi : Prop -> Prop) :
  (X = Y) -> (Psi X -> Psi Y).
Proof.
  assert (S1 : (exists Phi : Predicate 1, (Psi X <-> Phi X) /\ (Psi Y <-> Phi Y))).
  {
    (* I don't think this is provable! *)
    pose proof n12_1 as n12_1.
    admit.
  }
  assert (S2 : (X = Y) -> forall Phi : Predicate 1, Phi X -> Phi Y).
  {
    apply n13_1.
  }
  assert (S3 : (X = Y) -> (forall Phi : Predicate 1, 
    ((Psi X <-> Phi X) /\ (Psi Y <-> Phi Y)) -> (Psi X -> Psi Y))).
  {
    (* I think this step is also unobtainable: we only have an
    assertion that there "some" Phis satisfie the condition, but 
    eventually we have to prove that "all" Phis satisfy the condition.
    Below is an incomplete attempt for the proof.
    *)
    destruct S1 as [Phi HS1].
    destruct HS1 as [HS1_1 HS1_2].
    pose proof (n4_84 (Psi X) (Phi X) (Phi Y)) as n4_84.
    MP n4_84 HS1_1.
    pose proof (n4_85 (Psi Y) (Phi Y) (Psi X)) as n4_85.
    MP n4_84 HS1_2.
    rewrite -> n4_84 in n4_85.
    (* setoid_rewrite <- n4_85 in S2. *)
    admit.
  }
  assert (S4 : (X = Y) -> (exists Phi : Predicate 1, 
    ((Psi X <-> Phi X) /\ (Psi Y <-> Phi Y))) -> (Psi X -> Psi Y)).
  {
    now rewrite -> Variants.n10_23_pred in S3.
  }
  assert (S5 : (X = Y) -> (Psi X -> Psi Y)).
  {
    intro Hp.
    pose proof (S4 Hp) as S4_1.
    clear S2 S3 S4.
    now MP S4_1 S1.
  }
  exact S5.
Admitted.

Open Scope single_app_equiv.

Theorem n13_11 (X Y : Prop) :
  (X = Y) <-> 
    (forall Phi : Predicate 1, (Phi X) <-> (Phi Y)).
Proof.
  (* TOOLS *)
  set (IPhi := Intro_pred "Phi" 1).
  (* ******** *)
  assert (S1 : (forall Phi : Predicate 1, Phi X <-> Phi Y)
    -> (forall Phi : Predicate 1, Phi X -> Phi Y)).
  {
    (* TODO: make a matrix and generalize it; eventually 
      apply n10_22 *)
    pose proof Variants.n10_22_pred as n10_22.
    admit.
  }
  assert (S2 : (forall Phi : Predicate 1, Phi X <-> Phi Y)
    -> (X = Y)).
  { now rewrite <- n13_1 in S1. }
  
    Close Scope double_app_impl.
    Close Scope single_app_equiv.
    Close Scope single_app_impl.
 
  assert (S3 : (X = Y) -> (IPhi X -> IPhi Y)).
  { apply n13_101. }
  assert (S4 : (X = Y) -> ((~IPhi X) -> (~IPhi Y))).
  {
    (* n1_7 ignored *)
    admit.
  }
  assert (S5 : (X = Y) -> (IPhi Y -> IPhi X)).
  {
    pose proof (Transp2_17 (IPhi Y) (IPhi X)) as Transp2_17.
    now Syll S4 Transp2_17 S5.
  }
  assert (S6 : (X = Y) -> (IPhi X <-> IPhi Y)).
  {
    pose proof (Comp3_43 (X = Y) (IPhi X → IPhi Y) (IPhi Y → IPhi X))
      as Comp3_43.
    assert (C1 : (X = Y → IPhi X → IPhi Y) ∧ (X = Y → IPhi Y → IPhi X)).
    { 
      clear S1 S2 S4.
      now Conj S3 S5 C1.
    }
    MP Comp3_43 C1.
    now rewrite <-Equiv4_01 in Comp3_43.
  }
  assert (S7 : (X = Y) -> (forall Phi : Predicate 1, Phi X <-> Phi Y)).
  {
    pose proof (Variants.n10_11_pred IPhi (fun P =>
      X = Y → P X ↔ P Y)) as n10_11.
    MP n10_11 S6.
    pose proof (Variants.n10_21_pred (fun P =>
      P X ↔ P Y) (X = Y)) as n10_21.
    now rewrite -> n10_21 in n10_11.
  }
  assert (S8 : (X = Y) <-> (forall Phi : Predicate 1, (Phi X) <-> (Phi Y))).
  {
    clear S1 S3 S4 S5 S6. move S2 after S7.
    assert (C1 : (X = Y → ∀ Phi : Predicate 1, Phi X ↔ Phi Y)
      /\ ((∀ Phi : Predicate 1, Phi X ↔ Phi Y) → X = Y)).
    { now Conj S7 S2 C1. }
    now Equiv C1.
  }
  exact S8.
Admitted.

Theorem n13_12 (X Y : Prop) (Psi : Prop -> Prop) :
  (X = Y) -> (Psi X <-> Psi Y).
Proof.
  assert (S1 : (X = Y) -> ((Psi X -> Psi Y) /\ ((~Psi X) -> (~Psi Y)))).
  {
    pose proof n13_101 as n13_101.
    pose proof Comp3_43 as Comp3_43.
    (* Same as n13_11.S4, and this is currently under investigation *)
    admit.
  }
  assert (S2 : (X = Y) -> (Psi X <-> Psi Y)).
  {
    intro Hp.
    pose proof (S1 Hp) as S1_1.
    destruct S1_1 as [S1_1l S1_1r].
    pose proof (Transp2_17 (Psi Y) (Psi X)) as Transp2_17.
    MP Transp2_17 S1_1r.
    assert (C1 : (Psi X → Psi Y) /\ (Psi Y → Psi X)).
    {
      clear S1 Hp.
      now Conj S1_1l Transp2_17 C1.
    }
    now Equiv C1.
  }
  exact S2.
Admitted.

Theorem n13_13 (X Y : Prop) (Psi : Prop -> Prop) :
  ((Psi X) /\ (X = Y)) -> Psi Y.
Proof.
  pose proof (n13_101 X Y Psi) as n13_101.
  pose proof (Comm2_04 (X = Y) (Psi X) (Psi Y)) as Comm2_04.
  MP Comm2_04 n13_101.
  pose proof (Imp3_31 (Psi X) (X = Y) (Psi Y)) as Imp3_31.
  now MP Imp3_31 Comm2_04.
Qed.

Theorem n13_14 (X Y : Prop) (Psi : Prop -> Prop) :
  (Psi X) /\ (~ Psi Y) -> (~ (X = Y)).
Proof.
  pose proof (n13_13 X Y Psi) as n13_13.
  pose proof (n4_14 (Psi X) (X = Y) (Psi Y)) as n4_14.
  now rewrite -> n4_14 in n13_13.
Qed.

Theorem n13_15 (X : Prop) : X = X.
Proof.
  pose proof (Id2_08 X) as Id2_08.
  pose proof (Variants.n10_11_pred
    (fun x => x)
    (fun P => P X -> P X)
  ) as n10_11.
  MP n10_11 Id2_08.
  pose proof (n13_1 X X) as n13_1.
  now rewrite <- n13_1 in n10_11.
Qed.

Theorem n13_16 (X Y : Prop) : (X = Y) <-> (Y = X).
Proof.
  pose proof (n13_11 X Y) as n13_11a.
  rewrite -> Variants.n10_32_pred in n13_11a.
  now rewrite <- n13_11 in n13_11a.
Qed.

(* A theorem that is shown how the related propositions are 
being used explicitly in original text *)
Theorem n13_17 (X Y Z : Prop) :
  ((X = Y) /\ (Y = Z)) -> (X = Z).
Proof.
  assert (S1 : ((X = Y) /\ (Y = Z)) 
    -> ((forall Phi : Predicate 1, Phi X -> Phi Y) 
      /\ (forall Phi : Predicate 1, Phi Y -> Phi Z))).
  {
    pose proof n13_1 as n13_1.
    (* We currently didn't allow `/\` yet *)
    admit.
  }
  assert (S2 : ((X = Y) /\ (Y = Z)) 
    -> (forall Phi : Predicate 1, Phi X -> Phi Z)).
  {
    intros Hp.
    pose proof (S1 Hp) as S1_1.
    pose proof (n10_3_pred
      (fun P => P X) (fun P => P Y) (fun P => P Z)) as n10_3_pred.
    now MP n10_3_pred S1_1.
  }
  assert (S3 : ((X = Y) /\ (Y = Z)) -> (X = Z)).
  { now rewrite <- n13_01 in S2. }
  exact S3.
Admitted.

Theorem n13_18 (X Y Z : Prop) :
  ((X = Y) /\ (~(X = Z))) -> ~(Y = Z).
Proof.
Admitted.

Theorem n13_181 (X Y Z : Prop) :
  ((X = Y) /\ (~(Y = Z))) -> ~(X = Z).
Proof.
Admitted.

Theorem n13_182 (X Y Z : Prop) :
  (X = Y) -> ((Z = X) <-> (Z = Y)).
Proof.
Admitted.

Theorem n13_183 (X Y : Prop) :
  (X = Y) <-> ((X = z) <[- z -]> (z = Y)).
Proof.
Admitted.

Theorem n13_19 (X : Prop) : exists y, y = X.
Proof.
Admitted.

Theorem n13_191 (X : Prop) (Phi : Prop -> Prop) :
  (y = X) -[ y ]> (Phi y = Phi X).
Proof.
Admitted.

Theorem n13_192 (B : Prop) (Psi : Prop -> Prop) :
  exists c, ((x = B) <[- x -]> (x = c)) /\ (Psi c <-> Psi B).
Proof.
Admitted.

Theorem n13_193 (X Y : Prop) (Phi : Prop -> Prop) :
  (Phi X /\ (X = Y)) <-> (Phi Y /\ (X = Y)).
Proof.
Admitted.

Theorem n13_194 (X Y : Prop) (Phi : Prop -> Prop) :
  (Phi X /\ (X = Y)) <-> (Phi X /\ Phi Y /\ (X = Y)).
Proof.
Admitted.

Theorem n13_195 (X : Prop) (Phi : Prop -> Prop) : 
  (exists y, (y = X) /\ Phi y) <-> Phi X.
Proof.
Admitted.

Theorem n13_196 (X : Prop) (Phi : Prop -> Prop) : 
  (~Phi X) <-> (Phi y <[- y -]> (~(y = X))).
Proof.
Admitted.

Close Scope single_app_impl.
Open Scope double_app_impl.

Theorem n13_21 (X Y : Prop) (Phi : Prop -> Prop -> Prop) : 
  (((z = X) /\ (w = Y)) -[ z w ]> ((Phi z w) <-> (Phi X Y))).
Proof.
Admitted.

Theorem n13_22 (X Y : Prop) (Phi : Prop -> Prop -> Prop) : 
  exists z w, (z = X) /\ (w = Y) /\ (Phi z w <-> Phi X Y).
Proof.
Admitted.

Theorem n13_3 (A X : Prop) (Phi : Prop -> Prop) : 
  (Phi A \/ (~Phi A)) -> ((Phi X \/ (~Phi X)) <-> ((X = A) \/ (~(X = A)))).
Proof.
Admitted.

Close Scope double_app_impl.
Close Scope single_app_equiv.

(* 
Close Scope double_app_impl.
Close Scope single_app_equiv.
Close Scope single_app_impl.
*)
