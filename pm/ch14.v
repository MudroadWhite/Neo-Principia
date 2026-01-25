Require Import PM.pm.lib.
Require Import PM.pm.ch1.
Require Import PM.pm.ch2.
Require Import PM.pm.ch3.
Require Import PM.pm.ch4.
Require Import PM.pm.ch5.
Require Import PM.pm.ch10.
Require Import PM.pm.ch11.
Require Import PM.pm.ch12.
Require Import PM.pm.ch13.

Require Import Logic.FunctionalExtensionality.

(* TODO:
- design a notation for all the iota functions
- fix all the `replace`s *)

(* 
The decription, or I would personally call it the iota operator, designs a special kind of 
parameter for functions. They will be passed into propositional functions normally, but unlike 
normal parameters that only calculates everything within themselves, they will rewrite on the 
whole propositional function, and on other terms that are not within them.

An extra "scope" notation is used for the iota operator, to determine the sub expression that
should be treated as the proposisional function.

Our way to simulate this idea is firstly define a series of functions prefixed with `iota`. Functions 
provide a similar functionality to scopes. Then we allow people to write `Iota "name" x` if we 
need a iota variable, but it's just for readability. **There are nothing to rely on to check 
if they have been used correctly**, nor does it actually modify the rest of the function it 
is contained in. 

With this notation, all propositional functions with iota variables have to be written explicitly
starting with `(fun x => ...)`, in contrast to just building an arbitary proposition with iota 
variables immediately. The resulted notation is quite different from how it looks like originally, 
but it can correctly express what should a iota do and limit its scope as in the text.

The definitions are being put into the `lib.v`. 
*)

(* TODO: make the definitions into a notation in the future 
Declare Scope single_description. *)

Open Scope single_app_equiv.

Definition n14_01 (s : string) (Phi Psi : Prop → Prop) : 
  (iota_f s Phi Psi) = exists b, (Phi x <[- x -]> (x = b)) ∧ Psi b. 
Admitted.

Definition n14_02 (Phi : Prop → Prop) :
  (iota_E Phi) = exists b, (Phi x <[- x -]> (x = b)). 
Admitted.

Definition n14_03 (s1 s2 : string) (Phi Psi : Prop → Prop) (f : Prop → Prop → Prop) :
  (iota_f2 s1 s2 Phi Psi f) = 
    iota_f s1 Phi (fun b => iota_f s2 Psi 
      (fun c => f (Iota s1 b) (Iota s2 c))).
Admitted.

Definition n14_04 (s1 s2 : string) (Phi Psi : Prop → Prop) (f : Prop → Prop → Prop) : 
  (iota_f2_1 s2 s1 Psi Phi f) = iota_f2 s2 s1 Psi Phi (fun x y => f y x).
Admitted.

Theorem n14_1 (s : string) (Phi Psi : Prop → Prop) : (iota_f s Phi Psi) ↔ 
  exists b, (Phi x <[- x -]> (x = b)) ∧ Psi b.
Proof.
  pose proof (n4_2 (iota_f s Phi Psi)) as n4_2.
  now rewrite -> n14_01 in n4_2 at 2.
Qed.

(* The equivalent with n14_1, with scope notation in its original 
  representation omitted. With our definition, we might just make 
  another definition copying `iota_f` to indicate it is getting 
  scope notation in the text... *)
Theorem n14_101 (s : string) (Phi Psi : Prop → Prop) : (iota_f s Phi Psi) ↔ 
  exists b, (Phi x <[- x -]> (x = b)) ∧ Psi b.
Proof. exact (n14_1 s Phi Psi). Qed.

Theorem n14_11  (Phi : Prop → Prop) : (iota_E Phi) 
  ↔ (exists b, Phi x <[- x -]> (x = b)).
Proof.
  pose proof (n4_2 (iota_E Phi)) as n4_2.
  now rewrite -> n14_02 in n4_2 at 2.
Qed.

Theorem n14_111 (s1 s2 : string) (Phi Psi : Prop → Prop) 
  (f : Prop → Prop → Prop) :
  (iota_f2_1 s2 s1 Psi Phi f) ↔ (exists b c, 
    (Phi x <[- x -]> (x = b)) ∧ (Psi x <[- x -]> (x = c)) ∧ (f b c)).
Proof.
  assert (S1 : iota_f2_1 s2 s1 Psi Phi f ↔ 
    iota_f s2 Psi (fun c => iota_f s1 Phi 
      (fun b => f (Iota s1 b) (Iota s2 c)))).
  {
    pose proof (n4_2 (iota_f2_1 s2 s1 Psi Phi f)) as n4_2.
    rewrite -> n14_04 in n4_2 at 2.
    now rewrite -> (n14_03 s2 s1) in n4_2.
  }
  assert (S2 : iota_f2_1 s2 s1 Psi Phi f ↔ 
    (iota_f s2 Psi (fun c =>
      exists b, (Phi x <[- x -]> (x = b)) ∧ f b c))).
  {
    replace (λ c, iota_f s1 Phi (λ b, f (Iota s1 b) (Iota s2 c)))
    with (λ c, iota_f s1 Phi (λ b, f b c))
    in S1 by reflexivity.
    (* Simplification: this place needs functional extentionality for our designed 
    notation of iota. Seems like the only way to survive *)
    assert (S1_1 : (λ c, iota_f s1 Phi (λ b, f b c))
      = (λ c, (exists b, (Phi x <[- x -]> (x = b)) ∧ f b c))).
    {
      extensionality c. (* function extentionality *)
      pose proof (n14_1 s1 Phi (fun b => f b c)) as n14_1.
      now apply propositional_extensionality.
    }
    now rewrite -> S1_1 in S1.
  }
  assert (S3 : iota_f2_1 s2 s1 Psi Phi f ↔ 
    (exists c, (Psi x <[- x -]> (x = c)) 
    ∧ exists b, (Phi x <[- x -]> (x = b)) ∧ f b c)).
  { now rewrite -> n14_1 in S2. }
  assert (S4 : iota_f2_1 s2 s1 Psi Phi f ↔ 
    (exists b c, (Phi x <[- x -]> (x = b)) ∧ (Psi x <[- x -]> (x = c))
      ∧ f b c)).
  {
    pose proof (n11_55
      (fun c => (Psi x <[- x -]> (x = c)))
      (fun c b => ( Phi x<[- x -]> (x = b)) ∧ f b c)
    ) as n11_55.
    rewrite <- n11_55 in S3.
    (* We can see that there are some (non?)trivial steps that still need to be
    finished... *)
    pose proof (n11_42
      (fun x y => ( Psi x0<[-x0-]>x0 = x ))
      (fun x y => ( Phi x0<[-x0-]>x0 = y ) ∧ f y x)
    ) as n11_42. simpl in n11_42.
    (* rewrite -> n11_42 in S3. *)
    pose proof n11_58 as n11_58.
    admit.
  }
  exact S4.
Admitted.

Theorem n14_112 (s1 s2 : string) (Phi Psi : Prop → Prop) 
  (f : Prop → Prop → Prop) : 
  (iota_f2 s1 s2 Phi Psi f) ↔ exists b c, 
    (Phi x <[- x -]> x = b) ∧ (Psi x <[- x -]> x = c) ∧ f b c.
Proof.
  assert (S1 : (iota_f2 s1 s2 Phi Psi f) ↔ (iota_f s1 Phi 
    (fun b => iota_f s2 Psi (fun c => f (Iota s1 b) (Iota s2 c))))).
  {
    pose proof (n4_2 (iota_f2 s1 s2 Phi Psi f)) as n4_2.
    now rewrite -> n14_03 in n4_2 at 2.
  }
  assert (S2 : (iota_f2 s1 s2 Phi Psi f) ↔ (iota_f s1 Phi (fun b => 
    exists c, (Psi x <[- x -]> (x = c)) ∧ f b c))).
  {
    replace ((λ b, iota_f s2 Psi
      (λ c, f (Iota s1 b) (Iota s2 c))))
    with (λ b, iota_f s2 Psi (λ c, f b c))
    in S1 by reflexivity.
    assert (S1_1 : (λ b, iota_f s2 Psi (λ c : Prop, f b c))
      = (λ b, exists c, (Psi x <[- x -]> (x = c)) ∧ f b c)).
    {
      extensionality b.
      pose proof (n14_1 s2 Psi (fun c => f b c)) as n14_1. 
      now apply propositional_extensionality.
    }
    now rewrite -> S1_1 in S1.
  }
  assert (S3 : (iota_f2 s1 s2 Phi Psi f) ↔ exists b, 
    (Phi x <[- x -]> x = b) ∧ (exists c, (Psi x <[- x -]> x = c) ∧ f b c)).
  { now rewrite -> n14_1 in S2. } 
  assert (S4 : (iota_f2 s1 s2 Phi Psi f) ↔ exists b c, 
    (Phi x <[- x -]> x = b) ∧ (Psi x <[- x -]> x = c) ∧ f b c).
  { admit. }
Admitted.

Theorem n14_113 (s1 s2 : string) (Phi Psi : Prop → Prop) 
  (f : Prop → Prop → Prop) : 
  iota_f2 s2 s1 Psi Phi (fun y x => f x y) ↔ iota_f2 s1 s2 Phi Psi f. 
Proof.
  pose proof (n14_111 s1 s2 Phi Psi f) as n14_111.
  rewrite <- (n14_112 s1 s2) in n14_111.
  now rewrite -> n14_04 in n14_111.
Qed.

Open Scope double_app_equiv.
Open Scope double_app_impl.

Theorem n14_12 (Phi : Prop → Prop) : 
  iota_E Phi → ((Phi x ∧ Phi y) -[ x y ]> (x = y)).
Proof.
  (* TOOLS *)
  set (B := Individual "b").
  set (X := Individual "x").
  (* ******** *)
  assert (S1 : iota_E Phi -> exists b, Phi x <[- x -]> x = b).
  {
    pose proof (n14_11 Phi) as n14_11.
    (* simplification: we use `Simp` if necessary *)
    now destruct n14_11.
  }
  assert (S2 : (Phi x <[- x -]> x = B) 
    -> ((Phi x ∧ Phi y) <[- x y -]> (x = B ∧ y = B))).
  {
    (* NOTE: this place shows that we cannot assign a instance 
    automatically: in this complicated situation we are having 
    candidates being not unique. Might be interesting to check 
    in the future... *)
    pose proof (n4_38
      (Phi X) (Phi X) (X = B) (X = B)) as n4_38.
    rewrite <- n4_24 in n4_38.
    pose proof (n10_1 (fun x => (Phi x ↔ x = B)) X) as n10_1.
    Syll n10_1 n4_38 Sa.
    pose proof (n11_11 X X (fun z w => 
      (∀ x : Prop, Phi x ↔ x = B) →
      (Phi z ∧ Phi w ↔ z = B ∧ w = B))) as n11_11.
    MP n11_11 Sa.
    now rewrite <- n11_3 in n11_11.
  }
  assert (S3 : (Phi x <[- x -]> x = B) 
  -> ((Phi x ∧ Phi y) -[ x y ]> (x = y))).
  {
    intros Hp.
    pose proof (S2 Hp) as S2.
    (* simplifications... don't want to figure out how to do 
    it correctly atm *)
    intros x y.
    pose proof (S2 x y) as S2.
    destruct S2 as [S2l _].
    pose proof (n13_172 B x y) as n13_172.
    now Syll S2l n13_172 S3.
  }
  assert (S4 : (exists b, (Phi x <[- x -]> (x = b)))
    -> ((Phi x ∧ Phi y) -[ x y ]> (x = y))).
  {
    pose proof (n10_11 B (fun b =>
      Phi x <[- x -]> x = b  →  (Phi x ∧ Phi y) -[ x y ]> (x = y)
      )) as n10_11.
    MP n10_11 S3.
    now rewrite -> n10_23 in n10_11.
  }
  assert (S5 : iota_E Phi → ((Phi x ∧ Phi y) -[ x y ]> (x = y))).
  { now Syll S1 S4 S5. }
  exact S5.
Qed.

Close Scope double_app_equiv.

Theorem n14_121 (B C : Prop) (Phi : Prop → Prop) : 
  ((Phi x <[- x -]> x = B) ∧ (Phi x <[- x -]> x = C))
  → B = C. 
Proof.
  assert (S1 : ((Phi x <[- x -]> x = B) ∧ (Phi x <[- x -]> x = C))
    -> ((Phi B ↔ (B = B)) ∧ (Phi B ↔ (B = C)))).
  {
    pose proof (n10_1 (fun x => Phi x ↔ (x = B)) B) as n10_1a.
    pose proof (n10_1 (fun x => Phi x ↔ (x = C)) B) as n10_1b.
    Conj n10_1a n10_1b C1.
    pose proof (n3_47
      (Phi x<[-x-]>x = B) (Phi x<[-x-]>x = C)
      (Phi B ↔ (B = B)) (Phi B ↔ (B = C))
    ) as n3_47.
    now MP n3_47 C1.
  }
  assert (S2 : ((Phi x <[- x -]> x = B) ∧ (Phi x <[- x -]> x = C))
    -> (Phi B ∧ (Phi B ↔ (B = C)))).
  {
    (* I don't know why *13.15 is being used here in such a way *)
    pose proof n13_15.
    admit.
  }
  assert (S3 : ((Phi x <[- x -]> x = B) ∧ (Phi x <[- x -]> x = C))
    -> (B = C)).
  {
    (* Simplifications... *)
    intro Hp.
    pose proof (S2 Hp) as S2.
    destruct S2 as [A1 A2].
    destruct A2 as [A2l _].
    assert (S2_1 : Phi B /\ (Phi B → B = C)).
    { 
      clear S1.
      now Conj A1 A2l S2_1. 
    }
    pose proof (Ass3_35 (Phi B) (B = C)) as Ass3_35.
    now MP Ass3_35 S2_1.
  }
  exact S3.
Admitted.

Open Scope single_app_impl.

Theorem n14_122 (B : Prop) (Phi : Prop → Prop) :
  ((Phi x <[- x -]> (x = B)) ↔ ((Phi x -[ x ]> (x = B)) ∧ Phi B))
  ∧
  (((Phi x -[ x ]> (x = B)) ∧ Phi B) ↔ ((Phi x -[ x ]> (x = B)) ∧ exists x, Phi x)). 
Proof.
  (* TOOLS *)
  set (X := Individual "x").
  (* ******** *)
  assert (S1 : (Phi x <[- x -]> (x = B)) 
    ↔ ((Phi x -[ x ]> (x = B)) ∧ ((x = B) -[ x ]> Phi x))).
  { apply  n10_22. }
  assert (S2 : (Phi x <[- x -]> (x = B)) 
    ↔ ((Phi x -[ x ]> (x = B)) ∧ Phi B)).
  {
    pose proof (n13_191 B Phi) as n13_191.
    now rewrite -> n13_191 in S1.
  }
  assert (S3 : (Phi X -> (X = B))
    -> (Phi X ↔ (Phi X ∧ (X = B)))).
  {
    pose proof (n4_71 (Phi X) (X = B)) as n4_71.
    now destruct n4_71.
  }
  assert (S4 : (Phi x -[ x ]> (x = B))
    -> (Phi x <[- x -]> (Phi x ∧ (x = B)))).
  {
    pose proof (n10_11 X (fun x =>
      (Phi x -> (x = B)) -> (Phi x 
        ↔ (Phi x ∧ (x = B))))) as n10_11.
    MP n10_11 S3.
    pose proof (n10_27 (fun x => Phi x -> (x = B))
      (fun x => Phi x ↔ (Phi x ∧ (x = B)))) 
      as n10_27.
    now MP n10_27 n10_11.
  }
  assert (S5 : (Phi x -[ x ]> (x = B))
    -> ((exists x, Phi x) ↔ (exists x, Phi x ∧ (x = B)))).
  {
    pose proof (n10_281 Phi (fun x => Phi x ∧ x = B)) 
      as n10_281.
    now Syll S4 n10_281 S5.
  }
  assert (S6 : (Phi x -[ x ]> (x = B)) -> ((exists x, 
    Phi x) ↔ Phi B)).
  {
    setoid_rewrite -> n4_3 in S5 at 2.
    now rewrite -> n13_195 in S5.
  }
  assert (S7 : ((Phi x -[ x ]> (x = B)) ∧ (exists x, Phi x))
    ↔ ((Phi x -[ x ]> (x = B)) ∧ Phi B)).
  { now rewrite -> n5_32 in S6. }
  assert (S8 : ((Phi x <[- x -]> (x = B)) ↔ ((Phi x -[ x ]> (x = B)) ∧ Phi B))
    ∧ (((Phi x -[ x ]> (x = B)) ∧ Phi B) 
      ↔ ((Phi x -[ x ]> (x = B)) ∧ exists x, Phi x))).
  {
    clear S1 S3 S4 S5 S6.
    now Conj S2 S7 S8.
  }
  exact S8.
Qed.

Open Scope double_app_equiv.
Open Scope double_app_impl.

Theorem n14_123 (X Y : Prop) (Phi : Prop → Prop → Prop) : 
  ((Phi z w <[- z w -]> (z = X ∧ w = Y)) 
    ↔ ((Phi z w -[ z w ]> (z = X ∧ w = Y)) ∧ Phi X Y))
  ∧
  (((Phi z w -[ z w ]> (z = X ∧ w = Y)) ∧ Phi X Y)
    ↔ ((Phi z w -[ z w ]> (z = X ∧ w = Y)) ∧ exists z w, Phi z w)).
Proof.
  (* TOOLS *)
  set (Z := Individual "z").
  set (W := Individual "w").
  (* ******** *)
  assert (S1 : (Phi z w <[- z w -]> (z = X ∧ w = Y)) 
    ↔ ((Phi z w -[ z w ]> (z = X ∧ w = Y)) 
      ∧ (((z = X ∧ w = Y) -[ z w ]> Phi z w)))).
  {
    pose proof (n11_31 
      (fun z w => Phi z w -> (z = X ∧ w = Y))
      (fun z w => ((z = X ∧ w = Y) -> Phi z w))) as n11_31a.
    symmetry in n11_31a.
    (* Seems like the `Equiv` here isn't supported very well *)
    (* rewrite <- Equiv4_01 in n11_31a. *)
    admit.
  }
  assert (S2 : (Phi z w <[- z w -]> (z = X ∧ w = Y)) 
    ↔ ((Phi z w -[ z w ]> (z = X ∧ w = Y)) ∧ Phi X Y)).
  { now rewrite -> n13_21 in S1. }
  assert (S3 : (Phi Z W -> ((Z = X) ∧ (W = Y)))
    -> (Phi Z W ↔ (Phi Z W ∧ (Z = X) ∧ (W = Y)))).
  {
    pose proof (n4_71 (Phi Z W) ((Z = X) ∧ (W = Y))) as n4_71.
    now destruct n4_71.
  } 
  assert (S4 : (Phi z w -[ z w ]> ((z = X) ∧ (w = Y)))
    -> (Phi z w <[- z w -]> (Phi z w ∧ (z = X) ∧ (w = Y)))).
  {
    pose proof (n11_11 Z W (fun z w =>
      (Phi z w -> ((z = X) ∧ (w = Y)))
        -> (Phi z w ↔ (Phi z w 
          ∧ (z = X) ∧ (w = Y))))) as n11_11.
    MP n11_11 S4.
    pose proof (n11_32 (fun z w => Phi z w -> ((z = X) ∧ (w = Y)))
      (fun z w => Phi z w ↔ (Phi z w 
        ∧ (z = X) ∧ (w = Y)))) as n11_32.
    now MP n11_32 n11_11.
  }
  assert (S5 : (Phi z w -[ z w ]> ((z = X) ∧ (w = Y)))
    -> ((exists z w, Phi z w) ↔ (exists z w, 
      Phi z w ∧ (z = X) ∧ (w = Y)))).
  {
    pose proof (n11_341 Phi (fun z w => 
      Phi z w ∧ (z = X) ∧ (w = Y))) as n11_341.
    now Syll n11_341 S4 S5.
  }
  assert (S6 : (Phi z w -[ z w ]> ((z = X) ∧ (w = Y)))
    -> ((exists z w, Phi z w) ↔ Phi X Y)).
  {
    setoid_rewrite -> n4_3 in S5 at 3.
    setoid_rewrite -> n4_32 in S5.
    now rewrite -> n13_22 in S5.
  }
  assert (S7 : ((Phi z w -[ z w ]> ((z = X) ∧ (w = Y)))
      ∧ (exists z w, Phi z w)
    ↔ ((Phi z w -[ z w ]> (z = X ∧ w = Y)) ∧ Phi X Y))).
  { now rewrite -> n5_32 in S6. }
  assert (S8 : ((Phi z w <[- z w -]> (z = X ∧ w = Y)) 
      ↔ ((Phi z w -[ z w ]> (z = X ∧ w = Y)) ∧ Phi X Y))
    ∧ (((Phi z w -[ z w ]> (z = X ∧ w = Y)) ∧ Phi X Y)
      ↔ ((Phi z w -[ z w ]> (z = X ∧ w = Y)) ∧ exists z w, Phi z w))).
  {
    clear S1 S3 S4 S5 S6.
    now Conj S2 S7 S8.
  }
  exact S8.
Admitted.

(* TODO: 4-var impl notation will be supported in the future *)
Theorem n14_124 (Phi : Prop → Prop → Prop) : 
  (exists x y, (Phi z w <[- z w -]> (z = x ∧ w = y)))
  ↔ ((exists x y, Phi x y) 
    ∧ forall z w u v, (Phi z w ∧ Phi u v) → (z = u ∧ w = v)). 
Proof.
  (* TOOLS *)
  set (X := Individual "x").
  set (Y := Individual "y").
  set (Z := Individual "z").
  set (W := Individual "w").
  set (U := Individual "u").
  set (V := Individual "v").
  (* ******** *)
  assert (S1 : (exists x y, (Phi z w <[- z w -]> (z = x ∧ w = y)))
    -> exists x y, Phi x y).
  { 
    (* This can be done as in some previous chapter, but I 
    don't want to fill out at the moment *)
    pose proof n14_123 as n14_123.
    pose proof Simp3_27 as Simp3_27.
    admit.
  }
  assert (S2 : (Phi z w <[- z w -]> ((z = X) ∧ (w = Y)))
    -> (((Phi Z W) ∧ (Phi U V))
      -> (Z = X ∧ W = Y ∧ U = X ∧ V = Y))).
  {
    pose proof (n11_1 Z W (fun z w =>
      (Phi z w) ↔ ((z = X) ∧ (w = Y)))) as n11_1a.
    pose proof (n11_1 U V (fun z w =>
      (Phi z w) ↔ ((z = X) ∧ (w = Y)))) as n11_1b.
    pose proof (n3_47 ) as n3_47.
    (* Involves some very complicated treatments on destructing
    and recombining the ↔s. We might want to abstract such 
    procedure into a new theorem *)
    admit.
  }
  assert (S3 : (Phi z w <[- z w -]> ((z = X) ∧ (w = Y)))
    -> (((Phi Z W) ∧ (Phi U V)) -> ((Z = U) ∧ (W = V)))).
  {
    (* simplification: tedious reordering... *)
    assert (S2_1 : (Z = X ∧ W = Y ∧ U = X ∧ V = Y)
      ↔ ((Z = X ∧ U = X) ∧ (W = Y ∧ V = Y))).
    {
      (* TODO: we need theorem for commutativity for ∧ *)
      admit. 
    }
    rewrite -> S2_1 in S2. clear S2_1.
    pose proof (n13_172 X Z U) as n13_172a.
    pose proof (n13_172 Y W V) as n13_172b.
    pose proof (n3_47
      (Z = X ∧ U = X) (W = Y ∧ V = Y)
      (Z = U) (W = V)) as n3_47.
    assert (C1 : (Z = X ∧ U = X → Z = U) ∧ (W = Y ∧ V = Y → W = V)).
    { clear n3_47; now Conj n13_172a n13_172b C1. }
    MP n3_47 C1.
    (* simplification for syll *)
    intros Hp.
    pose proof (S2 Hp) as S2.
    now Syll S2 n3_47 S3.
  }
  assert (S4 : (exists x y, Phi z w <[- z w -]> ((z = x) ∧ (w = y)))
    -> (((Phi Z W) ∧ (Phi U V)) -> ((Z = U) ∧ (W = V)))).
  {
    pose proof (n11_11 X Y (fun x y =>
      (Phi z w <[- z w -]> ((z = x) ∧ (w = y)))
        -> (((Phi Z W) ∧ (Phi U V)) -> ((Z = U) ∧ (W = V))))) 
      as n11_11.
    MP n11_11 S3.
    now rewrite -> n11_35 in n11_11.
  }
  assert (S5 : (exists x y, Phi z w <[- z w -]> ((z = x) ∧ (w = y)))
    -> (forall z w u v, (Phi z w ∧ Phi u v) -> ((z = u) ∧ (w = v)))).
  {
    (* For 4 variables, the generalization has applied twice! *)
    pose proof (n11_11 U V (fun u v =>
      (exists x y, Phi z w <[- z w -]> ((z = x) ∧ (w = y)))
      -> (((Phi Z W) ∧ (Phi u v)) -> ((Z = u) ∧ (W = v))))) 
      as n11_11a.
    MP n11_11a S4.
    rewrite <- n11_3 in n11_11a.
    pose proof (n11_11 Z W (fun z w =>
    (exists x y, Phi z w <[- z w -]> ((z = x) ∧ (w = y)))
      -> (forall u v, ((Phi z w) ∧ (Phi u v)) -> ((z = u) ∧ (w = v)))
      )) as n11_11b.
    MP n11_11b n11_11a.
    now rewrite <- n11_3 in n11_11b.
  }
  assert (S6 : ((Phi X Y) ∧ (forall z w u v, 
    ((Phi z w) ∧ (Phi u v)) -> ((z = u) ∧ (w = v)))
      -> (Phi X Y ∧ ((Phi z w ∧ Phi X Y) -[ z w ]> ((z = X) ∧ (w = Y)))))).
  {
    (* The ordering here is annoying... *)
    pose proof (n11_1 X Y (fun u v =>
      (∀ z w, Phi z w ∧ Phi u v → z = u ∧ w = v))) as n11_1.
    assert (A1 : (∀ x y z w : Prop, Phi z w ∧ Phi x y → z = x ∧ w = y)
      ↔ (∀ z w x y : Prop, Phi z w ∧ Phi x y → z = x ∧ w = y)).
    { admit. }
    rewrite -> A1 in n11_1.
    pose proof (Fact3_45
      (∀ z w x y : Prop, Phi z w ∧ Phi x y → z = x ∧ w = y)
      ((Phi z w ∧ Phi X Y)-[ z w ]> z = X ∧ w = Y)
      (Phi X Y)) as Fact3_45.
    MP Fact3_45 n11_1.
    rewrite -> n4_3 in Fact3_45.
    replace (((Phi z w ∧ Phi X Y)-[ z w ]> z = X ∧ w = Y ) ∧ Phi X Y)
      with (Phi X Y ∧ ((Phi z w ∧ Phi X Y)-[ z w ]> z = X ∧ w = Y))
      in Fact3_45.
    2: { apply propositional_extensionality; now rewrite -> n4_3. }
    exact Fact3_45.
  }
  assert (S7 : ((Phi X Y) ∧ (forall z w u v, 
    ((Phi z w) ∧ (Phi u v)) -> ((z = u) ∧ (w = v))))
    -> (Phi X Y ∧ (Phi z w -[ z w ]> ((z = X) ∧ (w = Y))))).
  {
    (* I don't think *5.33 can be directly applied here and we need
    a quantified version *)
    (* rewrite <- n5_33 in S6. *)
    admit.
  }
  assert (S8 : ((Phi X Y) ∧ (forall z w u v, 
    ((Phi z w) ∧ (Phi u v)) -> ((z = u) ∧ (w = v))))
    -> (Phi z w <[- z w -]> ((z = X) ∧ (w = Y)))).
  {
    pose proof (n14_123 X Y Phi) as n14_123.
    destruct n14_123 as [n14_123l _].
    replace (Phi X Y ∧ Phi z w-[ z w ]>z = X ∧ w = Y )
      with ((Phi z w-[ z w ]>z = X ∧ w = Y) ∧ Phi X Y)
      in S7.
    2: { apply propositional_extensionality. now rewrite -> n4_3. }
    now rewrite <- n14_123l in S7.
  }
  assert (S9 : ((exists x y, Phi x y) ∧ (forall z w u v,
      (Phi z w ∧ Phi u v) -> ((z = u) ∧ (w = v)))
    -> (exists x y, Phi z w <[- z w -]> ((z = x) ∧ (w = y))))).
  {
    pose proof n11_45 as _n11_45.
    pose proof (n11_11 X Y (fun x y =>
      ((Phi x y) ∧ (forall z w u v, 
        ((Phi z w) ∧ (Phi u v)) -> ((z = u) ∧ (w = v))))
        -> (Phi z w <[- z w -]> ((z = x) ∧ (w = y))))) as n11_11.
    MP n11_11 S8.
    pose proof (n11_34
      (fun x y => Phi x y ∧ (forall z w u v,
        (Phi z w ∧ Phi u v) -> ((z = u) ∧ (w = v))))
      (fun x y => (Phi z w <[- z w -]> ((z = x) ∧ (w = y))))) 
      as n11_34.
    MP n11_34 n11_11.
    setoid_rewrite -> n4_3 in n11_34 at 1.
    rewrite -> n11_45 in n11_34.
    now rewrite -> n4_3 in n11_34 at 1.
  }
  assert (S10 : (∃ x y,  Phi z w<[- z w -]>z = x ∧ w = y )
    ↔ (∃ x y, Phi x y) 
      ∧ ∀ z w u v, Phi z w ∧ Phi u v → z = u ∧ w = v).
  {
    clear S2 S3 S4 S6 S7 S8.
    assert (C1 : ((∃ x y,  Phi z w <[- z w -]> z = x ∧ w = y ) → ∃ x y : Prop, Phi x y)
      ∧ ((∃ x y,  Phi z w <[- z w -]> z = x ∧ w = y )
        → ∀ z w u v, Phi z w ∧ Phi u v → z = u ∧ w = v)).
    { clear S9. now Conj S1 S5 C1. }
    pose proof (Comp3_43
      (∃ x y, Phi z w <[- z w -]> z = x ∧ w = y)
      (∃ x y, Phi x y)
      (∀ z w u v, Phi z w ∧ Phi u v → z = u ∧ w = v)) 
      as Comp3_43.
    MP Comp3_43 C1.
    clear S1 S5 C1.
    move S9 after Comp3_43.
    Conj Comp3_43 S9 S10.
    now Equiv S10.
  }
  exact S10.
Admitted.

Theorem n14_13 (A : Prop) (s : string) (Phi : Prop → Prop) : 
  (iota_f s Phi (fun x => A = (Iota s x)))
  ↔ (iota_f s Phi (fun x => (Iota s x) = A)). 
Proof.
  (* TOOLS *)
  set (B := Individual "b").
  (* ******** *)
  assert (S1 : (iota_f s Phi (fun x => A = (Iota s x)))
    ↔ (exists b, (Phi x <[- x -]> (x = b)) ∧ A = b)).
  { apply n14_1. }
  assert (S2 : ((Phi x <[- x -]> (x = B)) ∧ (A = B))
    ↔ ((Phi x <[- x -]> (x = B)) ∧ (B = A))).
  {
    pose proof (n13_16 A B) as n13_16.
    pose proof (n4_36 (A = B) (B = A) (Phi x <[- x -]> (x = B))) as n4_36.
    MP n4_36 n13_16.
    rewrite -> n4_3 in n4_36.
    replace (B = A ∧  Phi x <[- x -]> x = B) with 
      ((Phi x <[- x -]> x = B) ∧ B = A) in n4_36.
    2: { apply propositional_extensionality. now rewrite -> n4_3. }
    exact n4_36.
  }
  assert (S3 : (exists b, (Phi x <[- x -]> x = b) ∧ (A = b))
    ↔ (exists b, (Phi x <[- x -]> x = b) ∧ (b = A))).
  {
    pose proof (n10_11 B (fun b => 
        ((Phi x <[- x -]> (x = b)) ∧ (A = b))
      ↔ ((Phi x <[- x -]> (x = b)) ∧ (b = A)))) as n10_11.
    MP n10_11 S2.
    pose proof (n10_281 
      (fun b => (Phi x <[- x -]> (x = b)) ∧ (A = b))
      (fun b => (Phi x <[- x -]> (x = b)) ∧ (b = A))) as n10_281.
    now MP n10_281 n10_11.
  }
  assert (S4 : (exists b, (Phi x <[- x -]> x = b) ∧ (A = b))
    ↔ (iota_f s Phi (fun x => (Iota s x) = A))).
  { now rewrite <- (n14_1 s Phi  (fun b => b = A)) in S3. }
  assert (S5 : (iota_f s Phi (fun x => A = (Iota s x)))
    ↔ (iota_f s Phi (fun x => (Iota s x) = A))).
  { now rewrite -> S4 in S1. }
  exact S5.
Qed.

(* TODO: rewrite the definition correctly *)
(* There are 2 ways to intrepret the iotas in this proposition. Original text
has also given both ways to interpre them correspondingly. It seems that
we will take the one-at-a-time as the usual way *)
Theorem n14_131 (Phi Psi : Prop → Prop) : 
  iota_f "Phi" Phi (fun x => iota_f "Psi" Psi (fun y =>
    (Iota "Phi" x) = (Iota "Psi" y)))
  ↔
  iota_f "Psi" Psi (fun y => iota_f "Phi" Phi (fun x =>
    (Iota "Psi" y) = (Iota "Phi" x))).
Proof.
  assert (S1 : iota_f "Phi" Phi (fun x => iota_f "Psi" Psi (fun y =>
      (Iota "Phi" x) = (Iota "Psi" y)))
    ↔ (exists b, (Phi x <[- x -]> (x = b)) 
      ∧ iota_f "Psi" Psi (fun y => b = (Iota "Psi" y)))).
  { apply n14_1. }
  assert (S2 : iota_f "Phi" Phi (fun x => iota_f "Psi" Psi (fun y =>
      (Iota "Phi" x) = (Iota "Psi" y)))
    ↔ (exists b, (Phi x <[- x -]> (x = b)) 
      ∧ (exists c, (Psi x <[- x -]> (x = c)) ∧ (b = c)))).
  { now setoid_rewrite -> n14_1 in S1 at 3. }
  assert (S3 : iota_f "Phi" Phi (fun x => iota_f "Psi" Psi (fun y =>
      (Iota "Phi" x) = (Iota "Psi" y)))
    ↔ (exists c, (Psi x <[- x -]> (x = c))
      ∧ (exists b, (Phi x <[- x -]> (x = b)) ∧ (b = c)))).
  {
    setoid_rewrite -> n4_3 in S2 at 2.
    setoid_rewrite -> n4_3 in S2 at 3.
    rewrite -> n11_6 in S2.
    setoid_rewrite <- n4_3 in S2 at 3.
    now setoid_rewrite <- n4_3 in S2 at 2.
  }
  assert (S4 : iota_f "Phi" Phi (fun x => iota_f "Psi" Psi (fun y =>
      (Iota "Phi" x) = (Iota "Psi" y)))
    ↔ (exists c, (Psi x <[- x -]> (x = c)) 
      ∧ iota_f "Phi" Phi (fun x => (Iota "Phi" x) = c))).
  { now setoid_rewrite <- (n14_1 "Phi") in S3 at 2. }
  assert (S5 : iota_f "Phi" Phi (fun x => iota_f "Psi" Psi (fun y =>
      (Iota "Phi" x) = (Iota "Psi" y)))
    ↔ (exists c, (Psi x <[- x -]> (x = c)) 
      ∧ iota_f "Phi" Phi (fun x => c = (Iota "Phi" x)))).
  { now setoid_rewrite <- n14_13 in S4. }
  assert (S6 : iota_f "Phi" Phi (fun x => iota_f "Psi" Psi 
      (fun y => (Iota "Phi" x) = (Iota "Psi" y)))
    ↔ iota_f "Psi" Psi (fun y => iota_f "Phi" Phi (fun x =>
      (Iota "Psi" y) = (Iota "Phi" x)))).
  { now rewrite <- (n14_1 "Psi") in S5. }
  exact S6.
Qed.

Theorem n14_131_alt (s1 s2 : string) (Phi Psi : Prop → Prop) : 
  iota_f2 s1 s2 Phi Psi (fun x y => (Iota s1 x) = (Iota s2 y))
  ↔
  iota_f2 s2 s1 Psi Phi (fun x y => (Iota s2 y) = (Iota s1 x)). 
Proof.
  assert (S1 : iota_f2 s1 s2 Phi Psi (fun x y => (Iota s1 x) = (Iota s2 y))
    ↔ exists b c, (Phi x <[- x -]> (x = b)) 
      ∧ (Psi x <[- x -]> (x = c)) ∧ (b = c)).
  {
    (* We use the definition of iota_f2 instead, for the obvious reason.
     *14.111 ignored *)
    apply n14_112.
  }
  assert (S2 : iota_f2 s1 s2 Phi Psi (fun x y => (Iota s1 x) = (Iota s2 y))
    ↔ exists b c, (Psi x <[- x -]> (x = c)) 
      ∧ (Phi x <[- x -]> (x = b)) ∧ (c = b)).
  {
    (* *11.11, *11.341 ignored *)
    setoid_rewrite -> n13_16 in S1 at 4.
    setoid_rewrite -> n4_3 in S1 at 2.
    setoid_rewrite -> n4_32 in S1.
    now setoid_rewrite -> n4_3 in S1 at 4.
  }
  assert (S3 : iota_f2 s1 s2 Phi Psi (fun x y => 
      (Iota s1 x) = (Iota s2 y))
    ↔ iota_f2 s2 s1 Psi Phi (fun x y => (Iota s2 y) = (Iota s1 x))).
  {
    (* much of the citations are wrong... *)
    rewrite -> n11_23 in S2.
    pose proof (n14_112 s2 s1 Psi Phi
      (fun x y => Iota s2 y = Iota s1 x)) as n14_112.
    setoid_rewrite -> n13_16 in S2 at 4.
    now rewrite <- n14_112 in S2.
  }
  exact S3.
Qed.

Theorem n14_14 (A B : Prop) (s : string) (Phi : Prop → Prop) :
  ((A = B) ∧ (iota_f s Phi (fun x => B = (Iota s x))))
  → (iota_f s Phi (fun x => A = (Iota s x))).
Proof.
  rewrite -> n4_3.
  rewrite -> n13_16.
  exact (n13_13 B A (fun a => 
      (iota_f s Phi (fun x => a = (Iota s x))))).
Qed.

Theorem n14_142 (A : Prop) (s1 s2 : string) (Phi Psi : Prop → Prop) :
  iota_f s1 Phi (fun x => A = Iota s1 x)
    ∧ iota_f s1 Phi (fun x => iota_f s2 Psi 
      (fun y => Iota s1 x = Iota s2 y))
  → iota_f s2 Psi (fun x => A = Iota s2 x).
Proof.
  assert (S1 : (iota_f s1 Phi (fun x => A = Iota s1 x)
      ∧ iota_f s1 Phi (fun x => iota_f s2 Psi 
        (fun y => Iota s1 x = Iota s2 y)))
    -> ((exists b, (Phi x <[- x -]> (x = b)) ∧ (A = b)) 
      ∧ (exists c, (Phi x <[- x -]> (x = c)) ∧ iota_f s2 Psi 
        (fun x => c = (Iota s2 x))))).
  {
    pose proof (n14_1 s1 Phi (fun b => A = Iota s1 b)) 
      as n14_1a.
    destruct n14_1a as [n14_1al _].
    pose proof (n14_1 s1 Phi (fun c =>
      iota_f s2 Psi (fun y => c = Iota s2 y))) as n14_1b.
    destruct n14_1b as [n14_1bl _].
    Conj n14_1al n14_1bl C1.
    pose proof (n3_47
      (iota_f s1 Phi (λ b, A = Iota s1 b))
      (iota_f s1 Phi (λ c, iota_f s2 Psi (λ y, c = Iota s2 y)))
      (∃ b, (Phi x <[- x -]> x = b) ∧ A = Iota s1 b)
      (∃ b, (Phi x <[- x -]> x = b) ∧ iota_f s2 Psi (λ y, b = Iota s2 y))) 
      as n3_47.
    now MP n3_47 C1.
  }
  assert (S2 : (iota_f s1 Phi (fun x => A = Iota s1 x)
    ∧ iota_f s1 Phi (fun x => iota_f s2 Psi 
      (fun y => Iota s1 x = Iota s2 y)))
  -> ((Phi x <[- x -]> (x = A))
    ∧ (exists c, (Phi x <[- x -]> (x = c)) ∧ iota_f s2 Psi 
        (fun x => c = (Iota s2 x))))).
  {
    setoid_rewrite -> n4_3 in S1 at 3.
    setoid_rewrite -> n13_16 in S1 at 3.
    now rewrite -> n13_195 in S1.
  }
  assert (S3 : (iota_f s1 Phi (fun x => A = Iota s1 x)
    ∧ iota_f s1 Phi (fun x => iota_f s2 Psi 
      (fun y => Iota s1 x = Iota s2 y)))
  -> exists c, (Phi x <[- x -]> (x = A)) /\ (Phi x <[- x -]> (x = c)) 
      ∧ iota_f s2 Psi (fun x => c = (Iota s2 x))).
  { now rewrite <- n10_35 in S2. }
  assert (S4 : (iota_f s1 Phi (fun x => A = Iota s1 x)
    ∧ iota_f s1 Phi (fun x => iota_f s2 Psi 
      (fun y => Iota s1 x = Iota s2 y)))
  -> exists c, (Phi x <[- x -]> (x = A)) /\ (A = c)
      /\ iota_f s2 Psi (fun x => c = (Iota s2 x))).
  {
    intros Hp.
    pose proof (S3 Hp) as S3.
    (* I don't think here is provable *)
    pose proof n14_121 as n14_121.
    admit.
  }
  assert (S5 : iota_f s1 Phi (fun x => A = Iota s1 x)
      ∧ iota_f s1 Phi (fun x => iota_f s2 Psi 
        (fun y => Iota s1 x = Iota s2 y))
    → iota_f s2 Psi (fun x => A = Iota s2 x)).
  {
    (* I think it could be that *14.121 should be used in last step
    but in that case the *3.27 here will not be used. Aka S4 has been
    typed wrong in original text with an extra `<->` term
    TODO: we can correct both of the steps in the future *)
    pose proof Simp3_27 as Simp3_27.
    pose proof n13_195 as n13_195.
    admit.
  }
  exact S5.
Admitted.

Theorem n14_144 (s1 s2 s3 : string) (Phi Psi Chi : Prop → Prop) : 
  ((iota_f2 s1 s2 Phi Psi (fun x y => (Iota s1 x) = (Iota s2 y)))
    ∧ (iota_f2 s2 s3 Psi Chi (fun x y => (Iota s2 x) = (Iota s3 y))))
  → (iota_f2 s1 s3 Phi Chi (fun x y => (Iota s1 x) = (Iota s3 y))).
Proof.
Admitted.

Theorem n14_145 (A : Prop) (Phi Psi : Prop → Prop) : 
  ((iota_f "Phi" Phi (fun x => A = (Iota "Phi" x))) 
    ∧ (iota_f "Psi" Psi (fun x => A = (Iota "Psi" x))))
  → (iota_f2 "Phi" "Psi" Phi Psi (fun x y => (Iota "Phi" x) = (Iota "Psi" y))).
Proof.
Admitted.

Theorem n14_15 (B : Prop) (Phi Psi : Prop → Prop) : 
  (iota_f "Phi" Phi (fun x => (Iota "Phi" x) = B))
  → (iota_f "Phi" Phi (fun x => Psi (Iota "Phi" x))
    ↔ Psi B).
Proof.
Admitted.

Theorem n14_16 (Phi Psi Chi : Prop → Prop) :
  (iota_f2 "Phi" "Psi" Phi Psi (fun x y => (Iota "Phi" x) = (Iota "Psi" y)))
  →
  (iota_f2 "Phi" "Psi" Phi Psi (fun x y => 
    (Chi (Iota "Phi" x)) = (Chi (Iota "Psi" y)))).
Proof.
Admitted.

Theorem n14_17 (B : Prop) (Phi : Prop → Prop) : 
  (iota_f "Phi" Phi (fun x => (Iota "Phi" x) = B))
  ↔
  (forall Psi : Predicate 1, iota_f "Phi" Phi (fun x =>
    Psi (Iota "Phi" x) ↔ Psi B)).
Proof.
Admitted.

Theorem n14_171 (B : Prop) (Phi : Prop → Prop) : 
  (iota_f "Phi" Phi (fun x => (Iota "Phi" x) = B))
  ↔
  (forall Psi : Predicate 1, iota_f "Phi" Phi (fun x =>
    Psi B → Psi (Iota "Phi" x))).
Proof.
Admitted.

Theorem n14_18 (Phi Psi : Prop → Prop) :
  iota_E Phi → (forall x, Psi x → iota_f "Phi" Phi (fun x =>
    Psi (Iota "Phi" x))).
Proof.
Admitted.

Theorem n14_2 (X A : Prop) : 
  (iota_f "=a" (fun x => x = A)
    (fun y => (Iota "=a" y) = A)).
Proof.
Admitted.

Theorem n14_201 (Phi : Prop → Prop) : iota_E Phi → exists x, Phi x. 
Proof.
Admitted.

Theorem n14_202 (B : Prop) (Phi : Prop → Prop) : 
  ((Phi x <[- x -]> x = B) ↔ (iota_f "Phi" Phi (fun x => (Iota "Phi" x) = B)))
  ∧
  ((iota_f "Phi" Phi (fun x => (Iota "Phi" x) = B)) ↔ (Phi x <[- x -]> B = x))
  ∧
  ((Phi x <[- x -]> B = x) ↔ (iota_f "Phi" Phi (fun x => B = (Iota "Phi" x)))).
Proof.
Admitted.

Theorem n14_203 (Phi : Prop → Prop) : iota_E Phi 
  ↔ ((exists x, Phi x) ∧ ((Phi x ∧ Phi y)) -[ x y ]> (x = y)).
Proof.
Admitted.

Theorem n14_204 (B : Prop) (Phi : Prop → Prop) : iota_E Phi 
  ↔ exists b, (iota_f "Phi" Phi (fun x => (Iota "Phi" x) = b)).
Proof.
Admitted.

Theorem n14_205 (Phi Psi : Prop → Prop) : (iota_f "Phi" Phi Psi)
  ↔ exists b, (iota_f "Phi" Phi (fun x => b = (Iota "Phi" x))) ∧ Psi b.
Proof.
Admitted.

Theorem n14_21 (Phi Psi : Prop → Prop) : (iota_f "Phi" Phi Psi) → iota_E Phi.
Proof.
Admitted.

Theorem n14_22 (Phi : Prop → Prop) : iota_E Phi ↔ iota_f "Phi" Phi Phi.
Proof.
Admitted.

Theorem n14_23 (Phi Psi : Prop → Prop) : iota_E (fun x => Phi x ∧ Psi x) 
  ↔ iota_f "Phi x ∧ Psi x" (fun x => Phi x ∧ Psi x) Phi.
Proof.
Admitted.

Theorem n14_24 (Phi : Prop → Prop) : iota_E Phi 
  ↔ iota_f "Phi" Phi (fun x => Phi y <[- y -]> y = (Iota "Phi" x)).
Proof.
Admitted.

Theorem n14_241 (Phi : Prop → Prop) : iota_E Phi 
  → (Phi y <[- y -]> iota_f "Phi" Phi (fun x => y = (Iota "Phi" x))).
Proof.
Admitted.

Theorem n14_242 (B : Prop) (Phi Psi : Prop → Prop) : (Phi x <[- x -]> x = B)
  → (Psi B ↔ iota_f "Phi" Phi Psi).
Proof.
Admitted.

Theorem n14_25 (Phi Psi : Prop → Prop) : iota_E Phi 
  → ((Phi x <[- x -]> Psi x) ↔ iota_f "Phi" Phi Psi).
Proof.
Admitted.

Theorem n14_26 (Phi Psi : Prop → Prop) : iota_E Phi 
  → exists x, ((Phi x ∧ Psi x) ↔ iota_f "Phi" Phi Psi)
    ∧ ((iota_f "Phi" Phi Psi) ↔ (Phi x <[- x -]> Psi x)).
Proof.
Admitted.

Theorem n14_27 (Phi Psi : Prop → Prop) : iota_E Phi 
  → ((Phi x <[- x -]> Psi x) 
    ↔ iota_f2 "Phi" "Psi" Phi Psi (fun x y =>
      (Iota "Phi" x) = (Iota "Psi" y))).
Proof.
Admitted.

Theorem n14_271 (Phi Psi : Prop → Prop) : (Phi x <[- x -]> Psi x)
  → ((iota_E Phi) ↔ (iota_E Psi)).
Proof.
Admitted.

Theorem n14_272 (Phi Psi Chi : Prop → Prop) : (Phi x <[- x -]> Psi x)
  → (iota_f2 "Phi" "Psi" Phi Psi (fun x y =>
    Chi (Iota "Phi" x) ↔ Chi (Iota "Psi" y))).
Proof.
Admitted.

Theorem n14_28 (Phi : Prop → Prop) : iota_E Phi
  ↔ (iota_f2 "Phi" "Phi" Phi Phi (fun x y =>
    (Iota "Phi" x) = (Iota "Phi" y))).
Proof.
Admitted.

Theorem n14_3 (Phi Chi f : Prop → Prop) : 
  (((p ↔ q) -[ p q ]> (f p ↔ f q)) ∧ iota_E Phi)
  →
  ((f (iota_f "Phi" Phi Chi)) ↔ iota_f "Phi" Phi (fun x =>
    f (Chi (Iota "Phi" x)))).
Proof.
Admitted.

Theorem n14_31 (P : Prop) (Phi Chi : Prop → Prop) : iota_E Phi
  → ((iota_f "Phi" Phi (fun x => P ∨ Chi (Iota "Phi" x)))
    ↔ P ∨ (iota_f "Phi" Phi Chi)).
Proof.
Admitted.

Theorem n14_32 (Phi Chi : Prop → Prop) : iota_E Phi
  ↔ ((iota_f "Phi" Phi (fun x => ~ Chi (Iota "Phi" x)))
    ↔ ~ (iota_f "Phi" Phi Chi)).
Proof.
Admitted.

Theorem n14_33 (P : Prop) (Phi Chi : Prop → Prop) : iota_E Phi
  → ((iota_f "Phi" Phi (fun x => P → Chi (Iota "Phi" x)))
    ↔ (P → iota_f "Phi" Phi Chi)).
Proof.
Admitted.

(* Is there a typo in this proposition? An identitical conclusion? *)
Theorem n14_331 (P : Prop) (Phi Chi : Prop → Prop) : iota_E Phi
  → ((iota_f "Phi" Phi (fun x => Chi (Iota "Phi" x) → P))
    ↔ (iota_f "Phi" Phi (fun x => Chi (Iota "Phi" x) → P))).
Proof.
Admitted.

Theorem n14_332 (P : Prop) (Phi Chi : Prop → Prop) : iota_E Phi
  → ((iota_f "Phi" Phi (fun x => P ↔ Chi (Iota "Phi" x)))
    ↔ (P ↔ (iota_f "Phi" Phi Chi))).
Proof.
Admitted.

Theorem n14_34 (P : Prop) (Phi Chi : Prop → Prop) : 
  (P ∧ iota_f "Phi" Phi Chi) ↔ iota_f "Phi" Phi (fun x =>
    P ∧ Chi (Iota "Phi" x)).
Proof.
Admitted.

Close Scope single_app_equiv.
Close Scope single_app_impl.
Close Scope double_app_equiv.
Close Scope double_app_impl.