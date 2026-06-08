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
Require Import PM.pm.ch14.

(* TODO: 
- Change the definitions in this chapter to monomorphic version; provide variants 
  to patch up
- For class, provide an assumption to associate specific class var with specific
  function
- Prettify the code and the notation. 0302 for hat or directly generate from internet
*)

Declare Scope debug_class.
Declare Scope class.

Definition n10_01_pred (φ : (Prop → Prop) → Prop) : 
  (∃ x, φ x) = ¬ (∀ x, ¬ φ x). 
Admitted.

Definition n10_11_pred (Y : Order 1) (φ : Order 1 → Prop)
  : φ Y → ∀ x, φ x.
Admitted.

Definition n10_11_pred2_1 (Y : Order2 2) (φ : Order2 2 → Prop)
  : φ Y → ∀ x, φ x.
Admitted.

Definition n10_11_pred_1 (Y : Order 2) (φ : Order 2 → Prop)
  : φ Y → ∀ x, φ x.
Admitted.

Definition n10_21_pred (φ : Order 1 → Prop) (P : Prop) :
  (∀ x : Order 1, P → φ x) ↔ (P → (∀ x : Order 1, φ x)).
Admitted.

Definition n10_21_pred_1 (φ : Order 2 → Prop) (P : Prop) :
  (∀ x : Order 2, P → φ x) ↔ (P → (∀ x : Order 2, φ x)).
Admitted.

Definition n10_27_pred_1 (φ ψ : Order 2 → Prop) : 
  (∀ z, φ z → ψ z) → ((∀ z, φ z) → (∀ z, ψ z)).
Admitted.

Definition n10_28_pred (φ ψ : (Prop → Prop) → Prop) :
  (∀ x, φ x → ψ x) → ((∃ x, φ x) → (∃ x, ψ x)).
Admitted.

Definition n10_28_pred_1 (φ ψ : Order 2 → Prop) :
  (∀ x, φ x → ψ x) → ((∃ x, φ x) → (∃ x, ψ x)).
Admitted.

Definition n10_281_pred (φ ψ : (Prop → Prop) → Prop) :
  (∀ x, φ x ↔ ψ x) → ((∃ x, φ x) ↔ (∃ x, ψ x)).
Admitted.

Definition n10_281_pred2_1 (φ ψ : Order2 2 → Prop) :
  (∀ x, φ x → ψ x) → ((∃ x, φ x) → (∃ x, ψ x)).
Admitted.

Definition n10_33_pred_1 (φ : Order 2 → Prop) (P : Prop) :
  (∀ x, φ x ∧ P) ↔ ((∀ x, φ x) ∧ P).
Admitted.

Definition n10_35_pred (φ : (Prop → Prop) → Prop) (P : Prop) :
  (∃ x, P ∧ φ x) ↔ P ∧ (∃ x, φ x).
Admitted.

Definition n10_5_pred (φ ψ : (Prop → Prop) → Prop) :
  (∃ x, φ x ∧ ψ x) → ((∃ x, φ x) ∧ (∃ x, ψ x)).
Admitted.

Definition n11_11_pred (Z W : Prop → Prop) (φ : (Prop → Prop) 
  → (Prop → Prop) → Prop) : (φ Z W) → (∀ x y, φ x y).
Admitted.

Definition n11_2_pred (φ : (Prop → Prop) → (Prop → Prop) → Prop) : 
  (∀ x y, φ x y) ↔ (∀ y x, φ x y).
Admitted.

Definition n13_16_pred (X Y : Prop -> Prop) : (X = Y) ↔ (Y = X).
Admitted.

Definition n13_195_pred (X : Prop -> Prop) (φ : (Prop -> Prop) → Prop) : 
  (∃ y, (y = X) ∧ φ y) ↔ φ X.
Admitted.

Open Scope iota_description.

Definition n14_21_pred (φ ψ : (Prop → Prop) → Prop) : 
  [ι φ | ιφ => ψ ιφ] → [ιE φ]. Admitted.

Close Scope iota_description.

Open Scope formal_equiv.

(* This is a very ironic variant: we shouldn't write down such a variant
if we have designed the AoR correctly *)
Definition n12_1_pred (φ : (Prop → Prop) → Prop) : 
  ∃ f : (Order 2), (φ x) <[- (x : Order 1) -]> ((fun (F : Order 2) =>
    F x) f).
Admitted.

(* 
Using Records to define the Class symbol seems to be the best balance to 
expose the `A` type when needed and hide away the underlying function against 
unnecessary argument passes
*)
Module Class.
  Record t (A : Type) : Type := {
    (* For storing the A type *)
    get_A := A;
    (* UNUSED *)
    get_func : get_A → Prop;
  }.
  Definition mk {A : Type} (φ : A → Prop) := Build_t A φ.
End Class.

Example class_example_1 := Class.mk (fun (x : Prop) => x = x).
Example class_mk_destruct_example_1 := 
  class_example_1.(Class.get_func Prop).
Example class_mk_destruct_example_2 := 
  class_example_1.(Class.get_A Prop).  

(* We need the `B` because `f` could maybe accept more parameters *)
Definition class_app {A B : Type} (f : (A → Prop) → B) (cls : Class.t A) : B. Admitted.

(* NOTE: This is a very ad-hoc implementation for functions that takes classes as parameters. 
We are still figuring out the correct way to correctly define functions taking arbitrary 
"level"s of class as parameter. See n20_08. From the nature of this definition, it seems 
that `app` is supposed to generate the related `mk` in a "smart" way. `c` suffix stands for 
"applying on another *c*lass".
Note that this notation and corresponded *20.08 is not used in the whole chapter *)
Definition class_app_c {A B : Type} (f : ((A → Prop) → Prop) → B) 
  (ψ : (A → Prop) → Prop) : B. Admitted.

(* By *20.02, `in` needs to be interpreted as a function working directly
on the underlying function `φ`. `in` itself is considered a propositional 
function *)
Definition class_in {A : Type} (X : A) (φ : A → Prop) : Prop. Admitted.

Definition class_in_c {A : Type} (α : Class.t A) (ψ : (A → Prop) → Prop) : Prop.
Admitted.

Definition Cls {A : Type} : Class.t A. Admitted.

Open Scope debug_class.
Notation "'^' z => B" := (Class.mk (fun z => B))
  (at level 130, z binder, right associativity) : debug_class.
Example class_example_2 := ^ (z : Prop) => z = z.

(* Dark magic: we re-define the exact notation simutaneously for parsing and printing.
This allows `let`s being simplified when printing the definition.
Tradeoff: it might affect how `setoid_rewrite` identify the terms *)
Notation "[ cls @ classname => B ]" := (
    let A := cls.(Class.get_A _) in
    (* let f := (fun (classname : A → Prop) => B) in
    let Af := cls.(Class.get_func) in
    f Af *)
    class_app (fun (classname : A → Prop) => B) cls)
  (at level 150, classname binder, right associativity, only parsing) : debug_class.
Notation "[ cls @ classname => B ]" := (class_app (fun classname => B) cls)
  (at level 150, classname binder, right associativity, only printing) : debug_class.
Example class_app_example_1 := [class_example_1 @ cx => cx = cx].
Example class_app_example_2 := [^(z : Prop) => z = z @ cz => cz = cz].
Example class_app_example_3 := [class_example_1 @ c1 => [class_example_1 @ c2 => c1 = c2]].

Notation "[ ^ ^ ψ @ cclassname => B ]" :=
  (class_app_c (fun cclassname => B) ψ)
  (at level 150, cclassname binder, right associativity) : debug_class.
Example class_app_c_example_1 {A : Type} (ψ : (A → Prop) → Prop) := 
  [^^ ψ @ cαψ => cαψ].

Notation "x '<class_in>' φ" := (class_in x φ)
  (at level 120, right associativity) : debug_class.
Example class_in_example (x : Prop) := x <class_in> (fun z => z = z).

(* Another `class_in` specifically for classes. All these should be subject to
future refinements... *)
Notation "c '<class_in_fc>^' ψ" := (class_in_c c ψ) 
  (at level 120, right associativity) : debug_class.

(* Might still not work for even more and worse complicated situations.
TODO: generalize to `f α` and name it `class_scope_dup`
*)
Definition class_scope_eq {A : Type} (α : Class.t A) :
  [α @ cz => cz = cz] ↔ [α @ cz1 => [α @ cz2 => cz1 = cz2]].
Admitted.

Open Scope iota_description.

Definition ι_class_scope_eq {A : Type} (α : Class.t A) (f : (A → Prop) → Prop) 
  (g : (A → Prop) → (A → Prop) → Prop) :
  [α @ cα => [ι (fun α => [α @ cα => f cα])
  | ια => [ια @ cια => g cια cα]]]
  ↔
  [ι (fun α => [α @ cα => f cα]) | ια =>
  [ια @ cια => [α @ cα => g cια cα]]]. Admitted.

Close Scope iota_description.

(* **************** *)
(* Definition n10_01_class {A : Type} (φ : Class.t A → Prop) : 
  (∃ x, φ x) = ¬ (∀ x, ¬ φ x). Admitted.  *)

Definition n10_1_class {A : Type} (φ : Class.t A → Prop) (Y : Class.t A) :
  (∀ x, φ x) → φ Y. Admitted.

Definition n10_11_class {A : Type} (Y : Class.t A) (φ : Class.t A → Prop) 
  : φ Y → ∀ x, φ x. Admitted.

Definition n10_14_class {A : Type} (φ ψ : Class.t A → Prop) (Y : Class.t A) : 
  (∀ x, φ x) ∧ (∀ x, ψ x)
  → φ Y ∧ ψ Y.
Admitted.

Definition n10_21_class {A : Type} (φ : Class.t A → Prop) (P : Prop) :
  (∀ x, P → φ x) ↔ (P → (∀ x, φ x)). Admitted.

Definition n10_23_class {A : Type} (φ : Class.t A → Prop) (P : Prop) :
  (∀ x, φ x → P) ↔ ((∃ x, φ x) → P). Admitted.

Definition n10_24_class {A : Type} (φ : Class.t A → Prop) (Y : Class.t A) :
  φ Y → ∃ x, φ x. Admitted.

Definition n13_183_class {A : Type} (X Y : Class.t A) :
  ([X @ cx => [Y @ cy => cx = cy]]) ↔ 
    ([X @ cx => [z @ cz => cx = cz]] 
      <[- z -]> [z @ cz => [Y @ cy => cz = cy]]). Admitted.

Open Scope iota_description.

(* NOTE: here we can see a non-trivial variant involving the scoping...
  and we cannot determine the right representation so far. When it comes to 
  deep embedding, specifying how to automatically determine the `app`somehow
  for different apolications seems to be critical
*)
Definition n14_1_class {A : Type} (φ ψ : Class.t A → Prop) : [ι φ | ιφ => ψ ιφ]
  ↔ ∃ b, (φ x <[- x -]> [x @ cx => [b @ cb => cx = cb]]) 
    ∧ ψ b. Admitted.

(* This is a variant that has never been used so far *)
Definition n14_13_class {B : Type} (A : Class.t B) (φ : Class.t B → Prop) : 
  [ι φ | ιφ => [A @ cA => [ιφ @ cιφ => cA = cιφ]]] 
  ↔ [ι φ | ιφ => [ιφ @ cιφ => [A @ cA => cιφ = cA]]]. Admitted.

(* Another possible variant, which is actually used... This is why such
  variants are annoying *)
Definition n14_13_class_alt {B : Type} (A : B → Prop) (φ : Class.t B → Prop) : 
  [ι φ | ιφ => [ιφ @ cιφ => A = cιφ]]
  ↔ [ι φ | ιφ => [ιφ @ cιφ => cιφ = A]]. Admitted.

Close Scope iota_description.

(* **************** *)
Definition n20_01 (ψ : Prop → Prop) (f : (Prop → Prop) → Prop) :
  ([^z => ψ z @ cψ => f cψ])
  = (∃ φ : Order 1, (φ x <[- x -]> ψ x) ∧ f φ).
Admitted.

Definition n20_02 (X : Prop) (φ : Prop → Prop) :
  (X <class_in> φ) = φ X.
Admitted.

(* cf. p.188: The definition of `Cls` is also a "partial definition" and
should be considered in specific context.
Also: "we have merely defined certain *uses* of such expressions..."
we can see explicitly that for all definitions in Principia it is allowed
to add more "uses" to the expressioins whenever we want 
*)
Definition n20_03 {A : Type} :
  Cls = (^ (α : A → Prop) => (∃ (φ : A → Prop), 
    [^ (z : A) => φ z @ cφ => α = cφ])).
Admitted.

(* We won't define a notation for this abbreviation for now *)
Definition n20_04 {A : Type} (X Y : A) (α : Class.t A) :
  ([α @ cα => X <class_in> cα] 
    ∧ [α @ cα => Y <class_in> cα])
  = 
  ([α @ cα => X <class_in> cα] 
  ∧ [α @ cα => Y <class_in> cα]).
Admitted.

Definition n20_05 {A : Type} (X Y Z : A) (α : Class.t A):
  ([α @ cα => X <class_in> cα] 
    ∧ [α @ cα => Y <class_in> cα]
    ∧ [α @ cα => Z <class_in> cα])
  = (([α @ cα => X <class_in> cα] 
      ∧ [α @ cα => Y <class_in> cα]) 
    ∧ [α @ cα => Z <class_in> cα]).
Admitted.

(* We won't define a notation for this abbreviation for now *)
Definition n20_06 {A : Type} (X : A) (α : Class.t A) :
  (~ [α @ cα => X <class_in> cα]) 
  = (~ [α @ cα => X <class_in> cα]).
Admitted.

Definition n20_07 {A : Type} (f : (A → Prop) → Prop) :
  (* NOTE: we can see here `φ` has been unsatisfying: it is not defined with \
  `Order` anymore... maybe we need to adjust `A` in the future to make it compatible
  with `Order`s 
  If we change `A` to `Order x`, it means we don't allow future symbols other than class
  which has been a very annoying ambiguity
  *)
  (∀ (α : Class.t A), [α @ cα => f cα])
  = (∀ φ : (A → Prop), [^z => φ z @ cφ => f cφ]).
Admitted.

Definition n20_071 {A : Type} (f : (A → Prop) → Prop) :
  (∃ (α : Class.t A), [α @ cα => f cα])
  = (∃ φ : (A → Prop), [^z => φ z @ cφ => f cφ]).
Admitted.

Open Scope iota_description.

Definition n20_072 {A : Type} (X : A) (φ f : (A → Prop) → Prop) :
  [ι φ | ιφ => f ιφ]
    = (∃ gamma : Class.t A, ([α @ cα => φ cα] 
      <[- (α : Class.t A) -]> (α = gamma)) 
      ∧ ([gamma @ cgamma => f cgamma])).
Admitted.

Close Scope iota_description.

Definition n20_08 {A : Type} (f : ((A → Prop) → Prop) → Prop)
  (ψ : (A → Prop) → Prop) :
  [^^ ψ @ cαψ => f cαψ]
  = ((∃ φ : (A → Prop) → Prop, [α @ cα => ψ cα] 
      <[- (α : Class.t A) -]> [α @ cα => φ cα]
    ∧ f φ)).
Admitted.

Definition n20_081 {A : Type} (α : Class.t A) (ψ : (A → Prop) → Prop) :
  (α <class_in_fc>^ ψ) = [α @ cα => ψ cα].
Admitted.

(* **************** *)
Theorem n20_1 (ψ : Prop → Prop) (f : (Prop → Prop) → Prop) :
  ([^ (z : Prop) => ψ z @ zψ => f zψ]) ↔ ∃ φ : Order 1, 
    (φ x <[- x -]> ψ x) ∧ f φ.
Proof.
  pose proof (n4_2 ([^ (z : Prop) => ψ z @ zψ => f zψ])) as n4_2.
  now rewrite -> n20_01 in n4_2 at 2.
Qed.

Theorem n20_11 (ψ χ : Prop → Prop) (f : (Prop → Prop) → Prop) :
  (ψ x <[- x -]> χ x) → (([^z => ψ z @ cψ => f cψ]) 
    ↔ ([^z => χ z @ cχ => f cχ])).
Proof.
  (* TOOLS *)
  set (X := Intro_individual "x").
  set (Iφ := Intro_pred "φ" 1).
  (* ******** *)
  assert (S1 : (ψ x <[- x -]> χ x) → ((φ x <[- x -]> ψ x)
      <[- φ -]> (φ x <[- x -]> χ x))).
  {
    pose proof (n4_86 (ψ X) (χ X) (Iφ X)) as n4_86.
    setoid_rewrite -> n4_21 in n4_86 at 3.
    setoid_rewrite -> n4_21 in n4_86 at 4.
    pose proof (n10_11 X (fun x => ψ x ↔ χ x 
      → (Iφ x ↔ ψ x) ↔ (Iφ x ↔ χ x))) as n10_11a.
    MP n10_11a n4_86.
    pose proof (n10_27 (fun x => ψ x ↔ χ x)
      (fun x => (Iφ x ↔ ψ x) ↔ (Iφ x ↔ χ x))) as n10_27.
    MP n10_27 n10_11a.
    pose proof (n10_271 (fun x => Iφ x ↔ ψ x)
      (fun x => Iφ x ↔ χ x)) as n10_271.
    Syll_as n10_27 n10_271 Sy1.
    pose proof (n10_11_pred Iφ (fun φ => (φ z <[- z -]> ψ z) 
      ↔ φ z <[- z -]> χ z)) as n10_11b.
    clear n4_86 n10_11a n10_27 n10_271.
    now Syll_as Sy1 n10_11b S1.
  }
  assert (S2 : (ψ x <[- x -]> χ x) 
    → (((φ x <[- x -]> ψ x) ∧ f φ)
      <[- φ -]> ((φ x <[- x -]> χ x) ∧ f φ))).
  {
    intro Hp.
    pose proof (S1 Hp) as S1.
    pose proof (n4_36 (Iφ x <[- x -]> ψ x) (Iφ x <[- x -]> χ x) 
      (f Iφ)) as n4_36.
    pose proof (n10_11_pred Iφ (fun φ => 
      (φ x <[- x -]> ψ x) ↔ (φ x <[- x -]> χ x)
        → (φ x <[- x -]> ψ x) ∧ f φ↔ (φ x <[- x -]> χ x) ∧ f φ)) 
        as n10_11.
    MP n10_11 n4_36.
    pose proof (n10_27_pred (fun φ => (φ x<[- x -]> ψ x) 
      ↔ (φ x <[- x -]> χ x))
      (fun φ => (φ x <[- x -]> ψ x) ∧ f φ
        ↔ (φ x <[- x -]> χ x) ∧ f φ)) as n10_27.
    MP n10_27 n10_11.
    now MP n10_27 S1.
  }
  assert (S3 : (ψ x <[- x -]> χ x) 
    → ((∃ φ : Order 1, (φ x <[- x -]> ψ x) ∧ f φ)
      ↔ (∃ φ : Order 1, (φ x <[- x -]> χ x) ∧ f φ))).
  {
    intro Hp.
    pose proof (S2 Hp) as S2.
    pose proof (n10_281_pred
      (fun φ => (φ x <[- x -]> ψ x) ∧ f φ)
      (fun φ => (φ x <[- x -]> χ x) ∧ f φ)) as n10_281.
    clear S1.
    now MP n10_281 S2.
  }
  assert (S4 : (ψ x <[- x -]> χ x)
    → (([^z => ψ z @ cψ => f cψ]) 
      ↔ ([^z => χ z @ cχ => f cχ]))).
  {
    intro Hp.
    pose proof (S3 Hp) as S3.
    now repeat rewrite <- n20_1 in S3.
  }
  exact S4.
Qed.

Theorem n20_111 (f g : (Prop → Prop) → Prop) : 
  (f φ <[- φ -]> g φ)
  → (([^z => φ z @ cz => f cz]) <[- φ -]> ([^z => φ z @ cz => g cz])).
Proof.
  (* TOOLS *)
  set (Iφ := Intro_pred "φ" 1).
  set (Iψ := Intro_pred "ψ" 1).
  (* ******** *)
  assert (S1 : (f φ <[- φ -]> g φ)
    → ((Iφ x <[- x -]> Iψ x) ∧ f Iψ
      ↔ (Iφ x <[- x -]> Iψ x) ∧ g Iψ)).
  {
    (* We don't use Fact3_45 here as n4_36 suits better *)
    pose proof (n4_36 (f Iψ) (g Iψ) (Iφ x<[-x : Prop-]>Iψ x)) 
      as n4_36.
    setoid_rewrite -> n4_3 in n4_36 at 3.
    setoid_rewrite -> n4_3 in n4_36 at 5.
    pose proof (n10_1_pred (fun φ => f φ ↔ g φ) Iψ)
      as n10_1.
    now Syll_as n10_1 n4_36 S1.
  }
  assert (S2 : (f φ <[- φ -]> g φ)
    → (((Iφ x <[- x -]> ψ x) ∧ f ψ)
      <[- ψ -]> ((Iφ x <[- x -]> ψ x) ∧ g ψ))).
  {
    pose proof (n10_11_pred
      Iψ (fun ψ => (f φ <[- φ -]> g φ) 
      → (((Iφ x <[- x -]> ψ x) ∧ f ψ)
        ↔ ((Iφ x <[- x -]> ψ x) ∧ g ψ)))) as n10_11.
    MP n10_11 S1.
    now rewrite -> n10_21_pred in n10_11.
  }
  assert (S3 : (f φ <[- φ -]> g φ)
    → ((∃ ψ, (Iφ x <[- x -]> ψ x) ∧ f ψ)
      ↔ (∃ ψ, (Iφ x <[- x -]> ψ x) ∧ g ψ))).
  {
    intro Hp.
    pose proof (S2 Hp) as S2.
    clear S1.
    pose proof (n10_281_pred
      (fun ψ => (Iφ x <[- x -]> ψ x) ∧ f ψ)
      (fun ψ => (Iφ x <[- x -]> ψ x) ∧ g ψ)) as n10_281.
    now MP n10_281 S2.
  }
  assert (S4 : (f φ <[- φ -]> g φ)
    → (([^z => Iφ z @ cz => f cz]) 
      ↔ ([^z => Iφ z @ cz => g cz]))).
  {
    setoid_rewrite -> n4_21 in S3 at 3.
    setoid_rewrite -> n4_21 in S3 at 4.
    now repeat setoid_rewrite <- n20_1 in S3.
  }
  assert (S5 : (f φ <[- φ -]> g φ)
    → (([^z => φ z @ cz => f cz]) 
      <[- φ -]> ([^z => φ z @ cz => g cz]))).
  {
    pose proof n10_11_pred.
    pose proof (n10_11_pred Iφ
      (fun φ0 => (f φ<[-φ : Prop → Prop-]>g φ)
        → ([^z => φ0 z @ zψ => f zψ])
          ↔ ([^z => φ0 z @ zψ => g zψ]))) as n10_11.
    MP n10_11 S4.
    now rewrite -> n10_21_pred in n10_11.
  }
  exact S5.
Qed.

Theorem n20_112 (f : (Prop → Prop) → Prop) : ∃ g : (Prop → Prop) → Prop, 
  ([^z => φ z @ cφ => f cφ]) <[- φ -]> ([^z => φ z @ cφ => g cφ]).
Proof.
  (* TOOLS *)
  set (Ig := Intro_pred "g" 2).
  (* ******** *)
  assert (S1 : ∃ g, f φ <[- φ -]> g φ).
  { apply n12_1_pred. }
  assert (S2 : ∃ g : (Prop → Prop) → Prop, 
    ([^z => φ z @ cφ => f cφ]) <[- φ -]> ([^z => φ z @ cφ => g cφ])).
  {
    pose proof (n20_111 f Ig) as n20_111.
    pose proof (n10_11_pred_1 Ig (fun g => (f φ <[- φ -]> g φ)
      → ([^z => φ z @ cφ => f cφ]) <[- φ -]>
        ([^z => φ z @ cφ => g cφ]))) as n10_11.
    MP n10_11 n20_111.
    pose proof (n10_28_pred_1 (fun g => (f φ <[- φ -]> g φ))
      (fun g => ([^z => φ z @ cφ => f cφ]) 
        <[- φ -]> ([^z => φ z @ cφ => g cφ]))) as n10_28.
    MP n10_28 n10_11.
    now MP n10_28 S1.
  }
  exact S2.
Qed.

(* This is the class version of n12_1. As we currently cannot correctly 
  implement n12_1, our implementation in n20_12 isn't nice as well *)
Theorem n20_12 (ψ : Prop → Prop) (f : (Prop → Prop) → Prop): 
  ∃ φ : Order 1, (φ x <[- x -]> ψ x) ∧
    (([^z => ψ z @ cψ => f cψ]) ↔ ([^z => φ z @ cφ => f cφ])).
Proof.
  pose proof n20_11 as n20_11.
  (* unprovable *)
Admitted.

Theorem n20_13 (ψ χ : Prop → Prop) : (ψ x <[- x -]> χ x)
  → ([^z => ψ z @ cψ => ([^z => χ z @ cχ => cψ = cχ])]).
Proof.
  (* TOOLS *)
  set (Iφ := Intro_pred "φ" 1).
  set (X := Intro_individual "x").
  (* ******** *)
  assert (S1 : ([^z => ψ z @ cψ => [^z => χ z @ cχ => cψ = cχ]])
    ↔ ∃ φ, (ψ x <[- x -]> φ x) ∧ ([^z => χ z @ cχ => φ = cχ])).
  {
    pose proof (n20_1 ψ (fun cψ => [^z => χ z @ cχ => cψ = cχ])) 
      as n20_1.
    now setoid_rewrite -> n4_21 in n20_1 at 2.
  }
  assert (S2 : ([^z => ψ z @ cψ => [^z => χ z @ cχ => cψ = cχ]])
    ↔ ∃ φ θ, (ψ x <[- x -]> φ x) ∧ (χ x <[- x -]> θ x)
      ∧ (φ = θ)).
  {
    (* We have to generalize the Iφ to fit in the proof *)
    pose proof (n20_1 χ (fun cz => Iφ = cz)) as n20_1.
    pose proof (n4_36 ([^z => χ z @ cχ => Iφ = cχ])
      (∃ θ : Order 1, (θ x <[- x -]> χ x)
        ∧ Iφ = θ)
      (ψ x <[- x -]> Iφ x)) as n4_36.
    MP n4_36 n20_1.
    pose proof (n10_11_pred Iφ (fun φ =>
      (([^z => χ z @ cχ => φ = cχ])
          ∧ (ψ x <[- x -]> φ x))
          ↔ ((∃ θ : Order 1, (θ x <[- x -]> χ x)
          ∧ φ = θ) ∧ (ψ x <[- x -]> φ x)))) 
      as n10_11.
    MP n10_11 n4_36.
    pose proof (n10_281_pred
      (fun φ => ([^z => χ z @ cχ => φ = cχ])
        ∧ (ψ x <[- x -]> φ x))
      (fun φ => (∃ θ : Order 1, (θ x <[- x -]> χ x)
        ∧ φ = θ) ∧  (ψ x <[- x -]> φ x))) 
      as n10_281.
    MP n10_281 n10_11.
    setoid_rewrite -> n4_3 in n10_281 at 2.
    setoid_rewrite -> n4_3 in n10_281 at 4.
    setoid_rewrite <- n10_35_pred in n10_281.
    setoid_rewrite -> n4_21 in n10_281 at 4.
    now rewrite -> n10_281 in S1.
  }
  assert (S3 : (ψ x <[- x -]> χ x)
    → ∃ φ, (ψ x <[- x -]> φ x) ∧ (χ x <[- x -]> φ x)).
  {
    pose proof (n12_1 ψ) as n12_1a.
    pose proof (n12_1 χ) as n12_1b.
    (* Unprovable: we cannot merge the `∃` for now *)
    pose proof n10_321 as n10_321.
    admit.
  }
  assert (S4 : (ψ x <[- x -]> χ x) →
    ∃ φ θ, (ψ x <[- x -]> φ x)
      ∧ (χ x <[- x -]> θ x) ∧ (φ = θ)).
  {
    pose proof (n13_195_pred χ (fun f => f X)) as n13_195.
    pose proof (n10_11 X (fun x => 
      (∃ f, f = χ ∧ f x) ↔ χ x)) as n10_11.
    MP n10_11 n13_195.
    setoid_rewrite <- n10_11 in S3 at 2.
    setoid_rewrite -> n4_3 in S3 at 2.
    setoid_rewrite <- n10_33 in S3.
    setoid_rewrite <- n4_3 in S3 at 2.
    (* unprovable: no theorem for `<->`'s conversion with `exists` *)
    pose proof n10_35_pred as _n10_35.
    (* setoid_rewrite <- n10_35_pred in S3. *)
    admit.
  }
  assert (S5 : (ψ x <[- x -]> χ x)
    → ([^z => ψ z @ cψ => ([^z => χ z @ cχ => cψ = cχ])])).
  { now rewrite <- S2 in S4. }
  exact S5.
Admitted.

Theorem n20_14 (ψ χ : Prop → Prop) :
  ([^z => ψ z @ cψ => ([^z => χ z @ cχ => cψ = cχ])])
  → (ψ x <[- x -]> χ x).
Proof.
  assert (S1 : [^z => ψ z @ cψ => [^z => χ z @ cχ => cψ = cχ]]
    ↔ (∃ φ, (ψ x <[- x -]> φ x) 
      ∧ [^z => χ z @ cχ => φ = cχ])).
  {
    pose proof (n20_1 ψ (fun cz => [^z => χ z @ cχ => cz = cχ])) 
      as n20_1.
    setoid_rewrite <- n4_21 in n20_1 at 2.
    exact n20_1.
  }
  assert (S2 : [^z => ψ z @ cψ => [^z => χ z @ cχ => cψ = cχ]]
    ↔ (∃ (φ θ : Prop → Prop), (ψ x <[- x -]> φ x) 
      ∧ (χ x <[- x -]> θ x) ∧ (φ = θ))).
  {
    setoid_rewrite -> n20_1 in S1 at 2.
    setoid_rewrite -> n4_21 in S1 at 3.
    now setoid_rewrite <- n10_35_pred in S1.
  }
  assert (S3 : [^z => ψ z @ cψ => [^z => χ z @ cχ => cψ = cχ]]
    ↔ (∃ φ, (ψ x <[- x -]> φ x) ∧ (χ x <[- x -]> φ x))).
  {
    setoid_rewrite -> n10_35_pred in S2.
    setoid_rewrite -> n4_3 in S2 at 4.
    (* simplification: some tiny trick when `setoid_rewrit` doesn't immediately
      work *)
    pose proof n13_195_pred as n13_195.
    setoid_rewrite <- n13_16_pred in n13_195.
    now setoid_rewrite -> n13_195 in S2.
  }
  assert (S4 : [^z => ψ z @ cψ => [^z => χ z @ cχ => cψ = cχ]]
    → (ψ x <[- x -]> χ x)).
  {
    (* simplification *)
    intro Hp.
    destruct S3 as [S3 _].
    pose proof (S3 Hp) as S3.
    pose proof n10_322 as n10_322.
    (* unprovable: we don't have rules to apply `∃` in this way *)
    admit.
  }
  exact S4.
Admitted.

Theorem n20_15 (ψ χ : Prop → Prop) : (ψ x <[- x -]> χ x)
  ↔ ([^z => ψ z @ cψ => ([^z => χ z @ cχ => cψ = cχ])]).
Proof.
  pose proof (n20_13 ψ χ) as n20_13.
  pose proof (n20_14 ψ χ) as n20_14.
  Conj_as n20_13 n20_14 C1.
  now Equiv C1.
Qed.

Theorem n20_151 (ψ : Prop → Prop) : 
  ∃ φ : Order 1, [^z => ψ z @ cψ => 
    [^z => φ z @ cφ => cψ = cφ]].
Proof.
  (* TOOLS *)
  set (Iφ := Intro_pred "φ" 1).
  (* ******** *)
  assert (S1 : (ψ x <[- x -]> Iφ x) → [^z => ψ z @ cψ => 
    [^z => Iφ z @ cφ => cψ = cφ]]).
  { apply n20_15. }
  assert (S2 : (∃ φ, ψ x <[- x -]> φ x) 
    → (∃ φ, [^z => ψ z @ cψ => [^z => φ z @ cφ => cψ = cφ]])).
  {
    pose proof (n10_11_pred Iφ (fun φ =>
      (ψ x <[- x -]> φ x) → [^z => ψ z @ cψ => 
        [^z => φ z @ cφ => cψ = cφ]])) as n10_11.
    MP n10_11 S1.
    pose proof (n10_28_pred
      (fun φ => ψ x <[- x -]> φ x)
      (fun φ => [^z => ψ z @ cψ => [^z => φ z @ cφ => cψ = cφ]])) 
      as n10_28.
    now MP n10_28 n10_11.
  }
  assert (S3 : ∃ φ : Order 1, [^z => ψ z @ cψ => 
    [^z => φ z @ cφ => cψ = cφ]]).
  {
    pose proof (n12_1 ψ) as n12_1.
    (* Surprisingly, we can use n12_1 here *)
    now MP S2 n12_1.
  }
  exact S3.
Qed.

Theorem n20_16 (ψ : Prop → Prop) (f : (Prop → Prop) → Prop) :
  ∃ φ : Order 1, [^z => ψ z @ cψ => f cψ] ↔ 
    [^z => φ z @ cφ => f cφ].
Proof.
  pose proof (n20_12 ψ f) as n20_12.
  pose proof (n10_5_pred
    (fun φ => φ x <[- x -]> ψ x)
    (fun φ => ([^z => ψ z @ cψ => f cψ]) 
      ↔ ([^z => φ z @ cφ => f cφ]))) as n10_5.
  MP n10_5 n20_12.
  (* simplification *)
  now destruct n10_5.
Qed.

Theorem n20_17 (ψ : Prop → Prop) (f : (Prop → Prop) → Prop) :
  ∀ φ, [^z => ψ z @ cψ => f cψ] → 
    [^z => φ z @ cφ => f cφ].
Proof.
  pose proof n20_16 as n20_16.
  pose proof n10_1 as n10_1.
  (* unprovable *)
Admitted.

Theorem n20_18 (φ ψ : Prop → Prop) (f : (Prop → Prop) → Prop) : 
  [^z => φ z @ cφ => [^z => ψ z @ cψ => cφ = cψ]]
  → ([^z => φ z @ cφ => f cφ] ↔ [^z => ψ z @ cψ => f cψ]).
Proof.
  pose proof (n20_11 φ ψ f) as n20_11.
  now rewrite -> n20_15 in n20_11.
Qed.

Theorem n20_19 (ψ χ : Prop → Prop) : 
  [^z => ψ z @ cψ => [^z => χ z @ cχ => cψ = cχ]]
  ↔ (∀ f : (Order 1 → Prop), [^z => ψ z @ cψ => f cψ]
    → [^z => χ z @ cχ => f cχ]).
Proof.
  (* TOOLS *)
  set (λ P0 Q0 : Prop, eq_to_equiv (P0 ↔ Q0) ((P0 → Q0) ∧ (Q0 → P0)) 
    (Equiv4_01 P0 Q0))
  as Equiv4_01a.
  set (X := Intro_individual "x").
  set (If := Intro_pred "f" 2).
  set (Iφ := Intro_pred "φ" 1).
  set (Iθ := Intro_pred "θ" 1).
  (* ******** *)
  assert (S1 : [^z => ψ z @ cψ => [^z => χ z @ cχ => cψ = cχ]]
    → (∀ f, [^z => ψ z @ cψ => f cψ] →
      [^z => χ z @ cχ => f cχ])).
  {
    pose proof (n20_18 ψ χ If) as n20_18.
    pose proof (n10_11_pred_1 If (fun f =>
      [^z => ψ z @ cψ => [^z => χ z @ cχ => cψ = cχ]]
        → ([^z => ψ z @ cψ => f cψ] ↔ [^z => χ z @ cχ => f cχ]))) as n10_11.
    MP n10_11 n20_18.
    rewrite -> n10_21_pred_1 in n10_11.
    (* simplification *)
    intros Hp f.
    pose proof (n10_11 Hp f) as n10_11.
    now destruct n10_11.
  }
  assert (S2 : ((Iφ x <[- x -]> ψ x) ∧ (Iθ x <[- x -]> χ x)
      ∧ ([^z => ψ z @ cψ => If cψ] → [^z => χ z @ cχ => If cχ]))
    → ([^z => Iφ z @ cφ => If cφ] → [^z => Iθ z @ cθ => If cθ])).
  {
    (* simplification *)
    intro Hp.
    destruct Hp as [Hp1 [Hp2 Hp3]].
    rewrite -> n20_15 in Hp1.
    rewrite -> n20_15 in Hp2.
    pose proof (n20_18 Iφ ψ If) as n20_18a.
    MP n20_18a Hp1.
    pose proof (n20_18 Iθ χ If) as n20_18b.
    MP n20_18b Hp2.
    rewrite <- n20_18a in Hp3.
    now setoid_rewrite <- n20_18b in Hp3.
  }
  assert (S3 : (((Iφ x <[- x -]> ψ x) ∧ (Iθ x <[- x -]> χ x))
      ∧ (∀ f, [^z => ψ z @ cψ => f cψ] → [^z => χ z @ cχ => f cχ]))
    → ∀ f, ([^z => Iφ z @ cφ => f cφ] → [^z => Iθ z @ cθ => f cθ])).
  {
    pose proof (n10_11_pred_1 If (fun f => 
      ((Iφ x <[- x -]> ψ x) ∧ (Iθ x <[- x -]> χ x)
        ∧ ([^z => ψ z @ cψ => f cψ] → [^z => χ z @ cχ => f cχ]))
      → ([^z => Iφ z @ cφ => f cφ] → [^z => Iθ z @ cθ => f cθ]))) 
      as n10_11.
    MP n10_11 S2.
    pose proof (n10_27_pred_1
      (fun f => (Iφ x <[- x -]> ψ x) ∧ (Iθ x <[- x -]> χ x)
        ∧ ([^z => ψ z @ cψ => f cψ] → [^z => χ z @ cχ => f cχ]))
      (fun f => [^z => Iφ z @ cφ => f cφ] → [^z => Iθ z @ cθ => f cθ])) 
      as n10_27.
    MP n10_27 n10_11.
    setoid_rewrite <- n4_32 in n10_27 at 1.
    setoid_rewrite -> n4_3 in n10_27 at 1.
    rewrite -> n10_33_pred_1 in n10_27.
    now rewrite <- n4_3 in n10_27.
  }
  assert (S4 : (((Iφ x <[- x -]> ψ x) ∧ (Iθ x <[- x -]> χ x))
      ∧ (∀ f, [^z => ψ z @ cψ => f cψ] → [^z => χ z @ cχ => f cχ]))
    → ((Iφ x <[- x -]> Iφ x) → (Iφ x <[- x -]> Iθ x))).
  {
    (* unprovable: *20.112 seems to be incorrectly used *)
    pose proof n20_112 as n20_112.
    pose proof n10_1 as n10_1.
    admit.
  }
  assert (S5 : (((Iφ x <[- x -]> ψ x) ∧ (Iθ x <[- x -]> χ x))
      ∧ (∀ f, [^z => ψ z @ cψ => f cψ] → [^z => χ z @ cχ => f cχ]))
    → (Iφ x <[- x -]> Iθ x)).
  {
    (* simplification *)
    intro Hp.
    pose proof (S4 Hp) as S4.
    pose proof (n4_2 (Iφ X)) as n4_2.
    pose proof (n10_11 X (fun x => Iφ x ↔ Iφ x)) as n10_11.
    MP n10_11 n4_2.
    now MP S4 n10_11.
  }
  assert (S6 : (((Iφ x <[- x -]> ψ x) ∧ (Iθ x <[- x -]> χ x))
      ∧ (∀ f, [^z => ψ z @ cψ => f cψ] → [^z => χ z @ cχ => f cχ]))
    → (ψ x <[- x -]> χ x)).
  {
    (* *10.301 *10.32 ignored *)
    (* simplification *)
    intros Hp.
    pose proof (S5 Hp) as S5.
    destruct Hp as [Hp1 Hp3].
    destruct Hp1 as [Hp1 Hp2].
    setoid_rewrite -> Hp1 in S5.
    now setoid_rewrite -> Hp2 in S5.
  }
  assert (S7 : (((Iφ x <[- x -]> ψ x) ∧ (Iθ x <[- x -]> χ x))
      ∧ (∀ f, [^z => ψ z @ cψ => f cψ] → [^z => χ z @ cχ => f cχ]))
    → ([^z => ψ z @ cψ => [^z => χ z @ cχ => cψ = cχ]])).
  { now setoid_rewrite -> n20_15 in S6 at 3. }
  assert (S8 : (∃ φ θ, ((φ x <[- x -]> ψ x) ∧ (θ x <[- x -]> χ x)))
      ∧ (∀ f, [^z => ψ z @ cψ => f cψ] → [^z => χ z @ cχ => f cχ])
    → [^z => ψ z @ cψ => [^z => χ z @ cχ => cψ = cχ]]).
  {
    pose proof (n10_11_pred Iθ
      (fun θ =>
          (((Iφ x <[- x -]>ψ x) ∧ θ x <[- x -]> χ x)
        ∧ (∀ f, ([^z => ψ z @ cψ => f cψ])
          → [^z => χ z @ cχ => f cχ])
        → [^z => ψ z @ cψ => [^z => χ z @ cχ => cψ = cχ]]))) 
        as n10_1a.
    MP n10_1a S7.
    pose proof (n10_11_pred Iφ
      (fun φ => forall θ, 
        (((φ x <[- x -]> ψ x) ∧ θ x <[- x -]> χ x)
        ∧ (∀ f, ([^z => ψ z @ cψ => f cψ]) 
          → [^z => χ z @ cχ => f cχ]))
        → [^z => ψ z @ cψ => [^z => χ z @ cχ => cψ = cχ]]))
        as n10_1b.
    MP n10_1b n10_1a.
    setoid_rewrite -> n10_23_pred in n10_1b.
    setoid_rewrite -> n10_23_pred in n10_1b.
    setoid_rewrite -> n4_3 in n10_1b at 1.
    pose proof n10_35 as _n10_35.
    setoid_rewrite -> n10_35_pred in n10_1b.
    setoid_rewrite -> n10_35_pred in n10_1b.
    now rewrite <- n4_3 in n10_1b.
  }
  assert (S9 : (∀ f : (Prop -> Prop) -> Prop, [^z => ψ z @ cψ => f cψ] → [^z => χ z @ cχ => f cχ])
    → [^z => ψ z @ cψ => [^z => χ z @ cχ => cψ = cχ]]).
  {
    pose proof n12_1 as n12_1.
    admit.
  }
  assert (S10 : [^z => ψ z @ cψ => [^z => χ z @ cχ => cψ = cχ]]
    ↔ (∀ f : (Order 1 → Prop), [^z => ψ z @ cψ => f cψ]
      → [^z => χ z @ cχ => f cχ])).
  {
    Conj_as S1 S9 C1.
    (* NOTE: we cannot use Equiv ltac for unknown reason *)
    now setoid_rewrite <- Equiv4_01a in C1.
  }
  exact S10.
Admitted.

Theorem n20_191 (ψ χ : Prop → Prop) : 
  [^z => ψ z @ cψ => [^z => χ z @ cχ  => cψ = cχ]]
  ↔ ∀ f : (Order 1 → Prop), [^z => ψ z @ cψ => 
    [^z => χ z @ cχ => f cψ  ↔ f cχ]].
Proof.
  (* *20.18 ignored *)
  (* unprovable: the `<->` generated has to go pass the scopes *)
  pose proof (n20_19 ψ χ) as n20_19a.
  pose proof (n20_19 χ ψ) as n20_19b.
  pose proof n10_22 as n10_22.
Admitted.

Theorem n20_2 (φ : Prop → Prop) : [^z => φ z @ cφ1 => 
  [^z => φ z @ cφ2 => cφ1 = cφ2]].
Proof.
  (* TOOLS *)
  set (X := Intro_individual "x").
  (* ******** *)
  assert (S1 : [^z => φ z @ cφ1 => 
    [^z => φ z @ cφ2 => cφ1 = cφ2]] ↔ (φ x <[- x -]> φ x)).
  {
    pose proof (n20_15 φ φ) as n20_15.
    now rewrite -> n4_21 in n20_15.
  }
  assert (S2 : [^z => φ z @ cφ1 => [^z => φ z @ cφ2 => cφ1 = cφ2]]).
  {
    destruct S1 as [_ S1].
    pose proof (n4_2 (φ X)) as n4_2.
    pose proof (n10_11 X (fun x => φ x ↔ φ x)) as n10_11.
    MP n10_11 n4_2.
    now MP S1 n10_11.
  }
  exact S2.
Qed.

Theorem n20_21 (φ ψ : Prop → Prop) : [^z => φ z @ cφ => 
  [^z => ψ z @ cψ => cφ = cψ]] ↔ [^z => ψ z @ cψ => 
  [^z => φ z @ cφ => cψ = cφ]].
Proof.
  pose proof (n20_15 φ ψ) as n20_15a.
  pose proof (n20_15 ψ φ) as n20_15b.
  pose proof (n10_32 φ ψ) as n10_32.
  now rewrite -> n20_15a, -> n20_15b in n10_32.
Qed.

(* This is a custom alternative for convinient reconstruction in our code *)
Definition n20_21_alt {A : Type} (α β : Class.t A) :
  [α @ cα => [β @ cβ => cα = cβ]]
  ↔ [β @ cβ => [α @ cα => cβ = cα]].
Admitted.

Theorem n20_22 (φ ψ χ : Prop → Prop) : 
  ([^z => φ z @ cφ => [^z => ψ z @ cψ => cφ = cψ]] 
    ∧ [^z => ψ z @ cψ => [^z => χ z @ cχ => cψ = cχ]])
  → [^z => φ z @ cφ => [^z => χ z @ cχ => cφ = cχ]].
Proof.
  pose proof (n20_15 φ ψ) as n20_15a.
  pose proof (n20_15 ψ χ) as n20_15b.
  pose proof (n20_15 φ χ) as n20_15c.
  pose proof (n10_301 φ ψ χ) as n10_301.
  now rewrite -> n20_15a, -> n20_15b, -> n20_15c in n10_301.
Qed.

Theorem n20_23 (φ ψ χ : Prop → Prop) : 
  ([^z => φ z @ cφ => [^z => ψ z @ cψ => cφ = cψ]] 
    ∧ [^z => φ z @ cφ => [^z => χ z @ cχ => cφ = cχ]])
  → [^z => ψ z @ cψ => [^z => χ z @ cχ => cψ = cχ]].
Proof.
  pose proof (n20_21 φ ψ) as n20_21.
  pose proof (n20_22 ψ φ χ) as n20_22.
  now rewrite <- n20_21 in n20_22.
Qed.

Theorem n20_24 (φ ψ χ : Prop → Prop) : 
  ([^z => ψ z @ cψ => [^z => φ z @ cφ => cψ = cφ]] 
    ∧ [^z => χ z @ cχ => [^z => φ z @ cφ => cχ = cφ]])
  → [^z => ψ z @ cψ => [^z => χ z @ cχ => cψ = cχ]].
Proof.
  pose proof (n20_21 φ χ) as n20_21.
  pose proof (n20_22 ψ φ χ) as n20_22.
  now rewrite -> n20_21 in n20_22.
Qed.

(* 
  NOTE: While class is said to be an "incomplete symbol", the utilization of *10.1 in 
  this proof reveals that Russell might actually want to give class a "type"(as in Rocq) 
  that is beyond the hierarchy of propositions and functions.
  This is also the first proof where we have to provide a "class individual" by
  providing a underlying function for the class
*)
Theorem n20_25 (φ ψ : Prop → Prop) :
  ([α @ cα => [^z => φ z @ cφ => cα = cφ]] <[- α -]>
    [α @ cα => [^z => ψ z @ cψ => cα = cψ]])
  → [^z => φ z @ cφ => [^z => ψ z @ cψ => cφ = cψ]].
Proof.
  (* TOOLS *)
  set (Fα := Intro_pred "Fα" 1).
  set (α := (^z => Fα z)).
  (* ******** *)
  assert (S1 : ([α @ cα => [^z => φ z @ cφ => cα = cφ]] 
      <[- α -]> [α @ cα => [^z => ψ z @ cψ => cα = cψ]])
    → ([^z => φ z @ cφ1 => [^z => φ z @ cφ2 => cφ1 = cφ2]]
     ↔ [^z => φ z @ cφ1 => [^z => ψ z @ cψ => cφ1 = cψ]])).
  {
    pose proof (n10_1_class (fun α => [α @ cα => 
        [^z => φ z @ cφ => cα = cφ]] ↔ 
      [α @ cα => [^z => ψ z @ cψ => cα = cψ]])
      (^z => φ z)) as n10_1.
    exact n10_1.
  }
  assert (S2 : ([α @ cα => [^z => φ z @ cφ => cα = cφ]] 
      <[- α -]> [α @ cα => [^z => ψ z @ cψ => cα = cψ]])
    → [^z => φ z @ cφ => [^z => ψ z @ cψ => cφ = cψ]]).
  {
    (* simplification *)
    intro Hp.
    pose proof (S1 Hp) as S1.
    destruct S1 as [S1 _].
    pose proof (n20_2 φ) as n20_2.
    now MP S1 n20_2.
  }
  assert (S3 : ([α @ cα => [^z => φ z @ cφ => cα = cφ]]
      ∧ [^z => φ z @ cφ => [^z => ψ z @ cψ => cφ = cψ]])
    → [α @ cα => [^z => ψ z @ cψ => cα = cψ]]).
  { apply n20_22. }
  assert (S4 : ([^z => φ z @ cφ => [^z => ψ z @ cψ => cφ = cψ]])
    → ([α @ cα => [^z => φ z @ cφ => cα = cφ]]
      → [α @ cα => [^z => ψ z @ cψ => cα = cψ]])).
  {
    pose proof (Exp3_3 
      ([α @ cα => [^z => φ z @ cφ => cα = cφ]])
      ([^z => φ z @ cφ => [^z => ψ z @ cψ => cφ = cψ]])
      ([α @ cα => [^z => ψ z @ cψ => cα = cψ]]))
      as Exp3_3.
    MP Exp3_3 S3.
    pose proof (Comm2_04
      ([α @ cα => [^z => φ z @ cφ => cα = cφ]])
      ([^z => φ z @ cφ => [^z => ψ z @ cψ => cφ = cψ]])
      ([α @ cα => [^z => ψ z @ cψ => cα = cψ]]))
      as Comm2_04.
    now MP Comm2_04 Exp3_3.
  }
  assert (S5 : ([^z => φ z @ cφ => [^z => ψ z @ cψ => cφ = cψ]]
      ∧ [α @ cα => [^z => ψ z @ cψ => cα = cψ]])
    → ([α @ cα => [^z => φ z @ cφ => cα = cφ]])).
  {
    pose proof (n20_24 ψ φ Fα) as n20_24.
    now setoid_rewrite -> n20_21 in n20_24 at 3.
  }
  assert (S6 : [^z => φ z @ cφ => [^z => ψ z @ cψ => cφ = cψ]]
    → ([α @ cα => [^z => ψ z @ cψ => cα = cψ]]
      → [α @ cα => [^z => φ z @ cφ => cα = cφ]])).
  {
    pose proof (Exp3_3
      ([^z => φ z @ cφ => [^z => ψ z @ cψ => cφ = cψ]])
      ([α @ cα => [^z => ψ z @ cψ => cα = cψ]])
      ([α @ cα => [^z => φ z @ cφ => cα = cφ]])) 
      as Exp3_3.
    now MP Exp3_3 S5.
  }
  assert (S7 : [^z => φ z @ cφ => [^z => ψ z @ cψ => cφ = cψ]]
    → ([α @ cα => [^z => φ z @ cφ => cα = cφ]]
      ↔ [α @ cα => [^z => ψ z @ cψ => cα = cψ]])).
  {
    (* simplification *)
    intro Hp.
    pose proof (S4 Hp) as S4.
    pose proof (S6 Hp) as S6.
    clear S1 S2 S3 S5.
    Conj_as S4 S6 C1.
    now Equiv C1.
  }
  assert (S8 : [^z => φ z @ cφ => [^z => ψ z @ cψ => cφ = cψ]]
    → ([α @ cα => [^z => φ z @ cφ => cα = cφ]]
      <[- α -]> [α @ cα => [^z => ψ z @ cψ => cα = cψ]])).
  {
    pose proof (n10_11_class α
      (fun α => [^z => φ z @ cφ => [^z => ψ z @ cψ => cφ = cψ]]
        → ([α @ cα => [^z => φ z @ cφ => cα = cφ]]
          ↔ [α @ cα => [^z => ψ z @ cψ => cα = cψ]])))
      as n10_11.
    MP n10_11 S7.
    now rewrite -> n10_21_class in n10_11.
  }
  assert (S9 : ([α @ cα => [^z => φ z @ cφ => cα = cφ]] <[- α -]>
      [α @ cα => [^z => ψ z @ cψ => cα = cψ]])
    → [^z => φ z @ cφ => [^z => ψ z @ cψ => cφ = cψ]]).
  {
    Conj_as S2 S8 C1.
    now Equiv C1.
  }
  exact S9.
Qed.

(* TODO in doc: the 1st step of this proof reveals some deeper notation consistency 
  issue... designing a custum representation of these symbols seems to be a interesting
  technical problem 
*)
Theorem n20_3 (X : Prop) (ψ : Prop → Prop ) : 
  ([^z => ψ z @ cψ => X <class_in> cψ]) ↔ ψ X.
Proof.
  (* TOOLS *)
  set (Iφ := Intro_pred "φ" 1).
  (* ******** *)
  assert (S1 : [^z => ψ z @ cψ => X <class_in> cψ]
    ↔ ∃ φ, (ψ y <[- y -]> φ y) 
      ∧ (X <class_in> φ)).
  {
    pose proof (n20_1 ψ (fun cz => X <class_in> cz)) as n20_1.
    now setoid_rewrite -> n4_21 in n20_1 at 2.
  }
  assert (S2 : [^z => ψ z @ cψ => X <class_in> cψ]
    ↔ (∃ φ, (ψ y <[- y -]> φ y) ∧ φ X)).
  { now setoid_rewrite -> n20_02 in S1. }
  assert (S3 : [^z => ψ z @ cψ => X <class_in> cψ]
    ↔ ∃ φ, (ψ y <[- y -]> φ y) ∧ ψ X).
  {
    simpl; simpl in S2.
    pose proof (n10_43 Iφ ψ X) as n10_43.
    pose proof (n10_11_pred Iφ (fun φ =>
      ((φ z <[- z -]> ψ z) ∧ φ X )
      ↔ (φ z <[- z -]>ψ z) ∧ ψ X)) 
      as n10_11.
    MP n10_11 n10_43.
    pose proof (n10_281_pred
      (fun φ => (φ z <[- z -]> ψ z) ∧ φ X)
      (fun φ => (φ z <[- z -]> ψ z) ∧ ψ X)) 
      as n10_281.
    MP n10_281 n10_11.
    setoid_rewrite -> n4_21 in n10_281 at 2.
    setoid_rewrite -> n4_21 in n10_281 at 3.
    now rewrite -> n10_281 in S2.
  }
  assert (S4 : [^z => ψ z @ cψ => X <class_in> cψ]
    ↔ (∃ φ, ψ y <[- y -]> φ y) ∧ ψ X).
  {
    pose proof n10_35 as _n10_35.
    setoid_rewrite -> n4_3 in S3 at 2.
    setoid_rewrite -> n10_35_pred in S3.
    now setoid_rewrite <- n4_3 in S3 at 2.
  }
  assert (S5 : [^z => ψ z @ cψ => X <class_in> cψ]
    ↔ ψ X).
  {
    (* unprovable. *)
    pose proof n12_1.
    admit.
  }
  exact S5.
Admitted.

Definition n20_3_pred (X : Prop -> Prop) (ψ : (Prop -> Prop) → Prop) : 
  ([^z => ψ z @ cψ => X <class_in> cψ]) ↔ ψ X.
Admitted.

Theorem n20_31 (ψ χ : Prop → Prop) : 
  [^z => ψ z @ cψ => [^z => χ z @ cχ => cψ = cχ]]
  ↔ (([^z => ψ z @ cψ => x <class_in> cψ])
    <[- x -]> [^z => χ z @ cχ => x <class_in> cχ]).
Proof.
  pose proof (n20_15 ψ χ) as n20_15.
  setoid_rewrite <- n20_3 in n20_15 at 3.
  setoid_rewrite <- n20_3 in n20_15 at 3.
  now rewrite -> n4_21 in n20_15.
Qed.

Theorem n20_32 (φ : Prop → Prop) :
  [^x => [^z => φ z @ cφ => x <class_in> cφ] @ cz
    => [^z => φ z @ cφ => cz = cφ]].
Proof.
  set (X := Intro_individual "x").
  pose proof (n20_15 (fun x =>
    [^z => φ z @ cφ => x <class_in> cφ]) 
    φ) as n20_15.
  pose proof (n20_3 X φ) as n20_3.
  pose proof (n10_11 X
    (fun x => ([^z => φ z @ cφ => x <class_in> cφ]) ↔ φ x)) 
    as n10_11.
  MP n10_11 n20_3.
  now rewrite -> n20_15 in n10_11.
Qed.

Theorem n20_33 (Fα : Prop → Prop) (φ : Prop → Prop) :
  let α := (^z => Fα z) in
  [α @ cα => [^z => φ z @ cφ => cα = cφ]]
  ↔ ([α @ cα => x <class_in> cα] <[- x -]> φ x).
Proof.
  (* TOOLS *)
  set (α := (^z => Fα z)).
  (* ******** *)
  assert (S1 : [α @ cα => [^z => φ z @ cφ => cα = cφ]]
    ↔ ([α @ cα => x <class_in> cα] 
      <[- x -]> [^z => φ z @ cφ => x <class_in> cφ])).
  {
    pose proof n20_31 as n20_31.
    admit.
  }
  assert (S2 : [α @ cα => [^z => φ z @ cφ => cα = cφ]]
    ↔ ([α @ cα => x <class_in> cα] <[- x -]> φ x)).
  { now setoid_rewrite -> n20_3 in S1. }
  exact S2.
Admitted.

Open Scope formal_impl.

Theorem n20_34 (X Y : Prop) :
  (X = Y) ↔ ([α @ cα => X <class_in> cα]  
    -[ α ]> [α @ cα => Y <class_in> cα]).
Proof.
  (* TOOLS *)
  set (λ f0 : (Prop → Prop) → Prop, eq_to_equiv
    (∀ α, [α @ cα => f0 cα])
    (∀ φ, [^z => φ z @ cφ => f0 cφ])
    (n20_07 f0)) as n20_07a.
  (* ******** *)
  assert (S1 : ([α @ cα => X <class_in> cα]  
      -[ α ]> [α @ cα => Y <class_in> cα])
    ↔ ([^z => φ z @ cφ => X <class_in> cφ] 
      -[ φ ]> [^z => φ z @ cφ => Y <class_in> cφ])).
  {
    pose proof (n4_2 ([α @ cα => X <class_in> cα]  
      -[ α ]> [α @ cα => Y <class_in> cα])) as n4_2.
    simpl; simpl in n4_2.
    simpl in n20_07a.
    (* unprovable: scoping issue *)
    admit.
  }
  assert (S2 : ([α @ cα => X <class_in> cα]  
      -[ α ]> [α @ cα => Y <class_in> cα])
    ↔ (φ X -[ φ ]> φ Y)).
  {
    setoid_rewrite -> n20_3 in S1 at 1.
    now setoid_rewrite -> n20_3 in S1 at 1.
  }
  assert (S3 : ([α @ cα => X <class_in> cα]  
      -[ α ]> [α @ cα => Y <class_in> cα])
    ↔ (X = Y)).
  { now rewrite <- n13_1 in S2. }
  (* simplification... *)
  symmetry.
  exact S3.
Admitted.

(* NOTE: implicit interpretation *)
Theorem n20_35 (X Y : Prop) :
  (X = Y) ↔ ([α @ cα => X <class_in> cα] 
    <[- α -]> [α @ cα => Y <class_in> cα]).
Proof.
  pose proof (n13_11 X Y) as n13_11.
  pose proof n20_3 as _n20_3.
  simpl in _n20_3. simpl.
  setoid_rewrite <- n20_3 in n13_11 at 5.
  simpl in n13_11.
  setoid_rewrite <- n20_3 in n13_11 at 4.
  simpl in n13_11.
  (* unprovable *)  
Admitted.

Theorem n20_4 (Fα : Prop → Prop) :
  let α := (^z => Fα z) in
  ([α @ cα => [Cls @ Cls => cα <class_in> Cls]]) ↔ 
    (∃ (φ : Order 1), [α @ cα => 
    [^z => φ z @ cφ => cα = cφ]]).
Proof.
  (* TOOLS *)
  set (IX := Intro_pred "x" 1).
  set (α := ^z => Fα z).
  (* ******** *)
  pose proof (n20_3_pred IX (fun Fα =>
    ∃ φ, [^z => φ z @ cφ => Fα = cφ])) 
    as n20_3.
  (* unprovable: scoping issue *)
Admitted.

Theorem n20_41 (ψ : Prop → Prop) : [^z => ψ z @ cψ => 
  [Cls @ Cls => cψ <class_in> Cls]].
Proof.
  pose proof (n20_151 ψ) as n20_151.
  now rewrite <- n20_4 in n20_151.
Qed.

(* NOTE: In this proof, `ψ` is associated with `α` in the text without being 
claimed explicitly *)
Theorem n20_42 (Fα : Prop → Prop) : 
  let α := (^z => Fα z) in
    [(^z => [α @ cα => z <class_in> cα])
      @ cz => [α @ cα => cz = cα]].
Proof.
  (* TOOLS *)
  set (X := Intro_individual "x").
  set (Iψ := Intro_pred "ψ" 1).
  set (α := ^z => Fα z).
  (* ******** *)
  assert (S1 : ([^z => Iψ z @ cψ => x <class_in> cψ]) <[- x -]> Iψ x).
  {
    pose proof (n20_3 X Iψ) as n20_3.
    pose proof (n10_11 X (fun x =>
      (([^z => Iψ z @ cψ => x <class_in> cψ]) ↔ Iψ x))) 
      as n10_11.
    now MP n10_11 n20_3.
  }
  assert (S2 : [^x => [^z => Iψ z @ cψ => x <class_in> cψ] @ cz
    => [^x => Iψ x @ cψ => cz = cψ]]).
  {
    pose proof n20_15 as n20_15.
    admit.
  }
  (* TODO: rename the ^z => ψ z into α *)
  admit.
Admitted.

(* TODO: figure out how to express this *)
Theorem n20_43 (α β : Class.t Prop) : 
  [α @ cα => [β @ cβ => cα = cβ]]
    ↔ ([α @ cα => x <class_in> cα] 
      <[- x -]> [β @ cβ => x <class_in> cβ]).
Proof.
  (* TODO: α function conversion *)
  pose proof n20_31 as n20_31.
Admitted.

Open Scope iota_description.

Theorem n20_5 (φ ψ : Prop → Prop) :
  [ι φ | ιφ => [^z => ψ z @ cψ => ιφ <class_in> cψ]]
  ↔ [ι φ | ιφ => ψ ιφ].
Proof.
  assert (S1 : [ι φ | ιφ => [^z => ψ z @ cψ => ιφ <class_in> cψ]]
    ↔ (∃ c, (φ x <[- x -]> (x = c)) ∧ [^z => ψ z @ cψ => c <class_in> cψ])).
  { apply n14_1. }
  assert (S2 : [ι φ | ιφ => [^z => ψ z @ cψ => ιφ <class_in> cψ]]
    ↔ (∃ c, (φ x <[- x -]> (x = c)) ∧ ψ c)).
  { now setoid_rewrite -> n20_3 in S1 at 2. }
  assert (S3 : [ι φ | ιφ => [^z => ψ z @ cψ => ιφ <class_in> cψ]]
    ↔ [ι φ | ιφ => ψ ιφ]).
  { now setoid_rewrite <- n14_1 in S2. }
  exact S3.
Qed.

Theorem n20_51 (φ : Prop → Prop) (B : Prop) :
  [ι φ | ιφ => ιφ = B]
  ↔ ([ι φ | ιφ => [α @ cα => ιφ <class_in> cα]]
    <[- α -]> [α @ cα => B <class_in> cα]).
Proof.
  (* TOOLS *)
  set (Iψ := Intro_pred "ψ" 1).
  set (α := (^z => Iψ z)).
  (* ******** *)
  assert (S1 : ([ι φ | ιφ => [^z => Iψ z @ cψ => ιφ <class_in> cψ]]
      ↔ [^z => Iψ z @ cψ => B <class_in> cψ])
    ↔ ([ι φ | ιφ => Iψ ιφ] ↔ Iψ B)).
  {
    pose proof (n20_5 φ Iψ) as n20_5.
    pose proof (n20_3 B Iψ) as n20_3.
    pose proof n4_86 as _n4_86.
    pose proof (n4_86
      ([ι φ | ιφ => [^z => Iψ z @ cψ => ιφ <class_in> cψ]])
      ([ι φ | ιφ => Iψ ιφ])
      ([^z => Iψ z @ cψ => B <class_in> cψ])) 
      as n4_86.
    MP n4_86 n20_5.
    now setoid_rewrite -> n20_3 in n4_86 at 2.
  }
  (* NOTE: here is an interesting conflict: we are generalizing both on a class made
    out of `ψ` and `ψ` itself in different parts of a proposition *)
  assert (S2 : ([ι φ | ιφ => [α @ cα => ιφ <class_in> cα]]
      <[- α -]> [α @ cα => B <class_in> cα])
    ↔ ([ι φ | ιφ => ψ ιφ] <[- ψ -]> ψ B)).
  {
    (* unprovable: we're missing theorem of the form of
      `(∀ x, φ x ↔ P) → ((∀ x, φ x) ↔ P)`
      destructing the equivalence does the work, but become extremely tedious *)
    pose proof (n10_11_class α (fun α =>
      ([ι φ | ιφ => [α @ cα => ιφ <class_in> cα]]
        ↔ [α @ cα => B <class_in> cα])
      ↔ ([ι φ | ιφ => Iψ ιφ] ↔ Iψ B))) as n10_11_class.
    MP n10_11_class S1.
    pose proof n10_11_pred as _n10_11_pred.
    admit.
  }
  assert (S3 : ([ι φ | ιφ => [α @ cα => ιφ <class_in> cα]]
      <[- α -]> [α @ cα => B <class_in> cα])
    ↔ [ι φ | ιφ => ιφ = B]).
  { now setoid_rewrite <- n14_17 in S2. }
  assert (S4 : [ι φ | ιφ => ιφ = B]
    ↔ ([ι φ | ιφ => [α @ cα => ιφ <class_in> cα]]
      <[- α -]> [α @ cα => B <class_in> cα])).
  { now rewrite -> n4_21 in S3. }
  exact S4.
Admitted.

Theorem n20_52 (φ : Prop → Prop) : [ιE φ]
  ↔ (∃ b, [ι φ | ιφ => [α @ cα =>
    (ιφ <class_in> cα)]]
    <[- α -]> [α @ cα => b <class_in> cα]).
Proof.
  (* TOOLS *)
  set (B := Intro_individual "b").
  (* ******** *)
  assert (S1 : (∃ b : Prop, [ι φ | ιφ => ιφ = b])
    ↔ ∃ b : Prop, ([ι φ | ιφ => [α @ cα => 
      ιφ <class_in> cα]] <[- α -]> 
        [α @ cα => b <class_in> cα])).
  {
    pose proof (n20_51 φ B) as n20_51.
    pose proof (n10_11 B (fun b =>
      ([ι φ | ιφ => ιφ = b])
        ↔ ([ι φ | ιφ => [α @ cα => ιφ <class_in> cα]])
          <[- α -]>([α @ cα => b <class_in> cα]))) 
      as n10_11.
    MP n10_11 n20_51.
    pose proof (n10_281 
      (fun b => [ι φ | ιφ => ιφ = b])
      (fun b => ([ι φ | ιφ => [α @ cα => ιφ <class_in> cα]])
        <[- α -]> ([α @ cα => b <class_in> cα])))
      as n10_281.
    now MP n10_281 n10_11.
  }
  assert (S2 : [ιE φ]
    ↔ (∃ b, [ι φ | ιφ => [α @ cα =>
      (ιφ <class_in> cα)]]
      <[- α -]> [α @ cα => b <class_in> cα])).
  { now rewrite <- n14_204 in S1. }
  exact S2.
Qed.

Theorem n20_53 (Fα : Prop → Prop) (φ : (Prop → Prop) → Prop) : 
  let α := (^z => Fα z) in
  ([β @ cβ => [α @ cα => cβ = cα]]
    -[ β ]> [β @ cβ => φ cβ])
      ↔ [α @ cα => φ cα].
Proof.
  (* TOOLS *)
  set (Fβ := Intro_pred "β" 1).
  set (α := ^z => Fα z).
  set (β := ^z => Fβ z).
  (* ******** *)
  assert (S1 : ([β @ cβ => [α @ cα => cβ = cα]]
      -[ β ]> [β @ cβ => φ cβ])
    → ([α @ cα => cα = cα]
      → [α @ cα => φ cα])).
  {
    setoid_rewrite -> class_scope_eq.
    apply (n10_1_class (fun β =>
      ([β @ cβ => [α @ cα => cβ = cα]]
        → [β @ cβ => φ cβ])) α).
  }
  assert (S2 : ([β @ cβ => [α @ cα => cβ = cα]]
      -[ β ]> [β @ cβ => φ cβ])
    → [α @ cα => φ cα]).
  {
    (* simplification *)
    intro Hp.
    pose proof (S1 Hp) as S1.
    pose proof (n20_2 Fα) as n20_2.
    rewrite <- class_scope_eq in n20_2.
    now MP S1 n20_2.
  }
  assert (S3 : [β @ cβ => [α @ cα => cβ = cα]]
    → ([α @ cα => φ cα] → [β @ cβ => φ cβ])).
  {
    (* *20.21 ignored *)
    pose proof (n20_18 Fβ Fα φ) as n20_18.
    (* simplification... *)
    intro Hp.
    pose proof (n20_18 Hp) as n20_18.
    rewrite -> n4_21 in n20_18.
    now destruct n20_18.
  }
  assert (S4 : [α @ cα => φ cα]
    → ([β @ cβ => [α @ cα => cβ = cα]]
      → [β @ cβ => φ cβ])).
  {
    pose proof (Comm2_04
      ([β @ cβ => [α @ cα => cβ = cα]])
      ([α @ cα => φ cα])
      ([β @ cβ => φ cβ])) as Comm2_04.
    now MP Comm2_04 S3.
  }
  assert (S5 : [α @ cα => φ cα]
    → ([β @ cβ => [α @ cα => cβ = cα]]
      -[ β ]> [β @ cβ => φ cβ])).
  {
    pose proof (n10_11_class β (fun β =>
      [α @ cα => φ cα]
        → ([β @ cβ => [α @ cα => cβ = cα]]
          → [β @ cβ => φ cβ]))) as n10_11.
    MP n10_11 S4.
    now rewrite -> n10_21_class in n10_11.
  }
  assert (S6 : (([β @ cβ => [α @ cα => cβ = cα]]) 
    -[ β ]> [β @ cβ => φ cβ]) 
      ↔ [α @ cα => φ cα]).
  {
    Conj_as S2 S5 C1.
    now Equiv C1.
  }
  exact S6.
Qed.

Theorem n20_54 (Fα : Prop → Prop) (φ : (Prop → Prop) → Prop) : 
  let α := (^z => Fα z) in (∃ β, 
    [β @ cβ => [α @ cα => cβ = cα]] ∧ [β @ cβ => φ cβ])
      ↔ [α @ cα => φ cα].
Proof.
  (* TOOLS *)
  set (α := ^z => Fα z).
  set (Fβ := Intro_pred "β" 1).
  set (β := ^z => Fβ z).
  (* ******** *)
  assert (S1 : ([β @ cβ => [α @ cα => cβ = cα]] 
    ∧ [β @ cβ => φ cβ]) -[ β ]> [α @ cα => φ cα]).
  {
    (* unprovable: it seems to be not fit. TODO: figure out what is going on
    in the future *)
    admit.
  }
  assert (S2 : (∃ β, [β @ cβ => [α @ cα => cβ = cα]]
      ∧ [β @ cβ => φ cβ])
    → [α @ cα => φ cα]).
  { now rewrite -> n10_23_class in S1. }
  (* NOTE: notice the `cα = cα` below which is "illegal" *)
  assert (S3 : [α @ cα => φ cα]
    → ([α @ cα => cα = cα]
      ∧ [α @ cα => φ cα])).
  {
    setoid_rewrite -> class_scope_eq.
    pose proof (n20_2 Fα) as n20_2.
    pose proof (n3_2
      ([α @ cα1 => [α @ cα2 => cα1 = cα2]])
      ([α @ cα => φ cα])) as n3_2.
    now MP n3_2 n20_2.
  }
  assert (S4 : [α @ cα => φ cα]
    → (∃ β, [β @ cβ => 
        [α @ cα => cβ = cα]]
      ∧ [β @ cβ => φ cβ])).
  {
    (* NOTE: we dont pick all `α`s in this step *)
    setoid_rewrite -> class_scope_eq in S3.
    pose proof (n10_24_class (fun β => [β @ cβ => 
      [α @ cα => cβ = cα]]
      ∧ [β @ cβ => φ cβ])
      α) as n10_24.
    now Syll_as S3 n10_24 S4.
  }
  assert (S5 : (∃ β, [β @ cβ => [α @ cα => cβ = cα]] 
    ∧ [β @ cβ => φ cβ]) 
      ↔ [α @ cα => φ cα]).
  {
    Conj_as S2 S4 C1.
    now Equiv C1.
  }
  exact S5.
Admitted.

(* TODO: redesign n20_55 *)
(* I'm quite proud that the class notation can work nicely together with ιs *)
Theorem n20_55 (φ : Prop → Prop) : 
  [ι (fun α => ([α @ cα => x <class_in> cα]) <[- x -]> φ x)
    | ια => [^z => φ z @ cφ => [ια @ cια => cφ = cια]]].
Proof.
  (* TOOLS *)
  set (Fα := Intro_pred "α" 1).
  set (α := ^z => Fα z).
  (* ******** *)
  assert (S1 : ([α @ cα => x <class_in> cα]
      <[- x -]> φ x)
    <[- α -]> ([α @ cα => [^z => φ z @ cφ => cα = cφ]])).
  {
    pose proof (n20_33 Fα φ) as n20_33.
    rewrite -> n4_21 in n20_33.
    pose proof (n10_11_class α (fun α =>
      ([α @ cα => x <class_in> cα]  <[- x -]> φ x)
      ↔ ([α @ cα => [^z => φ z @ cφ => cα = cφ]])))
      as n10_11.
    now MP n10_11 n20_33.
  }
  assert (S2 : ∃ β, (([α @ cα => x <class_in> cα]
        <[- x -]> φ x)
      <[- α -]> [α @ cα => [β @ cβ => cα = cβ]])
    ∧ [^z => φ z @ cφ => [β @ cβ => cφ = cβ]]).
  {
    pose proof (n20_54 φ (fun φ =>
      ([α @ cα => x <class_in> cα]
        <[- x -]> φ x)
      <[- α -]> ([α @ cα => [^z => φ z @ cφ => cα = cφ]]))) 
      as n20_54.
    simpl in n20_54.
    setoid_rewrite -> n4_3 in n20_54 at 2.
    setoid_rewrite -> n20_21_alt in n20_54 at 2.
    (* TODO:
    [α @ cz => φ (ψ cz)]
    ↔
    φ ([α @ cz => ψ cz])
    *)
    (* rewrite <- n20_54 in S1. *)
    admit.
  }
  assert (S3 : [ι (fun α => ([α @ cα => x <class_in> cα]) 
    <[- x -]> φ x) | ια => 
    [^z => φ z @ cφ => [ια @ cια => cφ = cια]]]).
  {
    simpl in S2.
    (* TODO: make a class specific vertsion for n14_1 *)
    (* TODO: is the citation wrong? and we should pick from this chapter
      instead? *)
    pose proof n14_1 as n14_1.
    admit.
  }
  exact S3.
Admitted.

(* TODO: this might have some severe denotational problem about what kind of function
should we use for the ι φ... *)
Theorem n20_56 (φ : Prop → Prop) : [ιE (fun α : Class.t Prop =>
  [α @ cα => x <class_in> cα] <[- x -]> φ x)].
Proof.
  pose proof (n20_55 φ) as n20_55.
  pose proof (n14_21_pred 
    (fun fα => 
      let α := (^z => fα z) in
      ([α @ cα => x <class_in> cα] <[- x -]> φ x))
    (fun ια => [^z => φ z @ cφ => cφ = ια]))
    as n14_21.
  (* unprovable: n20_55 doesn't have the correct form
  TODO: redesign n20_55 in the future. Or is *20.55 ill desigend? Since it
  is a new notation with new interpretation but without equipping with 
  notation supps *)
  admit.
Admitted.

Theorem n20_57 (φ : Prop → Prop) (f g : (Prop → Prop) → Prop) : 
  [ι (fun α => [α @ cα => f cα]) | ια =>
    [(^z => φ z) @ cz => [ια @ cια => cz = cια]]]
  → ([^z => φ z @ cz => g cz] ↔ [ι (fun α => [α @ cα => f cα]) 
    | ια => [ια @ cια => g cια]]).
Proof.
  assert (S1 : [ι (fun α => [α @ cα => f cα]) | ια =>
    [^z => φ z @ cφ => [ια @ cια => cφ = cια]]]
    ↔ (∃ β, ([α @ cα => f cα] <[- α -]> 
      [α @ cα => [β @ cβ => cα = cβ]])
      /\ [^z => φ z @ cφ => [β @ cβ => cφ = cβ]])).
  { apply n14_1_class. }
  assert (S2 : [ι (fun α => [α @ cα => f cα]) | ια =>
    [^z => φ z @ cφ => [ια @ cια => cφ = cια]]]
    ↔ ([α @ cα => f cα] 
      <[- α -]> [α @ cα => [^z => φ z @ cφ => cα = cφ]])).
  {
    setoid_rewrite -> n20_21_alt in S1 at 2.
    pose proof n20_54 as _n20_54.
    simpl in _n20_54, S1; simpl.
    (* TODO: is there some rule to extend the n20_54? *)
    (* setoid_rewrite -> n20_54 in S1 at 2. *)
    admit.
  }
  assert (S3 : [ι (fun α => [α @ cα => f cα]) | ια =>
    [ια @ cια => g cια]]
    ↔ (∃ β, ([α @ cα => f cα] 
        <[- α -]> [α @ cα => [β @ cβ => cα = cβ]])
      /\ [β @ cβ => g cβ])).
  { apply n14_1_class. }
  assert (S4 : [ι (fun α => [α @ cα => f cα]) | ια =>
      [(^z => φ z) @ cφ => [ια @ cια => cφ = cια]]]
    → ([ι (fun α => [α @ cα => f cα]) | ια =>
      [ια @ cια => g cια]]
      ↔ (∃ β, ([α @ cα => [^z => φ z @ cφ => cα = cφ]]
        <[- α -]> [α @ cα => [β @ cβ => cα = cβ]])
        /\ [β @ cβ => g cβ]))).
  {
    (* simplification *)
    intro Hp.
    destruct S2 as [S2 _].
    pose proof (S2 Hp) as S2.
    now setoid_rewrite -> S2 in S3 at 2.
  }
  assert (S5 : [ι (fun α => [α @ cα => f cα]) | ια =>
      [(^z => φ z) @ cφ => [ια @ cια => cφ = cια]]]
    → ([ι (fun α => [α @ cα => f cα]) | ια =>
        [ια @ cια => g cια]]
      ↔ (∃ β, [^z => φ z @ cφ => 
        [β @ cβ => cφ = cβ]] 
        /\ [β @ cβ => g cβ]))).
  {
    setoid_rewrite -> n20_21_alt in S4 at 2.
    now setoid_rewrite <- n13_183_class in S4.
  }
  assert (S6 : [ι (fun α => [α @ cα => f cα]) | ια =>
      [(^z => φ z) @ cφ => [ια @ cια => cφ = cια]]]
    → ([ι (fun α => [α @ cα => f cα]) | ια =>
      [ια @ cια => g cια]]
      ↔ [^z => φ z @ cφ => g cφ])).
  {
    setoid_rewrite -> n20_21_alt in S5 at 2.
    now setoid_rewrite -> n20_54 in S5.
  }
  assert (S7 : [ι (fun α => [α @ cα => f cα]) | ια =>
      [(^z => φ z) @ cφ => [ια @ cια => cφ = cια]]]
    → ([^z => φ z @ cφ => g cφ] ↔ [ι (fun α => [α @ cα => f cα]) 
      | ια => [ια @ cια => g cια]])).
  { now setoid_rewrite -> n4_21 in S6 at 1. }
  exact S7.
Admitted.

Theorem n20_58 (φ : Prop → Prop) :
  [ι (fun α => [α @ cα => [^z => φ z @ cφ => cα = cφ]]) 
    | ια => [^z => φ z @ cφ => [ια @ cια =>
      cφ = cια]]].
Proof.
  (* TOOLS *)
  set (Fα := Intro_pred "α" 1).
  set (α := ^z => Fα z).
  (* ******** *)
  assert (S1 : [α @ cα => [^z => φ z @ cφ => cα = cφ]]
    <[- α -]> [α @ cα => [^z => φ z @ cφ => cα = cφ]]).
  {
    pose proof (n4_2 ([α @ cα => [^z => φ z @ cφ => cα = cφ]])) 
      as n4_2.
    pose proof (n10_11_class α (fun α => 
      [α @ cα => [^z => φ z @ cφ => cα = cφ]]
      ↔ [α @ cα => [^z => φ z @ cφ => cα = cφ]]))
      as n10_11.
    now MP n10_11 n4_2.
  }
  assert (S2 : ∃ β, ([α @ cα => 
    [^z => φ z @ cφ => cα = cφ]] 
      <[- α -]> [α @ cα => [β @ cβ => cα = cβ]])
    /\ [^z => φ z @ cφ => [β @ cβ => cφ = cβ]]).
  {
    simpl in S1; simpl.
    
    (* NOTE: i think the proof order is wrong. we should have first constructed
      the `∃` and then generalize the `α`. Otherwise it's making things
      so tedious that we will break everything down to reconstruct again. *)
    (* TODO: I want to instantiate S1 again and find another way to construct the 
      proof *)
    (* setoid_rewrite <- n20_54 in S1. *)
    admit.
  }
  assert (S3 : [ι (fun α => [α @ cα => [^z => φ z @ cφ => cα = cφ]]) 
    | ια => [^z => φ z @ cφ => [ια @ cια =>
      cφ = cια]]]).
  { now rewrite <- n14_1_class in S2. }
  exact S3.
Admitted.

(* NOTE: 
  1. notice that we can see `ψ z^` being used in the text to represent
  the function itself 
  2. (p.194) "When there are no contrary, descriptions have larger scope
  than classes." The contrary can be witnessed, exclusively, in this 
  theoremby, as the first step is taking *20.1 to unfolding the definition *)
Theorem n20_59 (φ : Prop → Prop) (f : (Prop → Prop) → Prop) :
  [^z => φ z @ cφ => [ι (fun α => [α @ cα => f cα])
    | ια => [ια @ cια => cφ = cια]]]
  ↔
  [ι (fun α => [α @ cα => f cα]) | ια => 
    [ια @ cια => 
      [^z => φ z @ cφ => cια = cφ]]].
Proof.
  assert (S1 : [^z => φ z @ cφ => [ι (fun α => [α @ cα => f cα])
    | ια => [ια @ cια => cφ = cια]]]
    ↔ (∃ ψ, (φ x <[- x -]> ψ x)
      /\ [ι (fun α => [α @ cα => f cα]) 
        | ια => [ια @ cια =>
          ψ = cια]])).
  {
    pose proof (n20_1 φ (fun cψ =>
      [ι (fun α => [α @ cα => f cα])
      | ια => [ια @ cια => cψ = cια]]
    )) as n20_1.
    now setoid_rewrite -> n4_21 in n20_1 at 2.
  }
  assert (S2 : [^z => φ z @ cφ => [ι (fun α => [α @ cα => f cα])
    | ια => [ια @ cια => cφ = cια]]]
    ↔ (∃ ψ, (φ x <[- x -]> ψ x)
      /\ [ι (fun α => [α @ cα => f cα]) 
        | ια => [ια @ cια =>
          cια = ψ]])).
  { now setoid_rewrite -> n14_13_class_alt in S1. }
  assert (S3 : [^z => φ z @ cφ => [ι (fun α => [α @ cα => f cα])
    | ια => [ια @ cια => cφ = cια]]]
    ↔ [ι (fun α => [α @ cα => f cα]) | ια => 
      [ια @ cια => 
        [^z => φ z @ cφ => cια = cφ]]]).
  {
    setoid_rewrite -> n4_21 in S2 at 2.
    setoid_rewrite <- n20_1 in S2.
    pose proof (ι_class_scope_eq 
      (^z => φ z) f
      (fun cια cα => cια = cα)) 
      as ι_class_scope_eq.
    now setoid_rewrite -> (ι_class_scope_eq) in S2.
  }
  exact S3.
Qed.

Theorem n20_6 (f : (Prop → Prop) → Prop) :
  (∃ α, [α @ cα => f cα])
  ↔ (~∀ α, ~ [α @ cα => f cα]).
Proof.
  (* TOOLS *)
  set (λ φ0 : (Prop → Prop) → Prop, eq_to_equiv (∃ x, φ0 x) (¬(∀ x, ¬ φ0 x))
    (n10_01_pred φ0)) as n10_01a.
  set (λ f0 : (Prop → Prop) → Prop, eq_to_equiv
    (∀ α, [α @ cα => f0 cα])
    (∀ φ, [^z => φ z @ cφ => f0 cφ])
    (n20_07 f0)) as n20_07a.
  set (λ f0 : (Prop → Prop) → Prop, eq_to_equiv 
    (∃ α, [α @ cα => f0 cα])
    (∃ φ, [^z => φ z @ cφ => f0 cφ])
    (n20_071 f0)) as n20_071a.
  simpl in n10_01a, n20_07a, n20_071a.
  (* ******** *)
  assert (S1 : (∃ α, [α @ cα => f cα]) 
    ↔ (∃ φ, [^z => φ z @ cφ => f cφ])).
  {
    pose proof (n4_2 (∃ α, [α @ cα => f cα])) as n4_2.
    now setoid_rewrite -> n20_071a in n4_2 at 2.
  }
  assert (S2 : (∃ α, [α @ cα => f cα])
    ↔ (~ ∀ φ, ~ [^z => φ z @ cφ => f cφ])).
  { now setoid_rewrite -> n10_01a in S1. }
  assert (S3 : (∃ α, [α @ cα => f cα])
    ↔ (~∀ α, ~ [α @ cα => f cα])).
  {
    (* TODO: fix the scoping for `~, not specified in the proof *)
    (* setoid_rewrite <- n20_07a in S2. *)
    admit.
  }
  exact S3.
Admitted.

(* NOTE:
  1. As stated in the text, this theorem needs variants in practice.
  These variants are however, revealing that the distinction between
  representation and its underlying element is very obscure, as
  there are no specifications to distinguish between when to use what;
  no specifications to identify when do we need the underlying elements
  and when we don't
  2. This proposition has issue in associating function with class
*)
Theorem n20_61 (f : (Prop → Prop) → Prop) (φ : Prop → Prop) :
  let β := (^z => φ z) in
  (∀ α, [α @ cα => f cα])
    → [β @ cβ => f cβ].
Proof.
  (* TOOLS *)
  set (β := ^z => φ z).
  set (λ f0 : (Prop → Prop) → Prop, eq_to_equiv
    (∀ α, [α @ cα => f0 cα])
    (∀ φ, [^z => φ z @ cφ => f0 cφ])
    (n20_07 f0)) as n20_07a.
  (* ******** *)
  (* NOTE: notice the chaos of switching between a class variable and
    its underlying function. TODO: investigate class association issue *)
  assert (S1 : (∀ α, [α @ cα => f cα])
    → [^z => φ z @ cφ => f cφ]).
  {
    (* *20.07 ignored *)
    apply n10_1_class.
  }
  assert (S2 : (∀ α, [α @ cα => f cα])
    → [β @ cβ => f cβ]).
  { 
    (* We can already infer that this is the same proposition *)
    apply S1.
  }
  exact S2.
Qed.

(* Analogue to *20.17. Only write out here for demonstration *)
Definition n20_61_alt (f : (Prop → Prop) → Prop) (ψ : Prop → Prop) :
  (∀ α, [α @ cα => f cα])
  → [^z => ψ z @ cψ => f cψ].
Admitted.

(* Analogue to *20.41 *)
Definition n20_61_alt_1 (ψ : Prop → Prop) :
  ∃ α, [^z => ψ z @ cψ => [α @ cα => cψ = cα]].
Admitted.

(* Thm 20.62 : type formation rule for `∀ α` *)

Theorem n20_63 (P : Prop) (f : (Prop → Prop) → Prop) :
  (∀ α, P ∨ [α @ cα => f cα]) 
  → (P ∨ ∀ α, [α @ cα => f cα]).
Proof.
  (* TOOLS *)
  set (λ f0 : (Prop → Prop) → Prop, eq_to_equiv
    (∀ α, [α @ cα => f0 cα])
    (∀ φ, [^z => φ z @ cφ => f0 cφ])
    (n20_07 f0)) as n20_07a.
  (* ******** *)
  assert (S1 : (∀ α, P ∨ [α @ cα => f cα])
    ↔ ∀ φ, P \/ [^z => φ z @ cφ => f cφ]).
  {
    pose proof (n4_2 (∀ α, P ∨ [α @ cα => f cα])) as n4_2.
    (* unprovable: scoping issue. TODO: implement scoping in the future *)
    (* setoid_rewrite -> n20_07 in n4_2. *)
    admit.
  }
  assert (S2 : (∀ α, P ∨ [α @ cα => f cα])
    ↔ (P \/ ∀ φ, [^z => φ z @ cφ => f cφ])).
  {
    (* unprovable: *10.12 is single_direction *)
    (* TODO: check if its proof is double direction *)
    pose proof n10_12 as n10_12.
    admit.
  }
  assert (S3 : (∀ α, P ∨ [α @ cα => f cα])
    ↔ (P \/ ∀ α, [α @ cφ => f cφ])).
  { now setoid_rewrite <- n20_07 in S2. }
  assert (S4 : (∀ α, P ∨ [α @ cα => f cα]) 
    → (P ∨ ∀ α, [α @ cα => f cα])).
  { now destruct S3. }
  exact S4.
Admitted.

(* *20.631 - 633: other typing rules... TODO: fill in the future *)

(* manually associate β with ψ *)
Theorem n20_64 (f g : (Prop → Prop) → Prop) (ψ : Prop → Prop) : 
  let β := (^z => ψ z) in
  ((∀ α, [α @ cα => f cα]) 
    ∧ (∀ α, [α @ cα => g cα]))
  → (([β @ cβ => f cβ])
    ∧ ([β @ cβ => g cβ])).
Proof.
  (* TOOLS *)
  set (λ f0 : (Prop → Prop) → Prop, eq_to_equiv
    (∀ α, [α @ cα => f0 cα])
    (∀ φ, [^z => φ z @ cφ => f0 cφ])
    (n20_07 f0)) as n20_07a.
  set (β := ^z => ψ z).
  (* ******** *)
  assert (S1 : ((∀ α, [α @ cα => f cα]) 
      ∧ (∀ α, [α @ cα => g cα]))
    ↔ ((∀ φ, [^z => φ z @ cφ => f cφ]) 
      /\ (∀ φ, [^z => φ z @ cφ => g cφ]))).
  {
    pose proof (n4_2 ((∀ α, [α @ cα => f cα]) 
      ∧ (∀ α, [α @ cα => g cα]))) as n4_2.
    setoid_rewrite -> n20_07a in n4_2 at 3.
    now setoid_rewrite -> n20_07a in n4_2 at 3.
  }
  assert (S2 : ((∀ α, [α @ cα => f cα]) 
      ∧ (∀ α, [α @ cα => g cα]))
    → ([^z => ψ z @ cψ => f cψ] /\ [^z => ψ z @ cψ => g cψ])).
  {
    (* simplification *)
    destruct S1 as [_ S1].
    simpl in S1.
    pose proof (n10_14_class
      (fun α => [α @ cα => f cα])
      (fun α => [α @ cα => g cα])
      (^z => ψ z)) as n10_14.
    now Syll_as S1 n10_14 S2.
  }
  (* The transition from ψ to β can be automatically completed *)
  exact S2.
Qed.

(* Another analogue to *12.1. Same as all above, we cannot formalize this for now *)
Theorem n20_7 (f : (Prop → Prop) → Prop) :
  ∃ (g : (Prop → Prop) → Prop), [α @ cα => f cα] 
    <[- α -]> [α @ cα => g cα].
Proof.
Admitted.

(* unprovable *)
Theorem n20_701 (φ : Prop → Prop) (f : (Prop → Prop) → Prop → Prop) :
  ∃ (g : (Prop → Prop) → Prop → Prop), ([^z => φ z @ cφ => f cφ x]
    <[- (φ : Prop → Prop) (x : Prop) -]> [^z => φ z @ cφ => g cφ x]).
Proof.
Admitted.

(* unprovable *)
Theorem n20_702 (f : Prop → (Prop → Prop) → Prop) :
  ∃ (g : Prop → (Prop → Prop) → Prop), ([^z => φ z @ cφ => f x cφ]
    <[- (φ : Prop → Prop) (x : Prop) -]> [^z => φ z @ cφ => g x cφ]).
Proof.
Admitted.

(* NOTE: most of the citations for the proofs are only providing 1-parameter
  versions for 2 parameter requirements *)
Theorem n20_703 (f : (Prop → Prop) → (Prop → Prop) → Prop) :
  ∃ (g : (Prop → Prop) → (Prop → Prop) → Prop), 
    ([^z => φ z @ cφ => [^z => ψ z @ cψ => f cφ cψ]]
  <[- φ ψ -]> [^z => φ z @ cφ => [^z => ψ z @ cψ => g cφ cψ]]).
Proof.
  (* TOOLS *)
  set (Iφ := Intro_pred "phi" 1).
  set (Iψ := Intro_pred "psi" 1).
  set (Ig := Intro_pred_2 "g" 2).
  (* ******** *)
  assert (S1 : ((f χ θ) <[- χ θ -]> (Ig χ θ))
    → (((Iφ x <[- x -]> χ x) /\ (Iψ x <[- x -]> θ x) /\ f χ θ)
      <[- χ θ -]>
      ((Iφ x <[- x -]> χ x) /\ (Iψ x <[- x -]> θ x) /\ Ig χ θ))).
  {
    (* unprovable. TODO: see if there is an alternative for 2 params for functions *)
    pose proof n10_311 as n10_311.
    admit.
  }
  assert (S2 : ((f χ θ) <[- χ θ -]> (Ig χ θ))
    → ((∃ χ θ, (φ x <[- x -]> χ x) /\ (ψ x <[- x -]> θ x)
        /\ f χ θ)
      <[- φ ψ -]>
        (∃ χ θ, (φ x <[- x -]> χ x) /\ (ψ x <[- x -]> θ x)
          /\ Ig χ θ))).
  {
    (* *11.3 ignored *)
    intro Hp.
    pose proof (S1 Hp) as S1.
    (* NOTE: here the priority of `φ ψ` and `χ θ`'s generalization
    is pretty confusing *)
    pose proof (n11_11_pred Iφ Iψ
      (fun φ ψ => 
        (((φ x <[- x -]> χ x) /\ (ψ x <[- x -]> θ x) /\ f χ θ)
        <[- χ θ -]>
        ((φ x <[- x -]> χ x) /\ (ψ x <[- x -]> θ x) /\ Ig χ θ)))) 
        as n11_11.
    MP n11_11 S1.
    (* NOTE: although it looks correct, I don't really know if this
    is technically permitted *)
    setoid_rewrite -> n11_2_pred in n11_11 at 2.
    setoid_rewrite -> n11_2_pred in n11_11 at 1.
    setoid_rewrite -> n11_2_pred in n11_11 at 3.
    setoid_rewrite -> n11_2_pred in n11_11 at 2.
    (* pose proof n11_3 as n11_3. *)
    (* unprovable: *11.341 cannot be used in this sense *)
    pose proof (n11_341) as n11_341.
    admit.
  }
  assert (S3 : ((f χ θ) <[- χ θ -]> (Ig χ θ))
    → ([^z => φ z @ cφ => [^z => ψ z @ cψ => f cφ cψ]]
      <[- φ ψ  -]>
      [^z => φ z @ cφ => [^z => ψ z @ cψ => Ig cφ cψ]])).
  {
    intro Hp.
    pose proof (S2 Hp) as S2.
    pose proof n20_1 as n20_1.
    (* unprovable: provide 2-parameters version for *20.1 *)
    simpl in n20_1. simpl.
    pose proof n10_35 as n10_35.
    simpl in n10_35.
    admit.
  }
  assert (S4 : (∃ g, (f χ θ <[- χ θ -]> g χ θ))
    → ∃ (g : (Prop → Prop) → (Prop → Prop) → Prop), 
      ([^z => φ z @ cφ => [^z => ψ z @ cψ => f cφ cψ]]
      <[- φ ψ -]> [^z => φ z @ cφ => [^z => ψ z @ cψ => g cφ cψ]])).
  {
    pose proof (n10_11_pred2_1 Ig (fun g =>
      (f χ θ <[- χ θ -]> g χ θ)
      → ([^z => φ z @ cφ =>
         [^z => ψ z @ cψ => f cφ cψ]])
         <[- φ ψ -]>
         ([^z => φ z @ cφ =>
          [^z => ψ z @ cψ => g cφ cψ]])))
      as n10_11.
    MP n10_11 S3.
    pose proof (n10_281_pred2_1
      (fun g => (f χ θ) <[- χ θ -]> (g χ θ))
      (fun g => 
        ([^z => φ z @ cφ => [^z => ψ z @ cψ => f cφ cψ]])
        <[- φ ψ -]>
        ([^z => φ z @ cφ => [^z => ψ z @ cψ => g cφ cψ]])))
      as n10_281.
    now MP n10_281 n10_11.
  }
  assert (S5 : ∃ (g : (Prop → Prop) → (Prop → Prop) → Prop), 
      ([^z => φ z @ cφ => [^z => ψ z @ cψ => f cφ cψ]]
    <[- φ ψ -]> [^z => φ z @ cφ => [^z => ψ z @ cψ => g cφ cψ]])).
  {
    (* unprovable *)
    admit.
  }
  exact S5.
Admitted.

Theorem n20_71 (Fα Fβ : Prop → Prop) :
  let α := (^z => Fα z) in
  let β := (^z => Fβ z) in
  [α @ cα => [β @ cβ => cα = cβ]] 
    ↔ ([α @ cα => g cα]
      -[ g ]> [β @ cβ => g cβ]).
Proof.
  apply n20_19.
Qed.

Theorem n20_8 (φ : Prop → Prop) (A : Prop) :
  (φ A ∨ (~ φ A)) → [^x => (φ x ∨ (~ φ x)) @ cz1 =>
    [^x => (x = A ∨ (~ (x = A))) @ cz2 => cz1 = cz2]].
Proof.
  (* TOOLS *)
  set (X := Intro_individual "x").
  (* ******** *)
  assert (S1 : (φ A ∨ (~ φ A)) 
    → ((φ x \/ ~ (φ x)) <[- x -]> ((x = A) \/ ~(x = A)))).
  {
    pose proof (n13_3 A X φ) as n13_3.
    pose proof (n10_11 X (fun x => 
      φ A ∨ ¬ φ A 
        → φ x ∨ ¬ φ x ↔ x = A ∨ x ≠ A)) 
      as n10_11.
    MP n10_11 n13_3.
    now rewrite -> n10_21 in n10_11.
  }
  assert (S2 : (φ A ∨ (~ φ A)) 
    → [^x => (φ x ∨ (~ φ x)) @ cz1 =>
      [^x => (x = A ∨ (~ (x = A))) @ cz2 => cz1 = cz2]]).
  { now rewrite -> n20_15 in S1. }
  exact S2.
Qed.

Theorem n20_81 (φ ψ : Prop → Prop) (A : Prop) :
  ((φ A ∨ (~ φ A)) ∧ (ψ A ∨ (~ ψ A)))
  → [^x => φ x ∨ (~ φ x) @ cz1 => 
    [^x => ψ x ∨ (~ ψ x) @ cz2 => cz1 = cz2]].
Proof.
  assert (S1 : ((φ A ∨ (~ φ A)) ∧ (ψ A ∨ (~ ψ A)))
    → [^x => φ x ∨ (~ φ x) @ cz1 => 
      [^x => (x = A) \/ ~ (x = A) @ cz2 => cz1 = cz2]]).
  {
    pose proof (Simp3_26
      (φ A ∨ ¬ φ A)
      (ψ A ∨ ¬ ψ A)) 
      as Simp3_26.
    pose proof (n20_8 φ A) as n20_8.
    now Syll_as Simp3_26 n20_8 S1.
  }
  assert (S2 : ((φ A ∨ (~ φ A)) ∧ (ψ A ∨ (~ ψ A)))
    → [^x => ψ x ∨ (~ ψ x) @ cz1 => 
      [^x => (x = A) \/ ~ (x = A) @ cz2 => cz1 = cz2]]).
  {
    pose proof (Simp3_27
      (φ A ∨ ¬ φ A)
      (ψ A ∨ ¬ ψ A)) 
      as Simp3_27.
    pose proof (n20_8 ψ A) as n20_8.
    now Syll_as Simp3_27 n20_8 S2.
  }
  assert (S3 : ((φ A ∨ (~ φ A)) ∧ (ψ A ∨ (~ ψ A)))
    → ([^x => φ x ∨ (~ φ x) @ cz1 => 
      [^x => (x = A) \/ ~ (x = A) @ cz2 => cz1 = cz2]]
      /\ [^x => ψ x ∨ (~ ψ x) @ cz3 => 
      [^x => (x = A) \/ ~ (x = A) @ cz2 => cz3 = cz2]])).
  {
    (* *10.121, *10.13 ignored. *10.13 might be wrongly 
      designed and unusable here *)
    pose proof (Comp3_43 ((φ A ∨ (~ φ A)) ∧ (ψ A ∨ (~ ψ A)))
      ([^x => φ x ∨ (~ φ x) @ cz1 => 
        [^x => (x = A) \/ ~ (x = A) @ cz2 => cz1 = cz2]])
      ([^x => ψ x ∨ (~ ψ x) @ cz3 => 
        [^x => (x = A) \/ ~ (x = A) @ cz2 => cz3 = cz2]])) 
      as Comp3_43.
    Conj_as S1 S2 C1.
    now MP Comp3_43 C1.
  }
  assert (S4 : ((φ A ∨ (~ φ A)) ∧ (ψ A ∨ (~ ψ A)))
    → [^x => φ x ∨ (~ φ x) @ cz1 => 
      [^x => ψ x ∨ (~ ψ x) @ cz2 => cz1 = cz2]]).
  {
    pose proof (n20_24 (fun x => x = A ∨ x ≠ A) 
      (fun x => φ x ∨ ¬ φ x)
      (fun x => ψ x ∨ ¬ ψ x)) 
      as n20_24.
    now Syll_as S3 n20_24 S4.
  }
  exact S4.
Qed.

Close Scope formal_equiv.
Close Scope formal_impl.
Close Scope debug_class.
Close Scope iota_description.
