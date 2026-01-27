Require Import PM.pm.lib.
Require Import PM.pm.ch10.
Require Import PM.pm.ch11.

Open Scope single_app_equiv.
Open Scope double_app_equiv.

(* 
Starting from chapter 12, every variables being quantified at the rhs has to be
either an "Individual" or a "Predicate". For example, "forall P, P ∧ Q" might 
never appear, and instead, it will be either "forall Individual P, P ∧ Q" or 
"forall Predicate Phi, Phi (Individual P)" where Phi P = P ∧ Q

TODO: expand the idea: This seems to be the only way to quantify the functions
*)

(* EXPERIMENTAL: axioms in this chapter aren't stable, since our definition of `Predicate` should 
be subject to refinements *)
Definition n12_1 (φ : Prop → Prop) : 
  exists f : (Predicate 1), (φ x) <[- x -]> (f x).
Admitted.

(* To be uncommented *)
(* Definition n12_11 (f Phi : Prop → Prop → Prop) :
  exists fPsi : Prop → Prop → Prop,
    exists f : Predicate2.t 1, (Phi x y) <[- x y -]> (f.(Predicate2.fix_func 1) x y fPsi).
Admitted. *)

Close Scope single_app_equiv.
Close Scope double_app_equiv.
