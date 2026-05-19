(* 
Draft: formal type system 
We want a type system with
- Propositions' type of order n (TODO: if they are still not the same type, is that necessary? if we are talking about 
"∀ propositions of a type", will identifying props in different range matters?)
- Functions'/matrices' type with order n, (?) maybe distinguish between different arguments
- Individual's type which we don't even know if it is needed
- **Untyped** functions(not matrices anymore?) as a *type* - taking in argument of order n,
   return an arbitarily large proposition of order greater than n
- Constant's type? or is it unnecessary?
- If things goes better, we should be able to prove equivalance to "of the same type" primitive proposition
*)

(* 
Draft: better `∃`, `∀` design
- define a "EForall" and wrap up with a notation in chapter 9
*)


Module Experiment_ch20.
  Record t {A : Type} : Type := {
    get_A : Type; 
  }. 
  Definition test := Build_t Prop Prop. 
  Definition test_get_A : test.(get_A). Admitted. 

  Definition test_1_1 : Prop :=
    ltac:(
      pose (x := test_get_A);
      cbn in x;
      exact x
    ).

  Definition test_1_2 := ltac:(
    let x := eval cbn in test_get_A in 
    let f := constr:(fun y : Prop => y) in
    exact (f x)).

  (* 
Definition testtest (cls : Class.t) := ltac:(
  let A := eval cbn in (cls.(Class.get_A)) in 
  let f := constr:((fun (classname : A -> Prop) => classname = classname)) in
  exact (class_app f cls)).
Compute testtest.
  *)
End Experiment_ch20.
