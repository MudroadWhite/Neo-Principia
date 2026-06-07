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

(* Draft: Automatic scoping PM symbol suite

Notation "[| O1 < mid_op > O2 |]" :=
  (expand_symbol O1
    (expand_symbol O2 (mid_op))).



*)