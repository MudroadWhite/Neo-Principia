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