module Subst_interface
open Term_interface
open FStar.List.Tot.Base

type subst = l:(list (variable * term)){
  for_all (fun (x,_) ->
    for_all (fun (_,t) -> not (var_occurs x t)) l
  ) l
}

(** Generation **)

assume val identity : subst

assume val create : variable -> term -> subst

assume val apply : subst -> term -> term

assume val compose : subst -> subst -> subst

assume val is_unify : term -> term -> bool

assume val mgu : t1:term -> t2:term{ is_unify t1 t2 } -> subst
