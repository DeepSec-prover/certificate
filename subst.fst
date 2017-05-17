module Subst

type subst = list (variable * term)

val apply : subst -> term -> term

val compose : subst -> subst -> subst

val is_unify : term -> term -> bool

val mgs : t1:term -> t2:term{ is_unify t1 t2 } -> subst
