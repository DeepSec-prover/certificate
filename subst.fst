module Subst

open Term

type subst = list (variable * term)

val isnt_cyclic : subst -> Tot bool
val get_term_list : subst -> Tot (list term)
val get_var_list : subst -> Tot (list variable)
val check_presence_varlist_termlist : list variable -> list term -> Tot bool

val mem: #a:eqtype -> a -> list a -> Tot bool
let rec mem #a x xs =
  match xs with
  | [] -> false
  | hd::tl -> hd=x || mem x tl

let rec get_term_list st =
match st with
| [] -> []
| hd::tl -> (snd hd)::(get_term_list tl)

let rec get_var_list st =
match st with
| [] -> []
| hd::tl -> (fst hd)::(get_var_list tl)

let rec check_presence_varlist_termlist lv lt =
  match lv with
  | [] -> true
  | hd::tl -> (is_var_present_list hd lt) && (check_presence_varlist_termlist tl lt)

let isnt_cyclic st =
  let lv = get_var_list st in
  let lt = get_term_list st in
  check_presence_varlist_termlist lv lt


val apply : subst -> term ->Tot term
val apply_list : subst -> list term ->Tot (list term)

val get_mem : variable -> subst -> Tot term


(** bad function rewrite later**)
let rec get_mem v st= match st with
| hd::tl -> if (fst hd)=v then (snd hd) else (get_mem v tl)
| [] -> Var v

let rec apply st t =
  match t with
  | Var v -> if mem v (get_var_list st) then (get_mem v st) else t
  | Func s args -> Func s (apply_list st args)
  | Name n -> t
  and apply_list st lt = match lt with
  | [] -> []
  | hd::tl -> (apply st hd)::(apply_list st tl)

val compose : subst -> subst -> Tot subst

let rec compose st1 st2 = match st1 with
 | [] -> st2
 | hd::tl -> hd::(compose tl st2)

(*
val is_unify : term -> term -> bool

val mgs : t1:term -> t2:term{ is_unify t1 t2 } -> subst*)


val ground_term_lemma : st:subst -> t:term -> Lemma (requires (is_ground t)) (ensures (apply st t)=t)

let rec ground_term_lemma st t = match st with
 | [] -> ()
 | hd::tl -> ground_term_lemma tl t

val compose_lemma : st1:subst -> st2:subst -> Lemma (requires true) (ensures (forall (t:term). apply (compose st1 st2) t = apply st2 (apply st1 t)))

let rec compose_lemma st1 st2 = match st1 with
 | [] -> ()
 | hd::tl -> compose_lemma tl st2

val assoc_lemma : st1:subst -> st2:subst -> Lemma (requires isnt_cyclic(compose st1 st2))(ensures forall (t:term). apply (compose st1 st2) t= apply st2 (apply st1 t) )

let rec assoc_lemma st1 st2 = match st1 with
| [] -> ()
| hd::tl-> assoc_lemma tl st2
