module Subst

open Term

type subst = list (variable * term)

val isnt_cyclic : subst -> Tot bool
val get_Images : subst -> Tot (list term)
val get_Domain : subst -> Tot (list variable)
val check_presence_varlist_termlist : list variable -> list term -> Tot bool

val mem: #a:eqtype -> a -> list a -> Tot bool
let rec mem #a x xs =
  match xs with
  | [] -> false
  | hd::tl -> hd=x || mem x tl

let rec get_Images st =
match st with
| [] -> []
| hd::tl -> (snd hd)::(get_Images tl)

let rec get_Domain st =
match st with
| [] -> []
| hd::tl -> (fst hd)::(get_Domain tl)

let rec check_presence_varlist_termlist lv lt =
  match lv with
  | [] -> true
  | hd::tl -> (is_var_present_list hd lt) && (check_presence_varlist_termlist tl lt)

let isnt_cyclic st =
  let lv = get_Domain st in
  let lt = get_Images st in
  check_presence_varlist_termlist lv lt


val apply : subst -> term ->Tot term
val apply_list : subst -> l1:list term ->Tot (l2:list term{FStar.List.Tot.length l1 = FStar.List.Tot.length l2})

val get_Term : variable -> subst -> Tot term


(** bad function rewrite later**)
let rec get_Term v st= match st with
| hd::tl -> if (fst hd)=v then (snd hd) else (get_Term v tl)
| [] -> Var v

let rec apply st t =
  match t with
  | Var v -> if mem v (get_Domain st) then (get_Term v st) else t
  | Func s args -> Func s (apply_list st args)
  | Name n -> t
  and apply_list st lt = match lt with
  | [] -> []
  | hd::tl -> (apply st hd)::(apply_list st tl)

val distinct_lists : #a:eqtype -> list a -> list a -> Tot bool

let rec distinct_lists #a l1 l2 =
match l1 with
  | [] -> true
  | hd::tl -> not(mem hd l2) && (distinct_lists tl l2)

val distinct_domain: subst -> subst -> Tot bool

let distinct_domain st1 st2 =
  let dom1 = get_Domain st1 in
  let dom2 = get_Domain st2 in
  distinct_lists dom1 dom2

val is_composable : subst -> subst -> Tot bool

let is_composable st1 st2 = (distinct_domain st1 st2 ) && (isnt_cyclic (FStar.List.Tot.append st1 st2) )

val compose : st1:subst -> st2:subst -> Tot subst

let rec compose st1 st2 = FStar.List.Tot.append st1 st2

(*
val is_unify : term -> term -> bool

val mgs : t1:term -> t2:term{ is_unify t1 t2 } -> subst*)


val ground_term_lemma : st:subst -> t:term -> Lemma (requires (is_ground t)) (ensures (apply st t)=t)
val ground_list_term_lemma : st:subst -> lt:list term -> Lemma (requires (is_ground_list lt)) (ensures (apply_list st lt)=lt)

let rec ground_term_lemma st t =
  match t with
  | Func _ args -> ground_list_term_lemma st args
  | Name _ -> ()
  and ground_list_term_lemma st lt =
  match lt with
  | [] -> ()
  | hd::tl -> (ground_term_lemma st hd) ; (ground_list_term_lemma st tl)

val compose_lemma : st1:subst -> st2:subst-> Lemma (requires (is_composable st1 st2)) (ensures forall (x:variable). mem x (get_Domain (compose st1 st2)) <==> ( (mem x (get_Domain st1) || mem x (get_Domain st2)) && not( mem x (get_Domain st1) && mem x (get_Domain st2))))

let rec compose_lemma st1 st2 =
  match st1 with
  | [] -> ()
  | hd::tl -> compose_lemma tl st2

(*val assoc_lemma : st1:subst -> st2:subst -> t:term -> Lemma (requires is_composable st1 st2)(ensures apply (compose st1 st2) t= apply st2 (apply st1 t))
let rec assoc_lemma st1 st2 t=
  match t with
  | Var v ->*)
