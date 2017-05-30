module Subst

open Term

type subst = list (variable * term)

(** Checks whether the substitution is cyclic or not   **)
val isnt_cyclic : subst -> Tot bool

(** Returns the list of the terms in the substitution the variables are mapped to**)
val get_Images : subst -> Tot (list term)

(** Returns the Domain of the substitution**)
val get_Domain : subst -> Tot (list variable)

(**Checks whether any variable in the first argument is present in
    any of the terms in the second argument or not.
    Returns true if no variable is present in any of the terms**)
val check_absence_vars_in_terms : list variable -> list term -> Tot bool

(**Checks whether the element is present in the list or not**)
val mem: #a:eqtype -> a -> list a -> Tot bool
let rec mem #a x xs = match xs with
  | [] -> false
  | hd::tl -> hd=x || mem x tl

let rec get_Images st = match st with
  | [] -> []
  | hd::tl -> (snd hd)::(get_Images tl)

let rec get_Domain st = match st with
  | [] -> []
  | hd::tl -> (fst hd)::(get_Domain tl)

let rec check_absence_vars_in_terms lv lt = match lv with
  | [] -> true
  | hd::tl -> not(is_var_present_list hd lt) && (check_absence_vars_in_terms tl lt)

(**States that if the variables arent present in a list, they are not going to be present in a smaller list**)
val aux_lemma1 : lv:list variable -> hd:term -> tl:list term -> Lemma
  (requires true)
  (ensures (check_absence_vars_in_terms lv (hd::tl)) ==> (check_absence_vars_in_terms lv tl) )
let rec aux_lemma1 lv hd tl = match lv with
  | [] -> ()
  | first::last -> aux_lemma1 last hd tl

let isnt_cyclic st =
  let lv = get_Domain st in
  let lt = get_Images st in
  check_absence_vars_in_terms lv lt

(**States that if a substitution isnt cyclic then a sub-list substitution isnt cyclic too**)
val aux_lemma2 : hd:(variable*term) -> tl:subst -> Lemma
  (requires true)
  (ensures isnt_cyclic (hd::tl) ==> isnt_cyclic tl )

let aux_lemma2 hd tl = aux_lemma1 (get_Domain tl) (snd hd) (get_Images tl)

(** The function that applies the substitution to a term.
    apply_list is the companion function for doing the same to lists**)
val apply : subst -> term ->Tot term
val apply_list : subst -> l1:list term ->Tot (l2:list term{FStar.List.Tot.length l1 = FStar.List.Tot.length l2})

(**Returns the term that the input variable corresponds to in the substitution**)
val get_Term : v:variable -> s:subst{ mem v (get_Domain s) } -> Tot term

let rec get_Term v st= match st with
  | hd::tl -> if (fst hd)=v then (snd hd) else (get_Term v tl)

let rec apply st t = match t with
  | Var v -> if mem v (get_Domain st) then (get_Term v st) else t
  | Func s args -> Func s (apply_list st args)
  | Name n -> t
  and apply_list st lt = match lt with
  | [] -> []
  | hd::tl -> (apply st hd)::(apply_list st tl)

(**Checks whether the input lists have a common element or not.
   Returns true if there is no common element**)
val distinct_lists : #a:eqtype -> list a -> list a -> Tot bool

let rec distinct_lists #a l1 l2 = match l1 with
  | [] -> true
  | hd::tl -> not(mem hd l2) && (distinct_lists tl l2)

(**Checks whether the input substitutions have non-overlapping domains or not**)
val distinct_domain: subst -> subst -> Tot bool

let distinct_domain st1 st2 =
  let dom1 = get_Domain st1 in
  let dom2 = get_Domain st2 in
  distinct_lists dom1 dom2

(**Checks whether the 2 input substitutions are composable or not.**)
val is_composable : subst -> subst -> Tot bool

let is_composable st1 st2 = (distinct_domain st1 st2)
                            && isnt_cyclic st1 && isnt_cyclic st2
                            && check_absence_vars_in_terms (get_Domain st1) (get_Images st2)

(**States that if hd::tl and st2 are composable then tl and st2 are composable too**)
val aux_lemma3 : hd:(variable*term) -> tl:subst -> st:subst -> Lemma
  (requires is_composable (hd::tl) st)
  (ensures is_composable tl st)

let rec aux_lemma3 hd tl st = aux_lemma2 hd tl

(**Returns the composition of two substitutions**)
val compose : st1:subst -> st2:subst -> Tot subst

let rec compose st1 st2 = match st1 with
  | [] -> st2
  | hd::tl -> (fst hd,apply st2 (snd hd))::(compose tl st2)

(**Checks whether the 2 substitutions are equivalent under application or not.
  Is different from equality operator as order here is unimportant.**)
type equal_subst (st1:subst) (st2:subst) (t:term)= ( apply st1 t = apply st2 t )

type equal_subst_list (st1:subst) (st2:subst) (lt:list term)= ( apply_list st1 lt = apply_list st2 lt )


(*
val is_unify : term -> term -> bool

val mgs : t1:term -> t2:term{ is_unify t1 t2 } -> subst*)

(**States that the application of a substitutions on a ground term returns the same term **)
val ground_term_lemma : st:subst -> t:term -> Lemma (requires (is_ground t)) (ensures (apply st t)=t)
val ground_list_term_lemma : st:subst -> lt:list term -> Lemma
  (requires (is_ground_list lt))
  (ensures (apply_list st lt)=lt)

let rec ground_term_lemma st t = match t with
  | Func _ args -> ground_list_term_lemma st args
  | Name _ -> ()
  and ground_list_term_lemma st lt = match lt with
  | [] -> ()
  | hd::tl -> (ground_term_lemma st hd) ; (ground_list_term_lemma st tl)

(**Auxiliary lemma for compose_lemma.
  States that the domain of composition of 2 composable substitutions is the
  union of the domains of the substitutions. **)
val compose_aux_lemma1 : st1:subst -> st2:subst -> Lemma
  (requires (is_composable st1 st2))
  (ensures forall (x:variable).
  mem x (get_Domain (compose st1 st2)) <==>
    ((mem x (get_Domain st1) || mem x (get_Domain st2))
      && not(mem x (get_Domain st1) && mem x (get_Domain st2)) )
  )

let rec compose_aux_lemma1 st1 st2 = match st1 with
  | [] -> ()
  | hd::tl -> aux_lemma3 hd tl st2 ; compose_aux_lemma1 tl st2

(**Auxiliary lemma for compose_lemma.
  States that the term corresponding to a variable v in composition of st1 and st2 is
  either the application of st2 to a term in st1 to which v corresponds to
  or the term in st2 itself which v corresponds to.  **)
val compose_aux_lemma2 : st1:subst -> st2:subst -> x:variable -> Lemma
 (requires (is_composable st1 st2))
 (ensures ( (mem x (get_Domain st1) ==> mem x (get_Domain (compose st1 st2)) /\ (get_Term x (compose st1 st2) = apply st2 (get_Term x st1))) /\
            (mem x (get_Domain st2) ==> mem x (get_Domain (compose st1 st2)) /\ (get_Term x (compose st1 st2) = get_Term x st2)) ) )

let rec compose_aux_lemma2 st1 st2 x = match st1 with
  | [] -> ()
  | hd::tl -> if x=fst hd then () else
    (aux_lemma3 hd tl st2 ; compose_aux_lemma1 st1 st2; compose_aux_lemma2 tl st2 x)

(**composition lemma.
  States that the application of composition of two substitutions is equal to
  the substitutions applied in succession.
  compose_list_lemma is the corresponding lemma for lists**)
val compose_lemma : st1:subst -> st2:subst -> t:term -> Lemma
  (requires is_composable st1 st2)
  (ensures apply (compose st1 st2) t= apply st2 (apply st1 t))

val compose_list_lemma : st1:subst -> st2:subst -> lt:list term -> Lemma
  (requires is_composable st1 st2)
  (ensures apply_list (compose st1 st2) lt = apply_list st2 (apply_list st1 lt))

let rec compose_lemma st1 st2 t = match t with
  | Var v -> compose_aux_lemma1 st1 st2; compose_aux_lemma2 st1 st2 v
  | Name n -> ()
  | Func s args -> compose_list_lemma st1 st2 args
  and compose_list_lemma st1 st2 lt = match lt with
  | [] -> ()
  | hd::tl -> compose_lemma st1 st2 hd ; compose_list_lemma st1 st2 tl

val aux_lemma4 : lv:list variable -> hd:term -> tl:list term -> Lemma
  (requires (check_absence_vars_in_terms lv (hd::tl)))
  (ensures (check_absence_vars_in_terms lv [hd]))

let rec aux_lemma4a lv hd tl = match lv with
  | [] -> ()
  | xs::ys -> aux_lemma4a ys hd tl

val commutation_aux_lemma1: t:term -> st:subst -> Lemma
  (requires (check_absence_vars_in_terms (get_Domain st) [t]) )
  (ensures (apply st t = t))

val commutation_aux_lemma1_list: lt:list term -> st:subst -> Lemma
  (requires (check_absence_vars_in_terms (get_Domain st) lt) )
  (ensures (apply_list st lt = lt))

let rec commutation_aux_lemma1 t st = match t with
  | Var v -> ()
  | Name n -> ()
  | Func s args -> commutation_aux_lemma1_list args st
and commutation_aux_lemma1_list lt st= match lt with
  | [] -> ()
  | hd::tl -> aux_lemma4 (get_Domain st) hd tl ; commutation_aux_lemma1 hd st ; commutation_aux_lemma1_list tl st
(*val commutation_aux_lemma1: st1:subst -> st2:subst -> v:variable -> Lemma
  (requires (is_composable st1 st2 && is_composable st2 st1) )
  (ensures (mem v (get_Domain st1) ==> (apply st2 (get_Term v st1) = get_Term v st1)) )

let rec commutation_aux_lemma1 st1 st2 v =*)

(*val commutation_aux_lemma2a : st1:subst -> st2:subst -> v:variable -> Lemma
  (requires (is_composable st1 st2 && is_composable st2 st1) )
  (ensures (mem v (get_Domain (compose st1 st2)) <==> mem v (get_Domain (compose st2 st1))) )

val commutation_aux_lemma2b : st1:subst -> st2:subst -> v:variable -> Lemma
  (requires (is_composable st1 st2 && is_composable st2 st1) )
  (ensures mem v (get_Domain (compose st1 st2)) ==> (get_Term v (compose st1 st2) = get_Term v (compose st2 st1)) )

let commutation_aux_lemma2a st1 st2 v = compose_aux_lemma1 st1 st2; compose_aux_lemma1 st2 st1

let commutation_aux_lemma2b st1 st2 v = commutation_aux_lemma2a st1 st2 v;*)

(*val commutation_lemma : st1:subst -> st2:subst -> t:term-> Lemma
  (requires (is_composable st1 st2 && is_composable st2 st1) )
  (ensures equal_subst (compose st1 st2) (compose st2 st1) t)

val commutation_list_lemma : st1:subst -> st2:subst -> lt:list term-> Lemma
  (requires (is_composable st1 st2 && is_composable st2 st1) )
  (ensures equal_subst_list (compose st1 st2) (compose st2 st1) lt)

let rec commutation_lemma st1 st2 t = match t with
  | Var v -> commutation_aux_lemma2 st1 st2 v
  | Name n -> ()
  | Func s args -> commutation_list_lemma st1 st2 args
and commutation_list_lemma st1 st2 lt = match lt with
  | [] -> ()
  | hd::tl -> commutation_lemma st1 st2 hd; commutation_list_lemma st1 st2 tl*)
