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
val get_Image : v:variable -> s:subst{ mem v (get_Domain s) } -> Tot term

let rec get_Image v st= match st with
  | hd::tl -> if (fst hd)=v then (snd hd) else (get_Image v tl)

let rec apply st t = match t with
  | Var v -> if mem v (get_Domain st) then (get_Image v st) else t
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

(**States that if hd::tl and st are composable then tl and st are composable too**)
val aux_lemma3a : hd:(variable*term) -> tl:subst -> st:subst -> Lemma
  (requires is_composable (hd::tl) st)
  (ensures is_composable tl st)

let rec aux_lemma3a hd tl st = aux_lemma2 hd tl

val aux_lemma3b : #a:eqtype -> l1:list a -> hd:a -> tl:list a -> Lemma
  (requires distinct_lists l1 (hd::tl))
  (ensures distinct_lists l1 tl)

let rec aux_lemma3b #a l1 hd tl = match l1 with
  | [] -> ()
  | xs::ys -> aux_lemma3b #a ys hd tl

val aux_lemma3c : st1:subst -> hd:(variable*term) -> tl:subst -> Lemma
  (requires distinct_domain st1 (hd::tl))
  (ensures distinct_domain st1 tl)

let aux_lemma3c st1 hd tl = aux_lemma3b (get_Domain st1) (fst hd) (get_Domain tl)


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
  | hd::tl -> aux_lemma3a hd tl st2 ; compose_aux_lemma1 tl st2

(**Auxiliary lemma for compose_lemma.
  States that the term corresponding to a variable v in composition of st1 and st2 is
  either the application of st2 to a term in st1 to which v corresponds to
  or the term in st2 itself which v corresponds to.  **)
val compose_aux_lemma2 : st1:subst -> st2:subst -> x:variable -> Lemma
 (requires (is_composable st1 st2))
 (ensures ( (mem x (get_Domain st1) ==> mem x (get_Domain (compose st1 st2)) /\ (get_Image x (compose st1 st2) = apply st2 (get_Image x st1))) /\
            (mem x (get_Domain st2) ==> mem x (get_Domain (compose st1 st2)) /\ (get_Image x (compose st1 st2) = get_Image x st2)) ) )

let rec compose_aux_lemma2 st1 st2 x = match st1 with
  | [] -> ()
  | hd::tl -> if x=fst hd then () else
    (aux_lemma3a hd tl st2 ; compose_aux_lemma1 st1 st2; compose_aux_lemma2 tl st2 x)

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


(** States that if the variables in lv are not present in the list hd::tl then
    they are neither present in the list [hd] nor in the list tl **)
val aux_lemma4 : lv:list variable -> hd:term -> tl:list term -> Lemma
  (requires (check_absence_vars_in_terms lv (hd::tl)))
  (ensures (check_absence_vars_in_terms lv [hd] && (check_absence_vars_in_terms lv tl)))
  [SMTPat (check_absence_vars_in_terms lv (hd::tl))]

let rec aux_lemma4 lv hd tl = match lv with
  | [] -> ()
  | xs::ys -> aux_lemma4 ys hd tl

(** States that if the variables in the list lv are not present the term Func s args ,
    then they are not present in any of the terms in the list args **)
val aux_lemma5: t:term -> lv:list variable -> Lemma
  (requires ( check_absence_vars_in_terms lv [t]) )
  (ensures ( (Func? t) ==> (check_absence_vars_in_terms lv (Func?.l t)) ) )

let rec aux_lemma5 t lv = match lv with
  | [] -> ()
  | hd::tl -> aux_lemma5 t tl

(** States that if the variables in the list lv are not present in the term Var v,
    then v doesn't belong in the list lv **)
val aux_lemma6 : lv:list variable -> t:term -> Lemma
  (requires check_absence_vars_in_terms lv [t] )
  (ensures ( (Var? t) ==> ( not(mem (Var?.v t) lv) ) ) )

let rec aux_lemma6 lv t = match lv with
  | [] -> ()
  | hd::tl -> aux_lemma6 tl t

val aux_lemma7 : st:subst -> hd:(variable*term) -> tl:subst -> Lemma
  (requires is_composable st (hd::tl))
  (ensures is_composable st tl)

let aux_lemma7 st hd tl =  aux_lemma2 hd tl; aux_lemma3c st hd tl; aux_lemma4 (get_Domain st) (snd hd) (get_Images tl)

(** States that if vars(t) where t is a term is disjoint from Domain(st),
    then application of st on t has no effect.
    The corresponding lemma for lists follows.**)
val commutation_aux_lemma1: t:term -> st:subst -> Lemma
  (requires (check_absence_vars_in_terms (get_Domain st) [t]) )
  (ensures (apply st t = t))

val commutation_aux_lemma1_list: lt:list term -> st:subst -> Lemma
  (requires (check_absence_vars_in_terms (get_Domain st) lt) )
  (ensures (apply_list st lt = lt))

let rec commutation_aux_lemma1 t st = match t with
  | Var v -> aux_lemma6 (get_Domain st) t
  | Name n -> ()
  | Func s args -> aux_lemma5 t (get_Domain st) ; commutation_aux_lemma1_list args st
and commutation_aux_lemma1_list lt st= match lt with
  | [] -> ()
  | hd::tl -> aux_lemma4 (get_Domain st) hd tl ;
              commutation_aux_lemma1 hd st ;
              commutation_aux_lemma1_list tl st

(** States that if the variables in the list lv are not present in the list hd::tl,
  where hd and tl are both lists, then they are not present in tl either. **)
val aux_lemma8: lv:list variable -> hd:list term -> tl:list term -> Lemma
  (requires check_absence_vars_in_terms lv (FStar.List.Tot.append hd tl))
  (ensures check_absence_vars_in_terms lv tl)

let rec aux_lemma8 lv hd tl = match hd with
  | [] -> ()
  | xs::ys -> aux_lemma4 lv xs (FStar.List.Tot.append ys tl) ; aux_lemma8 lv ys tl

(** States that if the two substutions are mutually composable, then the domain of st2
    is disjoint from the set vars(image of v in st1). **)
val commutation_aux_lemma2: st1:subst -> st2:subst -> v:variable -> Lemma
  (requires (is_composable st1 st2 && is_composable st2 st1) )
  (ensures (mem v (get_Domain st1) ==> check_absence_vars_in_terms (get_Domain st2) [get_Image v st1] ))

let rec commutation_aux_lemma2 st1 st2 v =  match st1 with
  | [] -> ()
  | hd::tl -> if v=(fst hd) then ( assert (check_absence_vars_in_terms  (get_Domain st2) ((snd hd)::(get_Images tl)) ) )
              else ( aux_lemma3a hd tl st2 ; aux_lemma7 st2 hd tl ; commutation_aux_lemma2 tl st2 v )

(** Commutation lemma
    States that if two substutions are mutually composable,
    then the order of composition doesn't matter. **)

val commutation_lemma : st1:subst -> st2:subst -> t:term-> Lemma
  (requires (is_composable st1 st2 && is_composable st2 st1) )
  (ensures equal_subst (compose st1 st2) (compose st2 st1) t)

val commutation_list_lemma : st1:subst -> st2:subst -> lt:list term-> Lemma
  (requires (is_composable st1 st2 && is_composable st2 st1) )
  (ensures equal_subst_list (compose st1 st2) (compose st2 st1) lt)

let rec commutation_lemma st1 st2 t = compose_aux_lemma1 st1 st2 ; compose_aux_lemma1 st2 st1 ;
                                      compose_lemma st1 st2 t; compose_lemma st2 st1 t; match t with
  | Var v -> if mem v (get_Domain st1) then (commutation_aux_lemma2 st1 st2 v; commutation_aux_lemma1 (get_Image v st1) st2)
             else if mem v (get_Domain st2) then (commutation_aux_lemma2 st2 st1 v; commutation_aux_lemma1 (get_Image v st2) st1)
             else ()
  | Name n -> ()
  | Func s args -> commutation_list_lemma st1 st2 args
and commutation_list_lemma st1 st2 lt = match lt with
  | [] -> ()
  | hd::tl -> commutation_lemma st1 st2 hd; commutation_list_lemma st1 st2 tl
