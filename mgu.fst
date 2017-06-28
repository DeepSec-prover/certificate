module Mgu

open Term
open Subst
open Fset
open Union

(** The function applies a substitution on a list of tuples of terms. **)
val apply_tuple_list : st:subst -> l:list (term*term) -> Tot (list (term*term))

let rec apply_tuple_list st l = match l with
  | [] -> []
  | (hd1,hd2)::tl -> (apply st hd1 , apply st hd2)::(apply_tuple_list st tl)

(** States that the length of the list is unchanged on application of a substitution **)
val apply_list_length_lemma : st:subst -> l:list (term*term) -> Lemma
  (requires true)
  (ensures ( List.Tot.length l = List.Tot.length (apply_tuple_list st l)) )

let rec apply_list_length_lemma st l = match l with
  | [] -> ()
  | hd::tl -> apply_list_length_lemma st tl

(** This function joins 2 lists of terms and forms a list of tuples of terms. The lists have to be of equal length. **)
val collate : l1:list term -> l2:list term {List.Tot.length l1 = List.Tot.length l2}-> Tot (list (term*term))

let rec collate l1 l2 = match l1,l2 with
  | [],[] -> []
  | hd1::tl1,hd2::tl2 -> (hd1,hd2)::(collate tl1 tl2)


(** These functions return the set of variables in a term and in a list of term respectively. **)
val get_fset_vars : term -> Tot (fset variable)
val get_fset_vars_list : list term -> Tot (fset variable)

let rec get_fset_vars t= match t with
  | Var v -> fsingleton v
  | Name n -> fempty
  | Func s args -> get_fset_vars_list args
and get_fset_vars_list lt = match lt with
  | [] -> fempty
  | hd::tl -> funion (get_fset_vars hd) (get_fset_vars_list tl)

(** These functions return the number of symbols in a term and in a list of terms. **)
val get_num_symbols : t:term -> Tot nat
val get_num_symbols_list : lt:list term-> Tot nat

let rec get_num_symbols t =
  match t with
  | Var v -> 1
  | Name n -> 1
  | (Func s args) -> 1 + get_num_symbols_list args
and get_num_symbols_list lt = match lt with
  | [] -> 0
  | hd::tl -> get_num_symbols hd + get_num_symbols_list tl

(** The function which returns the number of symbols in a list of tuples of terms **)
val get_num_symbols_tuple_list : ltt:list (term*term) -> Tot nat

let rec get_num_symbols_tuple_list ltt = match ltt with
  | [] -> 0
  | (hd1,hd2)::tl -> get_num_symbols hd1 + get_num_symbols hd2 + get_num_symbols_tuple_list tl

(** The function which returns the set of variables in a list of tuples of terms **)
val get_fset_vars_tuple_list : list (term*term) -> Tot (fset variable)

let rec get_fset_vars_tuple_list ltt = match ltt with
  | [] -> fempty
  | (hd1,hd2)::tl -> funion (get_fset_vars hd1)  (funion (get_fset_vars hd2) (get_fset_vars_tuple_list tl))

(** States that the set of variable in (t1,t2)::ltt is same as that of (t2,t1)::ltt **)
val tuple_fset_lemma : t1:term -> t2:term -> ltt: list (term*term) -> Lemma
  (requires true)
  (ensures (equal (get_fset_vars_tuple_list ( (t1,t2)::ltt )) (get_fset_vars_tuple_list ( (t2,t1)::ltt ))) )
  [SMTPat (get_fset_vars_tuple_list ( (t1,t2)::ltt ))]

let tuple_fset_lemma t1 t2 ltt = ()

val tuple_fset_size_lemma : t1:term -> t2:term -> ltt: list (term*term) -> Lemma
  (requires true)
  (ensures (size (get_fset_vars_tuple_list ( (t1,t2)::ltt )) = size (get_fset_vars_tuple_list ( (t2,t1)::ltt ))) )
  [SMTPat (size (get_fset_vars_tuple_list ( (t1,t2)::ltt )))]

let tuple_fset_size_lemma t1 t2 ltt = tuple_fset_lemma t1 t2 ltt; equal_size_lemma (get_fset_vars_tuple_list ( (t1,t2)::ltt )) (get_fset_vars_tuple_list ( (t2,t1)::ltt ))

(** Supporting lemmas for aux_lemma1c. State that vars(x{t/v}) is a subset of vars(x) U vars(t)  **)
val aux_lemma1a : x:term -> v:variable -> t:term -> Lemma
  (requires not(is_var_present v t))
  (ensures fsubset (get_fset_vars (apply [(v,t)] x)) (funion (get_fset_vars x) (get_fset_vars t)) )
val aux_lemma1b : lx:list term -> v:variable -> t:term -> Lemma
  (requires not(is_var_present v t))
  (ensures fsubset (get_fset_vars_list (apply_list [(v,t)] lx)) (funion (get_fset_vars_list lx) (get_fset_vars t)) )

let rec aux_lemma1a x v t = match x with
  | Var w -> if (v=w) then
            (assert(apply [(v,t)] x = t)) else
            (assert(apply [(v,t)] x = x))
  | Name n -> assert(equal (get_fset_vars x) fempty);
              assert(equal (funion (get_fset_vars x) (get_fset_vars t)) (funion fempty (funion (get_fset_vars x) (get_fset_vars t))))
  | Func s args -> aux_lemma1b args v t
  and aux_lemma1b lx v t =  match lx with
  | [] -> ()
  | hd::tl -> aux_lemma1a hd v t; aux_lemma1b tl v t

(** Supporting lemma for aux_lemma5. States that vars(ltt{t/v}) is a subset of vars( (Var v,t)::ltt ) **)
val aux_lemma1c : ltt:list (term*term) -> v:variable -> t:term -> Lemma
  (requires not(is_var_present v t))
  (ensures fsubset (get_fset_vars_tuple_list (apply_tuple_list [(v,t)] ltt)) (get_fset_vars_tuple_list ( (Var v,t)::ltt ) ) )

let rec aux_lemma1c ltt v t = match ltt with
  | [] -> ()
  | (hd1,hd2)::tl -> aux_lemma1a hd1 v t; aux_lemma1a hd2 v t; aux_lemma1c tl v t

  (** Supporting lemma for aux_lemma5. States that the variable v is present in the tuple list (Var v, t)::ltt **)
val aux_lemma2 : ltt:list (term*term) -> v:variable -> t:term -> Lemma
  (requires true)
  (ensures (mem v (get_fset_vars_tuple_list ((Var v,t)::ltt))) )

let aux_lemma2 ltt v t = ()

(** Supporting lemma for aux_lemma5. States that if is_var_present v t is false then v isnt present in the set of variables. **)
val aux_lemma3a : v:variable -> t:term -> Lemma (requires not(is_var_present v t)) (ensures not(mem v (get_fset_vars t)))
val aux_lemma3b : v:variable -> lt:list term -> Lemma (requires not(is_var_present_list v lt)) (ensures not(mem v (get_fset_vars_list lt)))

let rec aux_lemma3a v t = match t with
  | Var w -> assert(not(v=w))
  | Name n -> ()
  | Func s args -> aux_lemma3b v args
and aux_lemma3b v lt = match lt with
  | [] -> ()
  | hd::tl -> aux_lemma3a v hd ; aux_lemma3b v tl

(** Supporting lemma for aux_lemma5. States that the variable v is not present in the term after application of the substution {t/v} **)
val aux_lemma4a : t:term -> v:variable -> x:term -> Lemma(requires not(is_var_present v x))(ensures not(mem v (get_fset_vars (apply [(v,x)] t) )))
val aux_lemma4b : lt:list term -> v:variable -> x:term -> Lemma(requires not(is_var_present v x))(ensures not(mem v (get_fset_vars_list (apply_list [(v,x)] lt) )))

let rec aux_lemma4a t v x = match t with
  | Var w -> if not(v=w) then
            ( assert(apply [(v,x)] t = t); assert(equal (get_fset_vars t) (fsingleton w)); assert(not(mem v (fsingleton w))) ) else
            (assert(apply [(v,x)] t = x); aux_lemma3a v x )
  | Name n -> assert(apply [(v,x)] t = t); assert(equal (get_fset_vars t) (fempty)); assert(not(mem v fempty))
  | Func s args -> aux_lemma4b args v x
and aux_lemma4b lt v x = match lt with
  | [] -> ()
  | hd::tl -> aux_lemma4a hd v x ;  aux_lemma4b tl v x

(** Supporting lemma for aux_lemma5. States that the variable v is not present in the set of variables of a list of tuple of terms after application of the substitution {t/v} **)
val aux_lemma3 : ltt:list (term*term) -> v:variable -> t:term -> Lemma
  (requires not(is_var_present v t))
  (ensures not(mem v (get_fset_vars_tuple_list (apply_tuple_list [(v,t)] ltt))))

let rec aux_lemma3 ltt v t = match ltt with
  | [] -> ()
  | (hd1,hd2)::tl -> aux_lemma4a hd1 v t; aux_lemma4a hd2 v t; aux_lemma3 tl v t

(** Lemma for proving termination in 1st case. States that the number of variables decreases from the first call to the second. **)
val aux_lemma5 : ltt:list (term*term) -> v:variable -> t:term -> Lemma
  (requires not(is_var_present v t))
  (ensures size (get_fset_vars_tuple_list (apply_tuple_list [(v,t)] ltt)) < size (get_fset_vars_tuple_list ((Var v,t)::ltt)) )

let rec aux_lemma5 ltt v t = aux_lemma1c ltt v t; aux_lemma2 ltt v t; aux_lemma3 ltt v t ;
                             size_lemma v (get_fset_vars_tuple_list (apply_tuple_list [(v,t)] ltt)) (get_fset_vars_tuple_list ((Var v,t)::ltt))

(** Supporting lemma for aux_lemma7. States that the set of variables in the concatenation of 2 lists is equal to the union of the sets of variables in the lists. **)
val aux_lemma6a : ltt1:list (term*term) -> ltt2:list (term*term) -> Lemma
  (requires true)
  (ensures (equal (get_fset_vars_tuple_list (List.Tot.append ltt1 ltt2)) (funion (get_fset_vars_tuple_list ltt1) (get_fset_vars_tuple_list ltt2))))

let rec aux_lemma6a ltt1 ltt2 = match ltt1 with
  | [] -> ()
  | hd::tl -> aux_lemma6a tl ltt2

(** Supporting lemma for aux_lemma7. States that the set of variables in the collated form of 2 lists is equal to the union of the sets of variables of the 2 lists. **)
val aux_lemma6b : lt1:list term -> lt2:list term { List.Tot.length lt2 = List.Tot.length lt1 } -> Lemma
  (requires true)
  (ensures (equal (get_fset_vars_tuple_list (collate lt1 lt2)) (funion (get_fset_vars_list lt1) (get_fset_vars_list lt2))))

let rec aux_lemma6b lt1 lt2 = match lt1,lt2 with
  | [],[] -> ()
  | hd1::tl1,hd2::tl2 -> aux_lemma6b tl1 tl2

assume val aux_lemma6c : #a:eqtype -> s1:fset a -> s2:fset a -> s3:fset a -> Lemma
  (requires equal s1 s2)
  (ensures (equal (funion s1 s3) (funion s2 s3)))

(** Lemma for proving termination in the third case. States that the size of the variables set remains the same between the two calls. **)
val aux_lemma7 : lt1:list term -> lt2:list term {List.Tot.length lt2 = List.Tot.length lt1} ->  ltt:list (term*term) -> s:symbol { s.arity = List.Tot.length lt1 } -> Lemma
  (requires true )
  (ensures ( size (get_fset_vars_tuple_list (List.Tot.append (collate lt1 lt2) ltt)) = size (get_fset_vars_tuple_list ((Func s lt1, Func s lt2)::ltt)) ) )

let rec aux_lemma7 lt1 lt2 ltt s = aux_lemma6a (collate lt1 lt2) ltt; aux_lemma6b lt1 lt2 ;
    aux_lemma6c (get_fset_vars_tuple_list (collate lt1 lt2)) (funion (get_fset_vars_list lt1) (get_fset_vars_list lt2)) (get_fset_vars_tuple_list ltt);
    assert(equal (get_fset_vars_tuple_list (List.Tot.append (collate lt1 lt2) ltt)) (funion (funion (get_fset_vars_list lt1) (get_fset_vars_list lt2)) (get_fset_vars_tuple_list ltt)));
    assert(equal (get_fset_vars_tuple_list ((Func s lt1, Func s lt2)::ltt)) (funion (funion (get_fset_vars_list lt1) (get_fset_vars_list lt2)) (get_fset_vars_tuple_list ltt)));
    equal_size_lemma (get_fset_vars_tuple_list (List.Tot.append (collate lt1 lt2) ltt)) (funion (funion (get_fset_vars_list lt1) (get_fset_vars_list lt2)) (get_fset_vars_tuple_list ltt));
    equal_size_lemma (get_fset_vars_tuple_list ((Func s lt1, Func s lt2)::ltt)) (funion (funion (get_fset_vars_list lt1) (get_fset_vars_list lt2)) (get_fset_vars_tuple_list ltt))

(** Supporting lemma for aux_lemma10. States that the number of symbols in the collated form of 2 lists is equal to the sum of the numbers of symbols in each of them **)
val aux_lemma8 : lt1:list term -> lt2:list term { List.Tot.length lt2 = List.Tot.length lt1 } -> Lemma
  (requires true)
  (ensures (get_num_symbols_tuple_list (collate lt1 lt2) = get_num_symbols_list lt1 + get_num_symbols_list lt2))

let rec aux_lemma8 lt1 lt2 = match lt1,lt2 with
  | [],[] -> ()
  | hd1::tl1,hd2::tl2 -> aux_lemma8 tl1 tl2

(** Supporting lemma for aux_lemma10. States that the number of symbols in the concatenation of 2 lists is equal to the sum of the numbers of symbols in each of them **)
val aux_lemma9 : ltt1:list (term*term) -> ltt2:list (term*term) -> Lemma
  (requires true)
  (ensures (get_num_symbols_tuple_list (List.Tot.append ltt1 ltt2) = get_num_symbols_tuple_list ltt1 + get_num_symbols_tuple_list ltt2))

let rec aux_lemma9 ltt1 ltt2 = match ltt1 with
  | [] -> ()
  | hd::tl -> aux_lemma9 tl ltt2

(** Lemma for proving termination in the third case. States that the number of symbols decreases. **)
val aux_lemma10 : lt1:list term -> lt2:list term {List.Tot.length lt2 = List.Tot.length lt1} ->  ltt:list (term*term) -> s:symbol { s.arity = List.Tot.length lt1} -> Lemma
  (requires true )
  (ensures ( get_num_symbols_tuple_list (List.Tot.append (collate lt1 lt2) ltt) < get_num_symbols_tuple_list((Func s lt1, Func s lt2)::ltt)) )

let rec aux_lemma10 lt1 lt2 ltt s = aux_lemma9 (collate lt1 lt2) ltt; aux_lemma8 lt1 lt2

(** The main function calculating the mgu, takes in a list of tuple of terms and a substitution as an argument.
The substitution represents the (var,term) pairs already covered in the list thus far. May or may not return a substitution. **)
val sub_mgu : l:list (term*term) -> st:subst -> Tot (option subst) (decreases %[size (get_fset_vars_tuple_list l);(get_num_symbols_tuple_list l)])
let rec sub_mgu l st = match l with
  | [] -> Some st
  | (Var v, x)::tl
  | (x,Var v)::tl -> begin
                        if (is_var_present v x) then None
                        else (
                          let temp1 = (compose st [(v,x)]) in
                          let temp2 = (apply_tuple_list [(v,x)] tl) in
                          aux_lemma5 tl v x;
                          if None? (sub_mgu temp2 temp1) then None
                          else (sub_mgu temp2 temp1)
                        )
                     end
  | (Name a1, Name a2)::tl  -> if a1=a2 then (
      equal_size_lemma (get_fset_vars_tuple_list tl) (get_fset_vars_tuple_list l);
      assert(size (get_fset_vars_tuple_list tl) = size (get_fset_vars_tuple_list l));
      sub_mgu tl st
      ) else None
  | (Func s1 args1, Func s2 args2)::tl -> if s1 = s2 then (aux_lemma7 args1 args2 tl s1; aux_lemma10 args1 args2 tl s1;  sub_mgu (List.Tot.append (collate args1 args2) tl) st) else None
  | _ -> None

(** The main mgu function. Has a call to sub_mgu **)
val mgu : l:list (term*term) -> Tot (option subst)

let mgu l= sub_mgu l []

(** The main function which is called by is_Unifiable. **)
val sub_unifiable : l:list (term*term) -> st:subst -> Tot bool (decreases %[size (get_fset_vars_tuple_list l);(get_num_symbols_tuple_list l)])

let rec sub_unifiable l st = match l with
  | [] -> true
  | (Var v, x)::tl
  | (x,Var v)::tl -> begin
                        if (is_var_present v x) then false
                        else (
                          let temp1 = (compose st [(v,x)]) in
                          let temp2 = (apply_tuple_list [(v,x)] tl) in
                          aux_lemma5 tl v x;
                          (sub_unifiable temp2 temp1)
                        )
                     end
  | (Name a1, Name a2)::tl  -> if a1=a2 then (
      equal_size_lemma (get_fset_vars_tuple_list tl) (get_fset_vars_tuple_list l);
      assert(size (get_fset_vars_tuple_list tl) = size (get_fset_vars_tuple_list l));
      sub_unifiable tl st
      ) else false
  | (Func s1 args1, Func s2 args2)::tl -> if s1 = s2 then (aux_lemma7 args1 args2 tl s1; aux_lemma10 args1 args2 tl s1; sub_unifiable (List.Tot.append (collate args1 args2) tl) st) else false
  | _ -> false

(** This function determines whether the list of tuples of terms is unifiable or not. **)
val is_Unifiable : l:list (term*term) -> Tot bool

let is_Unifiable l = sub_unifiable l []

val is_unifier :ltt:list (term*term) -> st:subst -> Tot bool

let rec is_unifier ltt st = match ltt with
  | [] -> true
  | (hd1,hd2)::tl -> (apply st hd1 = apply st hd2) && (is_unifier tl st)

assume val mgu_lemma : ltt: list (term*term) -> st:subst -> Lemma
  (requires is_unifier ltt st)
  (ensures exists (st2:subst). (if Some? (mgu ltt) then st = compose (Some?.v (mgu ltt)) st2 else true ) )
