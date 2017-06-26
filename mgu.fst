module Mgu

open Term
open Subst
open Fset
open Union

val apply_tuple_list : st:subst -> l:list (term*term) -> Tot (list (term*term))

let rec apply_tuple_list st l = match l with
  | [] -> []
  | (hd1,hd2)::tl -> (apply st hd1 , apply st hd2)::(apply_tuple_list st tl)

val apply_list_length_lemma : st:subst -> l:list (term*term) -> Lemma
  (requires true)
  (ensures ( List.Tot.length l = List.Tot.length (apply_tuple_list st l)) )

let rec apply_list_length_lemma st l = match l with
  | [] -> ()
  | hd::tl -> apply_list_length_lemma st tl

val collate : l1:list term -> l2:list term {List.Tot.length l1 = List.Tot.length l2}-> Tot (list (term*term))

let rec collate l1 l2 = match l1,l2 with
  | [],[] -> []
  | hd1::tl1,hd2::tl2 -> (hd1,hd2)::(collate tl1 tl2)

(*val is_Unifiable : l:list (term*term) -> Tot bool

let rec is_Unifiable*)

(*val get_list_of_vars : term -> list variable -> Tot (list variable)
val get_list_of_vars_list : list term -> list variable -> Tot (list variable)

let rec get_list_of_vars t lv =
  match t with
  | Var v -> if mem v lv then lv else v::lv
  | Name n -> lv
  | (Func s args) -> get_list_of_vars_list args lv
and get_list_of_vars_list lt lv = match lt with
  | [] -> lv
  | hd::tl -> begin
                let temp1 = get_list_of_vars hd lv in
                get_list_of_vars_list tl temp1
              end*)

val get_fset_vars : term -> Tot (fset variable)
val get_fset_vars_list : list term -> Tot (fset variable)

let rec get_fset_vars t= match t with
  | Var v -> fsingleton v
  | Name n -> fempty
  | Func s args -> get_fset_vars_list args
and get_fset_vars_list lt = match lt with
  | [] -> fempty
  | hd::tl -> funion (get_fset_vars hd) (get_fset_vars_list tl)

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

val get_num_symbols_tuple_list : ltt:list (term*term) -> Tot nat

let rec get_num_symbols_tuple_list ltt = match ltt with
  | [] -> 0
  | (hd1,hd2)::tl -> get_num_symbols hd1 + get_num_symbols hd2 + get_num_symbols_tuple_list tl

val get_fset_vars_tuple_list : list (term*term) -> Tot (fset variable)

let rec get_fset_vars_tuple_list ltt = match ltt with
  | [] -> fempty
  | (hd1,hd2)::tl -> funion (get_fset_vars hd1)  (funion (get_fset_vars hd2) (get_fset_vars_tuple_list tl))

val tuple_fset_lemma : t1:term -> t2:term -> ltt: list (term*term) -> Lemma
  (requires true)
  (ensures (equal (get_fset_vars_tuple_list ( (t1,t2)::ltt )) (get_fset_vars_tuple_list ( (t2,t1)::ltt ))) )
  [SMTPat (get_fset_vars_tuple_list ( (t1,t2)::ltt ))]

let tuple_fset_lemma t1 t2 ltt = ()

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

val aux_lemma1c : ltt:list (term*term) -> v:variable -> t:term -> Lemma
  (requires not(is_var_present v t))
  (ensures fsubset (get_fset_vars_tuple_list (apply_tuple_list [(v,t)] ltt)) (get_fset_vars_tuple_list ( (Var v,t)::ltt ) ) )

let rec aux_lemma1c ltt v t = match ltt with
  | [] -> ()
  | (hd1,hd2)::tl -> aux_lemma1a hd1 v t; aux_lemma1a hd2 v t; aux_lemma1c tl v t

val aux_lemma2 : ltt:list (term*term) -> v:variable -> t:term -> Lemma
  (requires true)
  (ensures (mem v (get_fset_vars_tuple_list ((Var v,t)::ltt))) )

let aux_lemma2 ltt v t = ()

val aux_lemma3a : v:variable -> t:term -> Lemma (requires not(is_var_present v t)) (ensures not(mem v (get_fset_vars t)))
val aux_lemma3b : v:variable -> lt:list term -> Lemma (requires not(is_var_present_list v lt)) (ensures not(mem v (get_fset_vars_list lt)))

let rec aux_lemma3a v t = match t with
  | Var w -> assert(not(v=w))
  | Name n -> ()
  | Func s args -> aux_lemma3b v args
and aux_lemma3b v lt = match lt with
  | [] -> ()
  | hd::tl -> aux_lemma3a v hd ; aux_lemma3b v tl

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

val aux_lemma3 : ltt:list (term*term) -> v:variable -> t:term -> Lemma
  (requires not(is_var_present v t))
  (ensures not(mem v (get_fset_vars_tuple_list (apply_tuple_list [(v,t)] ltt))))

let rec aux_lemma3 ltt v t = match ltt with
  | [] -> ()
  | (hd1,hd2)::tl -> aux_lemma4a hd1 v t; aux_lemma4a hd2 v t; aux_lemma3 tl v t

val aux_lemma5 : ltt:list (term*term) -> v:variable -> t:term -> Lemma
  (requires not(is_var_present v t))
  (ensures size (get_fset_vars_tuple_list (apply_tuple_list [(v,t)] ltt)) < size (get_fset_vars_tuple_list ((Var v,t)::ltt)) )

let rec aux_lemma5 ltt v t = aux_lemma1c ltt v t; aux_lemma2 ltt v t; aux_lemma3 ltt v t ;
                             size_lemma v (get_fset_vars_tuple_list (apply_tuple_list [(v,t)] ltt)) (get_fset_vars_tuple_list ((Var v,t)::ltt))

assume val aux_lemma6 : lt1:list term -> lt2:list term ->  ltt:list (term*term) -> s:symbol -> Lemma
  (requires ((List.Tot.length lt1 = s.arity) && (List.Tot.length lt2 = s.arity) ) )
  (ensures (assert(List.Tot.length lt1 = List.Tot.length lt2); size (get_fset_vars_tuple_list (List.Tot.append (collate lt1 lt2) ltt)) < size (get_fset_vars_tuple_list ((Func s lt1, Func s lt2)::ltt) ) ))


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
      assert(size (get_fset_vars_tuple_list tl) = size (get_fset_vars_tuple_list l));
      sub_mgu tl st
      ) else None
  | (Func s1 args1, Func s2 args2)::tl -> if s1 = s2 then (sub_mgu (List.Tot.append (collate args1 args2) tl) st) else None
  | _ -> None

val mgu : l:list (term*term) -> Tot (option subst)

let mgu l= sub_mgu l []
