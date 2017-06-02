module Mgu

open Term
open Subst

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

val sub_comp : lt:list term -> Tot nat

let rec sub_comp lt = 

val get_num_vars : lt:list term -> list variable -> Tot nat (decreases sub_comp lt)

let rec get_num_vars lt lv =
  match lt with
  | (Var v)::tl -> if mem v lv then get_num_vars tl lv else get_num_vars tl (v::lv)
  | (Name n)::tl -> get_num_vars tl lv
  | (Func s args)::tl -> get_num_vars (List.Tot.append args tl) lv

val get_num_symbols : lt:list term -> Tot nat (decreases sub_comp lt)

let rec get_num_symbols lt =
  match lt with
  | (Var v)::tl -> 1 + get_num_symbols tl
  | (Name n)::tl -> 1 + get_num_symbols tl
  | (Func s args)::tl -> 1 + get_num_symbols (List.Tot.append args tl)

val sub_mgu : l:list (term*term) -> st:subst -> Tot (option subst) (decreases %[(get_num_vars l []);(get_num_symbols l)])
let rec sub_mgu l st = match l with
  | [] -> Some st
  | (Var v, x)::tl -> begin
                        if (is_var_present v x) then None
                        else (
                          let temp1 = (compose st [(v,x)]) in
                          let temp2 = (apply_tuple_list [(v,x)] tl) in
                          apply_list_length_lemma [(v,x)] tl;
                          (assert (temp2 << l));
                          if None? (sub_mgu temp2 temp1) then None
                          else (sub_mgu temp2 temp1)
                        )
                      end
  | (x,Var v)::tl -> begin
                        if (is_var_present v x) then None
                        else (
                          let temp1 = (compose st [(v,x)]) in
                          let temp2 = (apply_tuple_list [(v,x)] tl) in
                          apply_list_length_lemma [(v,x)] tl;
                          (*(assert (complexity temp2 < complexity l));*)
                          if None? (sub_mgu temp2 temp1) then None
                          else (sub_mgu temp2 temp1)
                        )
                     end
  | (Func s args1, Func s args2)::tl -> sub_mgu (List.Tot.append (collate args1 args2) tl) st
  | (Name a, Name a)::tl  -> sub_mgu tl st
  | _ -> None

val mgu : l:list (term*term) -> Tot (option subst)

let mgu l= sub_mgu l []
