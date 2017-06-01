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

val sub_comp: term -> Tot nat
val sub_comp_list : list term -> Tot nat

let rec sub_comp t = match t with
  | Var v -> 1
  | Name n -> 1
  | Func s args -> 1 + sub_comp_list args
and sub_comp_list args = match args with
  | [] -> 0
  | hd::tl -> sub_comp hd + sub_comp_list tl

val complexity : list (term*term) -> Tot nat

let rec complexity l = match l with
  | [] -> 0
  | hd::tl -> (sub_comp (fst hd)) + (sub_comp (snd hd)) + complexity tl

val sub_mgu : l:list (term*term) -> st:subst -> Tot (option subst)
let rec sub_mgu l st = match l with
  | [] -> Some st
  | (Var v, x)::tl -> begin
                        if not(isnt_cyclic [(v,x)]) then None
                        else (
                          let temp1 = (compose st [(v,x)]) in
                          let temp2 = (apply_tuple_list [(v,x)] tl) in
                          apply_list_length_lemma [(v,x)] tl;
                          (assert (complexity temp2 < complexity l));
                          if None? (sub_mgu temp2 temp1) then None
                          else (sub_mgu temp2 temp1)
                        )
                      end
  | (x,Var v)::tl -> begin
                        if not(isnt_cyclic [(v,x)]) then None
                        else (
                          let temp1 = (compose st [(v,x)]) in
                          let temp2 = (apply_tuple_list [(v,x)] tl) in
                          apply_list_length_lemma [(v,x)] tl;
                          (assert (complexity temp2 < complexity l));
                          if None? (sub_mgu temp2 temp1) then None
                          else (sub_mgu temp2 temp1)
                        )
                     end
  | (Func s args1, Func s args2)::tl -> sub_mgu (List.Tot.append (collate args1 args2) tl) st
  | _ -> None

val mgu : l:list (term*term) -> Tot (option subst)

let mgu l= sub_mgu l []