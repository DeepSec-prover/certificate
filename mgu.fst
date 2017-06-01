module Mgu

open Term
open Subst

val apply_tuple_list : st:subst -> l:list (term*term) -> Tot (list (term*term))

let rec apply_tuple_list st l = match l with
  | [] -> []
  | (hd1,hd2)::tl -> (apply st hd1 , apply st hd2)::(apply_tuple_list st tl)

val sub_mgu : l:list (term*term) -> st:subst -> Tot (option subst)
let rec sub_mgu l st = match l with
  | [] -> Some st
  | (Var v, x)::tl -> begin
                        let temp1 = (compose st [(v,x)]) in
                        let temp2 = (apply_tuple_list [(v,x)] tl) in
                        if None? (sub_mgu temp2 temp1) then None
                        else (sub_mgu temp2 temp1)
                      end
  | (x,Var v)::tl -> begin
                        let temp1 = (compose st [(v,x)]) in
                        let temp2 = (apply_tuple_list [(v,x)] tl) in
                        if None? (sub_mgu temp2 temp1) then None
                        else (sub_mgu temp2 temp1)
                     end
  | _ -> None
