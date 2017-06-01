module Mgu

open Term
open Subst

val apply_list_length_lemma : st:subst -> lt:list term -> Lemma
  (requires true)
  (ensures ( List.Tot.length lt = List.Tot.length (apply_list st lt)) )

let rec apply_list_length_lemma st lt = match lt with
  | [] -> ()
  | hd::tl -> apply_list_length_lemma st tl

val mgu: t1:term -> t2:term -> Tot (option subst)
val mgu_list : l1:list term -> l2:list term -> Tot (option subst)
let rec mgu t1 t2 = match t1,t2 with
  | Var v , x -> Some [(v,x)]
  | x , Var v -> Some [(v,x)]
  | Func s args1,Func s args2 -> mgu_list args1 args2
  | _,_ -> None
and mgu_list l1 l2 = match l1,l2 with
  | [],[] -> Some []
  | hd1::tl1 , hd2::tl2 -> begin
      let s1 = mgu hd1 hd2 in
      if None? s1 then None
      else (
            let s2 = Some?.v s1 in
            apply_list_length_lemma s2 tl1 ; apply_list_length_lemma s2 tl2;
            let s3 = mgu_list (apply_list s2 tl1) (apply_list s2 tl2) in
            if None? s3 then None
            else Some ( (FStar.List.Tot.hd s2)::( Some?.v s3 ) )
           )
      end
  | _,_ -> None
