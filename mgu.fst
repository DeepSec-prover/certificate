module Mgu

open Term
open Subst

val mgu: t1:term -> t2:term -> Tot (option subst)
val mgu_list : l1:list term -> l2:list term -> Tot (option subst)
let rec mgu t1 t2 = match t1,t2 with
  | Var v , Var x -> Some (v,x)
  | Var v , Name n -> Some(v,n)
  | Name n, Var v -> Some (v,n)
  | Func s args1,Func s args2 -> mgu_list args1 args2
  | _,_ -> None
and mgu_list l1 l2 = match l1,l2 with
  | [],[] -> Some []
  | hd1::tl1 , hd2::tl2 -> begin
      let s1 = mgu hd1 hd2 in
      if None? s1 then None
      else Some ( (Some?.v s1)::( mgu_list (apply_list s1 tl1) (apply_list s1 tl2) ) )
      end
