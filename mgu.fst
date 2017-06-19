module Mgu

open Term
open Subst
open FStar.Set
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

val get_num_vars : term -> set variable -> Tot (nat*(set variable))
val get_num_vars_list : list term -> set variable  -> Tot (nat*(set variable))

let rec get_num_vars t sv = match t with
  | Var v -> if mem v sv then (0,sv) else  (1,(union sv (singleton v)))
  | Name n -> (0,sv)
  | Func s args -> get_num_vars_list args sv
and get_num_vars_list lt sv = match lt with
  | [] -> (0,empty)
  | hd::tl -> begin
              let temp1 = get_num_vars hd sv in
              let temp2 = (get_num_vars_list tl (snd temp1)) in
              ((fst temp1)+(fst temp2),(snd temp2))
              end

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

val get_num_vars_tuple_list : list (term*term) -> set variable -> Tot nat

let rec get_num_vars_tuple_list ltt sv = match ltt with
  | [] -> 0
  | (hd1,hd2)::tl -> let temp1 = get_num_vars hd1 sv in
                    let temp2 = get_num_vars hd2 (snd temp1) in
                    (fst temp1) + (fst temp2) + (get_num_vars_tuple_list tl (snd temp2))

val rearrange_tuple_list : #a:eqtype -> list(a*a) -> Tot (list a)

let rec rearrange_tuple_list #a l = match l with
  | [] -> []
  | (x,y)::tl -> x::(y::(rearrange_tuple_list tl))


val aux_lemma1a : t:term -> sv1:set variable -> sv2:set variable -> Lemma (requires true) (ensures (subset sv1 sv2  ==> (fst (get_num_vars t sv1) >= fst (get_num_vars t sv2))))
val aux_lemma1b : lt:list term -> sv1:set variable -> sv2:set variable -> Lemma
  (requires subset sv1 sv2)
  (ensures (fst (get_num_vars_list lt sv1) >= fst (get_num_vars_list lt sv2)))
val aux_lemma1e : t:term -> sv:set variable -> Lemma (requires true)(ensures (subset (sv) (snd (get_num_vars t sv))))
val aux_lemma1f : lt:list term -> sv:set variable -> Lemma (requires true)(ensures (subset (sv) (snd (get_num_vars_list lt sv))))
let rec aux_lemma1e t sv = match t with
  | Var v -> ()
  | Name n -> ()
  | Func s args -> aux_lemma1f args sv
and aux_lemma1f lt sv = match lt with
  | [] -> ()
  | hd::tl -> aux_lemma1e hd sv

let rec aux_lemma1a t sv1 sv2 = match t with
  | Var v -> if mem v sv1 then (assert (fst (get_num_vars t sv1) = 0); assert (fst (get_num_vars t sv2) = 0))
             else if mem v sv2 then (assert (fst (get_num_vars t sv1) = 1); assert (fst (get_num_vars t sv2) = 0))
             else (assert (fst (get_num_vars t sv1) = 1); assert (fst (get_num_vars t sv2) = 1))
  | Name n -> (assert (fst (get_num_vars t sv1) = 0); assert (fst (get_num_vars t sv2) = 0))
  | Func s args -> aux_lemma1b args sv1 sv2
and aux_lemma1b lt sv1 sv2 = match lt with
  | [] -> ()
  | hd::tl -> aux_lemma1a hd sv1 sv2 ;aux_lemma1b tl sv1 sv2

val aux_lemma2 : hd1:term -> hd2:term -> tl:list (term*term) -> Lemma
  (requires true)
  (ensures get_num_vars_tuple_list ((hd1,hd2)::tl) empty <= fst (get_num_vars hd1 empty) + fst (get_num_vars hd2 empty) + get_num_vars_tuple_list tl empty)

let aux_lemma2 hd1 hd2 tl= ()

val aux_lemma9 : v:variable -> x:term -> ltt:list (term*term) -> Lemma
  (requires true)
  (ensures get_num_vars_tuple_list (apply_tuple_list [(v,x)] ltt) empty < get_num_vars_tuple_list ((Var v,x)::ltt) empty)

let rec aux_lemma9 v x ltt = admit()

val sub_mgu : l:list (term*term) -> st:subst -> Tot (option subst) (decreases %[get_num_vars_tuple_list l empty;(get_num_symbols_list (rearrange_tuple_list l))])
let rec sub_mgu l st = match l with
  | [] -> Some st
  | (Var v, x)::tl
  | (x,Var v)::tl -> begin
                        if (is_var_present v x) then None
                        else (
                          let temp1 = (compose st [(v,x)]) in
                          let temp2 = (apply_tuple_list [(v,x)] tl) in
                          aux_lemma9 v x tl;
                          if None? (sub_mgu temp2 temp1) then None
                          else (sub_mgu temp2 temp1)
                        )
                     end
  | (Func s1 args1, Func s2 args2)::tl -> if s1 = s2 then (sub_mgu (List.Tot.append (collate args1 args2) tl) st) else None
  | (Name a1, Name a2)::tl  -> if a1=a2 then sub_mgu tl st else None
  | _ -> None

val mgu : l:list (term*term) -> Tot (option subst)

let mgu l= sub_mgu l []
