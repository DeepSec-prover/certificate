module Term

(***********************
         Types
************************)

type symbol_cat =
  | Constructor: symbol_cat
  | Destructor: symbol_cat

type symbol =
  {
    name_s: string;
    arity: nat;
    category_s: symbol_cat
  }

type quantifier =
  | Free
  | Existential
  | Universal


type variable =
  {
    name: string;
    id: nat;
  }

type name_cat =
  | Public
  | Private

type name =
  {
    name_n : string;
    id : nat
  }

type term =
  | Var : v:variable -> term
  | Name : n:name -> term
  | Func : s:symbol -> l:(list term){ List.Tot.length l = s.arity } -> term

(*** Testing functions ***)
val is_variable : term ->Tot bool

let is_variable t = Var? t

val is_equal : term -> term -> Tot bool
val is_equal_list : list term -> list term -> Tot bool

let rec is_equal t1 t2 =
  match t1,t2 with
  | Var arg1 , Var arg2 -> (arg1=arg2)
  | Name arg1 ,Name arg2 -> (arg1=arg2)
  | Func s1 args1 ,Func s2 args2 -> (s1=s2)&&(is_equal_list args1 args2)
  | _,_ -> false
  and is_equal_list list1 list2 =
  match list1,list2 with
  | [],[] -> true
  | hd1::tl1,hd2::tl2 -> (is_equal hd1 hd2)&&(is_equal_list tl1 tl2)
  | _,_ -> false
val is_function : term ->Tot  bool

let is_function f = Func? f

val is_name : term ->Tot  bool

let is_name t = Name? t

val is_ground : t:term ->Tot  bool
val is_ground_list : list_term: list term ->Tot  bool

let rec is_ground t =
  match t with
  | Var _ -> false
  | Func _ args -> is_ground_list args
  | _ -> true
and is_ground_list list_term =
match list_term with
| [] -> true
| hd::tl -> is_ground hd && is_ground_list tl

val is_constructor : term -> bool

let is_constructor t =
  if not(is_function t) then false else
  if Constructor? ((Func?.s t).category_s) then true else false


val is_var_present : variable -> term -> Tot bool
val is_var_present_list : variable -> list term -> Tot bool

let rec is_var_present v t =
  match t with
  | Var x -> if x=v then true else false
  | Name n -> false
  | Func _ args -> is_var_present_list v args
  and is_var_present_list v term_list =
  match term_list with
  | [] -> true
  | hd::tl -> (is_var_present v hd) && (is_var_present_list v tl)



(*** Generation function ****)

val of_variable : variable -> term

let of_variable v = Var v

val of_name : name -> term

let of_name n = Name n

(*** Access function ****)

val apply_function : s:symbol -> l:list term{ List.Tot.length l = s.arity }-> term

let apply_function s l = Func s l

val root : t:term{ is_function t } -> symbol

let root t = Func?.s t

val variable_of : t:term { is_variable t } -> variable

let variable_of t = Var?.v t

val name_of : t:term { is_name t } -> name

let name_of t = Name?.n t
