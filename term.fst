module Term

(***********************
         Types
************************)

type symbol_cat =
  | Constructor: symbol_cat
  | Destructor: symbol_cat

and symbol =
  {
    name_s: string;
    arity: nat;
    category_s: symbol_cat
  }

and quantifier =
  | Free
  | Existential
  | Universal


and variable =
  {
    name: string;
    id: nat;
  }

and name_cat =
  | Public
  | Private

and name =
  {
    name_n : string;
    id : nat
  }

and term =
  | Var : variable -> term
  | Name : name -> term
  | Func : s:symbol -> l:(list term){ List.Tot.length l = s.arity } -> term

(*** Testing functions ***)

val is_equal : term -> term -> Tot bool

val is_function : term -> bool

val is_name : term -> bool

val is_variable : term -> bool

val is_ground : term -> bool

val is_constructor : term -> bool

(*** Generation function ****)

val of_variable : variable -> term

val of_name : name -> term

(*** Access function ****)

val apply_function : symbol -> term list -> term

val root : t:term{ is_function t } -> symbol

val variable_of : t:term { is_variable t } -> variable

val name_of : t:term { is_name t } -> name
