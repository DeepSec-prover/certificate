module Term_interface

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
  | Var : variable -> term
  | Name : name -> term
  | Func : s:symbol -> l:(list term){ List.Tot.length l = s.arity } -> term

(*** Variables ***)

(*** WARNING : DO NOT IMPLEMENT THIS FUNCTION ! Keep it as an assume ***)
assume val fresh : quantifier -> FStar.Set.set variable -> Tot variable

(*** WARNING : DO NOT IMPLEMENT THIS LEMMA ! Keep it as an assume ***)
assume val lemma_fresh : q:quantifier -> set:FStar.Set.set variable ->
  Lemma (requires True)
        (ensures (FStar.Set.mem (fresh q set) set = false))

(*** Testing functions ***)

assume val is_equal : term -> term -> Tot bool

assume val is_function : term -> Tot bool

assume val is_name : term -> Tot bool

assume val is_variable : term -> Tot bool

assume val is_ground : term -> Tot bool

assume val is_constructor : term -> Tot bool

assume val var_occurs : variable -> term -> Tot bool

(*** Generation function ****)

assume val of_variable : variable -> Tot term

assume val of_name : name -> Tot term

assume val apply_function : f:symbol -> l:(list term){ List.Tot.length l = f.arity } -> Tot term

(*** Access function ****)

assume val variable_of : t:term{ is_variable t } -> Tot variable

assume val name_of : t:term{ is_name t } -> Tot name

assume val root : t:term{ is_function t } -> Tot symbol

assume val get_args : term -> Tot (list term)
