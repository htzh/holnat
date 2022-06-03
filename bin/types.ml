type hol_type = Tyvar of string | Tyapp of string * hol_type list [@@deriving show]

type term =
  | Var of string * hol_type
  | Const of string * hol_type
  | Comb of term * term
  | Abs of term * term
