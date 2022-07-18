(* 変数を表す型 *)
type var = string

(* 二項演算子を表す型 *)
type prim = Plus | Minus | Mult | Lt

(* 値を表す型 *)
type value =
  | ILit of int
  | BLit of bool
  | Closure of env * var * exp
  | RecClosure of env * var * var * exp

(* 環境を表す型 *)
and env = Empty | Cons of env * var * value

(* 式を表す型 *)
and exp =
  | IExp of int
  | BExp of bool
  | Var of var
  | BinOp of prim * exp * exp
  | IfExp of exp * exp * exp
  | LetExp of var * exp * exp
  | FunExp of var * exp
  | AppExp of exp * exp
  | LetRecExp of var * var * exp * exp

(* 判断を表す型 *)
type judgement =
  | Eval of env * exp * value
  | PlusJ of int * int * int
  | MinusJ of int * int * int
  | MultJ of int * int * int
  | LtJ of int * int * bool
