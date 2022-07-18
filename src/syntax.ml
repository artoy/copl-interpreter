(* 変数を表す型 *)
type var = string

(* 二項演算子を表す型 *)
type prim = Plus | Minus | Mult | Lt

(* 値を表す型 *)
type value =
  | IntV of int
  | BoolV of bool
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
  | PlusJ of int * int * value
  | MinusJ of int * int * value
  | MultJ of int * int * value
  | LtJ of int * int * value

exception Not_bound

(* 環境から変数が束縛されている値を求める関数 *)
(* NOTE: 変数が複数の値に束縛されている場合は、抽象構文木の最も右側・外側の値を返す *)
let rec lookup x = function
  | Empty -> raise Not_bound
  | Cons (rest, var, value) -> if var = x then value else lookup x rest
