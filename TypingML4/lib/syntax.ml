module SI = Set.Make (Int)

exception Error of string

(* エラーを発生させる関数 *)
let err s = raise (Error s)

(* 変数を表す型 *)
type var = string

(* 二項演算子を表す型 *)
type prim = Plus | Minus | Mult | Lt

(* 型変数を表す型 *)
type tyvar = int

(* 型を表す型 *)
type ty = BoolT | IntT | FunT of ty * ty | ListT of ty | VarT of tyvar

(* 型環境を表す型 *)
and tyenv = Empty | ConsEnv of tyenv * var * ty

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
  | NilExp
  | ConsExp of exp * exp
  | MatchExp of exp * exp * var * var * exp

(* 判断を表す型 *)
type judgement = Typing of tyenv * exp * ty

exception Not_bound

(* 環境から変数が束縛されている値を求める関数 *)
(* NOTE: 変数が複数の値に束縛されている場合は、抽象構文木の最も右側・外側の値を返す *)
let rec lookup x = function
  | Empty -> raise Not_bound
  | ConsEnv (rest, var, ty) -> if var = x then ty else lookup x rest

(* 新しい型変数を作る関数 *)
let fresh_tyvar =
  let counter = ref 0 in
  let body () =
    let v = !counter in
    counter := v + 1;
    v
  in
  body

(* 型から型変数を取り出す関数 *)
let rec get_tyvar ty =
  match ty with
  | IntT -> SI.empty
  | BoolT -> SI.empty
  | FunT (t1, t2) -> SI.union (get_tyvar t1) (get_tyvar t2)
  | ListT t -> get_tyvar t
  | VarT t -> SI.singleton t

let string_of_prim = function
  | Plus -> "+"
  | Minus -> "-"
  | Mult -> "*"
  | Lt -> "<"

let rec string_of_ty = function
  | IntT -> "int"
  | BoolT -> "bool"
  | FunT (t1, t2) -> string_of_ty t1 ^ " -> " ^ string_of_ty t2
  | ListT t -> string_of_ty t ^ " list"
  | _ -> err "VarT does not appear in the output."

and string_of_tyenv = function
  | ConsEnv (Empty, var, t) -> var ^ " = " ^ string_of_ty t
  | ConsEnv (rest, var, t) ->
      string_of_tyenv rest ^ ", " ^ var ^ " = " ^ string_of_ty t
  | Empty -> ""

and string_of_exp = function
  | IExp i -> string_of_int i
  | BExp b -> string_of_bool b
  | Var v -> v
  | BinOp (op, e1, e2) ->
      string_of_exp e1 ^ " " ^ string_of_prim op ^ " " ^ string_of_exp e2
  | IfExp (e1, e2, e3) ->
      "if " ^ string_of_exp e1 ^ " then " ^ string_of_exp e2 ^ " else "
      ^ string_of_exp e3
  | LetExp (id, e1, e2) ->
      "let " ^ id ^ " = " ^ string_of_exp e1 ^ " in " ^ string_of_exp e2
  | FunExp (id, e) -> "fun " ^ id ^ " -> " ^ string_of_exp e
  | AppExp (e1, e2) -> string_of_exp e1 ^ " (" ^ string_of_exp e2 ^ ")"
  | LetRecExp (id1, id2, e1, e2) ->
      "let rec " ^ id1 ^ " = fun " ^ id2 ^ " -> " ^ string_of_exp e1 ^ " in "
      ^ string_of_exp e2
  | NilExp -> "[]"
  | ConsExp (e1, e2) ->
      "(" ^ string_of_exp e1 ^ ") :: (" ^ string_of_exp e2 ^ ")"
  | MatchExp (e1, e2, id1, id2, e3) ->
      "match " ^ string_of_exp e1 ^ " with [] -> " ^ string_of_exp e2 ^ " | "
      ^ id1 ^ " :: " ^ id2 ^ " -> " ^ string_of_exp e3

let string_of_judgement = function
  | Typing (env, e, t) ->
      string_of_tyenv env ^ " |- " ^ string_of_exp e ^ " : " ^ string_of_ty t
