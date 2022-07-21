exception Error of string

(* エラーを発生させる関数 *)
let err s = raise (Error s)

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
  | NilV
  | ConsV of value * value

(* 環境を表す型 *)
and env = Empty | ConsEnv of env * var * value

(* パターンを表す型 *)
and pat = VarPat of var | NilPat | ConsPat of pat * pat | Wild

(* パターンマッチ節を表す型 *)
(* NOTE: Term は terminal の略 *)
and clauses = Term of pat * exp | ConsCl of pat * exp * clauses

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
  | MatchExp of exp * clauses

(* 判断を表す型 *)
type judgement =
  | MatchJ of pat * value * env
  | NotMatchJ of pat * value
  | EvalJ of env * exp * value
  | PlusJ of value * value * value
  | MinusJ of value * value * value
  | MultJ of value * value * value
  | LtJ of value * value * value

exception Not_bound

(* 環境から変数が束縛されている値を求める関数 *)
(* NOTE: 変数が複数の値に束縛されている場合は、抽象構文木の最も右側・外側の値を返す *)
let rec lookup x = function
  | Empty -> raise Not_bound
  | ConsEnv (rest, var, value) -> if var = x then value else lookup x rest

let append_env env1 env2 =
  let rec append_env_with_tmp env1 env2 tmp =
    match (env2, tmp) with
    | Empty, Empty -> env1
    | Empty, ConsEnv (rest, id, v) ->
        append_env_with_tmp (ConsEnv (env1, id, v)) env2 rest
    | ConsEnv (rest, id, v), ConsEnv (_, _, _) ->
        append_env_with_tmp env1 rest (ConsEnv (tmp, id, v))
    | _ -> err "something wrong!"
  in
  append_env_with_tmp env1 env2 Empty

let string_of_prim = function
  | Plus -> "+"
  | Minus -> "-"
  | Mult -> "*"
  | Lt -> "<"

let rec string_of_value = function
  | IntV i -> string_of_int i
  | BoolV b -> string_of_bool b
  | Closure (env, id, e) ->
      "(" ^ string_of_env env ^ ")[fun " ^ id ^ " -> " ^ string_of_exp e ^ "]"
  | RecClosure (env, id, para, e) ->
      "(" ^ string_of_env env ^ ")[rec " ^ id ^ " = fun " ^ para ^ " -> "
      ^ string_of_exp e ^ "]"
  | NilV -> "[]"
  | ConsV (v1, v2) ->
      "(" ^ string_of_value v1 ^ ") :: (" ^ string_of_value v2 ^ ")"

and string_of_env = function
  | ConsEnv (Empty, var, value) -> var ^ " = " ^ string_of_value value
  | ConsEnv (rest, var, value) ->
      string_of_env rest ^ ", " ^ var ^ " = " ^ string_of_value value
  | Empty -> ""

and string_of_pat = function
  | VarPat id -> id
  | NilPat -> "[]"
  | ConsPat (p1, p2) ->
      "(" ^ string_of_pat p1 ^ ") :: (" ^ string_of_pat p2 ^ ")"
  | Wild -> "_"

and string_of_clauses = function
  | Term (p, e) -> string_of_pat p ^ " -> " ^ string_of_exp e
  | ConsCl (p, e, c) ->
      string_of_pat p ^ " -> " ^ string_of_exp e ^ " | " ^ string_of_clauses c

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
  | MatchExp (e, c) ->
      "match " ^ string_of_exp e ^ " with " ^ string_of_clauses c

let string_of_judgement = function
  | PlusJ (i1, i2, i3) ->
      string_of_value i1 ^ " plus " ^ string_of_value i2 ^ " is "
      ^ string_of_value i3
  | MinusJ (i1, i2, i3) ->
      string_of_value i1 ^ " minus " ^ string_of_value i2 ^ " is "
      ^ string_of_value i3
  | MultJ (i1, i2, i3) ->
      string_of_value i1 ^ " times " ^ string_of_value i2 ^ " is "
      ^ string_of_value i3
  | LtJ (i1, i2, i3) ->
      string_of_value i1 ^ " less than " ^ string_of_value i2 ^ " is "
      ^ string_of_value i3
  | _ -> err "something wrong!"
