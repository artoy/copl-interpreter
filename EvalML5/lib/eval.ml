open Syntax
open Match

let apply_prim op arg1 arg2 =
  match (op, arg1, arg2) with
  | Plus, IntV i1, IntV i2 -> IntV (i1 + i2)
  | Plus, _, _ -> err "Both arguments must be integer: +"
  | Minus, IntV i1, IntV i2 -> IntV (i1 - i2)
  | Minus, _, _ -> err "Both arguments must be integer: -"
  | Mult, IntV i1, IntV i2 -> IntV (i1 * i2)
  | Mult, _, _ -> err "Both arguments must be integer: *"
  | Lt, IntV i1, IntV i2 -> BoolV (i1 < i2)
  | Lt, _, _ -> err "Both arguments must be integer: <"

(* 式を評価する関数 *)
(* NOTE: 導出木を作る際に、導出木の結論部分に出現しない値を求めるのに用いる *)
let rec eval_exp env = function
  | Var x -> lookup x env
  | IExp i -> IntV i
  | BExp b -> BoolV b
  | BinOp (op, e1, e2) ->
      let arg1 = eval_exp env e1 in
      let arg2 = eval_exp env e2 in
      apply_prim op arg1 arg2
  | IfExp (e1, e2, e3) -> (
      let test = eval_exp env e1 in
      match test with
      | BoolV true -> eval_exp env e2
      | BoolV false -> eval_exp env e3
      | _ -> err "Test expression must be boolean: if")
  | LetExp (id, e1, e2) ->
      let value = eval_exp env e1 in
      eval_exp (ConsEnv (env, id, value)) e2
  | FunExp (id, e) -> Closure (env, id, e)
  | AppExp (e1, e2) -> (
      let funval = eval_exp env e1 in
      let arg = eval_exp env e2 in
      match funval with
      | Closure (env', id, body) ->
          let newenv = ConsEnv (env', id, arg) in
          eval_exp newenv body
      | RecClosure (env', id1, id2, body) ->
          let newenv = ConsEnv (ConsEnv (env', id1, funval), id2, arg) in
          eval_exp newenv body
      | _ -> err "Non-function value is applied")
  | LetRecExp (id1, id2, e1, e2) ->
      let newenv = ConsEnv (env, id1, RecClosure (env, id1, id2, e1)) in
      eval_exp newenv e2
  | NilExp -> NilV
  | ConsExp (e1, e2) ->
      let head = eval_exp env e1 in
      let tail = eval_exp env e2 in
      ConsV (head, tail)
  | MatchExp (e, c) -> (
      let v = eval_exp env e in
      match c with
      | Term (p, e') -> (
          let j = judge_match p v in
          match j with
          | MatchJ (_, _, env1) -> eval_exp (append_env env env1) e'
          | NotMatchJ (_, _) -> err "It does not match to all patterns"
          | _ -> err "It must either match or not match")
      | ConsCl (p, e', c') -> (
          let j = judge_match p v in
          match j with
          | MatchJ (_, _, env1) -> eval_exp (append_env env env1) e'
          | NotMatchJ (_, _) -> eval_exp env (MatchExp (e, c'))
          | _ -> err "It must either match or not match"))
