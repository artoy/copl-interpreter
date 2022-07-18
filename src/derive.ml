open Syntax
open Eval

(* 推論規則を表す型 *)
type rule =
  | EInt of env * int * value
  | EBool of env * bool * value
  | EIfT of env * exp * exp * exp * value * rule * rule
  | EIfF of env * exp * exp * exp * value * rule * rule
  | EPlus of env * exp * exp * value * rule * rule * rule
  | EMinus of env * exp * exp * value * rule * rule * rule
  | ETimes of env * exp * exp * value * rule * rule * rule
  | ELt of env * exp * exp * value * rule * rule * rule
  | EVar1 of env * exp * value
  | Evar2 of env * exp * value * env
  | ELet of env * var * exp * exp * value * rule * rule
  | BPlus of judgement
  | BMinus of judgement
  | BTimes of judgement
  | BLt of judgement

let rec derive_exp env e v =
  match e with
  | IExp i -> EInt (env, i, v)
  | BExp b -> EBool (env, b, v)
  | IfExp (e1, e2, e3) -> (
      let test = eval_exp env e1 in
      let d1 = derive_exp env e1 test in
      match test with
      | BoolV true ->
          let d2 = derive_exp env e2 in
          EIfT (env, e1, e2, e3, v, d1, d2)
      | BoolV false ->
          let d3 = derive_exp env e3 in
          EIfF (env, e1, e2, e3, v, d1, d3)
      | _ -> err "Test expression must be boolean: if")
  | BinOp (op, e1, e2) -> (
      let v1 = eval_exp env e1 in
      let v2 = eval_exp env e2 in
      let d1 = derive_exp env e1 v1 in
      let d2 = derive_exp env e2 v2 in
      match op with
      | Plus ->
          let d3 = derive_judgement (PlusJ (v1, v2, v)) in
          EPlus (env, e1, e2, v, d1, d2, d3)
      | Minus ->
          let d3 = derive_judgement (MinusJ (v1, v2, v)) in
          EMinus (env, e1, e2, v, d1, d2, d3)
      | Mult ->
          let d3 = derive_judgement (MultJ (v1, v2, v)) in
          ETimes (env, e1, e2, v, d1, d2, d3)
      | Lt ->
          let d3 = derive_judgement (LtJ (v1, v2, v)) in
          ELt (env, e1, e2, v, d1, d2, d3))
  | Var x -> (
      match env with
      | Empty -> err "Not bound"
      | Cons (rest, id, value) ->
          if x = id && v = value then EVar1 (env, Var x, v)
          else if x = id then err "The bound value is wrong"
          else Evar2 (env, Var x, v, rest))
  | LetExp (id, e1, e2) ->
      let v1 = eval_exp env e1 in
      let d1 = derive_exp env e1 v1 in
      let d2 = derive_exp (Cons (env, id, v1)) e2 v in
      ELet (env, id, e1, e2, v, d1, d2)

and derive_judgement j =
  match j with
  | Eval (env, exp, value) -> derive_exp env exp value
  | PlusJ (_, _, _) -> BPlus j
  | MinusJ (_, _, _) -> BMinus j
  | MultJ (_, _, _) -> BTimes j
  | LtJ (_, _, _) -> BLt j
