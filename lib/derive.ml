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
  | EVar1 of env * var * value
  | EVar2 of env * var * value * rule
  | ELet of env * var * exp * exp * value * rule * rule
  | EFun of env * var * exp
  | EApp of env * exp * exp * value * rule * rule * rule
  | ELetRec of env * var * var * exp * exp * value * rule
  | EAppRec of env * exp * exp * value * rule * rule * rule
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
          let d2 = derive_exp env e2 v in
          EIfT (env, e1, e2, e3, v, d1, d2)
      | BoolV false ->
          let d3 = derive_exp env e3 v in
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
          if x = id && v = value then EVar1 (env, id, v)
          else if x = id then err "The bound value is wrong"
          else
            let d = derive_exp rest e v in
            EVar2 (env, id, v, d))
  | LetExp (id, e1, e2) ->
      let v1 = eval_exp env e1 in
      let d1 = derive_exp env e1 v1 in
      let d2 = derive_exp (Cons (env, id, v1)) e2 v in
      ELet (env, id, e1, e2, v, d1, d2)
  | FunExp (id, e) -> EFun (env, id, e)
  | AppExp (e1, e2) -> (
      let v1 = eval_exp env e1 in
      let v2 = eval_exp env e2 in
      let d1 = derive_exp env e1 v1 in
      let d2 = derive_exp env e2 v2 in
      match v1 with
      | Closure (env', id, body) ->
          let d3 = derive_exp (Cons (env', id, v2)) body v in
          EApp (env, e1, e2, v, d1, d2, d3)
      | RecClosure (env', id, para, body) ->
          let d3 = derive_exp (Cons (Cons (env', id, v1), para, v2)) body v in
          EAppRec (env, e1, e2, v, d1, d2, d3)
      | _ -> err "Non-function value is applied")
  | LetRecExp (id1, id2, e1, e2) ->
      let d =
        derive_exp (Cons (env, id1, RecClosure (env, id1, id2, e1))) e2 v
      in
      ELetRec (env, id1, id2, e1, e2, v, d)

and derive_judgement j =
  match j with
  | Eval (env, exp, value) -> derive_exp env exp value
  | PlusJ (_, _, _) -> BPlus j
  | MinusJ (_, _, _) -> BMinus j
  | MultJ (_, _, _) -> BTimes j
  | LtJ (_, _, _) -> BLt j

let rec n_space n = if n = 0 then "" else "  " ^ n_space (n - 1)

(* 導出を出力する関数 *)
let rec pp_derivation n = function
  | EInt (env, i, v) ->
      let s =
        n_space n ^ string_of_env env ^ " |- " ^ string_of_int i ^ " evalto "
        ^ string_of_value v ^ " by E-Int {}"
      in
      print_string s
  | EBool (env, b, v) ->
      let s =
        n_space n ^ string_of_env env ^ " |- " ^ string_of_bool b ^ " evalto "
        ^ string_of_value v ^ " by E-Bool {}"
      in
      print_string s
  | EIfT (env, e1, e2, e3, v, d1, d2) ->
      let s1 =
        n_space n ^ string_of_env env ^ " |- if " ^ string_of_exp e1 ^ " then "
        ^ string_of_exp e2 ^ " else " ^ string_of_exp e3 ^ " evalto "
        ^ string_of_value v ^ " by E-IfT {"
      in
      let s2 = n_space n ^ "}" in
      print_string s1;
      print_newline ();
      pp_derivation (n + 1) d1;
      print_string ";";
      print_newline ();
      pp_derivation (n + 1) d2;
      print_newline ();
      print_string s2
  | EIfF (env, e1, e2, e3, v, d1, d2) ->
      let s1 =
        n_space n ^ string_of_env env ^ " |- if " ^ string_of_exp e1 ^ " then "
        ^ string_of_exp e2 ^ " else " ^ string_of_exp e3 ^ " evalto "
        ^ string_of_value v ^ " by E-IfF {"
      in
      let s2 = n_space n ^ "}" in
      print_string s1;
      print_newline ();
      pp_derivation (n + 1) d1;
      print_string ";";
      print_newline ();
      pp_derivation (n + 1) d2;
      print_newline ();
      print_string s2
  | EPlus (env, e1, e2, v, d1, d2, d3) ->
      let s1 =
        n_space n ^ string_of_env env ^ " |- " ^ string_of_exp e1 ^ " + "
        ^ string_of_exp e2 ^ " evalto " ^ string_of_value v ^ " by E-Plus {"
      in
      let s2 = n_space n ^ "}" in
      print_string s1;
      print_newline ();
      pp_derivation (n + 1) d1;
      print_string ";";
      print_newline ();
      pp_derivation (n + 1) d2;
      print_string ";";
      print_newline ();
      pp_derivation (n + 1) d3;
      print_newline ();
      print_string s2
  | EMinus (env, e1, e2, v, d1, d2, d3) ->
      let s1 =
        n_space n ^ string_of_env env ^ " |- " ^ string_of_exp e1 ^ " - "
        ^ string_of_exp e2 ^ " evalto " ^ string_of_value v ^ " by E-Minus {"
      in
      let s2 = n_space n ^ "}" in
      print_string s1;
      print_newline ();
      pp_derivation (n + 1) d1;
      print_string ";";
      print_newline ();
      pp_derivation (n + 1) d2;
      print_string ";";
      print_newline ();
      pp_derivation (n + 1) d3;
      print_newline ();
      print_string s2
  | ETimes (env, e1, e2, v, d1, d2, d3) ->
      let s1 =
        n_space n ^ string_of_env env ^ " |- " ^ string_of_exp e1 ^ " * "
        ^ string_of_exp e2 ^ " evalto " ^ string_of_value v ^ " by E-Times {"
      in
      let s2 = n_space n ^ "}" in
      print_string s1;
      print_newline ();
      pp_derivation (n + 1) d1;
      print_string ";";
      print_newline ();
      pp_derivation (n + 1) d2;
      print_string ";";
      print_newline ();
      pp_derivation (n + 1) d3;
      print_newline ();
      print_string s2
  | ELt (env, e1, e2, v, d1, d2, d3) ->
      let s1 =
        n_space n ^ string_of_env env ^ " |- " ^ string_of_exp e1 ^ " < "
        ^ string_of_exp e2 ^ " evalto " ^ string_of_value v ^ " by E-Lt {"
      in
      let s2 = n_space n ^ "}" in
      print_string s1;
      print_newline ();
      pp_derivation (n + 1) d1;
      print_string ";";
      print_newline ();
      pp_derivation (n + 1) d2;
      print_string ";";
      print_newline ();
      pp_derivation (n + 1) d3;
      print_newline ();
      print_string s2
  | EVar1 (env, id, v) ->
      let s =
        n_space n ^ string_of_env env ^ " |- " ^ id ^ " evalto "
        ^ string_of_value v ^ " by E-Var1 {}"
      in
      print_string s
  | EVar2 (env, id, v, d) ->
      let s1 =
        n_space n ^ string_of_env env ^ " |- " ^ id ^ " evalto "
        ^ string_of_value v ^ " by E-Var2 {"
      in
      let s2 = n_space n ^ "}" in
      print_string s1;
      print_newline ();
      pp_derivation (n + 1) d;
      print_newline ();
      print_string s2
  | ELet (env, id, e1, e2, v, d1, d2) ->
    
