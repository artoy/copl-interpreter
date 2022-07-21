open Syntax
open Eval
open Match

(* 推論規則を表す型 *)
type rule =
  | MVar of var * value * env
  | MNil
  | MCons of pat * pat * value * value * env * rule * rule
  | MWild of value
  | NMConsNil of value * value
  | NMNilCons of pat * pat
  | NMConsConsL of pat * pat * value * value * rule
  | NMConsConsR of pat * pat * value * value * rule
  | EInt of env * int * value
  | EBool of env * bool * value
  | EIfT of env * exp * exp * exp * value * rule * rule
  | EIfF of env * exp * exp * exp * value * rule * rule
  | EPlus of env * exp * exp * value * rule * rule * rule
  | EMinus of env * exp * exp * value * rule * rule * rule
  | ETimes of env * exp * exp * value * rule * rule * rule
  | ELt of env * exp * exp * value * rule * rule * rule
  | EVar of env * var * value
  | ELet of env * var * exp * exp * value * rule * rule
  | EFun of env * var * exp
  | EApp of env * exp * exp * value * rule * rule * rule
  | ELetRec of env * var * var * exp * exp * value * rule
  | EAppRec of env * exp * exp * value * rule * rule * rule
  | ENil of env
  | ECons of env * exp * exp * value * value * rule * rule
  | EMatchM1 of env * exp * pat * exp * value * rule * rule * rule
  | EMatchM2 of env * exp * pat * exp * clauses * value * rule * rule * rule
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
  | Var x ->
      if v = lookup x env then EVar (env, x, v) else err "Binded value is wrong"
  | LetExp (id, e1, e2) ->
      let v1 = eval_exp env e1 in
      let d1 = derive_exp env e1 v1 in
      let d2 = derive_exp (ConsEnv (env, id, v1)) e2 v in
      ELet (env, id, e1, e2, v, d1, d2)
  | FunExp (id, e) -> EFun (env, id, e)
  | AppExp (e1, e2) -> (
      let v1 = eval_exp env e1 in
      let v2 = eval_exp env e2 in
      let d1 = derive_exp env e1 v1 in
      let d2 = derive_exp env e2 v2 in
      match v1 with
      | Closure (env', id, body) ->
          let d3 = derive_exp (ConsEnv (env', id, v2)) body v in
          EApp (env, e1, e2, v, d1, d2, d3)
      | RecClosure (env', id, para, body) ->
          let d3 =
            derive_exp (ConsEnv (ConsEnv (env', id, v1), para, v2)) body v
          in
          EAppRec (env, e1, e2, v, d1, d2, d3)
      | _ -> err "Non-function value is applied")
  | LetRecExp (id1, id2, e1, e2) ->
      let d =
        derive_exp (ConsEnv (env, id1, RecClosure (env, id1, id2, e1))) e2 v
      in
      ELetRec (env, id1, id2, e1, e2, v, d)
  | NilExp -> ENil env
  | ConsExp (head, tail) -> (
      match v with
      | ConsV (vHead, vTail) ->
          let d1 = derive_exp env head vHead in
          let d2 = derive_exp env tail vTail in
          ECons (env, head, tail, vHead, vTail, d1, d2)
      | _ -> err "Value must be Cons")
  | MatchExp (e, c) -> (
      let v1 = eval_exp env e in
      match c with
      | Term (p, e') -> (
          let j = judge_match p v1 in
          match j with
          | MatchJ (_, _, env1) ->
              let d1 = derive_exp env e v1 in
              let d2 = derive_judgement j in
              let d3 = derive_exp (append_env env env1) e' v in
              EMatchM1 (env, e, p, e', v, d1, d2, d3)
          | NotMatchJ (_, _) -> err "It does not match to all patterns"
          | _ -> err "It must either match or not match")
      | ConsCl (p, e', c') -> (
          let j = judge_match p v1 in
          match j with
          | MatchJ (_, _, env1) ->
              let d1 = derive_exp env e v1 in
              let d2 = derive_judgement j in
              let d3 = derive_exp (append_env env env1) e' v in
              EMatchM2 (env, e, p, e', c', v, d1, d2, d3)
          | NotMatchJ (_, _) ->
              let d1 = derive_exp env e v1 in
              let d2 = derive_judgement j in
              let d3 = derive_exp env (MatchExp (e, c')) v in
              EMatchM1 (env, e, p, e', v, d1, d2, d3)
          | _ -> err "It must either match or not match"))

and derive_judgement j =
  match j with
  | EvalJ (env, exp, value) -> derive_exp env exp value
  | PlusJ (_, _, _) -> BPlus j
  | MinusJ (_, _, _) -> BMinus j
  | MultJ (_, _, _) -> BTimes j
  | LtJ (_, _, _) -> BLt j

(* n の数だけインデントのための空白を生成する関数 *)
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
  | EVar (env, id, v) ->
      let s =
        n_space n ^ string_of_env env ^ " |- " ^ id ^ " evalto "
        ^ string_of_value v ^ " by E-Var {}"
      in
      print_string s
  | ELet (env, id, e1, e2, v, d1, d2) ->
      let s1 =
        n_space n ^ string_of_env env ^ " |- let " ^ id ^ " = "
        ^ string_of_exp e1 ^ " in " ^ string_of_exp e2 ^ " evalto "
        ^ string_of_value v ^ " by E-Let {"
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
  | EFun (env, id, e) ->
      let s =
        n_space n ^ string_of_env env ^ " |- fun " ^ id ^ " -> "
        ^ string_of_exp e ^ " evalto (" ^ string_of_env env ^ ")[fun " ^ id
        ^ " -> " ^ string_of_exp e ^ "]" ^ " by E-Fun {}"
      in
      print_string s
  | EApp (env, e1, e2, v, d1, d2, d3) ->
      let s1 =
        n_space n ^ string_of_env env ^ " |- " ^ string_of_exp e1 ^ " ("
        ^ string_of_exp e2 ^ ") evalto " ^ string_of_value v ^ " by E-App {"
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
  | ELetRec (env, id, para, e1, e2, v, d) ->
      let s1 =
        n_space n ^ string_of_env env ^ " |- let rec " ^ id ^ " = fun " ^ para
        ^ " -> " ^ string_of_exp e1 ^ " in " ^ string_of_exp e2 ^ " evalto "
        ^ string_of_value v ^ " by E-LetRec {"
      in
      let s2 = n_space n ^ "}" in
      print_string s1;
      print_newline ();
      pp_derivation (n + 1) d;
      print_newline ();
      print_string s2
  | EAppRec (env, e1, e2, v, d1, d2, d3) ->
      let s1 =
        n_space n ^ string_of_env env ^ " |- " ^ string_of_exp e1 ^ " ("
        ^ string_of_exp e2 ^ ") evalto " ^ string_of_value v ^ " by E-AppRec {"
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
  | ENil env ->
      let s = n_space n ^ string_of_env env ^ " |- [] evalto [] by E-Nil {}" in
      print_string s
  | ECons (env, head, tail, vHead, vTail, d1, d2) ->
      let s1 =
        n_space n ^ string_of_env env ^ " |- (" ^ string_of_exp head ^ ") :: ("
        ^ string_of_exp tail ^ ") evalto (" ^ string_of_value vHead ^ ") :: ("
        ^ string_of_value vTail ^ ") by E-Cons {"
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
  | EMatchNil (env, e1, e2, head, tail, e3, v, d1, d2) ->
      let s1 =
        n_space n ^ string_of_env env ^ " |- match " ^ string_of_exp e1
        ^ " with [] -> " ^ string_of_exp e2 ^ " | " ^ head ^ " :: " ^ tail
        ^ " -> " ^ string_of_exp e3 ^ " evalto " ^ string_of_value v
        ^ " by E-MatchNil {"
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
  | EMatchCons (env, e1, e2, head, tail, e3, v, d1, d2) ->
      let s1 =
        n_space n ^ string_of_env env ^ " |- match " ^ string_of_exp e1
        ^ " with [] -> " ^ string_of_exp e2 ^ " | " ^ head ^ " :: " ^ tail
        ^ " -> " ^ string_of_exp e3 ^ " evalto " ^ string_of_value v
        ^ " by E-MatchCons {"
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
  | BPlus j ->
      let s = n_space n ^ string_of_judgement j ^ " by B-Plus {}" in
      print_string s
  | BMinus j ->
      let s = n_space n ^ string_of_judgement j ^ " by B-Minus {}" in
      print_string s
  | BTimes j ->
      let s = n_space n ^ string_of_judgement j ^ " by B-Times {}" in
      print_string s
  | BLt j ->
      let s = n_space n ^ string_of_judgement j ^ " by B-Lt {}" in
      print_string s
