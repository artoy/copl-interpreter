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
  | EMatchN of env * exp * pat * exp * clauses * value * rule * rule * rule
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
              EMatchN (env, e, p, e', c', v, d1, d2, d3)
          | _ -> err "It must either match or not match"))

and derive_judgement j =
  match j with
  | MatchJ (p, v, env) -> (
      match (p, v) with
      | VarPat x, _ -> MVar (x, v, ConsEnv (Empty, x, v))
      | NilPat, NilV -> MNil
      | ConsPat (p1, p2), ConsV (v1, v2) -> (
          let j1 = judge_match p1 v1 in
          let j2 = judge_match p2 v2 in
          match (j1, j2) with
          | MatchJ (_, _, env1), MatchJ (_, _, env2) ->
              let d1 = derive_judgement (MatchJ (p1, v1, env1)) in
              let d2 = derive_judgement (MatchJ (p2, v2, env2)) in
              MCons (p1, p2, v1, v2, env, d1, d2)
          | _ -> err "Must match!")
      | Wild, _ -> MWild v
      | _ -> err "Something wrong!")
  | NotMatchJ (p, v) -> (
      match (p, v) with
      | ConsPat (p1, p2), ConsV (v1, v2) -> (
          let j1 = judge_match p1 v1 in
          match j1 with
          | NotMatchJ (_, _) ->
              let d = derive_judgement (NotMatchJ (p1, v1)) in
              NMConsConsL (p1, p2, v1, v2, d)
          | MatchJ (_, _, _) ->
              let d = derive_judgement (NotMatchJ (p2, v2)) in
              NMConsConsR (p1, p2, v1, v2, d)
          | _ -> err "It must either match or not match")
      | NilPat, ConsV (v1, v2) -> NMConsNil (v1, v2)
      | ConsPat (p1, p2), NilV -> NMNilCons (p1, p2)
      | _ -> err "Something wrong!")
  | EvalJ (env, exp, value) -> derive_exp env exp value
  | PlusJ (_, _, _) -> BPlus j
  | MinusJ (_, _, _) -> BMinus j
  | MultJ (_, _, _) -> BTimes j
  | LtJ (_, _, _) -> BLt j

(* n の数だけインデントのための空白を生成する関数 *)
let rec n_space n = if n = 0 then "" else "  " ^ n_space (n - 1)

(* 導出を出力する関数 *)
let rec pp_derivation n = function
  | MVar (x, v, env) ->
      let s =
        n_space n ^ x ^ " matches " ^ string_of_value v ^ " when ("
        ^ string_of_env env ^ ") by M-Var {}"
      in
      print_string s
  | MNil ->
      let s = n_space n ^ "[] matches [] when () by M-Nil {}" in
      print_string s
  | MCons (p1, p2, v1, v2, env, d1, d2) ->
      let s1 =
        n_space n ^ "(" ^ string_of_pat p1 ^ ") :: (" ^ string_of_pat p2
        ^ ") matches (" ^ string_of_value v1 ^ ") :: (" ^ string_of_value v2
        ^ ") when (" ^ string_of_env env ^ ") by M-Cons {"
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
  | MWild v ->
      let s =
        n_space n ^ "_ matches " ^ string_of_value v ^ " when () by M-Var {}"
      in
      print_string s
  | NMConsNil (v1, v2) ->
      let s =
        n_space n ^ "[] doesn't match (" ^ string_of_value v1 ^ ") :: ("
        ^ string_of_value v2 ^ ") by M-ConsNil {}"
      in
      print_string s
  | NMNilCons (p1, p2) ->
      let s =
        n_space n ^ "(" ^ string_of_pat p1 ^ ") :: (" ^ string_of_pat p2
        ^ ") doesn't match [] by M-NilCons {}"
      in
      print_string s
  | NMConsConsL (p1, p2, v1, v2, d) ->
      let s1 =
        n_space n ^ "(" ^ string_of_pat p1 ^ ") :: (" ^ string_of_pat p2
        ^ ") doesn't match (" ^ string_of_value v1 ^ ") :: ("
        ^ string_of_value v2 ^ ") by M-ConsConsL {}"
      in
      let s2 = n_space n ^ "}" in
      print_string s1;
      print_newline ();
      pp_derivation (n + 1) d;
      print_newline ();
      print_string s2
  | NMConsConsR (p1, p2, v1, v2, d) ->
      let s1 =
        n_space n ^ "(" ^ string_of_pat p1 ^ ") :: (" ^ string_of_pat p2
        ^ ") doesn't match (" ^ string_of_value v1 ^ ") :: ("
        ^ string_of_value v2 ^ ") by M-ConsConsR {}"
      in
      let s2 = n_space n ^ "}" in
      print_string s1;
      print_newline ();
      pp_derivation (n + 1) d;
      print_newline ();
      print_string s2
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
  | EMatchM1 (env, e0, p, e, v, d1, d2, d3) ->
      let s1 =
        n_space n ^ string_of_env env ^ " |- match " ^ string_of_exp e0
        ^ " with " ^ string_of_pat p ^ " -> " ^ string_of_exp e ^ " evalto "
        ^ string_of_value v ^ " by E-MatchM1 {"
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
  | EMatchM2 (env, e0, p, e, c, v, d1, d2, d3) ->
      let s1 =
        n_space n ^ string_of_env env ^ " |- match " ^ string_of_exp e0
        ^ " with " ^ string_of_pat p ^ " -> " ^ string_of_exp e ^ " | "
        ^ string_of_clauses c ^ " evalto " ^ string_of_value v
        ^ " by E-MatchM2 {"
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
  | EMatchN (env, e0, p, e, c, v, d1, d2, d3) ->
      let s1 =
        n_space n ^ string_of_env env ^ " |- match " ^ string_of_exp e0
        ^ " with " ^ string_of_pat p ^ " -> " ^ string_of_exp e ^ " | "
        ^ string_of_clauses c ^ " evalto " ^ string_of_value v
        ^ " by E-MatchN {"
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
