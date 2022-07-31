open Syntax
open Typing

(* 推論規則を表す型 *)
type rule =
  | TInt of tyenv * int
  | TBool of tyenv * bool
  | TIf of tyenv * exp * exp * exp * ty * rule * rule * rule
  | TPlus of tyenv * exp * exp * rule * rule
  | TMinus of tyenv * exp * exp * rule * rule
  | TTimes of tyenv * exp * exp * rule * rule
  | TLt of tyenv * exp * exp * rule * rule
  | TVar of tyenv * var * ty
  | TLet of tyenv * var * exp * exp * ty * rule * rule
  | TFun of tyenv * var * exp * ty * ty * rule
  | TApp of tyenv * exp * exp * ty * rule * rule
  | TLetRec of tyenv * var * var * exp * exp * ty * rule * rule
  | TNil of tyenv * ty
  | TCons of tyenv * exp * exp * ty * rule * rule
  | TMatch of tyenv * exp * exp * var * var * exp * ty * rule * rule * rule

let rec derive_exp tyenv e ty =
  match e with
  | IExp i -> TInt (tyenv, i)
  | BExp b -> TBool (tyenv, b)
  | IfExp (e1, e2, e3) ->
      let d1 = derive_exp tyenv e1 BoolT in
      let d2 = derive_exp tyenv e2 ty in
      let d3 = derive_exp tyenv e3 ty in
      TIf (tyenv, e1, e2, e3, ty, d1, d2, d3)
  | BinOp (op, e1, e2) -> (
      let d1 = derive_exp tyenv e1 IntT in
      let d2 = derive_exp tyenv e2 IntT in
      match op with
      | Plus -> TPlus (tyenv, e1, e2, d1, d2)
      | Minus -> TMinus (tyenv, e1, e2, d1, d2)
      | Mult -> TTimes (tyenv, e1, e2, d1, d2)
      | Lt -> TLt (tyenv, e1, e2, d1, d2))
  | Var x ->
      if ty = lookup x tyenv then TVar (tyenv, x, ty)
      else err "Binded value is wrong"
  | LetExp (id, e1, e2) ->
      let _, t1, _ = pt tyenv e1 in
      let d1 = derive_exp tyenv e1 t1 in
      let d2 = derive_exp (ConsEnv (tyenv, id, t1)) e2 ty in
      TLet (tyenv, id, e1, e2, ty, d1, d2)
  | FunExp (id, e) -> (
      match ty with
      | FunT (t1, t2) ->
          let d1 = derive_exp (ConsEnv (tyenv, id, t1)) e t2 in
          TFun (tyenv, id, e, t1, t2, d1)
      | _ -> err "The type should be a function type.")
  | AppExp (e1, e2) ->
      let _, t1, _ = pt tyenv e1 in
      let _, t2, _ = pt tyenv e2 in
      let d1 = derive_exp tyenv e1 t1 in
      let d2 = derive_exp tyenv e2 t2 in
      TApp (tyenv, e1, e2, ty, d1, d2)
  | LetRecExp (id1, id2, e1, e2) -> (
      let s, _, vars = pt tyenv e in
      match vars with
      | [ VarT v1; VarT v2 ] -> (
          let t12 = get_ty_from_tyvar s v1 in
          let t1 = get_ty_from_tyvar s v2 in
          match t1 with
          | FunT (_, t2) ->
              let d1 =
                derive_exp (ConsEnv (ConsEnv (tyenv, id1, t12), id2, t1)) e1 t2
              in
              let d2 = derive_exp (ConsEnv (tyenv, id1, t12)) e2 ty in
              TLetRec (tyenv, id1, id2, e1, e2, ty, d1, d2)
          | _ -> err "Something wrong in derive let rec")
      | _ -> err "Something wrong in derive let rec")
  | NilExp -> TNil (tyenv, ty)
  | ConsExp (e1, e2) -> (
      match ty with
      | ListT t ->
          let d1 = derive_exp tyenv e1 t in
          let d2 = derive_exp tyenv e2 ty in
          TCons (tyenv, e1, e2, t, d1, d2)
      | _ -> err "Type must be list")
  | MatchExp (e1, e2, id1, id2, e3) -> (
      let _, tlist, _ = pt tyenv e1 in
      match tlist with
      | ListT t ->
          let d1 = derive_exp tyenv e1 tlist in
          let d2 = derive_exp tyenv e2 ty in
          let d3 =
            derive_exp (ConsEnv (ConsEnv (tyenv, id1, t), id2, tlist)) e3 ty
          in
          TMatch (tyenv, e1, e2, id1, id2, e3, ty, d1, d2, d3)
      | _ -> err "Value after match must be Nil or Cons")

and derive_judgement j =
  match j with Typing (tyenv, e, ty) -> derive_exp tyenv e ty

(* n の数だけインデントのための空白を生成する関数 *)
let rec n_space n = if n = 0 then "" else "  " ^ n_space (n - 1)

(* 導出を出力する関数 *)
let rec pp_derivation n = function
  | TInt (tyenv, i) ->
      let s =
        n_space n ^ string_of_tyenv tyenv ^ " |- " ^ string_of_int i
        ^ " : int by T-Int {}"
      in
      print_string s
  | TBool (tyenv, b) ->
      let s =
        n_space n ^ string_of_tyenv tyenv ^ " |- " ^ string_of_bool b
        ^ " : bool by T-Bool {}"
      in
      print_string s
  | TIf (tyenv, e1, e2, e3, ty, d1, d2, d3) ->
      let s1 =
        n_space n ^ string_of_tyenv tyenv ^ " |- if " ^ string_of_exp e1
        ^ " then " ^ string_of_exp e2 ^ " else " ^ string_of_exp e3 ^ " : "
        ^ string_of_ty ty ^ " by T-If {"
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
  | TPlus (tyenv, e1, e2, d1, d2) ->
      let s1 =
        n_space n ^ string_of_tyenv tyenv ^ " |- " ^ string_of_exp e1 ^ " + "
        ^ string_of_exp e2 ^ " : int by T-Plus {"
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
  | TMinus (tyenv, e1, e2, d1, d2) ->
      let s1 =
        n_space n ^ string_of_tyenv tyenv ^ " |- " ^ string_of_exp e1 ^ " - "
        ^ string_of_exp e2 ^ " : int by T-Minus {"
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
  | TTimes (tyenv, e1, e2, d1, d2) ->
      let s1 =
        n_space n ^ string_of_tyenv tyenv ^ " |- " ^ string_of_exp e1 ^ " * "
        ^ string_of_exp e2 ^ " : int by T-Times {"
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
  | TLt (tyenv, e1, e2, d1, d2) ->
      let s1 =
        n_space n ^ string_of_tyenv tyenv ^ " |- " ^ string_of_exp e1 ^ " < "
        ^ string_of_exp e2 ^ " : bool by T-Lt {"
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
  | TVar (tyenv, id, ty) ->
      let s =
        n_space n ^ string_of_tyenv tyenv ^ " |- " ^ id ^ " : "
        ^ string_of_ty ty ^ " by T-Var {}"
      in
      print_string s
  | TLet (tyenv, id, e1, e2, ty, d1, d2) ->
      let s1 =
        n_space n ^ string_of_tyenv tyenv ^ " |- let " ^ id ^ " = "
        ^ string_of_exp e1 ^ " in " ^ string_of_exp e2 ^ " : " ^ string_of_ty ty
        ^ " by T-Let {"
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
  | TFun (tyenv, id, e, ty1, ty2, d1) ->
      let s =
        n_space n ^ string_of_tyenv tyenv ^ " |- fun " ^ id ^ " -> "
        ^ string_of_exp e ^ " : (" ^ string_of_ty ty1 ^ " -> "
        ^ string_of_ty ty2 ^ ") by T-Fun {}"
      in
      print_string s
  | TApp (tyenv, e1, e2, ty, d1, d2) ->
      let s1 =
        n_space n ^ string_of_tyenv tyenv ^ " |- " ^ string_of_exp e1 ^ " ("
        ^ string_of_exp e2 ^ ") evalto " ^ string_of_ty ty ^ " by E-App {"
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
  | TLetRec (tyenv, id, para, e1, e2, ty, d1, d2) ->
      let s1 =
        n_space n ^ string_of_tyenv tyenv ^ " |- let rec " ^ id ^ " = fun "
        ^ para ^ " -> " ^ string_of_exp e1 ^ " in " ^ string_of_exp e2 ^ " : "
        ^ string_of_ty ty ^ " by T-LetRec {"
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
  | TNil (tyenv, ty) ->
      let s =
        n_space n ^ string_of_tyenv tyenv ^ " |- [] : " ^ string_of_ty ty
        ^ " list by E-Nil {}"
      in
      print_string s
  | TCons (tyenv, e1, e2, ty, d1, d2) ->
      let s1 =
        n_space n ^ string_of_tyenv tyenv ^ " |- (" ^ string_of_exp e1
        ^ ") :: (" ^ string_of_exp e2 ^ ") : " ^ string_of_ty ty
        ^ " list by E-Cons {"
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
  | TMatch (tyenv, e1, e2, id1, id2, e3, ty, d1, d2, d3) ->
      let s1 =
        n_space n ^ string_of_tyenv tyenv ^ " |- match " ^ string_of_exp e1
        ^ " with [] -> " ^ string_of_exp e2 ^ " | " ^ id1 ^ " :: " ^ id2
        ^ " -> " ^ string_of_exp e3 ^ " : " ^ string_of_ty ty
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