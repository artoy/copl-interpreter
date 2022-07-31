open Syntax

type ty_subst = (tyvar * ty) list
type ty_equation = (ty * ty) list

(* 型の等式制約（方程式）を抽出する関数 *)
let rec extract tyenv e =
  match e with
  | IExp _ -> ([], IntT)
  | BExp _ -> ([], BoolT)
  | Var v -> ([], lookup v tyenv)
  | BinOp (p, e1, e2) ->
      let eq1, ty1 = extract tyenv e1 in
      let eq2, ty2 = extract tyenv e2 in
      let eq3 = eq1 @ eq2 @ [ (ty1, IntT); (ty2, IntT) ] in
      if p = Lt then (eq3, BoolT) else (eq3, IntT)
  | IfExp (e1, e2, e3) ->
      let eq1, ty1 = extract tyenv e1 in
      let eq2, ty2 = extract tyenv e2 in
      let eq3, ty3 = extract tyenv e3 in
      let eq4 = eq1 @ eq2 @ eq3 @ [ (ty1, BoolT); (ty2, ty3) ] in
      (eq4, ty2)
  | LetExp (id, e1, e2) ->
      let eq1, ty1 = extract tyenv e1 in
      let eq2, ty2 = extract (ConsEnv (tyenv, id, ty1)) e2 in
      let eq3 = eq1 @ eq2 in
      (eq3, ty2)
  | FunExp (id, e) ->
      let newty = VarT (fresh_tyvar ()) in
      let eq, ty0 = extract (ConsEnv (tyenv, id, newty)) e in
      (eq, FunT (newty, ty0))
  | AppExp (e1, e2) ->
      let eq1, ty1 = extract tyenv e1 in
      let eq2, ty2 = extract tyenv e2 in
      let newty = VarT (fresh_tyvar ()) in
      let eq3 = eq1 @ eq2 @ [ (ty1, FunT (ty2, newty)) ] in
      (eq3, newty)
  | LetRecExp (id1, id2, e1, e2) ->
      let newty1 = VarT (fresh_tyvar ()) in
      let newty2 = VarT (fresh_tyvar ()) in
      let eq1, ty1 =
        extract (ConsEnv (ConsEnv (tyenv, id1, newty1), id2, newty2)) e1
      in
      let eq2, ty2 = extract (ConsEnv (tyenv, id1, newty1)) e2 in
      let eq3 = eq1 @ eq2 @ [ (newty1, FunT (newty2, ty1)) ] in
      (eq3, ty2)
  | NilExp ->
      let newty = VarT (fresh_tyvar ()) in
      ([], ListT newty)
  | ConsExp (e1, e2) ->
      let eq1, ty1 = extract tyenv e1 in
      let eq2, ty2 = extract tyenv e2 in
      let eq3 = eq1 @ eq2 @ [ (ty2, ListT ty1) ] in
      (eq3, ty2)
  | MatchExp (e1, e2, id1, id2, e3) ->
      let eq1, ty1 = extract tyenv e1 in
      let eq2, ty2 = extract tyenv e2 in
      let newty = VarT (fresh_tyvar ()) in
      let eq3, ty3 =
        extract (ConsEnv (ConsEnv (tyenv, id1, newty), id2, ListT newty)) e3
      in
      let eq4 = eq1 @ eq2 @ eq3 @ [ (ty1, ListT newty); (ty2, ty3) ] in
      (eq4, ty2)
