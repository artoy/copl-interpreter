open Syntax

(* NOTE: 型代入は (tyvar * ty), 型の等式制約は (ty * ty) で表している *)

(* 型の等式制約の集合に型代入を適用する関数 *)
let rec subst_to_equations subst eqs =
  match subst with
  | v, t -> (
      match eqs with
      | [] -> []
      | (l, r) :: rest ->
          if l = VarT v && r = VarT v then
            (t, t) :: subst_to_equations subst rest
          else if l = VarT v then (t, r) :: subst_to_equations subst rest
          else if r = VarT v then (l, t) :: subst_to_equations subst rest
          else (l, r) :: subst_to_equations subst rest)

(* 型の等式制約の集合に型代入のリストを適用する関数 *)
let rec subst_list_to_equations substs eqs =
  match substs with
  | [] -> eqs
  | head :: tail -> subst_list_to_equations tail (subst_to_equations head eqs)

(* 型代入のリストを型に適用する関数 *)
let rec subst_list_to_ty substs ty =
  match substs with
  | [] -> ty
  | (v, t) :: rest ->
      let rec subst_to_ty subst ty =
        match ty with
        | IntT -> IntT
        | BoolT -> BoolT
        | FunT (ty1, ty2) -> FunT (subst_to_ty subst ty1, subst_to_ty subst ty2)
        | ListT t -> ListT (subst_to_ty subst t)
        | VarT x -> if x = v then t else ty
      in
      subst_list_to_ty rest (subst_to_ty (v, t) ty)

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

(* 単一化を行う関数 *)
let rec unify eq =
  match eq with
  | [] -> []
  | (l, r) :: rest -> (
      if l = r then unify rest
      else
        match (l, r) with
        | VarT v, _ ->
            if SI.mem v (get_tyvar r) then err "Failed to occur check."
            else
              let s = unify (subst_to_equations (v, r) rest) in
              (v, r) :: s
        | _, VarT v ->
            if SI.mem v (get_tyvar l) then err "Failed to occur check."
            else
              let s = unify (subst_to_equations (v, l) rest) in
              (v, l) :: s
        | FunT (l1, l2), FunT (r1, r2) -> unify (eq @ [ (l1, r1); (l2, r2) ])
        | ListT t1, ListT t2 -> unify (eq @ [ (t1, t2) ])
        | _ -> err "Cannot unify!")

(* 型推論を行い主要型を求める関数 *)
let pt tyenv e =
  let eq, ty = extract tyenv e in
  let s = unify eq in
  (s, subst_list_to_ty s ty)
