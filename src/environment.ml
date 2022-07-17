type 'a t = (Syntax.id * 'a) list

exception Not_bound

let empty = []

(* 環境に1つ変数束縛を追加する関数 *)
let extend x v env = (x, v) :: env

(* 環境から変数を探し、その値を返す関数 *)
let lookup x env = try List.assoc x env with Not_found -> raise Not_bound

(* 環境が束縛している全ての値に関数を適用する関数 *)
let rec map f = function [] -> [] | (id, v) :: rest -> (id, f v) :: map f rest

(* 環境に対して fold を行う関数 *)
let rec fold_right f env a =
  match env with [] -> a | (_, v) :: rest -> f v (fold_right f rest a)
