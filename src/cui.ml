open Syntax
open Eval
open Typing

(* インターフェース部分を表す関数 *)
let rec read_eval_print env tyenv =
  print_string "# ";
  flush stdout;
  (* 与えられたプログラムを抽象構文木に変換 *)
  let decl =
    try Parser.toplevel Lexer.main (Lexing.from_channel stdin) with
    | Failure s -> Exception s
    | _ -> Exception "syntax error"
  in
  (* 型推論を実行 *)
  (* let ty =
       try ty_decl tyenv decl with
       | Failure s -> Exception s
       | _ -> Exception "syntax error"
     in *)
  (* 次の環境と、宣言の場合は束縛された変数とその値を求める。式の場合は次の環境と式を評価した値を求める *)
  let id, newenv, v =
    try eval_decl env decl with Error s -> ("", env, ExceptV s)
  in
  (* 宣言の場合は束縛された変数とその値、式の場合は式を評価した値を出力する *)
  Printf.printf "val %s : " id;
  (* pp_ty ty; *)
  print_string " = ";
  pp_val v;
  print_newline ();
  (* 次の入力のために環境を更新してこれらの操作を繰り返す。 *)
  read_eval_print newenv tyenv

(* 大域環境を表す let 宣言 *)
let initial_env = Environment.empty

(* 大域の型環境を表す let 宣言 *)
let initial_tyenv = Environment.empty