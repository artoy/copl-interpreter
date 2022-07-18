open Syntax

let rec read_derive_print _ =
  print_string "# ";
  flush stdout;
  (* 入力をパース *)
  let judgement = Parser.toplevel Lexer.main (Lexing.from_channel stdin) in
  (* 導出木を求める *)
  let derivation = derive_judgement Empty judgement in
  (* pp_derivation derivation; *)
  print_newline ();
  read_derive_print 0