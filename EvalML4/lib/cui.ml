open Derive

let rec read_derive_print _ =
  print_string "# ";
  (* flush しないと出力されない *)
  flush stdout;
  (* 入力をパース *)
  let judgement = Parser.toplevel Lexer.main (Lexing.from_channel stdin) in
  (* 導出木を求める *)
  let derivation = derive_judgement judgement in
  pp_derivation 0 derivation;
  (* print_newline は flush も行う *)
  print_newline ();
  read_derive_print 0