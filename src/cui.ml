let rec read_derive_print _ =
  print_string "# ";
  flush stdout;
  (* 入力をパース *)
  let judgement =
    try Parser.toplevel Lexer.main (Lexing.from_channel stdin)
    with Failure s -> Exception s
  in
  (* 導出木を求める *)
  let derivation =
    try derive Environment.empty judgement with Failure s -> Exception s
  in
  pp_derivation derivation;
  print_newline ();
  read_derive_print 0