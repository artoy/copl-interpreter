{
let reservedWords = [
  ("else", Parser.ELSE);
  ("false", Parser.FALSE);
  ("if", Parser.IF);
  ("then", Parser.THEN);
  ("true", Parser.TRUE);
  ("in", Parser.IN);
  ("let", Parser.LET);
  ("fun", Parser.FUN);
  ("rec", Parser.REC);
  ("evalto", Parser.EVALTO);
  ("match", Parser.MATCH);
  ("with", Parser.WITH);
  ("int", Parser.TYINT);
  ("bool", Parser.TYBOOL);
  ("list", Parser.TYLIST);
]
}

rule main = parse
  (* ignore spacing and newline characters *)
  [' ' '\009' '\012' '\n']+     { main lexbuf }

| "-"? ['0'-'9']+
    { Parser.INT (int_of_string (Lexing.lexeme lexbuf)) }

| "(" { Parser.LPAREN }
| ")" { Parser.RPAREN }
| ";;" { Parser.SEMISEMI }
| "+" { Parser.PLUS }
| "-" { Parser.MINUS }
| "*" { Parser.MULT }
| "<" { Parser.LT }
| "=" { Parser.EQ }
| "->" { Parser.RARROW }
| "|-" { Parser.VDASH }
| "[]" { Parser.NIL }
| "," { Parser.COLUMN }
| "[" { Parser.LBOX }
| "]" { Parser.RBOX }
| "::" { Parser.APPEND }
| "|" { Parser.BAR }
| ":" { Parser.COLON }

| ['a'-'z'] ['a'-'z' '0'-'9' '_' '\'']*
    { let id = Lexing.lexeme lexbuf in
      try
        List.assoc id reservedWords
      with
      _ -> Parser.ID id
    }
| eof { exit 0 }
