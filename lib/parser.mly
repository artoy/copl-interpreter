%{
open Syntax
%}

%token LPAREN RPAREN SEMISEMI
%token PLUS MINUS MULT LT
%token IF THEN ELSE TRUE FALSE
%token LET IN EQ
%token RARROW FUN
%token REC
%token EVALTO VDASH COLUMN LBOX RBOX

%token <int> INT
%token <Syntax.var> VAR

%start toplevel
%type <Syntax.judgement> toplevel
%%

toplevel :
  env=Env VDASH e=Expr EVALTO v=Value SEMISEMI { Eval(env, e, v) }

Expr :
    i=INT { IExp i }
  | TRUE   { BExp true }
  | FALSE  { BExp false }
  | x=VAR  { Var x }
  | LPAREN e=Expr RPAREN { e }

Value :
    i=INT { IntV i }
  | TRUE   { BoolV true }
  | FALSE  { BoolV false }
  | LPAREN env=Env RPAREN LBOX FUN x=VAR RARROW e=Expr RBOX { Closure(env, x, e) }
  | LPAREN env=Env RPAREN LBOX REC x1=VAR EQ FUN x2=VAR RARROW e=Expr RBOX { RecClosure(env, x1, x2, e) }

Env :
    env=Env COLUMN x=VAR EQ v=Value { Cons(env, x, v) }
  | x=VAR EQ v=Value { Cons(Empty, x, v) }