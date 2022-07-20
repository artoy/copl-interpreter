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

// NOTE: evalto を使わない判断は扱わないものとする
toplevel :
    env=Env VDASH e=Expr EVALTO v=Value SEMISEMI { Eval(env, e, v) }
  | VDASH e=Expr EVALTO v=Value SEMISEMI { Eval(Empty, e, v) }

Expr :
  e=LTExpr { e }

LTExpr :
    l=PExpr LT r=PExpr { BinOp (Lt, l, r) }
  | e=PExpr { e }

PExpr :
    l=PExpr PLUS r=MExpr { BinOp (Plus, l, r) }
  | l=PExpr MINUS r=MExpr { BinOp (Minus, l, r) }
  | e=MExpr { e }

MExpr :
    l=MExpr MULT r=SyntacticExpr { BinOp (Mult, l, r) }
  | e=SyntacticExpr { e }

SyntacticExpr :
    e=IfExpr { e }
  | e=LetExpr { e }
  | e=FunExpr { e }
  | e=AppExpr { e }

IfExpr :
    IF c=Expr THEN t=Expr ELSE e=Expr { IfExp (c, t, e) }

LetExpr :
    LET x=VAR EQ e1=Expr IN e2=Expr { LetExp (x, e1, e2) }
  | LET REC x1=VAR EQ FUN x2=VAR RARROW e1=Expr IN e2=Expr { LetRecExp (x1, x2, e1, e2) }

FunExpr :
    FUN x=VAR RARROW e=Expr { FunExp (x, e) }

AppExpr :
    e1=AppExpr e2=AExpr { AppExp (e1, e2) }
  | e=AExpr { e }

AExpr :
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