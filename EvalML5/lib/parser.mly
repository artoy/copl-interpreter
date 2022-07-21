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
%token MATCH WITH NIL APPEND BAR

%token <int> INT
%token <Syntax.var> ID

%start toplevel
%type <Syntax.judgement> toplevel
%%

// NOTE: evalto を使わない判断は扱わないものとする
toplevel :
    env=Env VDASH e=Expr EVALTO v=Value SEMISEMI { EvalJ (env, e, v) }
  | VDASH e=Expr EVALTO v=Value SEMISEMI { EvalJ (Empty, e, v) }

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
  | e=MatchExpr { e }
  | e=ConsExpr { e }
  | e=AppExpr { e }

IfExpr :
    IF c=Expr THEN t=Expr ELSE e=Expr { IfExp (c, t, e) }

LetExpr :
    LET x=ID EQ e1=Expr IN e2=Expr { LetExp (x, e1, e2) }
  | LET REC x1=ID EQ FUN x2=ID RARROW e1=Expr IN e2=Expr { LetRecExp (x1, x2, e1, e2) }

FunExpr :
    FUN x=ID RARROW e=Expr { FunExp (x, e) }

MatchExpr :
    MATCH e1=Expr WITH NIL RARROW e2=Expr BAR x1=ID APPEND x2=ID RARROW e3=Expr { MatchExp (e1, e2, x1, x2, e3) }

ConsExpr :
    i=AppExpr APPEND e=ConsExpr { ConsExp (i, e) }
  | e=AppExpr { e }

AppExpr :
    e1=AppExpr e2=AExpr { AppExp (e1, e2) }
  | e=AExpr { e }

AExpr :
    i=INT { IExp i }
  | TRUE   { BExp true }
  | FALSE  { BExp false }
  | x=ID  { Var x }
  | LPAREN e=Expr RPAREN { e }
  | NIL { NilExp }

Value :
    v=ConsValue { v }

ConsValue :
    head=AValue APPEND tail=ConsValue { ConsV (head, tail) }
  | v=AValue { v }

AValue :
    i=INT { IntV i }
  | TRUE   { BoolV true }
  | FALSE  { BoolV false }
  | LPAREN env=Env RPAREN LBOX FUN x=ID RARROW e=Expr RBOX { Closure (env, x, e) }
  | LPAREN env=Env RPAREN LBOX REC x1=ID EQ FUN x2=ID RARROW e=Expr RBOX { RecClosure (env, x1, x2, e) }
  | NIL { NilV }
  | LPAREN v=Value RPAREN { v }

Env :
    env=Env COLUMN x=ID EQ v=Value { ConsEnv (env, x, v) }
  | x=ID EQ v=Value { ConsEnv (Empty, x, v) }