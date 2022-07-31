%{
open Syntax
%}

%token LPAREN RPAREN SEMISEMI
%token PLUS MINUS MULT LT
%token IF THEN ELSE TRUE FALSE
%token LET IN EQ
%token RARROW FUN
%token REC
%token VDASH COLUMN
%token MATCH WITH NIL APPEND BAR
%token COLON TYINT TYBOOL TYLIST

%token <int> INT
%token <Syntax.var> ID

%start toplevel
%type <Syntax.judgement> toplevel
%%

toplevel :
    tyenv=TyEnv VDASH e=Expr COLON ty=Type SEMISEMI { Typing (tyenv, e, ty) }
  | VDASH e=Expr COLON ty=Type SEMISEMI { Typing (Empty, e, ty) }

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

Type :
    ty=FunType { ty }

FunType :
    t1=AType RARROW t2=FunType { FunT (t1, t2) }

AType :
    TYINT { IntT }
  | TYBOOL { BoolT }
  | ty=Type TYLIST { ListT ty }
  | LPAREN ty=Type RPAREN { ty }

TyEnv :
    tyenv=TyEnv COLUMN x=ID COLON ty=Type { ConsEnv (tyenv, x, ty) }
  | x=ID COLON ty=Type { ConsEnv (Empty, x, ty) }