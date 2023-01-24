%{
    open Ast
%}

%token <(Lexing.position * Lexing.position) * int> NUMBER
%token <(Lexing.position * Lexing.position) * string> IDENT
%token <(Lexing.position * Lexing.position) > ARROW, IF, THEN, ELSE, IN, LET, REC, TRUE, FALSE,
UNDERSCORE, LPAREN, RPAREN, LBRACKET, RBRACKET, SEMI, COLONEQUAL, OR, AND,
NEQUAL, EQUAL, LESS, GREATER, LESSEQ, GREATEREQ, IMPLIES, PLUS, MINUS, MOD, TIMES, DIV,
COMMA, FUN, FST, SND, NOT, EQUIV, APPROX, APPROXINV, BOT, BEGIN, END
UNIT, BOOL, INT, EOF


//%nonassoc IN
%nonassoc below_SEMI
%nonassoc SEMI                          (* below EQUAL ({lbl=...; lbl=...}) *)
//%nonassoc LET REF                     (* above SEMI ( ...; let ... in ...) *)
//%nonassoc FUN
%nonassoc THEN                          (* below ELSE (if ... then ...) *)
%nonassoc ELSE                          (* (if ... then ... else ...) *)
%nonassoc prec_tuple
%left     COMMA                         (* expr/expr_comma_list (e,e,e) *)
%right    ARROW                         (* function_type (t -> t -> t) *)
%right    OR                            (* expr (e || e || e) *)
%right    AND                           (* expr (e && e && e) *)
%left     EQUAL NEQUAL LESS GREATER LESSEQ GREATEREQ   (* expr (e OP e OP e) *)
%right    IMPLIES
%left     PLUS MINUS                    (* expr (e OP e OP e) *)
%left     TIMES DIV MOD                 (* expr (e OP e OP e) *)
%nonassoc prec_unary                    (* unary - *)
//%left prec_app
(* Finally, the first tokens of simple_expr are above everything else. *)
//%nonassoc BANG BEGIN FALSE NUMBER LBRACE IDENT LPAREN LBRACKET TRUE 




%type <Ast.program> program
%start <Ast.program> main

%%

main : a = program EOF   {a}
program :
  exp1=exp_seq re=relation_op exp2=exp_seq {{e1=exp1; e2=exp2; rel=re}}

%inline relation:
  | p = EQUIV     {(Equiv, p)}
  | p = APPROX    {raise (Error.ParseE (p, "Preorder relation is not yet supported"))}
  | p = APPROXINV {raise (Error.ParseE (p, "Inverse Preorder relation is not yet supported"))}

  relation_op:
  | r=relation {(fst r, Type.gen_type ())}
  | r=relation UNDERSCORE t=type_annot {(fst r, t)}
  | p = EOF       {raise (Error.ParseE (p, "File contains only one expression; it must have two expressions with a relation symbol in between"))}
  | p = relation EOF {raise (Error.ParseE (snd p, "Missing second top-level expression after relation symbol"))}

%inline unit: 
  | p1 = LPAREN p2 = RPAREN {(fst p1, snd p2)}

const_w_pos: 
  | c = NUMBER    {((ConstVal (IntConst (snd c))), Some (fst c))}
  | pos = TRUE    {((ConstVal (BoolConst true)), Some pos)}
  | pos = FALSE   {((ConstVal (BoolConst false)), Some pos)}
  | pos = unit    {((ConstVal UnitConst), Some pos)}

fun_w_pos:
  | pos = FUN param = fun_arg ARROW b = exp_seq 
  {(FunVal ({idid=(-1); str="_"}, Type.gen_type (), fst param, snd param, b), Some pos)}
  | pos = FUN fn = id_or_us param = fun_arg ARROW b = exp_seq
  {(FunVal (fn, Type.gen_type (), fst param, snd param, b), Some pos)}

fun_arg:
 | LPAREN param = paramid_w_type RPAREN {param}
 | param = paramid_w_type {param}


id_w_pos:
  | name = IDENT  {({idid=(-1); str=(snd name)}, Some (fst name))}

id_or_us:
  | UNDERSCORE    {{idid=(-1); str="_"}}
  | name = IDENT  {{idid=(-1); str=(snd name)}}

paramid_w_type:
  | UNDERSCORE     {({idid=(-1); str="_"}, Type.gen_type ())}
  | LPAREN RPAREN  {({idid=(-1); str="_"}, Type.UnitT)}
  | name = IDENT   {({idid=(-1); str=(snd name)}, Type.gen_type ())}

exp_seq:
  | e = exp
    %prec below_SEMI
    {e}
  | e = exp SEMI
    {e}
  | e1 = exp pos = SEMI e2 = exp_seq
    {SeqExp (e1, e2, Some pos)}


exp:
  | pos = BOT
    {BotExp (Some pos)}
  | i = id_w_pos 
    {IdentExp(fst i, snd i)}
  | v = const_w_pos
    {ValExp ((fst v), snd v)}
  | tp = tuple_w_pos
    %prec prec_tuple
    {TupleExp (fst tp, Some (snd tp))}
  | v = fun_w_pos
    {ValExp ((fst v), snd v)}

  | op = simple_op_exp rand = simple_exp
    {AppExp (op, rand, (Ast.get_lex_pos op))}

  | op = unary_op e1 = exp
    %prec prec_unary
    {ArithExp ((fst op), [e1], (snd op))}

  | e1 = exp op = bin_op e2 = exp         
    {ArithExp ((fst op), [e1; e2], (snd op))}

  | pos = IF e1 = exp_seq THEN e2 = exp ELSE e3 = exp
    {CondExp (e1, e2, e3, Some pos)}

  | pos = IF e1 = exp_seq THEN e2 = exp
    {CondExp (e1, e2, ValExp (ConstVal UnitConst, Some pos), Some pos)}

  | pos = LET i = id_or_us EQUAL e1 = exp_seq IN e2 = exp_seq
    {LetExp (i, Type.gen_type (), e1, e2, Some pos)}

  | pos = LET REC f = id_or_us x = paramid_w_type EQUAL e1 = exp_seq IN e2 = exp_seq
    {LetExp (f, Type.gen_type (), ValExp (FunVal (f, Type.gen_type (), fst x, snd x, e1), (get_lex_pos e1)), e2, Some pos)}

  | pos = LET f = id_or_us x=paramid_w_type EQUAL e1 = exp_seq IN e2 = exp_seq
    {LetExp (f, Type.gen_type (), ValExp (FunVal ({idid=(-1); str="_"}, Type.gen_type (), fst x, snd x, e1), (get_lex_pos e1)), e2, Some pos)}

  | pos = LET LPAREN p = pattern RPAREN EQUAL e1 = exp_seq IN e2 = exp_seq
    {LetTuple (p, e1, e2, Some pos)}
  | e = paren_expression
    {e}

  (* (a0, a1, a2)[1] = a1 *)
  | e1 = simple_exp pos = LBRACKET i = NUMBER DIV j = NUMBER RBRACKET
    {TupleProjExp (e1, snd i, snd j, Some pos)}
  (* (a0, a1, a2)[1:=b] = (a0, b, a2) *)
  | e1 = simple_exp pos = LBRACKET i = NUMBER DIV j = NUMBER COLONEQUAL e2 = exp RBRACKET
    {TupleUpdExp (e1, snd i, snd j, e2, Some pos)}

simple_op_exp:
  | pos = BOT
    {BotExp (Some pos)}
  | i = id_w_pos
    {IdentExp(fst i, snd i)}
  | v = const_w_pos
    {ValExp ((fst v), snd v)}
  | op = simple_op_exp rand = simple_exp
    {AppExp (op, rand, (Ast.get_lex_pos op))}
  (* Every other exp must be in parentheses/braces *)
  | e = paren_expression
    {e}

%inline simple_exp:
  | pos = BOT
    {BotExp (Some pos)}
  | i = id_w_pos
    {IdentExp(fst i, snd i)}
  | v = const_w_pos
    {ValExp (fst v, snd v)}
  (* Every other exp must be in parentheses/braces *)
  | e = paren_expression
    {e}

paren_expression:
  | LPAREN e = exp_seq RPAREN {e}
  | BEGIN e = exp_seq END {e}

  
unary_op:
  | pos = MINUS {(Negate, Some pos)}
  | pos = NOT   {(Not, Some pos)}
  | pos = FST   {(Fst, Some pos)}
  | pos = SND   {(Snd, Some pos)}

%inline bin_op:
  | pos = PLUS      {(Add, Some pos)}
  | pos = MINUS     {(Subtract, Some pos)}
  | pos = TIMES     {(Multiply, Some pos)}
  | pos = DIV       {(Divide, Some pos)}
  | pos = MOD       {(Modulo, Some pos)}
  | pos = AND       {(And, Some pos)}
  | pos = OR        {(Or, Some pos)}
  | pos = EQUAL     {(Equal, Some pos)}
  | pos = NEQUAL    {(Different, Some pos)}
  | pos = LESS      {(Less, Some pos)}
  | pos = GREATER   {(Greater, Some pos)}
  | pos = LESSEQ    {(LessEQ, Some pos)}
  | pos = GREATEREQ {(GreaterEQ, Some pos)}
  | pos = IMPLIES   {(Implies, Some pos)}


tuple_w_pos:
| lst_p = tuple_w_pos COMMA e = exp
  { ((fst lst_p) @ [e]), (snd lst_p) }
| e1 = exp pos = COMMA e2 = exp
  { [e1; e2], pos }

pattern:
| lst = pattern COMMA i = paramid_w_type
  { lst @ [i] }
| i1 = paramid_w_type COMMA i2 = paramid_w_type
  { [i1; i2] }


type_annot:
  | UNIT {Type.UnitT}
  | BOOL {Type.BoolT}
  | INT  {Type.IntT}
  | t1=type_annot ARROW t2=type_annot {Type.FunT([t1], t2)}
  | t = type_tuple
    %prec prec_tuple
    {Type.TupleT t}
  | LPAREN t=type_annot RPAREN {t}

type_tuple:
| lst = type_tuple TIMES t=type_annot
  { lst @ [t]}
| t1 = type_annot TIMES t2 = type_annot
  {[t1; t2]}
