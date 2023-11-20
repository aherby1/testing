%{
    open Ast
%}
%token <string> IDENT
%token LETPROVE
%token COLON
%token LPAREN
%token RPAREN
%token EQUALS
%token AXIOM
%token <string> INDUCTION

%token EOF
%start main
%type <program> main
%%
main:
| decls = declarations ; EOF { decls }

declarations:
| decl = declaration { [decl] }
| decl = declaration; decls = declarations { decl :: decls }

declaration:
| LETPROVE; name = IDENT; args = arguments; EQUALS; e1 = expression; EQUALS; e2 = expression
    { LetProve (name, args, (e1, e2)) }

arguments:
| LPAREN; args = arg_list; RPAREN { args }

arg_list:
| arg = argument { [arg] }
| arg = argument; args = arg_list { arg :: args }

argument:
| name = IDENT; COLON; typ = IDENT { (name, typ) }

expression:
 | LPAREN ; e = expression ; RPAREN { e }
 | nm = IDENT { Identifier nm }
 | e1 = expression; nm = IDENT 
    { Application (e1, Identifier nm) }
 | e1 = expression; LPAREN; e2 = expression; RPAREN
    { Application (e1, e2) }

 