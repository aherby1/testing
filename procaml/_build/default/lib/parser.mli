
(* The type of tokens. *)

type token = 
  | RPAREN
  | LPAREN
  | LETPROVE
  | INDUCTION of (string)
  | IDENT of (string)
  | EQUALS
  | EOF
  | COLON
  | AXIOM

(* This exception is raised by the monolithic API functions. *)

exception Error

(* The monolithic API. *)

val main: (Lexing.lexbuf -> token) -> Lexing.lexbuf -> (Ast.program)
