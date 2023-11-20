include Ast
module Parser = Parser
module Lexer = Lexer

let rec string_of_expression (e : expression)
  = match e with
    | Identifier nm -> nm
    | Application (e1, e2) ->
      (string_of_expression e1) ^
       " " ^ (string_of_expression_with_parens e2)
and string_of_expression_with_parens e
  = match e with
  | Identifier nm -> nm
  | Application _ -> "(" ^ string_of_expression e ^ ")"

let string_of_argument (name, typ) =
  name ^ " : " ^ typ

let string_of_arguments args =
  String.concat " " (List.map string_of_argument args)

let string_of_equality (e1, e2) =
  string_of_expression e1 ^ " = " ^ string_of_expression e2

let string_of_declaration decl =
  match decl with
  | LetProve (name, args, eq) ->
    "let (*prove*) " ^ name ^ " (" ^ string_of_arguments args ^ ")\n= " ^ string_of_equality eq ^ "\n(*hint: axiom *)\n"
  | FunctionDefStr (name, args, expr) ->
    "let " ^ name ^ " (" ^ string_of_arguments args ^ ") = " ^ string_of_expression expr ^ "\n"

let string_of_program (program : program) =
  String.concat "\n" (List.map string_of_declaration program)