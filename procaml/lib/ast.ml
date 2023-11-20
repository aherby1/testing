type arguments = (string * string) list

type declaration =
  | LetProve of string * arguments * equality
  | FunctionDefStr of string * arguments * expression
and
equality = expression * expression
and 
expression =
 | Identifier of string
 | Application of expression * expression
 | Declaration of declaration
 (* | match ... **)

type program = declaration list



 (*
    let prove (*prove*) foo (x: int) (y : int) = (x = y)

    let rec inc (x : nat = S x)

    let rec letter (x : int) = foo x x

    note: go through smaple ml and define all the types we will encounter
 *)

