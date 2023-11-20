
module MenhirBasics = struct
  
  exception Error
  
  let _eRR =
    fun _s ->
      raise Error
  
  type token = 
    | RPAREN
    | LPAREN
    | LETPROVE
    | INDUCTION of (
# 11 "lib/parser.mly"
       (string)
# 18 "lib/parser.ml"
  )
    | IDENT of (
# 4 "lib/parser.mly"
       (string)
# 23 "lib/parser.ml"
  )
    | EQUALS
    | EOF
    | COLON
    | AXIOM
  
end

include MenhirBasics

# 1 "lib/parser.mly"
  
    open Ast

# 38 "lib/parser.ml"

type ('s, 'r) _menhir_state = 
  | MenhirState00 : ('s, _menhir_box_main) _menhir_state
    (** State 00.
        Stack shape : .
        Start symbol: main. *)

  | MenhirState03 : (('s, _menhir_box_main) _menhir_cell1_LETPROVE _menhir_cell0_IDENT, _menhir_box_main) _menhir_state
    (** State 03.
        Stack shape : LETPROVE IDENT.
        Start symbol: main. *)

  | MenhirState07 : (('s, _menhir_box_main) _menhir_cell1_argument, _menhir_box_main) _menhir_state
    (** State 07.
        Stack shape : argument.
        Start symbol: main. *)

  | MenhirState12 : (('s, _menhir_box_main) _menhir_cell1_LETPROVE _menhir_cell0_IDENT _menhir_cell0_arguments, _menhir_box_main) _menhir_state
    (** State 12.
        Stack shape : LETPROVE IDENT arguments.
        Start symbol: main. *)

  | MenhirState13 : (('s, _menhir_box_main) _menhir_cell1_LPAREN, _menhir_box_main) _menhir_state
    (** State 13.
        Stack shape : LPAREN.
        Start symbol: main. *)

  | MenhirState17 : (('s, _menhir_box_main) _menhir_cell1_expression, _menhir_box_main) _menhir_state
    (** State 17.
        Stack shape : expression.
        Start symbol: main. *)

  | MenhirState22 : ((('s, _menhir_box_main) _menhir_cell1_LETPROVE _menhir_cell0_IDENT _menhir_cell0_arguments, _menhir_box_main) _menhir_cell1_expression, _menhir_box_main) _menhir_state
    (** State 22.
        Stack shape : LETPROVE IDENT arguments expression.
        Start symbol: main. *)

  | MenhirState27 : (('s, _menhir_box_main) _menhir_cell1_declaration, _menhir_box_main) _menhir_state
    (** State 27.
        Stack shape : declaration.
        Start symbol: main. *)


and ('s, 'r) _menhir_cell1_argument = 
  | MenhirCell1_argument of 's * ('s, 'r) _menhir_state * (string * string)

and 's _menhir_cell0_arguments = 
  | MenhirCell0_arguments of 's * (Ast.arguments)

and ('s, 'r) _menhir_cell1_declaration = 
  | MenhirCell1_declaration of 's * ('s, 'r) _menhir_state * (Ast.declaration)

and ('s, 'r) _menhir_cell1_expression = 
  | MenhirCell1_expression of 's * ('s, 'r) _menhir_state * (Ast.expression)

and 's _menhir_cell0_IDENT = 
  | MenhirCell0_IDENT of 's * (
# 4 "lib/parser.mly"
       (string)
# 98 "lib/parser.ml"
)

and ('s, 'r) _menhir_cell1_LETPROVE = 
  | MenhirCell1_LETPROVE of 's * ('s, 'r) _menhir_state

and ('s, 'r) _menhir_cell1_LPAREN = 
  | MenhirCell1_LPAREN of 's * ('s, 'r) _menhir_state

and _menhir_box_main = 
  | MenhirBox_main of (Ast.program) [@@unboxed]

let _menhir_action_01 =
  fun arg ->
    (
# 32 "lib/parser.mly"
                 ( [arg] )
# 115 "lib/parser.ml"
     : (Ast.arguments))

let _menhir_action_02 =
  fun arg args ->
    (
# 33 "lib/parser.mly"
                                  ( arg :: args )
# 123 "lib/parser.ml"
     : (Ast.arguments))

let _menhir_action_03 =
  fun name typ ->
    (
# 36 "lib/parser.mly"
                                   ( (name, typ) )
# 131 "lib/parser.ml"
     : (string * string))

let _menhir_action_04 =
  fun args ->
    (
# 29 "lib/parser.mly"
                                  ( args )
# 139 "lib/parser.ml"
     : (Ast.arguments))

let _menhir_action_05 =
  fun args e1 e2 name ->
    (
# 26 "lib/parser.mly"
    ( LetProve (name, args, (e1, e2)) )
# 147 "lib/parser.ml"
     : (Ast.declaration))

let _menhir_action_06 =
  fun decl ->
    (
# 21 "lib/parser.mly"
                     ( [decl] )
# 155 "lib/parser.ml"
     : (Ast.program))

let _menhir_action_07 =
  fun decl decls ->
    (
# 22 "lib/parser.mly"
                                           ( decl :: decls )
# 163 "lib/parser.ml"
     : (Ast.program))

let _menhir_action_08 =
  fun e ->
    (
# 39 "lib/parser.mly"
                                    ( e )
# 171 "lib/parser.ml"
     : (Ast.expression))

let _menhir_action_09 =
  fun nm ->
    (
# 40 "lib/parser.mly"
              ( Identifier nm )
# 179 "lib/parser.ml"
     : (Ast.expression))

let _menhir_action_10 =
  fun e1 nm ->
    (
# 42 "lib/parser.mly"
    ( Application (e1, Identifier nm) )
# 187 "lib/parser.ml"
     : (Ast.expression))

let _menhir_action_11 =
  fun e1 e2 ->
    (
# 44 "lib/parser.mly"
    ( Application (e1, e2) )
# 195 "lib/parser.ml"
     : (Ast.expression))

let _menhir_action_12 =
  fun decls ->
    (
# 18 "lib/parser.mly"
                             ( decls )
# 203 "lib/parser.ml"
     : (Ast.program))

let _menhir_print_token : token -> string =
  fun _tok ->
    match _tok with
    | AXIOM ->
        "AXIOM"
    | COLON ->
        "COLON"
    | EOF ->
        "EOF"
    | EQUALS ->
        "EQUALS"
    | IDENT _ ->
        "IDENT"
    | INDUCTION _ ->
        "INDUCTION"
    | LETPROVE ->
        "LETPROVE"
    | LPAREN ->
        "LPAREN"
    | RPAREN ->
        "RPAREN"

let _menhir_fail : unit -> 'a =
  fun () ->
    Printf.eprintf "Internal failure -- please contact the parser generator's developers.\n%!";
    assert false

include struct
  
  [@@@ocaml.warning "-4-37-39"]
  
  let rec _menhir_run_25 : type  ttv_stack. ttv_stack -> _ -> _menhir_box_main =
    fun _menhir_stack _v ->
      let decls = _v in
      let _v = _menhir_action_12 decls in
      MenhirBox_main _v
  
  let rec _menhir_goto_declarations : type  ttv_stack. ttv_stack -> _ -> (ttv_stack, _menhir_box_main) _menhir_state -> _menhir_box_main =
    fun _menhir_stack _v _menhir_s ->
      match _menhir_s with
      | MenhirState27 ->
          _menhir_run_28 _menhir_stack _v
      | MenhirState00 ->
          _menhir_run_25 _menhir_stack _v
      | _ ->
          _menhir_fail ()
  
  and _menhir_run_28 : type  ttv_stack. (ttv_stack, _menhir_box_main) _menhir_cell1_declaration -> _ -> _menhir_box_main =
    fun _menhir_stack _v ->
      let MenhirCell1_declaration (_menhir_stack, _menhir_s, decl) = _menhir_stack in
      let decls = _v in
      let _v = _menhir_action_07 decl decls in
      _menhir_goto_declarations _menhir_stack _v _menhir_s
  
  let rec _menhir_run_01 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_main) _menhir_state -> _menhir_box_main =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _menhir_stack = MenhirCell1_LETPROVE (_menhir_stack, _menhir_s) in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | IDENT _v ->
          let _menhir_stack = MenhirCell0_IDENT (_menhir_stack, _v) in
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | LPAREN ->
              let _tok = _menhir_lexer _menhir_lexbuf in
              (match (_tok : MenhirBasics.token) with
              | IDENT _v ->
                  _menhir_run_04 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState03
              | _ ->
                  _eRR ())
          | _ ->
              _eRR ())
      | _ ->
          _eRR ()
  
  and _menhir_run_04 : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_main) _menhir_state -> _menhir_box_main =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | COLON ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | IDENT _v_0 ->
              let _tok = _menhir_lexer _menhir_lexbuf in
              let (typ, name) = (_v_0, _v) in
              let _v = _menhir_action_03 name typ in
              (match (_tok : MenhirBasics.token) with
              | IDENT _v_0 ->
                  let _menhir_stack = MenhirCell1_argument (_menhir_stack, _menhir_s, _v) in
                  _menhir_run_04 _menhir_stack _menhir_lexbuf _menhir_lexer _v_0 MenhirState07
              | RPAREN ->
                  let arg = _v in
                  let _v = _menhir_action_01 arg in
                  _menhir_goto_arg_list _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
              | _ ->
                  _eRR ())
          | _ ->
              _eRR ())
      | _ ->
          _eRR ()
  
  and _menhir_goto_arg_list : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_main) _menhir_state -> _menhir_box_main =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s ->
      match _menhir_s with
      | MenhirState03 ->
          _menhir_run_09 _menhir_stack _menhir_lexbuf _menhir_lexer _v
      | MenhirState07 ->
          _menhir_run_08 _menhir_stack _menhir_lexbuf _menhir_lexer _v
      | _ ->
          _menhir_fail ()
  
  and _menhir_run_09 : type  ttv_stack. (ttv_stack, _menhir_box_main) _menhir_cell1_LETPROVE _menhir_cell0_IDENT -> _ -> _ -> _ -> _menhir_box_main =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      let args = _v in
      let _v = _menhir_action_04 args in
      let _menhir_stack = MenhirCell0_arguments (_menhir_stack, _v) in
      match (_tok : MenhirBasics.token) with
      | EQUALS ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | LPAREN ->
              _menhir_run_13 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState12
          | IDENT _v_0 ->
              let _tok = _menhir_lexer _menhir_lexbuf in
              let nm = _v_0 in
              let _v = _menhir_action_09 nm in
              _menhir_run_21 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState12 _tok
          | _ ->
              _eRR ())
      | _ ->
          _eRR ()
  
  and _menhir_run_13 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_main) _menhir_state -> _menhir_box_main =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _menhir_stack = MenhirCell1_LPAREN (_menhir_stack, _menhir_s) in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | LPAREN ->
          _menhir_run_13 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState13
      | IDENT _v ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let nm = _v in
          let _v = _menhir_action_09 nm in
          _menhir_run_15 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState13 _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_15 : type  ttv_stack. ((ttv_stack, _menhir_box_main) _menhir_cell1_LPAREN as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_main) _menhir_state -> _ -> _menhir_box_main =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | RPAREN ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let MenhirCell1_LPAREN (_menhir_stack, _menhir_s) = _menhir_stack in
          let e = _v in
          let _v = _menhir_action_08 e in
          _menhir_goto_expression _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | LPAREN ->
          let _menhir_stack = MenhirCell1_expression (_menhir_stack, _menhir_s, _v) in
          _menhir_run_17 _menhir_stack _menhir_lexbuf _menhir_lexer
      | IDENT _v_0 ->
          let _menhir_stack = MenhirCell1_expression (_menhir_stack, _menhir_s, _v) in
          _menhir_run_20 _menhir_stack _menhir_lexbuf _menhir_lexer _v_0
      | _ ->
          _eRR ()
  
  and _menhir_goto_expression : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_main) _menhir_state -> _ -> _menhir_box_main =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match _menhir_s with
      | MenhirState22 ->
          _menhir_run_23 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState12 ->
          _menhir_run_21 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState17 ->
          _menhir_run_18 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState13 ->
          _menhir_run_15 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _menhir_fail ()
  
  and _menhir_run_23 : type  ttv_stack. (((ttv_stack, _menhir_box_main) _menhir_cell1_LETPROVE _menhir_cell0_IDENT _menhir_cell0_arguments, _menhir_box_main) _menhir_cell1_expression as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_main) _menhir_state -> _ -> _menhir_box_main =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | LPAREN ->
          let _menhir_stack = MenhirCell1_expression (_menhir_stack, _menhir_s, _v) in
          _menhir_run_17 _menhir_stack _menhir_lexbuf _menhir_lexer
      | IDENT _v_0 ->
          let _menhir_stack = MenhirCell1_expression (_menhir_stack, _menhir_s, _v) in
          _menhir_run_20 _menhir_stack _menhir_lexbuf _menhir_lexer _v_0
      | EOF | LETPROVE ->
          let MenhirCell1_expression (_menhir_stack, _, e1) = _menhir_stack in
          let MenhirCell0_arguments (_menhir_stack, args) = _menhir_stack in
          let MenhirCell0_IDENT (_menhir_stack, name) = _menhir_stack in
          let MenhirCell1_LETPROVE (_menhir_stack, _menhir_s) = _menhir_stack in
          let e2 = _v in
          let _v = _menhir_action_05 args e1 e2 name in
          (match (_tok : MenhirBasics.token) with
          | LETPROVE ->
              let _menhir_stack = MenhirCell1_declaration (_menhir_stack, _menhir_s, _v) in
              _menhir_run_01 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState27
          | EOF ->
              let decl = _v in
              let _v = _menhir_action_06 decl in
              _menhir_goto_declarations _menhir_stack _v _menhir_s
          | _ ->
              _menhir_fail ())
      | _ ->
          _eRR ()
  
  and _menhir_run_17 : type  ttv_stack. (ttv_stack, _menhir_box_main) _menhir_cell1_expression -> _ -> _ -> _menhir_box_main =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | LPAREN ->
          _menhir_run_13 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState17
      | IDENT _v ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let nm = _v in
          let _v = _menhir_action_09 nm in
          _menhir_run_18 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState17 _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_18 : type  ttv_stack. ((ttv_stack, _menhir_box_main) _menhir_cell1_expression as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_main) _menhir_state -> _ -> _menhir_box_main =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | RPAREN ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let MenhirCell1_expression (_menhir_stack, _menhir_s, e1) = _menhir_stack in
          let e2 = _v in
          let _v = _menhir_action_11 e1 e2 in
          _menhir_goto_expression _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | LPAREN ->
          let _menhir_stack = MenhirCell1_expression (_menhir_stack, _menhir_s, _v) in
          _menhir_run_17 _menhir_stack _menhir_lexbuf _menhir_lexer
      | IDENT _v_0 ->
          let _menhir_stack = MenhirCell1_expression (_menhir_stack, _menhir_s, _v) in
          _menhir_run_20 _menhir_stack _menhir_lexbuf _menhir_lexer _v_0
      | _ ->
          _eRR ()
  
  and _menhir_run_20 : type  ttv_stack. (ttv_stack, _menhir_box_main) _menhir_cell1_expression -> _ -> _ -> _ -> _menhir_box_main =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      let MenhirCell1_expression (_menhir_stack, _menhir_s, e1) = _menhir_stack in
      let nm = _v in
      let _v = _menhir_action_10 e1 nm in
      _menhir_goto_expression _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_21 : type  ttv_stack. ((ttv_stack, _menhir_box_main) _menhir_cell1_LETPROVE _menhir_cell0_IDENT _menhir_cell0_arguments as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_main) _menhir_state -> _ -> _menhir_box_main =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      let _menhir_stack = MenhirCell1_expression (_menhir_stack, _menhir_s, _v) in
      match (_tok : MenhirBasics.token) with
      | LPAREN ->
          _menhir_run_17 _menhir_stack _menhir_lexbuf _menhir_lexer
      | IDENT _v_0 ->
          _menhir_run_20 _menhir_stack _menhir_lexbuf _menhir_lexer _v_0
      | EQUALS ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | LPAREN ->
              _menhir_run_13 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState22
          | IDENT _v_1 ->
              let _tok = _menhir_lexer _menhir_lexbuf in
              let nm = _v_1 in
              let _v = _menhir_action_09 nm in
              _menhir_run_23 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState22 _tok
          | _ ->
              _eRR ())
      | _ ->
          _eRR ()
  
  and _menhir_run_08 : type  ttv_stack. (ttv_stack, _menhir_box_main) _menhir_cell1_argument -> _ -> _ -> _ -> _menhir_box_main =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v ->
      let MenhirCell1_argument (_menhir_stack, _menhir_s, arg) = _menhir_stack in
      let args = _v in
      let _v = _menhir_action_02 arg args in
      _menhir_goto_arg_list _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
  
  let rec _menhir_run_00 : type  ttv_stack. ttv_stack -> _ -> _ -> _menhir_box_main =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | LETPROVE ->
          _menhir_run_01 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState00
      | _ ->
          _eRR ()
  
end

let main =
  fun _menhir_lexer _menhir_lexbuf ->
    let _menhir_stack = () in
    let MenhirBox_main v = _menhir_run_00 _menhir_stack _menhir_lexbuf _menhir_lexer in
    v
