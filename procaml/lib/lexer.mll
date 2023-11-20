{
    open Parser
    exception SyntaxError of string

    let keyword word =
        match word with
        | _     -> IDENT(word)
    let comment_keyword word =
        match word with
        | _       -> IDENT(word)
}

let newline = '\r' | '\n' | "\r\n"
rule token = parse
 | [' ' '\t'] {token lexbuf}
 | newline {Lexing.new_line lexbuf; token lexbuf}
 | "let (*prove*)" {LETPROVE}
 | "(*" { comment lexbuf }
 | ['a'-'z' 'A'-'Z' '0'-'9' '_' '\''] + as word {keyword word}
 | ':' { COLON }
 | '(' { LPAREN }
 | ')' { RPAREN }
 | '=' {EQUALS}
 | _ { raise (SyntaxError ("Unexpected char: " ^ Lexing.lexeme lexbuf)) }
 | eof { EOF }

and comment = parse
 | "*)" { token lexbuf }
 | newline { Lexing.new_line lexbuf;comment lexbuf }
 | "hint: axiom " { AXIOM }
 | "hint: induction " ['a'-'z' 'A'-'Z' '0'-'9' '_' '\''] + as var_name { INDUCTION(var_name) }
 | eof { raise (SyntaxError "Unclosed comment") }
 | _ { comment lexbuf }

