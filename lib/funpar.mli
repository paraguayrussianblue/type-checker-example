type token =
  | COMMA
  | SEMICOLON
  | COLON
  | LPAREN
  | RPAREN
  | PLUS
  | MINUS
  | TIMES
  | LT
  | EQ
  | GT
  | AND
  | NOT
  | OR
  | WHILE
  | DO
  | REF
  | BANG
  | ASSIGN
  | IF
  | THEN
  | ELSE
  | LET
  | IN
  | FUN
  | ARROW
  | TYPE
  | UMINUS
  | EOF
  | ID of (string)
  | NUM of (int)
  | PROJ of (int)

val prog :
  (Lexing.lexbuf  -> token) -> Lexing.lexbuf -> Absyn.prog
