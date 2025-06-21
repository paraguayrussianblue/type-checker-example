(* CSE322 Compiler Assignment 3 *)
(* Abstract Syntax Tree *)

type id = Symbol.symbol

type tp =
  (* integer type *)
  | Inttp
  (* n-ary tuples; n can be 0 *)
  | Tupletp of tp list
  (* function type with argument and result *)
  | Arrowtp of tp * tp
  (* ref type *)
  | Reftp of tp

type oper =
  (* 2-argument addition operation *)
  | Add
  (* 2-argument subtraction operation *)
  | Sub
  (* 2-argument multiplication operation *)
  | Mul
  (* less than operator; return 1 when true; 0 when false *)
  | LT
  (* equal operator; return 1 when true; 0 when false *)
  | Eq
  (* ref constructor *)
  | Ref
  (* ref dereference *)
  | Get
  (* ref assignment *)
  | Set

type exp =
  (* constant integer *)
  | Int of int
  (* identifier *)
  | Id of id
  (* unary or binary operator; expressions are evaluated left-to-right *)
  | Op of oper * exp list
  (* create a pair, triple etc. *)
  | Tuple of exp list
  (* get ith field from tuple *)
  | Proj of int * exp
  (* if first argument is 0 take the second branch;
     otherwise take the first branch *)
  | If of exp * exp * exp
  | While of exp * exp
  (* function call; call-by-value: evaluate the first expression until
     you get a value; evaluate the second expression until you get an
     argument; check the first value is a function; apply the function
     to the argument *)
  | Call of exp * exp
  (* evaluate the first expression; bind the resulting value
     to the identifier; evaluate the second expression *)
  | Let of id * exp * exp
  | Constrain of exp * tp
  (* mark position of expression in source *)
  | Pos of (Errormsg.pos * Errormsg.pos) * exp

type func = id * id * tp * tp * exp

type fundec = (Errormsg.pos * Errormsg.pos) * func

type prog = fundec list
