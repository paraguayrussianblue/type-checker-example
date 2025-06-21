(* CSE322 Compiler Assignment 3 *)
(* Type Checker *)

exception Unimplemented

(* Check the type of the program; if there are any errors, these are reported through ErrorMsg.error *)
val tc : Absyn.prog -> unit

(* Check if t1 is the subtype of t2 *)
val sub: Absyn.tp * Absyn.tp -> bool

(* Return the join of two types *)
val join: (Errormsg.pos * Errormsg.pos) -> Absyn.tp * Absyn.tp -> Absyn.tp

