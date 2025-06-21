(* CSE322 Compiler Assignment 3 *)
(* Auxiliary Module for Printing Error Message *)

exception Error

(* A "pos" value indicates the position of a file
   where an error is indicated. The position is
   represented as the distance from the beginning
   of the file, in characters. *)
type pos = int

(* "any_error" indicates if any error occurred or not *)
val any_error: bool ref

(* "reset(s)" updates the file name s and initializes
   line positions *)
val reset: string -> unit

(* "new_line(p)" informs that there is a newline at p *)
val new_line : (pos * pos) -> unit

(* "error((p1,p2),s)" reports the error "s" at (p1, p2).
   It uses the information reported by new_line(p)
   to indicate what line the error is in.  *)
val error : (pos * pos) * string -> unit

(* "impossible" raises an error *)
val impossible : string -> 'a

