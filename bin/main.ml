(* CSE322 Compiler Assignment 3 *)

open As3

exception Stop

let still_ok () = 
  if (!Errormsg.any_error) then raise Stop else ()

let compile filename =
  try
    let file = Stdlib.open_in filename in
    let _ = print_endline ("Compiling " ^ filename ^ " ...") in
    let lexbuf = Lexing.from_channel file in
    let _ = Errormsg.reset filename in
    let program = Funpar.prog Funlex.initial lexbuf in
    let _ = still_ok() in
    let _ = Typecheck.tc program in
    let _ = still_ok() in
    print_endline "Program is successfully type-checked";
  with Errormsg.Error -> print_endline "Compiler bug."
    | Stop -> print_endline "Compilation failed."
    | Typecheck.Unimplemented -> print_endline "Type checker is not implemented."

let () = compile "data/all.fun"
let () = compile "data/test.fun"
