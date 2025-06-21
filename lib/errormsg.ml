(* CSE322 Compiler Assignment 3 *)
(* Auxiliary Module for Printing Error Message *)

exception Error

type pos = int

let any_error = ref false

let cur_file = ref ""
let line_pos = ref [0]

let new_line p = line_pos := (snd p) :: !line_pos

let reset name = (
  any_error := false;
	cur_file := name;
	line_pos := [0])

let rec find_line l p = match l with
  | [] -> 0
  | hd::tl -> if hd <= p then List.length tl
              else find_line tl p

let error ((p1, p2), msg) =
  let n = find_line !line_pos p1 in
  let p = List.nth !line_pos (List.length !line_pos - n - 1) in
  let off1 = p1 - p + 1 in
  let off2 = p2 - p in
    (any_error := true;
	   Printf.printf "%s:%d:%d-%d: %s\n" !cur_file (n+1) off1 off2 msg)

let impossible msg =
  (Printf.printf "Error: %s\n" msg;
   Stdlib.flush Stdlib.stdout; raise Error)
