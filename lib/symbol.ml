(* CSE322 Compiler Assignment 3 *)
(* Symbol Table *)

type symbol = string * int

module IntMap = Map.Make(Int)

module SymbolTable = struct
  type key = symbol
  type 'a table = 'a IntMap.t
  let empty = IntMap.empty
  let add (s,n) a t = IntMap.add n a t
  let find (s,n) t = IntMap.find_opt n t
end

type 'a table= 'a SymbolTable.table

let empty = SymbolTable.empty
let add = SymbolTable.add
let find = SymbolTable.find

let next_sym = ref 0
let size_hint = 128

let hash_table : (string, int) Hashtbl.t = Hashtbl.create size_hint

let symbol (name: string) : symbol =
  match Hashtbl.find_opt hash_table name with
    | Some i -> (name, i)
    | None -> let i = !next_sym in
      next_sym := i+1;
		  Hashtbl.add hash_table name i; (name,i)

let name (name, i) = name

