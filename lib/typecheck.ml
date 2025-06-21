(* CSE322 Compiler Assignment 3 *)
(* Type Checker *)

module A = Absyn

let rec list2string l = match l with
  | [] -> ""
  | [t] -> t
  | h::t -> h ^ "," ^ list2string t

let rec tp2string tp = match tp with
  | A.Inttp -> "int"
  | A.Tupletp tps -> "<" ^ (list2string (List.map tp2string tps)) ^ ">"
  | A.Arrowtp (tp1, tp2) -> tp2string tp1 ^ " -> " ^ tp2string tp2
  | A.Reftp tp -> tp2string tp ^ " ref"

type context = A.tp Symbol.table

exception Unimplemented

(* sub: check if t1 is a subtype of t2 *)
let rec sub (t1,t2) =
  let width(tl1, tl2) = if (List.length tl1) >= (List.length tl2) then true else false in
  let rec depth(tl1, tl2) = match tl2 with
    | tp2::tl2' -> (match tl1 with tp1::tl1'-> if sub(tp1,tp2) then depth(tl1',tl2') else false | _ -> false)
    | [] -> true
  in match t1 with
    | A.Inttp -> if t2 = A.Inttp then true else false
    | A.Tupletp tps1 -> (match t2 with
      | A.Tupletp tps2 -> if width(tps1, tps2) then depth (tps1, tps2) else false
      | _ -> false)
    | A.Arrowtp (t1p1, t1p2) -> (match t2 with
      | A.Arrowtp (t2p1, t2p2) -> if sub (t2p1,t1p1) && sub(t1p2,t2p2) then true else false
      | _ -> false)
    | A.Reftp tp1 -> (match t2 with
      | A.Reftp tp2 -> if tp1 = tp2 then true else false
      | _ -> false)

(* check_sub: raise error if t1 is not a subtype of t2 *)
let check_sub pos (tp1, tp2) =
   if sub (tp1, tp2) then ()
   else Errormsg.error (pos, (tp2string tp1)^" is not a subtype of "^(tp2string tp2))

(* complain: alias for Errormsg.error *)
let complain pos err = Errormsg.error (pos, err)

(* join: compute the join of t1 and t2 *)
let rec join pos (t1,t2) : A.tp =
  (* check if st1 and st2 can be joined or not *)
  let rec check_join (st1, st2) = match st1 with
    | A.Inttp -> if sub(st1,st2) then true else false
    | A.Tupletp tps1 -> (match st2 with
      | A.Tupletp tps2 -> true
      | _ -> false)
    | A.Arrowtp (t1p1, t1p2) -> (match st2 with
      | A.Arrowtp (t2p1, t2p2) -> check_join(t1p1,t2p1) && check_join(t1p2,t2p2)
      | _ -> false)
    | A.Reftp tp1 -> (match st2 with
      | A.Reftp tp2 -> if tp1=tp2 then true else false
      | _ -> false) in
  (* join tl1 list and tl2 list *)
  let rec rec_join (tl1, tl2) =
    match (tl1, tl2) with
    | (tp1::tl1', tp2::tl2') -> if check_join(tp1,tp2) then join pos (tp1,tp2)::(rec_join (tl1', tl2'))
                                else []
    | ([], _) -> []
    | (_, []) -> []
  in match t1 with
    | A.Inttp -> if sub(t1,t2) then A.Inttp
                 else (complain pos ("t1(" ^ tp2string t1 ^ ") and t2(" ^ tp2string t2 ^ ") cannot join"); t1)
    | A.Tupletp tps1 -> (match t2 with
      | A.Tupletp tps2 -> A.Tupletp (rec_join (tps1, tps2))
      | _ -> (complain pos ("t1(" ^ tp2string t1 ^ ") and t2(" ^ tp2string t2 ^ ") cannot join"); t1))
    | A.Arrowtp (t1p1, t1p2) -> (match t2 with
      | A.Arrowtp (t2p1, t2p2) -> A.Arrowtp (join pos (t1p1,t2p1), join pos (t1p2,t2p2))
      | _ -> (complain pos ("t1(" ^ tp2string t1 ^ ") and t2(" ^ tp2string t2 ^ ") cannot join"); t1))
    | A.Reftp tp1 -> (match t2 with
      | A.Reftp tp2 -> if tp1 = tp2 then t1
                       else (complain pos ("t1(" ^ tp2string t1 ^ ") and t2(" ^ tp2string t2 ^ ") cannot join"); t1)
      | _ -> (complain pos ("t1(" ^ tp2string t1 ^ ") and t2(" ^ tp2string t2 ^ ") cannot join"); t1))

(* tc_exp: check the type of the given expression e *)
(* - ctxt: symbol table                             *)
(* - pos: position of the expression                *)
(* lib/typecheck.ml *)

let rec tc_exp (ctxt : A.tp Symbol.table) (pos : Errormsg.pos * Errormsg.pos) (e : A.exp) : A.tp =
  match e with
  | A.Int _ ->
      A.Inttp

  | A.Id x ->
      (match Symbol.find x ctxt with
       | Some tp -> tp
       | None ->
           Errormsg.error (pos, "undefined variable: " ^ Symbol.name x);
           A.Inttp)

  | A.Op (oper, args) ->
      let tc1 e1 = tc_exp ctxt pos e1 in
      let tc2 e1 e2 = (tc_exp ctxt pos e1, tc_exp ctxt pos e2) in
      begin match oper, args with
      | (A.Add | A.Sub | A.Mul | A.LT | A.Eq), [e1; e2] ->
          let t1, t2 = tc2 e1 e2 in
          check_sub pos (t1, A.Inttp);
          check_sub pos (t2, A.Inttp);
          A.Inttp

      | A.Ref, [e1] ->
          let t1 = tc1 e1 in
          A.Reftp t1

      (* deref : t ref → t *)
      | A.Get, [e1] ->
          let t1 = tc1 e1 in
          begin match t1 with
          | A.Reftp t_inner -> t_inner
          | _ ->
              Errormsg.error (pos, "deref of non-ref type: " ^ tp2string t1);
              A.Inttp
          end

      (* assignment : t ref × t → unit (즉 <>) *)
      | A.Set, [e_ref; e_val] ->
          let t_ref = tc1 e_ref in
          let t_val = tc1 e_val in
          begin match t_ref with
          | A.Reftp t_inner ->
              check_sub pos (t_val, t_inner);
              A.Tupletp []
          | _ ->
              Errormsg.error (pos, "assignment to non-ref type: " ^ tp2string t_ref);
              A.Tupletp []
          end

      | _ ->
          Errormsg.error (pos, "wrong arguments for operator");
          A.Inttp
      end

  | A.Tuple es ->
      let ts = List.map (tc_exp ctxt pos) es in
      A.Tupletp ts

  | A.Proj (i, e1) ->
      let t1 = tc_exp ctxt pos e1 in
      begin match t1 with
      | A.Tupletp ts when i >= 0 && i < List.length ts ->
          List.nth ts i
      | A.Tupletp _ ->
          Errormsg.error (pos, "tuple index out of bounds");
          A.Inttp
      | _ ->
          Errormsg.error (pos, "projection from non-tuple type: " ^ tp2string t1);
          A.Inttp
      end

  | A.If (e1, e2, e3) ->
      let t1 = tc_exp ctxt pos e1 in
      check_sub pos (t1, A.Inttp);
      let t2 = tc_exp ctxt pos e2 in
      let t3 = tc_exp ctxt pos e3 in
      join pos (t2, t3)

  | A.While (e1, e2) ->
      let t1 = tc_exp ctxt pos e1 in
      check_sub pos (t1, A.Inttp);
      let t2 = tc_exp ctxt pos e2 in
      check_sub pos (t2, A.Tupletp []);
      A.Tupletp []

  | A.Call (e1, e2) ->
      let tfun = tc_exp ctxt pos e1 in
      let targ = tc_exp ctxt pos e2 in
      begin match tfun with
      | A.Arrowtp (t_param, t_res) ->
          check_sub pos (targ, t_param);
          t_res
      | _ ->
          Errormsg.error (pos, "call of non-function type: " ^ tp2string tfun);
          A.Inttp
      end

  | A.Let (x, e1, e2) ->
      let t1 = tc_exp ctxt pos e1 in
      let ctxt' = Symbol.add x t1 ctxt in
      tc_exp ctxt' pos e2

  | A.Constrain (e1, tp_expected) ->
      let t1 = tc_exp ctxt pos e1 in
      check_sub pos (t1, tp_expected);
      tp_expected

  | A.Pos (pos', e_inner) ->
      tc_exp ctxt pos' e_inner


(* tc_fundec: check the type of the function definition *)
let tc_fundec ctxt ((pos, (f, x, tp1, tp2, exp)): A.fundec) =
  let ctxt' = Symbol.add x tp1 ctxt in
  let tp = tc_exp ctxt' pos exp
  in check_sub pos (tp, tp2)

(* do_another_fun: update the types of the functions *)
let do_another_fun ctxt (pos, fdec) =
  let (f, x, tp1, tp2, exp) = fdec in
  match Symbol.find f ctxt with
    (* check if the function name is duplicated *)
    | Some x -> (Errormsg.error(pos,"function name (" ^ Symbol.name f ^ ") is duplicated"); ctxt)
    | None -> if (Symbol.name f) = "main" then (* check if main function has int->int type *)
                (if (tp1 = A.Inttp) && (tp2 = A.Inttp) then Symbol.add f (A.Arrowtp (tp1, tp2)) ctxt
                 else (Errormsg.error(pos,"main function has wrong type"); Symbol.add f (A.Arrowtp (tp1, tp2)) ctxt))
              else Symbol.add f (A.Arrowtp (tp1, tp2)) ctxt

(* build_global_context: generate the initial symbol table *)
let build_global_context (fundecs): context =
  List.fold_left do_another_fun (Symbol.add (Symbol.symbol "print_int") (A.Arrowtp (A.Inttp, A.Tupletp [])) Symbol.empty) fundecs

(* tc: check the type of the program *)
let tc (fundecs : A.prog)  =
  let ctxt = build_global_context(fundecs) in
  let _ = List.map (tc_fundec ctxt) fundecs in
  ()

