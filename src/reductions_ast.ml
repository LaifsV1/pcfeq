open Ast
open Z3api

let is_ho_value = function
  | ConstVal _ -> false
  | FunVal   _ -> true
  | AbsCon   _ -> false
  | AbsFun   _ -> true
  | TupleVal _ -> false

(* evaluation frames - ala CEK machines *)
type eval_frame =
  | ArithECxt   of arith_op * value list * expression list * (Lexing.position * Lexing.position) option
  | AppOpECxt   of expression * (Lexing.position * Lexing.position) option
  | AppRandECxt of value * (Lexing.position * Lexing.position) option
  | CondECxt    of expression * expression * (Lexing.position * Lexing.position) option 
  | LetECxt     of ident * Type.t * expression * (Lexing.position * Lexing.position) option 
  | LetTupleECxt of (ident * Type.t) list * expression * (Lexing.position * Lexing.position) option 
  | SeqECxt     of expression * (Lexing.position * Lexing.position) option          (* semicolon *)
  | TupleECxt   of value list * expression list * (Lexing.position * Lexing.position) option
  | TupleProjECxt of int * int * (Lexing.position * Lexing.position) option
  | TupleFstUpdECxt of int * int * expression * (Lexing.position * Lexing.position) option
  | TupleSndUpdECxt of value * int * int * (Lexing.position * Lexing.position) option

let rec string_of_eval_frame frame =
  match frame with
  | ArithECxt   (op,vs,es,p) ->
     Printf.sprintf "ArithCxt (%s;[%s];[%s];%s)"
       (string_of_op op)
       (String.concat "," (List.map string_of_val vs))
       (String.concat "," (List.map string_of_exp es))
       (string_of_pos_option p)
  | AppOpECxt   (e,p) ->
     Printf.sprintf "AppOpCxt (%s;%s)"
       (string_of_exp e)
       (string_of_pos_option p)
  | AppRandECxt (v,p) ->
     Printf.sprintf "AppRandCxt (%s;%s)"
       (string_of_val v)
       (string_of_pos_option p)
  | CondECxt    (e1,e2,p) ->
     Printf.sprintf "CondCxt (%s;%s;%s)"
       (string_of_exp e1)
       (string_of_exp e2)
       (string_of_pos_option p)
  | LetECxt     (id,t,e,p) ->
     Printf.sprintf "LetCxt (%s;%s;%s;%s)"
       (string_of_id id)
       (Type.string_of_t t)
       (string_of_exp e)
       (string_of_pos_option p)
  | LetTupleECxt (idts,e,p) ->
     Printf.sprintf "LetTupleCxt ([%s];%s;%s)"
       (String.concat ","
          (List.map (fun (id,t) -> Printf.sprintf "(%s : %s)"
                                     (string_of_id id)
                                     (Type.string_of_t t)) idts))
       (string_of_exp e)
       (string_of_pos_option p)
  | SeqECxt     (e,p) ->
     Printf.sprintf "SeqCxt (%s;%s)"
       (string_of_exp e)
       (string_of_pos_option p)
  | TupleECxt   (vs,es,p) ->
     Printf.sprintf "SeqCxt ([%s];%s;%s)"
       (String.concat "," (List.map string_of_val vs))
       (String.concat "," (List.map string_of_exp es))
       (string_of_pos_option p)
  | TupleProjECxt (i,j,p) ->
     Printf.sprintf "TupleProjECxt ([%s/%s];%s)"
       (string_of_int i)
       (string_of_int j)
       (string_of_pos_option p)
  | TupleFstUpdECxt (i,j,e,p) -> 
     Printf.sprintf "TupleFstUpdECxt ([%s/%s:=%s];%s)"
       (string_of_int i)
       (string_of_int j)
       (string_of_exp e)
       (string_of_pos_option p)
   | TupleSndUpdECxt (v,i,j,p) ->
      Printf.sprintf "TupleSndUpdECxt (%s;[%s/%s:=];%s)"
       (string_of_val v)
       (string_of_int i)
       (string_of_int j)
       (string_of_pos_option p)

(* the type of an evaluation context
 *
 * the head of the list is supposed to be the inner-most evaluation frame
 * *)
type eval_cxt = eval_frame list

let string_of_ecxt ecxt = String.concat "::" (List.map string_of_eval_frame ecxt)

(* A CEK expression is decomposed in two parts:
  * - an evaluation context
  * - an inner expression
  *
  * Taken by CEK machines
  * *)
type cek_exp = {ecxt: eval_cxt; e: expression}

let string_of_cek_exp {ecxt;e} =
  Printf.sprintf "{%s ; %s}"
    (string_of_ecxt ecxt)
    (string_of_exp e)

(* the reduction configuration *)
type red_conf = {e: cek_exp}

(**TODO: dummy dependency tree for when we decide to add it**)
type dummy_dtree = DummyDT
