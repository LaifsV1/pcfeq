type arith_op =
  | Negate 
  | Add 
  | Subtract 
  | Multiply 
  | Divide 
  | Modulo
  | And 
  | Or 
  | Not 
  | Equal 
  | Different 
  | Less 
  | Greater
  | LessEQ
  | GreaterEQ
  | Implies
  | Fst
  | Snd

(* used to give objects unique ids *)
type uniqueId = int

let int_of_uniqueId : uniqueId -> int =
  fun x -> x

let next_fresh_id = ref 0
let get_fresh_id () = let x = !next_fresh_id in next_fresh_id := !next_fresh_id + 1; x
let reset_fresh_id () = next_fresh_id := 0; ()
let default_acname = "$ac"
let default_afname = "$af"

(* identifiers *)
type ident = {idid:uniqueId; str:string}
type const = 
  | IntConst  of int
  | BoolConst of bool
  | UnitConst
type lex_pos_opt = (Lexing.position * Lexing.position) option
type value =
  | ConstVal of const
  | TupleVal of value list
  | FunVal of ident * Type.t * ident * Type.t * expression (* ret_typ,arg_typ *)
  | AbsCon of uniqueId * Type.t * string
  | AbsFun of uniqueId * Type.t * Type.t * string * (value list) (* arg_typ,ret_typ *)
(** TODO: add list of values **)
and
expression =
  | ValExp    of value * lex_pos_opt
  | IdentExp  of ident * lex_pos_opt
  | ArithExp  of arith_op * expression list * lex_pos_opt
  | AppExp    of expression * expression * lex_pos_opt
  | CondExp   of expression * expression * expression * lex_pos_opt
  | LetExp    of ident * Type.t * expression * expression * lex_pos_opt
  | LetTuple  of (ident * Type.t) list * expression * expression * lex_pos_opt
  | SeqExp    of expression * expression * lex_pos_opt   (* semicolon *)
  | TupleExp  of expression list * lex_pos_opt
  | BotExp    of lex_pos_opt
  | TupleProjExp of expression * int * int * lex_pos_opt
  | TupleUpdExp  of expression * int * int * expression * lex_pos_opt

(* the program is two expressions and their relation *)
type relation =
  | Equiv
  | Approx
  | ApproxInv
type program = {e1:expression; e2:expression; rel:relation * Type.t}

(* convenience functions *)

let get_ret_type = function
  | FunVal (_, ft, _, _, _) -> ft
  | AbsFun (i, t1, t2, s, ls) -> t2
  | _ -> failwith "<get_ret_type>: not a function"

let string_of_position : Lexing.position -> string =
  fun {pos_fname ; pos_lnum ; pos_bol ; pos_cnum } ->
  Printf.sprintf "<line: %d, column: %d>" pos_lnum pos_cnum

let string_of_pos_option pos =
  match pos with
  | None -> "empty position"
  | Some (pos1,pos2) -> Printf.sprintf "%s,%s" (string_of_position pos1) (string_of_position pos2)

let get_lex_pos x = 
  match x with
  | ValExp (_, p) -> p
  | IdentExp (_, p) -> p
  | ArithExp (_, _, p) -> p
  | AppExp (_, _, p) -> p
  | CondExp (_, _, _, p) -> p
  | LetExp (_, _, _, _, p) -> p
  | LetTuple (_, _, _, p) -> p
  | SeqExp (_, _, p) -> p
  | TupleExp (_, p) -> p
  | BotExp p -> p
  | TupleProjExp (_, _, _, p) -> p
  | TupleUpdExp  (_, _, _, _, p) -> p
(*
 * print the AST
 *
 * *)

let string_of_op op =
  match op with
  | Negate    -> "-"
  | Add       -> "+"
  | Subtract  -> "-"
  | Multiply  -> "*"
  | Divide    -> "/"
  | Modulo    -> "%"
  | And       -> "&&"
  | Or        -> "||"
  | Not       -> "not"
  | Equal     -> "=="
  | Different -> "<>"
  | Less      -> "<"
  | Greater   -> ">"
  | LessEQ    -> "<="
  | GreaterEQ -> ">="
  | Implies -> "=>"
  | Fst       -> "fst"
  | Snd       -> "snd"

let string_of_id {idid; str} =
  if str = "_" then "_"
  else str ^ "_" ^ (string_of_int idid)

let string_of_const c =
  match c with
  | IntConst  i -> string_of_int i
  | BoolConst b -> string_of_bool b
  | UnitConst   -> "()"

let string_of_abs idid str = string_of_id {idid;str}

let rec string_of_val v =
  let rec iter f = function
    | [] -> ""
    | [i] -> f i
    | i :: rest -> (f i) ^ ", " ^ (iter f rest)
  in
   match v with
  | ConstVal c  -> string_of_const c
  | TupleVal (vs) ->
     Printf.sprintf "(%s)" (iter string_of_val vs)
  | FunVal (fid, ft, param, pt, e) ->
     Printf.sprintf "(fix %s. fun %s :(%s -> %s) -> %s)"
       (string_of_id fid) (string_of_id param)
       (Type.string_of_t pt) (Type.string_of_t ft) (string_of_exp e)
  | AbsCon (i, t, s) ->
     Printf.sprintf "(%s : %s)"
       (string_of_abs i s) (Type.string_of_t t)
  | AbsFun  (i, t1, t2, s, ls) ->
     Printf.sprintf "(%s : %s -> %s [+%d])"
       (string_of_abs i s) (Type.string_of_t t1) (Type.string_of_t t2) (List.length ls)
and string_of_exp exp =
  let rec iter f = function
    | [] -> ""
    | [i] -> f i
    | i :: rest -> (f i) ^ ", " ^ (iter f rest)
  in
  match exp with
  | ValExp    (v, p) -> string_of_val v
  | IdentExp  (id, p) -> string_of_id id
  | ArithExp  (op, es, p) ->
     Printf.sprintf "(%s %s)"
       (string_of_op op)
       (String.concat " " (List.map string_of_exp es))
  | AppExp    (e1, e2, p) ->
     Printf.sprintf "(%s %s)"
       (string_of_exp e1) (string_of_exp e2)
  | CondExp   (e1, e2, e3, p) ->
     Printf.sprintf "(if %s then %s else %s)"
       (string_of_exp e1) (string_of_exp e2) (string_of_exp e3)
  | LetExp    (i, it, e1, e2, p) ->
     Printf.sprintf "(let %s : %s = %s in %s)"
       (string_of_id i) (Type.string_of_t it) (string_of_exp e1) (string_of_exp e2)
  | LetTuple  (is_ts, e1, e2, p) ->
     Printf.sprintf "(let (%s):(%s) = %s in %s)"
       (iter (fun (id, _) -> string_of_id id) is_ts)
       (iter (fun (_, it) -> Type.string_of_t it) is_ts)
       (string_of_exp e1) (string_of_exp e2)
  | SeqExp    (e1, e2, p) ->
     Printf.sprintf "(%s ; %s)" (string_of_exp e1) (string_of_exp e2)
  | TupleExp  (es, p) ->
     Printf.sprintf "(%s)" (iter string_of_exp es)
  | BotExp    p -> "_bot_"
  | TupleProjExp (e1, i, j, p) ->
     Printf.sprintf "(%s[ %d / %d ])"
       (string_of_exp e1) i j
  | TupleUpdExp  (e1, i, j, e2, p) ->
     Printf.sprintf "(%s[ %d / %d := %s ])"
       (string_of_exp e1) i j (string_of_exp e2)

let string_of_pgm {e1 = e1; e2 = e2; rel = (r, t)} =
  (string_of_exp e1) ^ "\n" ^ (
    match r with
    | Equiv     -> "|||"
    | Approx    -> "|<|"
    | ApproxInv -> "|>|"
  ) ^ "_" ^ (Type.string_of_t t) ^ "\n" ^
  (string_of_exp e2)

let string_of_list string_of delim ls =
  String.concat delim (List.map string_of ls)
