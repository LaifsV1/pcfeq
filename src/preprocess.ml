open Ast

module StringMap = Map.Make(String)

(* assign_fresh_ids_to_names_XXX (XXX = val/exp)
 *
 * Assigns fresh ids to all *bound* identifiers and locations.
 * Lookup is by name.
 * Assumption: expression is double closed (for identifiers and locations)
 * Uses capture-avoiding substitution.
 * It does not affect abstract values.
 * This is used once after parsing.
 *
 * *)

let rec assign_fresh_ids_to_names_val env v =
  let refresh_id ({idid; str} as i) = if str = "_" then i else {idid = get_fresh_id (); str = str} in
  let extend str uid env = if str = "_" then env else (StringMap.add str uid env) in
  match v with
  | ConstVal _ -> v
  | TupleVal (vs) -> TupleVal (List.map (assign_fresh_ids_to_names_val env) vs)
  | FunVal (fid, ft, param, pt, e) ->
      let newfid = refresh_id fid in
      let newparam = refresh_id param in
      let newenv = extend param.str newparam.idid (extend fid.str newfid.idid env) in
      let newe = assign_fresh_ids_to_names_exp newenv e in
      FunVal (newfid, ft, newparam, pt, newe)
  | AbsCon _ -> v
  | AbsFun _ -> v

and assign_fresh_ids_to_names_exp env e =
  let refresh_id ({idid; str} as i) = if str = "_" then i else {idid = get_fresh_id (); str = str} in
  let extend str uid env = if str = "_" then env else (StringMap.add str uid env) in
  match e with
  | ValExp (v1, p) -> ValExp (assign_fresh_ids_to_names_val env v1, p)
  | IdentExp  (id, p) ->
     begin
       match StringMap.find_opt id.str env with
       | None ->
          raise (Error.SyntaxE (get_lex_pos e, "unbound variable: " ^ id.str))
       | Some i -> IdentExp ({idid=i; str=id.str}, p)
     end
  | ArithExp (op, es, p) -> 
      let newes = List.rev (List.fold_left (fun es e -> (assign_fresh_ids_to_names_exp env e) :: es) [] es) in
      ArithExp (op, newes, p)
  | AppExp (e1, e2, p) ->
      let newe1 = assign_fresh_ids_to_names_exp env e1 in
      let newe2 = assign_fresh_ids_to_names_exp env e2 in
      AppExp (newe1, newe2, p)
  | CondExp (e1, e2, e3, p) ->
      let newe1 = assign_fresh_ids_to_names_exp env e1 in
      let newe2 = assign_fresh_ids_to_names_exp env e2 in
      let newe3 = assign_fresh_ids_to_names_exp env e3 in
      CondExp (newe1, newe2, newe3, p)
  | LetExp (id, it, e1, e2, p) ->
      let newe1 = assign_fresh_ids_to_names_exp env e1 in
      let newid = refresh_id id in
      let newenv = extend id.str newid.idid env in
      let newe2 = assign_fresh_ids_to_names_exp newenv e2 in
      LetExp (newid, it, newe1, newe2, p)
  | LetTuple (ids_ts, e1, e2, p) ->
      let newe1 = assign_fresh_ids_to_names_exp env e1 in
      let new_ids_ts = List.rev (List.fold_left (fun new_ids_ts (i, it) -> (refresh_id i, it) :: new_ids_ts) [] ids_ts) in
      let newenv = List.fold_left (fun env ({idid;str}, it) -> extend str idid env) env new_ids_ts in
      let newe2 = assign_fresh_ids_to_names_exp newenv e2 in
      LetTuple (new_ids_ts, newe1, newe2, p)
  | SeqExp (e1, e2, p) ->
      let newe1 = assign_fresh_ids_to_names_exp env e1 in
      let newe2 = assign_fresh_ids_to_names_exp env e2 in
      SeqExp (newe1, newe2, p)
  | TupleExp (es, p) ->
      let newes = List.rev (List.fold_left (fun es e -> (assign_fresh_ids_to_names_exp env e) :: es) [] es) in
      TupleExp (newes, p)
  | BotExp _ -> e
  | TupleProjExp (e1, i, j, p) ->
      let newe1 = assign_fresh_ids_to_names_exp env e1 in
      TupleProjExp (newe1, i, j, p)
  | TupleUpdExp (e1, i, j, e2, p) ->
      let newe1 = assign_fresh_ids_to_names_exp env e1 in
      let newe2 = assign_fresh_ids_to_names_exp env e2 in
      TupleUpdExp (newe1, i, j, newe2, p)


let assign_fresh_ids_to_names_pgm ({e1; e2} as pgm) =
  let newe1 = assign_fresh_ids_to_names_exp StringMap.empty e1 in
  let newe2 = assign_fresh_ids_to_names_exp StringMap.empty e2 in
  {pgm with e1 = newe1; e2 = newe2}


