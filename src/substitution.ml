open Ast

module IntMap = Map.Make(Int)

(* refresh_bound_ids_XXX (XXX = val/exp)
 *
 * Assigns fresh ids to all *bound* identifiers and locations.
 * Lookup is by name.
 * Assumes the the Barendreght principle.
 * It does not affect abstract values or free identifiers/locations.
 * This is used during subtitution to maintain the the Barendreght principle.
 *
 * *)

let rec refresh_bound_ids_val_rec map v refresh_id =
  let extend str iold inew env = if str = "_" then env else (IntMap.add iold inew env) in
  match v with
  | ConstVal _ -> v
  | TupleVal vs ->
      let newvs = List.rev (List.fold_left (fun vs v -> (refresh_bound_ids_val_rec map v refresh_id) :: vs) [] vs) in
      TupleVal newvs
  | FunVal (fid, ft, param, pt, e) ->
      let newfid = refresh_id fid in
      let newparam = refresh_id param in
      let newmap = extend param.str param.idid newparam.idid (extend fid.str fid.idid newfid.idid map) in
      let newe = refresh_bound_ids_exp_rec newmap e refresh_id in
      FunVal (newfid, ft, newparam, pt, newe)
  | AbsCon _ -> v
  | AbsFun _ -> v
     

and refresh_bound_ids_exp_rec map e refresh_id =
  let extend str iold inew env = if str = "_" then env else (IntMap.add iold inew env) in
  match e with
  | ValExp (v, p) ->
      let newv = refresh_bound_ids_val_rec map v refresh_id in
      ValExp (newv, p)
  | IdentExp  (id, p) -> 
      (match IntMap.find_opt id.idid map with
       | None ->
          raise (Error.RuntimeE (get_lex_pos e, "refresh_exp unbound variable: " ^ id.str))
          (* only happens with new keywords *)
      | Some i -> IdentExp ({idid=i; str=id.str}, p))
  | ArithExp (op, es, p) ->
      let newes = List.map (fun e -> refresh_bound_ids_exp_rec map e refresh_id) es in
      ArithExp (op, newes, p)
  | AppExp (e1, e2, p) ->
      let newe1 = refresh_bound_ids_exp_rec map e1 refresh_id in
      let newe2 = refresh_bound_ids_exp_rec map e2 refresh_id in
      AppExp (newe1, newe2, p)
  | CondExp (e1, e2, e3, p) ->
      let newe1 = refresh_bound_ids_exp_rec map e1 refresh_id in
      let newe2 = refresh_bound_ids_exp_rec map e2 refresh_id in
      let newe3 = refresh_bound_ids_exp_rec map e3 refresh_id in
      CondExp (newe1, newe2, newe3, p)
  | LetExp (id, it, e1, e2, p) ->
      let newe1 = refresh_bound_ids_exp_rec map e1 refresh_id in
      let newid = refresh_id id in
      let newmap = extend id.str id.idid newid.idid map in
      let newe2 = refresh_bound_ids_exp_rec newmap e2 refresh_id in
      LetExp (newid, it, newe1, newe2, p)
  | LetTuple (ids_ts, e1, e2, p) ->
      let newe1 = refresh_bound_ids_exp_rec map e1 refresh_id in
      let new_ids_ts = List.rev (List.fold_left (fun new_ids_ts (i, it) -> (refresh_id i, it) :: new_ids_ts) [] ids_ts) in
      let newmap = List.fold_left2 (fun map ({idid = newidid}, _) ({idid;str}, _) -> extend str idid newidid map) map new_ids_ts ids_ts in
      let newe2 = refresh_bound_ids_exp_rec newmap e2 refresh_id in
      LetTuple (new_ids_ts, newe1, newe2, p)
   | SeqExp (e1, e2, p) ->
      let newe1 = refresh_bound_ids_exp_rec map e1 refresh_id in
      let newe2 = refresh_bound_ids_exp_rec map e2 refresh_id in
      SeqExp (newe1, newe2, p)
  | TupleExp (es, p) ->
      let newes = List.rev (List.fold_left (fun es e -> (refresh_bound_ids_exp_rec map e refresh_id) :: es) [] es) in
      TupleExp (newes, p)
   | BotExp _ -> e
   | TupleProjExp (e1, i, j, p) -> 
      let newe1 = refresh_bound_ids_exp_rec map e1 refresh_id in
      TupleProjExp (newe1, i, j, p)
   | TupleUpdExp  (e1, i, j, e2, p) ->
      let newe1 = refresh_bound_ids_exp_rec map e1 refresh_id in
      let newe2 = refresh_bound_ids_exp_rec map e2 refresh_id in
      TupleUpdExp  (newe1, i, j, newe2, p)



let refresh_bound_ids_exp e = 
  let refresh_id ({idid; str} as i) = if str = "_" then i else {idid = get_fresh_id (); str = str} in
  refresh_bound_ids_exp_rec IntMap.empty e refresh_id
let refresh_bound_ids_val v =
  let refresh_id ({idid; str} as i) = if str = "_" then i else {idid = get_fresh_id (); str = str} in
  refresh_bound_ids_val_rec IntMap.empty v refresh_id

let alpha_normalisation_exp e =
  let next_fresh_id = ref 0 in
  let get_fresh_id () = let x = !next_fresh_id in next_fresh_id := !next_fresh_id + 1; x in
  let refresh_id ({idid; str} as i) = if str = "_" then i else {idid = get_fresh_id (); str = str} in
  refresh_bound_ids_exp_rec IntMap.empty e refresh_id

let alpha_normalisation_val v =
  let next_fresh_id = ref 0 in
  let get_fresh_id () = let x = !next_fresh_id in next_fresh_id := !next_fresh_id + 1; x in
  let refresh_id ({idid; str} as i) = if str = "_" then i else {idid = get_fresh_id (); str = str} in
  refresh_bound_ids_val_rec IntMap.empty v refresh_id

(* subst_XXX
 *
 * Regular parallel substitution of free identifiers with values (assumed closed)
 * the Barendreght assumption for identifier ids.
 * This assumption is preserved by calling 'refresh_bound_ids' when a substitution is made
 *
 * *)
let rec subst_val map v =
  match v with
  | ConstVal _ -> v
  | TupleVal vs ->
      TupleVal (List.map (fun v -> subst_val map v) vs)
  | FunVal (fid, ft, param, pt, e) ->
      assert ((fid.idid = -1 || not (IntMap.mem fid.idid map))
              && (param.idid = -1 || not (IntMap.mem param.idid map)));
      FunVal (fid, ft, param, pt, subst_exp map e)
  | AbsCon _ -> v
  | AbsFun _ -> v
 

and subst_exp map e =
  match e with
  | ValExp    (v, p)          -> ValExp    (subst_val map v, p)         
  | IdentExp  ({idid = id; str = _}, p) -> begin
    match (IntMap.find_opt id map) with
    | None -> e
    | Some v -> ValExp (refresh_bound_ids_val v, None)
  end
  | ArithExp  (op, eLst, p)   -> ArithExp(op, (List.map (fun e -> subst_exp map e) eLst), p)  
  | AppExp    (e1, e2, p)     -> AppExp((subst_exp map e1), (subst_exp map e2), p)  
  | CondExp   (e1, e2, e3, p) -> CondExp((subst_exp map e1), (subst_exp map e2), (subst_exp map e3), p)
  | LetExp    (id, it, e1, e2, p) -> 
      assert (id.idid = -1 || not (IntMap.mem id.idid map));
      LetExp    (id, it, (subst_exp map e1), (subst_exp map e2), p)
  | LetTuple  (ids_ts, e1, e2, p)-> 
      let _ = List.map (fun ({idid}, _) -> assert ( idid = -1 || not (IntMap.mem idid map))) ids_ts in
      LetTuple (ids_ts, (subst_exp map e1), (subst_exp map e2), p)
  | SeqExp    (e1, e2, p)     -> SeqExp    ((subst_exp map e1), (subst_exp map e2), p)    
  | TupleExp  (es, p)         -> TupleExp  (List.map (fun e -> subst_exp map e) es, p)    
  | BotExp    p               -> e
  | TupleProjExp (e1, i, j, p) -> 
      TupleProjExp (subst_exp map e1, i, j, p)
  | TupleUpdExp  (e1, i, j, e2, p) ->
      TupleUpdExp  (subst_exp map e1, i, j, subst_exp map e2, p)


let empty = IntMap.empty
let extend {Ast.idid} v subst = IntMap.add idid v subst
let f map e = subst_exp map e

