(* This file contains functions used for normalisation of minimised configurations.
 * Idea:
 * 1. traverse configurations to (uniquely) accumulate all names present
 * 2. for each name found, generate a fresh ID in order of traversal
 * 3. (name , fresh ID) pairs form a substitution map used to rename all names
 *)

(* mini_cfg_pair : mini_cfg , label M_Map.t , sigma
 * mini_cfg      : cfg_exp , ecxt_frame list , Trace.t
 * Tace.t        : label
 *)

(** TODO: do we really need M in the minimal config? **)

open Ast
open Lts_ast

(********************************************
 * Types and Modules for the Identifier Map *
 ********************************************)
module Ident = struct
  type t = Ast.ident
  let compare {idid=id1; str=str1}
              {idid=id2; str=str2} =
    match compare id1 id2 with
    | 0 ->
       if str1 <> default_acname && str2 <> default_acname then
         if str1<>str2 then
           failwith
             (Printf.sprintf "ids not equal: %s and %s"
                (string_of_id {idid=id1; str=str1})
                (string_of_id {idid=id2; str=str2})); 0
    | c -> c
end
module IdentMap = Map.Make(Ident)
type ident_map = int IdentMap.t

(********************************************
 * Record type for names in a configuration *
 ********************************************)
type conf_names = { nxtid : int ; vars : ident_map }
let empty_conf_names = { nxtid = 0 ; vars = IdentMap.empty }

(******************************************
 * Adder Functions for the Identifier Map *
 ******************************************)
let add_var : Ast.ident -> conf_names -> conf_names =
  fun {idid; str} names ->
  if idid < 0 then
    {names with vars = IdentMap.add {idid;str} idid names.vars}
  else
    begin
      if IdentMap.mem {idid;str} names.vars then names
      else
        let nxtid = names.nxtid in
        {nxtid = nxtid+1 ; vars = IdentMap.add {idid;str} nxtid names.vars}
    end
let add_sigma : int -> string -> conf_names -> conf_names =
  fun idid str names ->
  if IdentMap.mem {idid;str} names.vars then names
  else
    let nxtid = names.nxtid in
    {nxtid = nxtid+1 ; vars = IdentMap.add {idid;str} nxtid names.vars}

(*******************************************
 * Getter Functions for the Identifier Map *
 *******************************************)
(******************************************
 * Default names for normalised variables *
 ******************************************)
let var_name = "$vn"
let abs_name = "$acn"
let sig_name = "$wn"
(*********************
 * GETTER FUNCTIONS  *
 *********************)
let get_mapped_s : string -> Ast.ident -> conf_names -> Ast.ident option =
  fun def_name {idid;str} names -> 
  match IdentMap.find_opt {idid;str=str} names.vars with
  | None -> None
  | Some id -> Some {idid=id;str=def_name}
let get_mapped_var : Ast.ident -> conf_names -> Ast.ident option =
  fun ident names ->
  get_mapped_s var_name ident names
let get_mapped_abs : Ast.ident -> conf_names -> Ast.ident option =
  fun abs names ->
  get_mapped_s abs_name abs names
let get_mapped_sig : Ast.ident -> conf_names -> Ast.ident option =
  fun ident names ->
  get_mapped_s sig_name ident names

(****************************************************************
 * Name Accumulator Functions to build the ID substitution maps *
 ****************************************************************)
(**************************
 * EXPRESSION ACCUMULATOR *
 **************************)
let rec names_of_exp : conf_names -> Ast.expression -> conf_names =
  fun acc exp -> 
  match exp with
  | ValExp    (v, p) -> names_of_val acc v
  | IdentExp  (id, p) -> acc
  | ArithExp  (op, es, p) -> List.fold_left names_of_exp acc es
  | AppExp    (e1, e2, p) -> names_of_exp (names_of_exp acc e1) e2
  | CondExp   (e1, e2, e3, p) ->
     names_of_exp (names_of_exp (names_of_exp acc e1) e2) e3
  (** VAR BINDER **)
  | LetExp    (i, it, e1, e2, p) ->
     let acc' = add_var i acc in
     names_of_exp (names_of_exp acc' e1) e2
  (** VAR BINDER **)
  | LetTuple  (is_ts, e1, e2, p) ->
     let acc' = List.fold_left (fun ns (i,it) -> add_var i ns) acc is_ts in
     names_of_exp (names_of_exp acc' e1) e2
  | SeqExp    (e1, e2, p) -> names_of_exp (names_of_exp acc e1) e2
  | TupleExp  (es, p) -> List.fold_left names_of_exp acc es
  | BotExp    p -> acc
  | TupleProjExp (e1,i,j,p) -> names_of_exp acc e1
  | TupleUpdExp (e1,i,j,e2,p) -> names_of_exp (names_of_exp acc e1) e2
(** TODO: found bug, fix in imperative tool **)
(**********************
 * VALUE ACCUMMULATOR *
 **********************)
and names_of_val : conf_names -> Ast.value -> conf_names =
  fun acc v ->
  match v with
  | ConstVal c -> acc
  | TupleVal vs -> List.fold_left names_of_val acc vs
  (** VAR BINDER **)    
  | FunVal (fid, ft, param, pt, e) ->
     let acc = add_var fid acc in
     let acc = add_var param acc in
     names_of_exp acc e
  (** ABS INSTANCE **)
  | AbsCon (idid, t, str) -> acc (* don't normalise opponent consts, only symbolic ones *)
  (** ABS INSTANCE **)
  | AbsFun  (i, t1, t2, s, ls) -> acc
(***********************
 * CONTEXT ACCUMULATOR *
 ***********************)
let rec names_of_cxt : conf_names -> Reductions_ast.eval_cxt -> conf_names =
  fun acc cxt ->
  match cxt with
  | [] -> acc
  | eframe :: rest ->
     let names_of_frame =
       begin
         match eframe with
         | ArithECxt (op, vs, es, p) ->
            List.fold_left names_of_exp
              (List.fold_left names_of_val acc vs) es
         | AppOpECxt (e2, p) -> names_of_exp acc e2
         | AppRandECxt (f, p) -> names_of_val acc f
         | CondECxt (e1, e2, p) -> names_of_exp (names_of_exp acc e1) e2
         | LetECxt (i, it, e2, p) -> names_of_exp (add_var i acc) e2
         | LetTupleECxt (is_ts, e2, p) ->
            let acc' = List.fold_left (fun ns (i,it) -> add_var i ns) acc is_ts in
            names_of_exp acc' e2
         | SeqECxt (e2,p) -> names_of_exp acc e2
         | TupleECxt (vs, es, p) ->
            List.fold_left names_of_exp 
              (List.fold_left names_of_val acc vs) es
         | TupleProjECxt (i,j,p) -> acc
         | TupleFstUpdECxt (i, j, e2, p) -> names_of_exp acc e2
         | TupleSndUpdECxt (v1, i, j, p) -> names_of_val acc v1
       end
     in
     names_of_cxt names_of_frame rest
(********************
 * PROP ACCUMULATOR *
 ********************)
let rec names_of_prop : conf_names -> Z3api.prop -> conf_names =
  fun acc prop ->
  let add_abs_of_string str =
    match String.split_on_char '_' str with
    | [s;i] -> add_sigma (int_of_string i) s acc
    | _ -> failwith (Printf.sprintf "names_of_prop: invalid format <%s>" str)
  in
  match prop with
  | IntProp _ -> acc
  | BoolProp _ -> acc
  | VarIntProp s -> add_abs_of_string s
  | VarBoolProp s -> add_abs_of_string s
  | AndProp ps -> List.fold_left names_of_prop acc ps
  | OrProp  ps -> List.fold_left names_of_prop acc ps
  | NotProp p  -> names_of_prop acc p
  | EqProp  (p1,p2) -> names_of_prop (names_of_prop acc p1) p2
  | IteProp (p1,p2,p3) -> names_of_prop (names_of_prop (names_of_prop acc p1) p2) p3
  | ImpliesProp (p1,p2) -> names_of_prop (names_of_prop acc p1) p2
  | LtProp (p1,p2) -> names_of_prop (names_of_prop acc p1) p2
  | LeProp (p1,p2) -> names_of_prop (names_of_prop acc p1) p2
  | GtProp (p1,p2) -> names_of_prop (names_of_prop acc p1) p2
  | GeProp (p1,p2) -> names_of_prop (names_of_prop acc p1) p2
  | AddProp ps -> List.fold_left names_of_prop acc ps
  | MulProp ps -> List.fold_left names_of_prop acc ps
  | SubProp ps -> List.fold_left names_of_prop acc ps
  | DivProp (p1,p2) -> names_of_prop (names_of_prop acc p1) p2
  | ModProp (p1,p2) -> names_of_prop (names_of_prop acc p1) p2
  | UminusProp p -> names_of_prop acc p
(*********************
 * SIGMA ACCUMULATOR *
 *********************)
let names_of_sigma : conf_names -> Z3api.sigma -> conf_names =
  fun acc sigma ->
  let aux : conf_names -> Z3api.sigma_prop -> conf_names =
    fun acc sigma_prop ->
    match sigma_prop with
    | TopIntVarConstNeq ((id1 , str1) , int2) -> add_sigma id1 str1 acc
    | TopBoolVarConstNeq ((id1 , str1) , bool2) -> add_sigma id1 str1 acc
    | TopIntVarNeq ((id1 , str1) , (id2 , str2)) -> add_sigma id2 str2 (add_sigma id1 str1 acc)
    | TopBoolVarNeq ((id1 , str1) , (id2 , str2)) -> add_sigma id2 str2 (add_sigma id1 str1 acc)
    | TopIntEq (id , prop) -> add_sigma id Z3api.default_sname (names_of_prop acc prop)
    | TopBoolEq (id , prop) -> add_sigma id Z3api.default_sname (names_of_prop acc prop)
    | TopBoolVar (id , str) -> add_sigma id str acc
    | TopNotBoolVar (id , str) -> add_sigma id str acc
  in
  List.fold_left aux acc sigma
(******************************
 * CEK EXPRESSION ACCUMULATOR *
 ******************************)
let names_of_cek_exp : conf_names -> Reductions_ast.cek_exp -> conf_names =
  fun acc {ecxt;e} -> names_of_cxt (names_of_exp acc e) ecxt
(******************************
 * CFG EXPRESSION ACCUMULATOR *
 ******************************)
let names_of_cfg_exp : conf_names -> Lts_ast.cfg_exp -> conf_names =
  fun acc e ->
  match e with
  | PExp cek_exp -> names_of_cek_exp acc cek_exp
  | OExp vs -> List.fold_left names_of_val acc vs
(***********************
 * PRVALUE ACCUMULATOR *
 ***********************)
let rec names_of_prvalue : conf_names -> Lts_ast.prvalue -> conf_names =
  fun acc prv ->
  match prv with
  | PrIndex _  -> acc
  | PrConst c  -> names_of_val acc c
  | PrTuple ls -> List.fold_left names_of_prvalue acc ls
(*********************
 * LABEL ACCUMULATOR *
 *********************)
let rec names_of_label : conf_names -> Lts_ast.label -> conf_names =
  fun acc label ->
  match label with
  | OpApp (prv,v) -> names_of_val (names_of_prvalue acc prv) v
  | PrApp (v,prv) -> names_of_prvalue (names_of_val acc v) prv
  | OpRet v   -> names_of_val acc v
  | PrRet prv -> names_of_prvalue acc prv
  | Mark  _   -> acc
(********************
 * TRACE ACCMULATOR *
 ********************)
let rec names_of_trace : conf_names -> Lts_ast.Trace.t -> conf_names =
  fun acc trace ->
  List.fold_left names_of_label acc trace
(*********************
 * M_Map ACCUMULATOR *
 *********************)
let names_of_m_map : conf_names -> Lts_ast.label Lts_ast.M_Map.t -> conf_names =
  fun acc m_map ->
  M_Map.fold (fun t l acc -> names_of_label (names_of_trace acc t) l) m_map acc
(**************************
 * ECXT_FRAME ACCUMULATOR *
 **************************)
let names_of_ecxt_frame : conf_names -> Lts_ast.ecxt_frame -> conf_names =
  fun acc (ecxt,_,t) ->
  names_of_cxt (names_of_trace acc t) ecxt
(*********************
 * STACK ACCUMULATOR *
 *********************)
let names_of_k : conf_names -> ecxt_frame list -> conf_names =
  fun acc k ->
  List.fold_left names_of_ecxt_frame acc k
(************************
 * MINI_CFG ACCUMULATOR *
 ************************)
let names_of_mini_cfg : conf_names -> Lts_ast.mini_cfg -> conf_names =
  fun acc {exp;k;t} ->
  names_of_trace (names_of_k (names_of_cfg_exp acc exp) k) t
(*****************************
 * MINI_CFG_PAIR ACCUMULATOR *
 *****************************)
let names_of_mini_cfg_pair : conf_names -> Lts_ast.mini_cfg_pair -> conf_names =
  fun acc {c1;c2;sigma} ->
  names_of_sigma (names_of_mini_cfg (names_of_mini_cfg acc c1) c2) sigma


(***************************
 * Normalisation Functions *
 ***************************)
(*************************
 * NORMALISE EXP AND VAL *
 *************************)
let rec normalise_exp : conf_names -> Ast.expression -> Ast.expression =
  fun names exp ->
  let helper x = normalise_exp names x in
  let id_get x =
    match get_mapped_var x names with
    | None ->
       failwith (Printf.sprintf "normalise_exp: id <%s> not found" (Ast.string_of_id x))
    | Some id -> id
  in
  match exp with
  | ValExp    (v, p) -> ValExp (normalise_val names v, p)
  | IdentExp  (id, p) -> IdentExp (id_get id, p)
  | ArithExp  (op, es, p) -> ArithExp (op, List.map helper es, p)
  | AppExp    (e1, e2, p) -> AppExp (helper e1, helper e2, p)
  | CondExp   (e1, e2, e3, p) -> CondExp (helper e1, helper e2, helper e3, p)
  | LetExp    (i, it, e1, e2, p) -> LetExp (id_get i, it, helper e1, helper e2, p)
  | LetTuple  (is_ts, e1, e2, p) ->
     LetTuple (List.map (fun(a,b)->(id_get a,b)) is_ts, helper e1, helper e2, p)
  | SeqExp    (e1, e2, p) -> SeqExp (helper e1, helper e2, p)
  | TupleExp  (es, p) -> TupleExp (List.map helper es, p)
  | BotExp    p -> BotExp p
  | TupleProjExp (e1, i, j, p) -> TupleProjExp (helper e1, i, j, p)
  | TupleUpdExp  (e1, i, j, e2, p) -> TupleUpdExp  (helper e1, i, j, helper e2, p)
  and
normalise_val : conf_names -> Ast.value -> Ast.value =
  fun names v ->
  let helper x = normalise_val names x in
  let id_get x =
    match get_mapped_var x names with
    | None ->
       failwith (Printf.sprintf "normalise_val: id <%s> not found" (Ast.string_of_id x))
    | Some id -> id
  in
  let sigma_get x f =
    match get_mapped_sig x names with
    | None ->
       begin
         match get_mapped_abs x names with (** TODO: get abs or get sig?? **)
         | None -> f x (* TODO: I think this is correct ?? *)
         | Some id -> f id
       end
    | Some id -> f id
  in
  match v with
  | ConstVal c -> ConstVal c
  | TupleVal vs -> TupleVal (List.map helper vs)
  | FunVal (fid, ft, param, pt, e) ->
     FunVal (id_get fid, ft, id_get param, pt, normalise_exp names e)
  | AbsCon (i, t, s) -> sigma_get {idid=i;str=s} (fun {idid;str} -> Ast.AbsCon (idid, t, str))
  | AbsFun _ -> v (**TODO: check if we want to normalise names**)
(*****************
 * NORMALISE CXT *
 *****************)
let normalise_cxt : conf_names -> Reductions_ast.eval_cxt -> Reductions_ast.eval_cxt =
  fun names cxt ->
  let id_get x =
    match get_mapped_var x names with
    | None ->
       failwith (Printf.sprintf "normalise_cxt: id <%s> not found" (Ast.string_of_id x))
    | Some id -> id
  in
  let val_normalise x = normalise_val names x in
  let exp_normalise x = normalise_exp names x in
  let current_frame_locs : Reductions_ast.eval_frame -> Reductions_ast.eval_frame =
    fun eframe ->
    begin
      match eframe with
      | ArithECxt (op, vs, es, p) -> ArithECxt (op,
                                             List.map val_normalise vs,
                                             List.map exp_normalise es, p)
      | AppOpECxt (e2, p) -> AppOpECxt (exp_normalise e2, p)
      | AppRandECxt (f, p) -> AppRandECxt (val_normalise f, p)
      | CondECxt (e1, e2, p) -> CondECxt (exp_normalise e1, exp_normalise e2, p)
      | LetECxt (i, it, e2, p) -> LetECxt (id_get i, it, exp_normalise e2, p)
      | LetTupleECxt (is_ts, e2, p) -> LetTupleECxt (List.map (fun(a,b)->id_get a,b) is_ts, e2, p)
      | SeqECxt (e2,p) -> SeqECxt (exp_normalise e2,p)
      | TupleECxt (vs, es, p) -> TupleECxt (List.map val_normalise vs, List.map exp_normalise es, p)
      | TupleProjECxt (i,j,p) -> TupleProjECxt (i,j,p)
      | TupleFstUpdECxt (i,j,e2,p) -> TupleFstUpdECxt (i,j, exp_normalise e2,p)
      | TupleSndUpdECxt (v1,i,j,p) -> TupleSndUpdECxt (val_normalise v1,i,j,p)
    end
  in
  List.map current_frame_locs cxt  
(*********************
 * NORMALISE CEK_EXP *
 *********************)
let normalise_cek_exp : conf_names -> Reductions_ast.cek_exp -> Reductions_ast.cek_exp =
  fun names {ecxt;e} -> {ecxt = normalise_cxt names ecxt; e = normalise_exp names e}
(*********************
 * NORMALISE CFG_EXP *
 *********************)
let normalise_cfg_exp : conf_names -> Lts_ast.cfg_exp -> Lts_ast.cfg_exp =
  fun names cfg_exp ->
  match cfg_exp with
  | PExp cek_exp -> PExp (normalise_cek_exp names cek_exp)
  | OExp vs      -> OExp (List.map (normalise_val names) vs)
(******************
 * NORMALISE PROP *
 ******************)
let rec normalise_prop : conf_names -> Z3api.prop -> Z3api.prop =
  fun names prop ->
  let sigma_get str id =
    let idid = int_of_string id in
    let ident = {Ast.idid;str} in
    match get_mapped_sig ident names with
    | None ->
       failwith (Printf.sprintf "normalise_val: id <%s> not found" (Ast.string_of_id ident))
    | Some {Ast.idid;str} -> idid
  in
  let update_id_on_w s =
    match String.split_on_char '_' s with
    | [str;id] -> Printf.sprintf "%s_%d" str (sigma_get str id)
    | _ -> failwith "normalise_prop: invalid symbol format"
  in
  let helper x = normalise_prop names x in
  match prop with
  | IntProp _ -> prop
  | BoolProp _ -> prop
  | VarIntProp s -> VarIntProp (update_id_on_w s)
  | VarBoolProp s -> VarBoolProp (update_id_on_w s)
  | AndProp ps -> AndProp (List.map helper ps)
  | OrProp  ps -> OrProp (List.map helper ps)
  | NotProp p  -> NotProp (helper p)
  | EqProp  (p1,p2) -> EqProp (helper p1, helper p2)
  | IteProp (p1,p2,p3) -> IteProp (helper p1, helper p2, helper p3)
  | ImpliesProp (p1,p2) -> ImpliesProp (helper p1, helper p2)
  | LtProp (p1,p2) -> LtProp (helper p1, helper p2)
  | LeProp (p1,p2) -> LeProp (helper p1, helper p2)
  | GtProp (p1,p2) -> GtProp (helper p1, helper p2)
  | GeProp (p1,p2) -> GeProp (helper p1, helper p2)
  | AddProp ps -> AddProp (List.map helper ps)
  | MulProp ps -> MulProp (List.map helper ps)
  | SubProp ps -> SubProp (List.map helper ps)
  | DivProp (p1,p2) -> DivProp (helper p1, helper p2)
  | ModProp (p1,p2) -> ModProp (helper p1, helper p2)
  | UminusProp p -> UminusProp (helper p)
(*******************
 * NORMALISE SIGMA *
 *******************)
let normalise_sigma : conf_names -> Z3api.sigma -> Z3api.sigma =
  fun names sigma ->
  let aux : Z3api.sigma_prop -> Z3api.sigma_prop =
    fun sigma_prop ->
    let abs_get x =
      match get_mapped_sig x names with
      | None ->
         failwith (Printf.sprintf "normalise_val: id <%s> not found" (Ast.string_of_id x))
      | Some {Ast.idid;str} -> idid
    in
    let norm_prop x = normalise_prop names x in
    match sigma_prop with
    | TopIntVarConstNeq ((id1 , str1) , int2) ->
       let new_id = abs_get {idid=id1;str=str1} in
       TopIntVarConstNeq ((new_id , str1) , int2)
    | TopBoolVarConstNeq ((id1 , str1) , bool2) ->
       let new_id = abs_get {idid=id1;str=str1} in
       TopBoolVarConstNeq ((new_id , str1) , bool2)
    | TopIntVarNeq ((id1 , str1) , (id2 , str2)) ->
       let new_id1 = abs_get {idid=id1;str=str1} in
       let new_id2 = abs_get {idid=id2;str=str2} in
       TopIntVarNeq ((new_id1 , str1) , (new_id2 , str2))
    | TopBoolVarNeq ((id1 , str1) , (id2 , str2)) ->
       let new_id1 = abs_get {idid=id1;str=str1} in
       let new_id2 = abs_get {idid=id2;str=str2} in
       TopBoolVarNeq ((new_id1 , str1) , (new_id2 , str2))
    | TopIntEq (id , prop) ->
       let new_id = abs_get {idid=id;str=Z3api.default_sname} in
       TopIntEq (new_id , norm_prop prop)
    | TopBoolEq (id , prop) ->
       let new_id = abs_get {idid=id;str=Z3api.default_sname} in
       TopBoolEq (new_id , norm_prop prop)
    | TopBoolVar (id , str) ->
       let new_id = abs_get {idid=id;str=str} in
       TopBoolVar (new_id , str)
    | TopNotBoolVar (id , str) ->
       let new_id = abs_get {idid=id;str=str} in
       TopNotBoolVar (new_id , str)
  in
  List.map aux sigma
(***************************************
 * NORMALISE PRVALUE, LABEL AND TRACES *
 ***************************************)
let rec normalise_prvalue : conf_names -> Lts_ast.prvalue -> Lts_ast.prvalue =
  fun names prv ->
  match prv with
  | PrIndex _ -> prv
  | PrConst v -> PrConst (normalise_val names v)
  | PrTuple vs -> PrTuple (List.map (normalise_prvalue names) vs)
let normalise_label : conf_names -> Lts_ast.label -> Lts_ast.label =
  fun names label ->
  match label with
  | OpApp (prv,v) -> OpApp (normalise_prvalue names prv, normalise_val names v)
  | PrApp (v,prv) -> PrApp (normalise_val names v, normalise_prvalue names prv)
  | OpRet v   -> OpRet (normalise_val names v)
  | PrRet prv -> PrRet (normalise_prvalue names prv)
  | Mark  _ -> label
let normalise_trace : conf_names -> Lts_ast.Trace.t -> Lts_ast.Trace.t =
  fun names trace -> List.map (normalise_label names) trace
(************************
 * NORMALISE ECXT_FRAME *
 ************************)
let normalise_ecxt_frame : conf_names -> Lts_ast.ecxt_frame -> Lts_ast.ecxt_frame =
  fun names (ecxt,typ,t) ->
  let new_ecxt = normalise_cxt names ecxt in
  let new_t = normalise_trace names t in
  (new_ecxt,typ,new_t)
(**********************
 * NORMALISE MINI_CFG *
 **********************)
let normalise_mini_cfg : conf_names -> Lts_ast.mini_cfg -> Lts_ast.mini_cfg =
  fun names {exp;k;t} ->
  let new_exp = normalise_cfg_exp names exp in
  let new_k = List.map (normalise_ecxt_frame names) k in
  let new_t = normalise_trace names t in
  {exp=new_exp;k=new_k;t=new_t}
(***************************
 * NORMALISE MINI_CFG_PAIR *
 ***************************)
let normalise_mini_cfg_pair : conf_names -> Lts_ast.mini_cfg_pair -> Lts_ast.mini_cfg_pair =
  fun names {c1;c2;sigma} ->
  let new_c1 = normalise_mini_cfg names c1 in
  let new_c2 = normalise_mini_cfg names c2 in
  let new_sig = normalise_sigma names sigma in
  {c1=new_c1;c2=new_c2;sigma=new_sig}

(*********************
 * TOPLEVEL FUNCTION *
 *********************)
let normalise : Lts_ast.mini_cfg_pair -> Lts_ast.mini_cfg_pair =
  fun cfg_pair ->
  let names = names_of_mini_cfg_pair empty_conf_names cfg_pair in
  normalise_mini_cfg_pair names cfg_pair


(**TODO: names of M and normalise M **)
(**TODO: add flags to print normalised confgs **)
