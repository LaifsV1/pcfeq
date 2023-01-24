open Ast                 (* Term Abstract Syntax Tree *)
open Reductions_ast
open Reductions          (* Term Semantics Reduction Rules *)
open Z3api               (* Z3 Interface to for symbolic execution *)

(****************************************
 * proponent values used for LTS labels *
 ****************************************)
type prindex = int
let inc_prindex id = id+1
type prvalue = PrIndex of prindex | PrConst of value | PrTuple of prvalue list
let rec string_of_prvalue = function
  | PrIndex id -> Printf.sprintf "idx_%d" id
  | PrConst v  -> string_of_val v
  | PrTuple vs -> Printf.sprintf "(%s)" (String.concat "," (List.map string_of_prvalue vs))

(* creates prvalues from val and accumulates all functions found *)
let prvalue_of_value : value -> prvalue * (value list) = fun v ->
  let rec prvalue_aux v idx funs =
    match v with
    | ConstVal _  -> PrConst v   , idx             , funs
    | FunVal   _  -> PrIndex idx , inc_prindex idx , ((idx,v) :: funs)
    | AbsCon   _  -> PrConst v   , idx             , funs
    | AbsFun   _  -> PrIndex idx , inc_prindex idx , ((idx,v) :: funs)
    | TupleVal ls ->
       let ts , new_idx , new_funs =
         List.fold_left
           (fun (vs,idx,fs) v ->
             let new_v , new_idx , new_fs = prvalue_aux v idx fs in
             (new_v::vs , new_idx , new_fs)) ([],idx,funs) ls
       in
       PrTuple (List.rev ts) , new_idx , new_funs
  in
  let new_prvalue , new_a , new_funs = prvalue_aux v 0 [] in
  (** NOTE: prvalue_aux does in-order traversal and returns funs in reverse.
      Fold_left at the end to reverse and remove the index.
      new_funs list should be in sync with prindex, in descending order. **)
  let final_funs , final_a =
    (List.fold_left
       (fun (acc,prev_id) (id,v) ->
         (* invariant: prvalue_aux generates funs in reverse order,
            always synced with PrIndex generation; so prev_id = current id incremented *)
         assert(prev_id = inc_prindex id);
         (v::acc,id)) ([],new_a) new_funs)
  in
  (* assert last element is indeed 0; i.e. the first prindex created *)
  assert(final_a = 0) ;
  (new_prvalue , final_funs)

(* list of variables - as strings - in prvalue *)
let cons_option x ls =
  match x with 
  | None -> ls
  | Some x -> x :: ls
let name_of_abscon = function
  | AbsCon (i, t, s) -> Some (string_of_abs i s)
  | _ -> None
let rec vars_in_prvalue acc = function
  | PrIndex _ -> acc
  | PrConst v -> cons_option (name_of_abscon v) acc
  | PrTuple ls ->
     List.fold_left (fun acc v -> vars_in_prvalue acc v) acc ls

(*************************
 * LTS TRANSITION LABELS *
 *************************)
type label =
  | OpApp  of prvalue * value  (* gamma idx * AbsCon/Fun * val *)
  | PrApp  of value * prvalue  (* AbsFun * value *)
  | OpRet  of value            (* AbsCon or AbsFun or Tuple of AbsFun/AbsCon *)
  | PrRet  of prvalue          (* ConstVal or AbsCon or AbsFun *)
  | Mark   of string           (* Used to Mark the trace *)
let string_of_label = function
  | OpApp (pr,v) -> Printf.sprintf "op_app %s %s" (string_of_prvalue pr) (string_of_val v)
  | PrApp (v,pr) -> Printf.sprintf "pr_app %s %s" (string_of_val v) (string_of_prvalue pr)
  | OpRet v      -> Printf.sprintf "op_ret %s" (string_of_val v)
  | PrRet pr     -> Printf.sprintf "pr_ret %s" (string_of_prvalue pr)
  | Mark  s      -> Printf.sprintf "<%s>" s
let bottom_label        = Mark "DIVERGES"
let bound_reached_label = Mark "BOUND EXCEEDED"
module Label = struct
  type t = label
  let compare l1 l2 = compare l1 l2 
end
module Trace = struct
  type t = label list
  let compare l1 l2 = compare l1 l2 
end
let string_of_trace t =
  let t = List.rev t in
  Printf.sprintf "%s" (String.concat "\n" (List.map string_of_label t))

(* list of variables - as strings - in label and trace *)
let vars_in_label acc = function
  | OpApp (prv , v) -> cons_option (name_of_abscon v) (vars_in_prvalue acc prv)
  | PrApp (v , prv) -> cons_option (name_of_abscon v) (vars_in_prvalue acc prv)
  | OpRet v         -> cons_option (name_of_abscon v) acc
  | PrRet prv       -> (vars_in_prvalue acc prv)
  | Mark _          -> acc
let vars_in_trace acc t =
  List.fold_left (fun acc label -> vars_in_label acc label) acc t
    
(* checks of prvalues are equivalent under a sigma by calling Z3 *)
let rec prvalues_equivalent sigma p1 p2 =
  if p1 = p2 then true
  else
    match p1 , p2 with
    | PrConst (AbsCon (id1,typ1,name1)) ,
      PrConst (AbsCon (id2,typ2,name2)) ->
       let p1_neq_p2_sigma = 
         match typ1,typ2 with
         | Type.BoolT,Type.BoolT -> sigma_add_bvar_neq (id1,name1) (id2,name2) sigma
         | Type.IntT ,Type.IntT  -> sigma_add_ivar_neq (id1,name1) (id2,name2) sigma
         | t1,t2 ->
            (** NOTE: T1 =/= T2 should not happen **)
            (assert(t1=t2);
             print_endline (string_of_prvalue p1);
             print_endline (string_of_prvalue p2);
             failwith "<prvalues_equivalent>: only bool/int allowed")
       in
       not(check_sat_sigma p1_neq_p2_sigma)
    | PrConst (AbsCon (id,typ,name)) , PrConst (ConstVal v)
      | PrConst (ConstVal v) , PrConst (AbsCon (id,typ,name)) ->
       let p1_neq_p2_sigma = 
         match v with
         | IntConst i ->
            (** NOTE: T1 =/= T2 should not happen **)
            (assert(typ = Type.IntT);
             sigma_add_iconst_neq (id,name) i sigma)
         | BoolConst b ->
            (** NOTE: T1 =/= T2 should not happen **)
            (assert(typ = Type.BoolT);
             sigma_add_bconst_neq (id,name) b sigma)
         | _ -> failwith "<prvalues_equivalent>: only bool/int allowed"
       in
       not(check_sat_sigma p1_neq_p2_sigma)
    | PrTuple l1 , PrTuple l2 ->
       let rec list_equal l1 l2 =
         match l1 , l2 with
         | [] , [] -> true
         | x :: xs , y :: ys ->
            if prvalues_equivalent sigma x y
            then list_equal xs ys
            else false
         | _ -> false
       in
       list_equal l1 l2
    | _ -> false

let labels_equivalent l1 l2 sigma =
  match l1 , l2 with
  | OpApp _ , OpApp _ -> l1 = l2
  | OpRet _ , OpRet _ -> l1 = l2
  | PrApp (AbsFun (a1, _, _, _, _), p1) ,
    PrApp (AbsFun (a2, _, _, _, _), p2) ->
     (** TODO: is U needed for equivalence?? **)
     if a1 = a2 then prvalues_equivalent sigma p1 p2 else false
  | PrRet p1 , PrRet p2 -> prvalues_equivalent sigma p1 p2
  | _ -> false

(**********************
 * EVALUATION CONTEXT *
 **********************)
type ecxt_frame = eval_cxt * Type.t * Trace.t

let string_of_ecxt_frame (ecxt,typ,trace) =
  Printf.sprintf "(%s , %s , %s)"
    (string_of_ecxt ecxt)
    (Type.string_of_t typ)
    (string_of_trace trace)

let string_of_k k =
  (String.concat "::" (List.map string_of_ecxt_frame k))

(*******************
 * OPPONENT VALUES *
 *******************)
(** NOTE: current alpha is the ID **)
type alpha = int
let inc_alpha a = a+1
let id_of_alpha a = a , inc_alpha a 

let rec opval_of_type : Type.t -> alpha -> value * alpha =
  fun t a ->
  match t with
  | Type.UnitT -> ConstVal UnitConst , a
  | BoolT | IntT ->
     let new_id , new_a = id_of_alpha a in
     AbsCon (new_id , t, Ast.default_acname) , new_a
  | Type.FunT (args,ret_type) ->
     begin
       match args with
       | arg_type::[] ->
          (** TODO: implement name reuse **)
          let new_id , new_a = id_of_alpha a in
          AbsFun (new_id, arg_type, ret_type, Ast.default_afname, []) , new_a
       | _ -> failwith "<opval_of_type>: unexpected FunT arg type."
     end
  | TupleT ls ->
     let new_ls , new_a =
       (** TODO: fold_right or fold_left ?? **)
       List.fold_left
         (fun (vs,a) t ->
           let new_v,new_a = opval_of_type t a in
           new_v::vs,new_a) ([],a) ls
     in
     TupleVal (List.rev new_ls) , new_a
  | VarT _ -> failwith "<opval_of_type>: only closed types at LTS; VarT not possible."

let rec opval_add_us us v =
  match v with
  | AbsFun (id,t1,t2,s,_) -> AbsFun (id,t1,t2,s,us)
  | TupleVal vs -> TupleVal (List.map (opval_add_us us) vs)
  | _ -> v

let rec opval_remove_us v =
  match v with
  | AbsFun (id,t1,t2,s,_) -> AbsFun (id,t1,t2,s,[])
  | TupleVal vs -> TupleVal (List.map opval_remove_us vs)
  | _ -> v

(*****************************************************
 * CALL-CACHING MAP + STACK-BASED DIVERGENCE FINDING *
 *****************************************************)
(* NOTE:
 * Q: should this be global?
 * A: has to be per path since differnt paths have different op choices
 * Q: do we need a stack?
 * A: we can use the trace for PrApp, but not for OpApp.
 *    also, it may be slow to traverse the trace each time.
 * Q: do we need to update M on skipped calls?
 * A: maybe not? cuz we didn't do the move?
 *)
let callskip_label = Mark "call skipped via caching"
let loopfound_label = Mark "loop found in stack"

module LabelMap = Map.Make(Label)
type callcache = { ccache : label LabelMap.t ;
                   cstack : label list }
let empty_cc = { ccache = LabelMap.empty ; cstack = [] }
let cc_push : callcache -> label -> callcache * bool =
  fun cc app_l ->
  (** NOTE: loop finding operational technique **)
  let loop_found = List.mem app_l cc.cstack in
  {cc with cstack = app_l::cc.cstack} , loop_found
let cc_pop : callcache -> label -> callcache =
  fun cc ret_l ->
  match cc.cstack with
  | [] -> failwith "<cc_pop>: empty stack"
  | app_l :: xs -> {ccache = LabelMap.add app_l ret_l cc.ccache ; cstack = xs}
let cc_find : callcache -> label -> label option =
  fun cc app_l ->
  LabelMap.find_opt app_l cc.ccache

(******************
 * CONFIGURATIONS *
 ******************)
module M_Map = Map.Make(Trace) (* we need to decide on a type for M *)
type pr_questions = label list
type stuck_data = Stuck of (label * pr_questions * Trace.t) | Bottom of Trace.t | NotStuck
type cfg_exp = PExp of cek_exp | OExp of (value list)
type cfg_side = Left | Right
type cfg =
  {
    exp : cfg_exp ;            (* either PExp or OExp. Check this if pr/op *)
    k   : ecxt_frame list ;    (* evaluation stack *)
    v   : (value list) list ;  (* vs stack *)
    t   : Trace.t ;            (* should this be in the pair? *)
    q   : pr_questions ;       (* list of questions the proponent has made *)
    sd  : stuck_data ;         (* if stuck, then Some (label,q) *)
    cc  : callcache ;          (* memoisation cache to skip calls *)
    ft  : Trace.t              (* full trace *)
  }
type cfg_env =                 (* environment needed to run cfg Pair *)
  {
    a : alpha ;                (* if M(trace) = null, sequentially gen alpha *)
    m : label M_Map.t ;        (* m : trans list -> trans option *)
    sigma : sigma ;            (* symbolic environment *)
    bound : int ;
    side  : cfg_side           (* Left or Right for c1 or c2 being evaluated *)
  }
type cfg_pair =
  {
    c1    : cfg ;
    c2    : cfg ;
    env   : cfg_env
  }
let mk_cfg e =
  {
    exp = PExp {ecxt = []; e = e} ;
    k   = [] ;
    v   = [] ;
    t   = [] ;
    q   = [] ;
    sd  = NotStuck ;
    cc  = empty_cc ; 
    ft  = []
  }
let mk_cfg_pair e1 e2 bound =
  {
    c1  = mk_cfg e1;
    c2  = mk_cfg e2;
    env =
      {
        a  = 0;
        m  = M_Map.empty;
        sigma = [];
        bound = bound ;
        side  = Left
      }
  }
let swap_side = function Left -> Right | Right -> Left
let m_get m trace = M_Map.find_opt trace m
let m_update m trace label = M_Map.add trace label m

let string_of_side = function
  | Left  -> "LHS"
  | Right -> "RHS"
let string_of_cfg_exp = function
  | PExp e ->
     Printf.sprintf "PExp %s"
       (string_of_cek_exp e)
  | OExp vs ->
     Printf.sprintf "OExp [%s]"
       (String.concat " ; " (List.map string_of_val vs))
let string_of_stuck_data = function
  | NotStuck -> "."
  | Stuck  _ -> "=STUCK-CONF=" (** TODO **)
  | Bottom _ -> "=BOTTOM-CONF=" (** TODO **)
let string_of_cfg {exp ; k ; t ; q ; sd ; ft} =
  Printf.sprintf "{\nexp = %s;\n k = %s;\n t =\n%s; ... ;\n sd = %s;\n ft =\n%s\n}"
    (string_of_cfg_exp exp)
    (string_of_k k)
    (string_of_trace t)
    (string_of_stuck_data sd)
    (string_of_trace ft)
let string_of_env {a;m;sigma;bound;side} =
  Printf.sprintf "{a = %d ; m = ...;\nsigma = %s ;\nbound = %d ;\nside = %s}"
    a
    (string_of_sigma sigma)
    bound
    (string_of_side side)
let string_of_cfg_pair {c1;c2;env} =
  Printf.sprintf "{c1 =\n%s;\nc2 =\n%s;\nenv = %s}"
    (string_of_cfg c1)
    (string_of_cfg c2)
    (string_of_env env)

(***********************************
 * FRONTIER AND ORDER OF TRAVERSAL *
 ***********************************)
type traversal = BFS | DFS | REV
type frontier = cfg_pair list

let add_pending_cfg traversal cfg_pair frontier =
  match traversal with
  | BFS -> List.rev_append (List.rev frontier) [cfg_pair]
  | DFS -> cfg_pair :: frontier
  | REV -> List.rev_append frontier [cfg_pair]
let add_pending_cfgs traversal cfgs frontier =
  List.fold_left
    (fun rest cfg_pair -> add_pending_cfg traversal cfg_pair rest) frontier cfgs
let frontier_length frontier = List.length frontier

(*********************************
 * MINIMISED CFG FOR MEMOISATION *
 *********************************)
(** TODO: MAYBE DO MEMOISATION PER TRACE INSTEAD OF GLOBALLY **)
(** NOTE: not remembering M is probably unsound, but rarely triggers **)
type mini_cfg =
  {
    exp : cfg_exp ;
    k   : ecxt_frame list ;
    t   : Trace.t
  }
type mini_cfg_pair =
  {
    c1    : mini_cfg ;
    c2    : mini_cfg ;
    sigma : sigma
  }
let dummy_cfg =
  {
    exp = OExp [] ;
    k   = [] ;
    t   = []
  }
let dummy_cfg_pair =
  {
    c1    = dummy_cfg ;
    c2    = dummy_cfg ;
    sigma = []
  }
let minimise_cfg_pair {c1={exp=e1;k=k1;t=t1}; c2={exp=e2;k=k2;t=t2}; env={sigma}} =
  {c1={exp=e1;k=k1;t=t1}; c2={exp=e2;k=k2;t=t2}; sigma}
let string_of_mini_cfg : mini_cfg -> string =
  fun {exp;k;t} ->
  Printf.sprintf "{\nexp = %s;\n k = %s;\n t =\n%s\n}"
    (string_of_cfg_exp exp)
    (string_of_k k)
    (string_of_trace t)
let string_of_mini_cfg_pair : mini_cfg_pair -> string =
  fun {c1;c2;sigma} ->
  Printf.sprintf "{c1 =\n%s;\nc2 =\n%s;\nsigma = %s}"
    (string_of_mini_cfg c1)
    (string_of_mini_cfg c2)
    (string_of_sigma sigma)

let init_memo n = Memoisation.make_bounded_set n dummy_cfg_pair

let empty_memo = Memoisation.make_bounded_set 0 dummy_cfg_pair

