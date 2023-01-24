(* LTS USING IMMUTABLE LIST *)

open Ast                 (* Term Abstract Syntax Tree *)
open Reductions_ast
open Reductions          (* Term Semantics Reduction Rules *)
open Z3api               (* Z3 Interface to for symbolic execution *)
open Lts_ast             (* Data structures used by the LTS *)
open Normalisation

(* LTS EXPLORATION OVERVIEW:
 * Toplevel function `process_frontier` processes the whole frontier of cfg_pairs.
 * It recursively explores one side at a time by switching sides at each call.
 * It passes a cfg_pair to toplevel function `process_cfg`.
 * Depending on side and player for the corresponding cfg side, `process_cfg` passes
 * a single cfg, env and sd to the correct move selectors `do_pr_moves` and `do_op_moves`.
 * These pass the cfg, env and sd to the correct move function.
 *)

(**********************
 * FLAGS AND COUNTERS *
 **********************)

(** EXIT STATUS **)
let exit_eq = 43
let exit_ineq = 42
let exit_unknown = 0

(** UP-TO TECHNIQUE FLAGS **)
(* memoisation *)
let memo_size = ref 0
let memo = ref empty_memo
let do_norm = ref false
let do_cc = ref false

(** OUTPUT REPORTING FLAGS **)
let start_bound   = ref 6
let bound_reached = ref 0     (* number of traces that reached the bound *)
let end_reached   = ref 0     (* number of traces explored *)
let memo_reached  = ref 0     (* number of traces pruned by memoisation *)
let traversal     = ref BFS
let not_real_fail = ref false

let reset_flags () =
  bound_reached := 0 ;
  end_reached   := 0 ;
  not_real_fail := false

(** DEBUG PRINTING FLAGS **)
let debug_frontier_length_flag = ref false
let debug_frontier_length frontier =
  if !debug_frontier_length_flag then
    Printf.printf "[printing frontier length]: %d\n\n" (frontier_length frontier)

let debug_cfg_pair_flag = ref false
let debug_cfg_pair cfg_pair =
  if !debug_cfg_pair_flag then
    Printf.printf "[printing cfgs] CFG PAIR:\n%s\n\n"
      (string_of_cfg_pair cfg_pair)

let debug_traces_flag = ref false
let debug_traces trace env =
  if !debug_traces_flag then
    begin
      Printf.printf "[printing traces] %s TRACE:\n%s\n\n"
        (string_of_side env.side)
        (string_of_trace trace) ;
      (match env.sigma with
       | [] -> ()
       | sigma ->
          let vars = List.sort_uniq compare (vars_in_trace [] trace) in
          print_endline "Satisfying Assignment:" ;
          filter_print_asignments_list env.sigma vars ;
          print_endline "")
    end

let debug_normalisation_flag = ref false
let debug_normalisation cfg_pair =
  if !debug_normalisation_flag then
    Printf.printf "[printing normalised cfgs] NORMALISED CFG PAIR:\n%s\n\n"
      (string_of_mini_cfg_pair cfg_pair)

(** FLAG SETTER FUNCTIONS **)
let set_debug_flags (f,c,t,n) =
  debug_frontier_length_flag := f ; 
  debug_cfg_pair_flag := c ;
  debug_traces_flag   := t ;
  debug_normalisation_flag := n

let set_upto_flags (n,c) =
  do_norm := n ;
  do_cc   := c

let set_traversal do_dfs =
  if do_dfs then traversal := DFS

let mark_trace_end trace env =
  (* print trace information *)
  debug_traces trace env ;
  (* increment number of traces finished *)
  end_reached := !end_reached + 1

let mark_bound_reached trace env =
  (* add "bound reached" at the end of the trace *)
  let trace = bound_reached_label :: trace in
  (* increment number of traces bounded *)
  bound_reached := !bound_reached + 1;
  (* pritn trace end debug and increment traces finished *)
  mark_trace_end trace env

let mark_memo_reached () =
  memo_reached := !memo_reached + 1;
  end_reached := !end_reached + 1

(************
 * MESSAGES *
 ************)

(* prints message at end of bisim. either:
 * success with no bound reached; or
 * finished with some traces reaching the bound *)
let bisim_end_message () =
  let this_exit_status = ref 0 in
  let message =
    Printf.sprintf
      "Exploration Finished! No difference found between the terms with bound = %d. \n%s"
      !start_bound
      (if !bound_reached = 0
       then
         (this_exit_status := exit_eq;
          Printf.sprintf
            "The bound was not exceeded in %d traces - the terms are equivalent!"
            !end_reached)
       else
         (this_exit_status := exit_unknown;
          Printf.sprintf
            "However, the bound was exceeded in %d of %d traces - the terms may be inequivalent."
            !bound_reached
            !end_reached))
  in
  print_endline message;
  Printf.printf "%d traces were pruned by memoisation\n" !memo_reached;
  exit !this_exit_status

(* label: move that was not matched
 * t1: full trace of cfg that failed to match
 * t2: full trace of other cfg
 * env: environment components of pair
 * move_mismatch: boolean, true if moves mismatched
 *)
type fail_reason = LabelMismatch of label | PrCallsMismatch | ExpectedBottom
let bisim_fail_message received_label t1 t2 env fail_reason =
  print_endline "Bisimulation failed! Terms are not equivalent!";
  Printf.printf "%d traces explored. %d traces pruned by memoisation.\n"
    !end_reached !memo_reached ;
  begin
    match fail_reason with
    | LabelMismatch expected_label -> 
       Printf.printf "%s failed to match move <%s> and played <%s> instead\n\n"
         (string_of_side env.side)
         (string_of_label expected_label)
         (string_of_label received_label)
    | PrCallsMismatch -> 
       Printf.printf "%s failed to match all proponent calls on %s\n\n"
         (string_of_side env.side)
         (string_of_side (swap_side env.side))
    | ExpectedBottom ->
       Printf.printf "%s attempted to play <%s> but %s is a bottom configuration\n\n"
         (string_of_side env.side)
         (string_of_label received_label)
         (string_of_side (swap_side env.side))
  end ;
  (match env.side with
   | Left ->
      Printf.printf "LHS trace:\n%s\n\n" (string_of_trace t1) ;
      Printf.printf "RHS trace:\n%s\n"   (string_of_trace t2)
   | Right ->
      Printf.printf "LHS trace:\n%s\n\n" (string_of_trace t2) ;
      Printf.printf "RHS trace:\n%s\n"   (string_of_trace t1)) ;
  (match env.sigma with
   | [] -> ()
   | sigma ->
      let vars = List.sort_uniq compare (vars_in_trace (vars_in_trace [] t1) t2) in
      Printf.printf "\nSatisfying Assignment: \n" ;
      filter_print_asignments_map env.sigma vars) ;
  exit exit_ineq

(** TODO: recursive types? **)
(** TODO: flag for cc **)
(** TODO: cc functions that use the flag? **)
(** TODO: flag for loop finding **)

(*****************************
 * LTS PROPONENT TRANSITIONS *
 *****************************)

(* PROP TAU: transitive closure of tau reductions until stuck on app or value
 * input: cek_exp , cfg , env
 * return: (cfg * env) list
 *)
let pr_tau : cek_exp -> cfg -> cfg_env -> (cfg * cfg_env) list =
  fun e c ({sigma;bound} as env) ->
  assert(env.bound >= 0);
  let next_confs = big_step {e = e} bound (sigma,DummyDT) in (**TODO: dummy DT**)
  let process_conf ({e=new_e},new_bound,(new_sigma,_)) =     (**TODO: dummy DT**)
    Some ({c   with exp   = PExp new_e},
          {env with sigma = new_sigma;
                    bound = new_bound})
  in
  (* filter out all bounds exceeded but continue processing confs *)
  List.filter_map process_conf next_confs

(* PROP RET: generic prop ret when provided a value. returns label of move.
 * input: value , vs in V stack , cfg , env 
 * return: (cfg * env * label)
 *)
let pr_ret : value -> cfg -> cfg_env -> cfg * cfg_env * label =
  fun v c env ->
  assert(env.bound >= 0);
  (** NOTE: c.v should be empty on observable moves **)
  let c , vs =
    match c.v with
    | [] -> assert(c.k = []) ; c , []
    | x::xs -> {c with v = xs} , x
  in
  let prvalue , new_fs = prvalue_of_value v in
  let new_label = PrRet(prvalue) in
  (* vs dropping at toplevel *) (**TODO: flag to turn on/off**) (**TODO: add label Mark**)
  let new_exp =
    match c.k with
    | [] -> OExp (new_fs)
    | _  -> OExp (new_fs @ vs)
  in
  {c with exp = new_exp ;
          t   = new_label :: c.t;
          ft  = new_label :: c.ft} , env , new_label

(* PROP APP: generic prop app when provided a function and a value.
 * input: fun_value * arg_value * ecxt_list * ret_type * cfg * env
 * return: (cfg * env)
 *)
let pr_app : value -> value -> value -> value list -> eval_cxt -> Type.t
             -> cfg -> cfg_env -> cfg * cfg_env =
  fun f v f_with_us us eval_frame hole_type c env ->
  assert(env.bound > 0);
  let prvalue , new_fs = prvalue_of_value v in
  let new_label = PrApp(f,prvalue) in
  let new_label_with_us = PrApp(f_with_us,PrConst v) in
  let normalised_label_with_us = (** TODO: flag to turn on/off **)
    let names_of_val = Normalisation.names_of_val empty_conf_names v in
    let norm_v = Normalisation.normalise_val names_of_val v in
    PrApp(f_with_us,PrConst norm_v)
  in
  let new_q = new_label :: c.q in (* add label to all proponent calls *)
  let new_exp , new_k , new_t , new_ft , new_cc , new_sd =
    (** normal pr app **)
    let do_normal_pr_app () =
      let new_t   = [new_label] in
      let new_ft  = new_label_with_us :: c.ft in
      let new_cc , loop_found =
        if !do_cc
        then cc_push c.cc normalised_label_with_us (** NOTE: label with us **)
        else c.cc , false
      in
      let new_exp , new_k , new_ft , new_sd =
        if Type.is_base_type hole_type && loop_found
        then
          begin
            (** NOTE: need to set the stuck data too **)
            let new_ft = loopfound_label :: new_ft in
            PExp {ecxt = eval_frame ; e = BotExp None} , c.k , new_ft , Bottom new_ft
          end
        else OExp (new_fs @ us) , ((eval_frame , hole_type , c.t) :: c.k) , new_ft , c.sd
      in
      new_exp , new_k , new_t , new_ft , new_cc , new_sd
    in
    (** call caching memoisation **)
    if !do_cc then
      begin
        match cc_find c.cc normalised_label_with_us with
        | None ->
           (* normal pr app *)
           do_normal_pr_app () 
        | Some (OpRet v) ->
           (** TODO: add statistics for pruned traces **)
           (* copy of OpRet case *)
           let new_abs_with_us = v in
           let new_ret_label_with_us = OpRet new_abs_with_us in
           let new_exp = PExp {ecxt = eval_frame; e = ValExp (new_abs_with_us,None)} in
           let new_ft  = new_ret_label_with_us :: callskip_label :: new_label_with_us :: c.ft in
           new_exp , c.k , c.t , new_ft , c.cc , c.sd
        | Some l' ->
           failwith
             (Printf.sprintf "<call caching: expected OpRet label, got: %s>"
                (string_of_label l'))
      end
    else
      (* normal pr app *) 
      do_normal_pr_app ()
  in
  {c with exp = new_exp ;
          k   = new_k ;
          t   = new_t ;
          q   = new_q ;
          cc  = new_cc ;
          sd  = new_sd ;
          ft  = new_ft } ,
  {env with bound = env.bound-1}


(****************************
 * LTS OPPONENT TRANSITIONS *
 ****************************)
(** TODO: type annotations for functions **)
(* OP RET:
 * (exct,hole_type,frame_t): evaluation stack frame
 * k_rest: rest of evaluation stack
 * m_val: return value to use if move is already in M
 *)
let op_ret : eval_cxt * Type.t * Trace.t -> ecxt_frame list -> value option -> value list
             -> cfg -> cfg_env -> cfg * cfg_env =
  fun (ecxt,hole_type,frame_t) krest m_val us c env -> 
  assert(env.bound >= 0);
  (* create abstract values for return *)
  let new_abs , new_a =
    (* if move already in memory, replay it *)
    match m_val with
    | None   -> opval_of_type hole_type env.a
    | Some v -> v , env.a
  in
  (** NOTE: alphas for M label don't have US **)
  let new_label = OpRet new_abs in (* removed opval_remove_us, shouldn't have us *)
  let new_abs_with_us = opval_add_us us new_abs in
  let new_label_with_us = OpRet new_abs_with_us in
  let new_m = m_update env.m c.t new_label in
  let new_exp = PExp {ecxt = ecxt; e = ValExp (new_abs_with_us,None)} in
  let new_cc =
    if !do_cc
    then cc_pop c.cc new_label_with_us
    else c.cc
  in
  {c with exp = new_exp ;
          k   = krest ;
          t   = frame_t ;
          cc  = new_cc ;
          ft  = new_label_with_us :: c.ft} ,
  {env with a = new_a ;
            m = new_m}

(* OP APP:
 * index: index of the function being applied
 * f: function value to apply and its lexical data
 * m_arg: argument value to use if move is already in M
 * arg_type: type of the argument to generate if move not in M
 *)
let op_app : prvalue -> value -> value option -> Type.t option -> value list
             -> cfg -> cfg_env -> cfg * cfg_env * label =
  fun prindex f m_arg arg_type us c env ->
  assert(env.bound > 0);
  (* create abstract values for call *)
  let new_abs , new_a =
    (* if move already in memory, replay it *)
    match m_arg , arg_type with
    | None   , Some typ -> opval_of_type typ env.a
    | Some v , None     -> v , env.a
    | _ -> failwith "<op_app>: incorrect use of m_arg or arg_type"
  in
  let new_label = OpApp (prindex, new_abs) in (* removed opval_remove_us, shouldn't have us *)
  (** NOTE: experimental removal of us from toplevel alphas **)
  let new_abs_with_us , new_ft =
    let top_drop_label = Mark "dropped top-level us" in
    let inner_drop_label = Mark "dropped inner us" in
    match c.k with (** TODO: add flags to turn on/off **)
    | [] -> new_abs , top_drop_label::c.ft
    | (_,hole_type,_)::k' ->
       if Type.is_base_type hole_type (** NOTE: experimental **)
       then new_abs , inner_drop_label::c.ft
       else opval_add_us us new_abs , c.ft (** DEFAULT CASE **)
  in
  let new_label_with_us = OpApp (prindex, new_abs_with_us) in
  let new_m = m_update env.m c.t new_label in
  let new_exp = (** NOTE: technically not sound because you need to do a reduction step here,
                          but may be a technical detail. **)
    PExp {ecxt = [] ; e = AppExp(ValExp(f,None),ValExp(new_abs_with_us,None),None)}
  in
  {c with exp = new_exp ;
          v   = us :: c.v ;
          t   = new_label :: c.t ;
          ft  = new_label_with_us :: new_ft} ,
  {env with a = new_a ;
            m = new_m;
            bound = env.bound} , (** NOTE: bound is already decreased by Reductions or by PrApp **)
  new_label

(**************************
 * OBSERVABLE TRANSITIONS *
 **************************)
(* these are transitions that need to syncrhonise. stuck data is checked for this. *)

(* OBSERVABLE MOVE:
 * input: cfg, env, label and other stuck data after running the generic version of move.
 * checks: that label and prquestions of move match the opposing stuck data provided.
 * returns: cfg , env after setting up cfg to get stuck.
 *)
let observable_move : cfg -> cfg_env -> label -> stuck_data -> cfg * cfg_env =
  fun new_c new_env new_label other_sd ->
  match other_sd with
  | NotStuck -> {new_c with sd = Stuck (new_label , new_c.q , new_c.ft)} , new_env
  | Stuck (other_label,other_q,other_ft) ->
     if other_label = new_label || (labels_equivalent other_label new_label new_env.sigma) 
     then
       (* check that all proponent calls done so far are the same *)
       if List.sort_uniq compare new_c.q = List.sort_uniq compare other_q
       then new_c , new_env
       else
         (** BISIM FAILS BECAUSE OF PR CALL MISMATCH **)
         bisim_fail_message new_label new_c.ft other_ft new_env PrCallsMismatch
     else
       (** BISIM FAILS BECAUSE OF MOVE MISMATCH **)
       bisim_fail_message new_label new_c.ft other_ft new_env (LabelMismatch other_label)
  | Bottom other_ft ->
     (** BISIM FAILS BECAUSE OF ONE SIDE BEING STUCK **)
     bisim_fail_message new_label new_c.ft other_ft new_env ExpectedBottom

(****************************
 * MOVE SELECTOR FUNCTIONS  *
 ****************************)
(* These return lists of (c,env,sd) *)
(** NOTE: only top level trace starts with PropRet. All others start with PropApp **)

(* successful observable move means other side was already None, or should be set to None *)
let maybe_observable_move k new_c new_env new_label other_sd =
  match k with
  | [] -> let new_c',new_env' = observable_move new_c new_env new_label other_sd in
          new_c' , new_env' , NotStuck
  | _  -> new_c  , new_env  , other_sd

let do_pr_move : cek_exp -> cfg -> cfg_env -> stuck_data -> (cfg * cfg_env * stuck_data) list =
  fun cek_e c ({sigma;bound} as env) other_sd ->
  (* prune all cfgs where bound = 0, SETS FLAG *)
  if env.bound <= 0 then (mark_bound_reached c.ft env ; []) else
    (* 1. do TAU MOVES *)
    let tau_confs = pr_tau cek_e c env in
    (* 2. select PR MOVE for each conf in tau_confs *)
    let select_pr_move (c,env) =
      (* prune all cfgs where bound = 0, SETS FLAG *)
      if env.bound <= 0 then (mark_bound_reached c.ft env ; None) else
        match c.exp with
        | PExp {ecxt = []; e = ValExp(v,_)} ->
           (* could be observable pr ret *)
           let new_c,new_env,new_label = pr_ret v c env in
           Some(maybe_observable_move c.k new_c new_env new_label other_sd)
        | PExp {ecxt = AppRandECxt((AbsFun(id,arg_type,ret_type,name,us) as f),_) :: ecxt_rest;
                e    = ValExp (v,_)} ->
           (* pr app cannot be observable *)
           let new_c,new_env =
             (** NOTE: removing us from AbsFun to avoid affecting the trace **)
             pr_app (AbsFun(id,arg_type,ret_type,name,[])) v f us ecxt_rest ret_type c env
           in
           Some(new_c , new_env , other_sd)
        | PExp {e = BotExp _} ->
           let c = {c with ft = bottom_label :: c.ft} in
           begin
             match other_sd with
             | Bottom _ -> mark_trace_end c.ft env ; None
             | NotStuck ->
                let new_c = {c with sd = Bottom c.ft} in
                Some(new_c,env,other_sd)
             | Stuck (other_label,other_q,other_ft) ->
                (** BISIM FAILS BECAUSE OF ONE SIDE BEING STUCK **)
                bisim_fail_message other_label other_ft c.ft
                  {env with side = swap_side env.side} (* other side made the move, so we swap *)
                  ExpectedBottom
           end
        | _ ->
           failwith
             (Printf.sprintf
                "<do_pr_move>: unexpected c.exp = %s" (string_of_cfg_exp c.exp))
    in
    List.filter_map select_pr_move tau_confs

let do_op_move : value list -> cfg -> cfg_env -> stuck_data -> (cfg * cfg_env * stuck_data) list =
  fun vs ({k;t} as c) ({a;m;sigma;bound} as env) other_sd ->
  (* prune all cfgs where bound = 0, SETS FLAG *)
  if env.bound <= 0 then (mark_bound_reached c.ft env ; []) else
    match m_get m t with
    | Some (OpApp(PrIndex id , v)) ->
       (* could be observable op app *)
       let f = List.nth vs id in
       let new_c,new_env,new_label = op_app (PrIndex id) f (Some v) None vs c env in
       [maybe_observable_move k new_c new_env new_label other_sd]
    | Some (OpRet v) ->
       begin
         match k with
         | [] -> failwith "<do_op_move>: empty stack when trying to replay a return"
         | kframe :: krest ->
            let new_c,new_env = op_ret kframe krest (Some v) vs c env in
            [new_c,new_env,other_sd]
       end
    | None ->
       begin
         match k with
         | [] ->
            (* could be observable op app *)
            begin
              match vs with
              | [] -> (mark_trace_end c.ft env ; [])
              | _  ->
                 let do_observable_op_app id f =
                   match f with
                   | FunVal (_,_,_,arg_type,_) ->
                      let new_c,new_env,new_label =
                        op_app (PrIndex id) f None (Some arg_type) vs c env
                      in
                      maybe_observable_move k new_c new_env new_label other_sd
                   | AbsFun (_,arg_type,_,_,vs) ->
                      (** NOTE: alphas can also be applied **)
                      (** NOTE: Added alpha here, but not sure if needed at top-level **)
                      let new_c,new_env,new_label =
                        op_app (PrIndex id) f None (Some arg_type) vs c env
                      in
                      maybe_observable_move k new_c new_env new_label other_sd
                   | _ -> failwith "<do_op_move>: expected only functions in OExp"
                 in
                 (* map observable op app to every v with corresponding index in vs *)
                 List.mapi do_observable_op_app vs
            end
         | kframe :: krest ->
            let ret_cfg,ret_env = op_ret kframe krest None vs c env in
            let do_op_app id f =
              match f with
              | FunVal (_,_,_,arg_type,_) ->
                 let new_c,new_env,_ =
                   op_app (PrIndex id) f None (Some arg_type) vs c env
                 in
                 [new_c , new_env , other_sd]
              | AbsFun (absid , arg_type , _ , _ , vs) ->
                 (** NOTE: alphas can also be applied **)
                 (** NOTE: Added alpha here, but not sure if needed at top-level **)
                 let new_c,new_env,_ =
                   op_app (PrIndex id) f None (Some arg_type) vs c env
                 in
                 [new_c , new_env , other_sd]
              | v -> print_endline (string_of_val v) ;
                     failwith "<do_op_move>: expected only functions in OExp"
            in
            (ret_cfg,ret_env,other_sd)::(List.concat (List.mapi do_op_app vs))
       end
    | _ -> failwith "<do_op_move>: unexpected label in M"

(***********************
 * TOP LEVEL FUNCTIONS *
 ***********************)

(* PROCESS_CFG:
 * Processes a single conf in a pair and returns a list of pairs.
 * Processes the conf depending on which side is currently active.
 * Swaps side if the other side is not a stuck configuration.
 * Each cfg_pair knows which side is currently being processed.
 * This function passes the conf to the correct move selector.
 *)
let process_cfg : cfg_pair -> cfg_pair list =
  fun ({c1;c2;env} as cfg_pair) ->
  debug_cfg_pair cfg_pair;
  if c1 = c2 then [] else (** NOTE: up-to identity. TODO: add flag **)
  (* grab conf C and opposing stuck data SD *)
  let c , other_sd , mk_new_pair =
    (* if other side is NotStuck after doing current move, swap to other side *)
    let get_new_side other_sd =
      match other_sd with
      | NotStuck -> swap_side env.side
      | _        -> env.side
    in
    match env.side with
    | Left  ->
       c1 , c2.sd , fun (c,env,osd) ->
                    {
                      c1  = c;
                      c2  = {c2 with sd = osd};
                      env = {env with side = get_new_side osd};
                      (* use new osd as it may have changed *)
                    }
    | Right ->
       c2 , c1.sd , fun (c,env,osd) ->
                    {
                      c1  = {c1 with sd = osd};
                      c2  = c;
                      env = {env with side = get_new_side osd};
                      (* use new osd as it may have changed *)
                    }
  in
  (* check if Pr or Op and send to correct move selector *)
  match c.exp with
  | PExp e ->
     (** inefficient. could pass rest but then no traversals **)
     List.map mk_new_pair (do_pr_move e c env other_sd)
  | OExp vs ->
     (** inefficient. could pass rest but then no traversals **)
     List.map mk_new_pair (do_op_move vs c env other_sd)

(* PROCESS_FRONTIER:
 * Processes a frontier of pairs until the frontier is empty.
 * Does this by processing one conf from one pair at a time.
 *)
let rec process_frontier : frontier -> unit =
  fun frontier ->
  debug_frontier_length frontier ; 
  match frontier with
  | [] -> bisim_end_message ()
  | cfg_pair :: rest ->
     let new_frontier =
       (** Minimise cfg_pair **)
       let mini_cfg_pair = minimise_cfg_pair cfg_pair in
       (** Normalise mini_cfg_pair **)
       let norm_cfg_pair =
         if !do_norm
         then
           begin
             let cfgpair = Normalisation.normalise mini_cfg_pair in
             debug_normalisation cfgpair ; cfgpair             
           end
         else mini_cfg_pair
       in
       (** Memoisation: try to add cfg_pair to memo **)
       if (Memoisation.add !memo norm_cfg_pair)
       then
         (** Adding to memo succeeded: cfg_pair not seen before **)
         add_pending_cfgs !traversal (process_cfg cfg_pair) rest
       else
         (** Adding to memo failed: cfg_pair already exists **)
         (mark_memo_reached (); rest)
     in
     (** potentially inefficient; one recursive call needed per side **)
     process_frontier new_frontier

(***************************************
 * MAIN FUNCTION TO START BISIMULATION *
 ***************************************)
(* sets-up flags, new cfg_pair in frontier and new calls process_frontier *)
let start_bisim e1 e2 bound debug_flags do_dfs memo_size' upto_flags =
  reset_flags () ;
  set_debug_flags debug_flags ;
  set_upto_flags upto_flags ; 
  set_traversal do_dfs ;
  start_bound := bound ;
  memo_size := memo_size' ; 
  memo := init_memo memo_size' ;
  let new_cfg_pair = mk_cfg_pair e1 e2 bound in
  process_frontier [new_cfg_pair]
