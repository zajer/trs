open Bigraph
type react = { label:string; lhs:Big.t; rhs:Big.t; f_sm:Fun.t option; f_rnm:Fun.t}
type t = { is:Big.t; rs:Big.t ; rf:Fun.t ; p:Iso.t ; rl:string}
let trans_to_string t =
    let init_state_label = "Init state:"
    and res_state_label = "Res state:"
    and residue_fun_label = "Residue fun:"
    and participant_label = "Participants:"
    in
        let init_state = init_state_label^"\n"^(Big.to_string t.is)
        and res_state = res_state_label^"\n"^(Big.to_string t.rs)
        and residue_fun = residue_fun_label^"\n"^(Fun.to_string t.rf)
        and participants = participant_label^"\n"^(Iso.to_string t.p)
        in
            (String.concat "\n" [init_state;res_state;residue_fun;participants])
let is_site_mapping_function_correct f_sm ~(lhs:Big.t) ~(rhs:Big.t) =
    let is_fsm_total = IntSet.equal (IntSet.of_int (rhs.p.s) ) (Fun.dom f_sm)
    and is_fsm_to_not_exceeding = IntSet.max_elt (Fun.codom f_sm) < Some (lhs.p.s)
    in
        is_fsm_total && is_fsm_to_not_exceeding
let is_residual_node_mapping_function_correct f_rnm ~(lhs:Big.t) ~(rhs:Big.t) =
    let is_frnm_not_exceeding = IntSet.max_elt (Fun.dom f_rnm) <= Some rhs.p.n && IntSet.max_elt (Fun.codom f_rnm) <= Some lhs.p.n
    in
        is_frnm_not_exceeding
let parse_react l ~(lhs:Big.t) ~(rhs:Big.t) ~(f_sm:Fun.t option) ~(f_rnm:Fun.t) =
    let is_f_sm_correct = match f_sm with 
        | None -> rhs.p.s = lhs.p.s
        | Some fsm -> is_site_mapping_function_correct fsm ~lhs ~rhs
    and is_f_rnm_correct = is_residual_node_mapping_function_correct f_rnm ~lhs ~rhs
    and is_label_not_empty = l <> ""
    in
        match is_f_sm_correct,is_f_rnm_correct,is_label_not_empty with
        | false, _, _ -> raise (invalid_arg "Sites mapping is not correct or is absent when needed")
        | _, false, _ -> raise (invalid_arg "Residual nodes mapping is not correct")
        | _, _, false -> raise (invalid_arg "Label cannot be empty")
        | true, true, true -> {label=l ; lhs ; rhs ; f_sm; f_rnm}
let apply_trr_with_occ (b:Big.t) (r:react) (lhs_occ:Big.occ) =
    let res_b,res_f = TBig.rewrite lhs_occ ~target:b ~r0:r.lhs ~r1:r.rhs ~f_s:r.f_sm ~f_r1_r0:r.f_rnm
    and res_iso = match lhs_occ with | iso, _, _ -> iso
    in
        { is=b; rs=res_b;rf=res_f;p=res_iso; rl=r.label}
let apply_trr (b:Big.t) (r:react) =
    let occs = Big.occurrences ~target:b ~pattern:r.lhs
    in  
        List.fold_left (fun res occ -> apply_trr_with_occ b r occ :: res) [] occs
let translate_trans ~(output_res_state:Big.t) ~(translated:t) =
    let translation = TBig.translate_equal ~from_b:translated.rs ~to_b:output_res_state
    in
        let res_residue_fun = Utils.transform_fun_dom translated.rf translation
        in
            {
                is=translated.is;
                rs=output_res_state; 
                rf=res_residue_fun;
                p=translated.p;
                rl=translated.rl
            }      
let split_into_iso_trans (patt:Big.t) (rest:t list) =
    let patt_key = Big.key patt
    in
        List.fold_left 
            (
                fun  (res_eq,res_neq) t-> 
                    if Big.key t.rs = patt_key && Big.equal t.rs patt then
                            t::res_eq,res_neq
                    else
                        res_eq,t::res_neq
            )
            ([],[])
            rest
let translate_all ors ttl =
    List.fold_left (fun res t -> translate_trans ~translated:t ~output_res_state:ors::res) [] ttl
let translate_all_iso_trans (patt:Big.t) (all:t list) =
    let eq,neq = split_into_iso_trans patt all    
    in
        let teq = translate_all patt eq
        in
            teq,neq
let rec unify_based_on_iso_res_states lot = 
    match lot with
    | [] -> []
    | t::rest -> 
        let merged_with_t, rest' = translate_all_iso_trans t.rs rest
        in 
            let merged_with_rest = unify_based_on_iso_res_states rest'
            in 
                [t.rs,t::merged_with_t] @ merged_with_rest
let step b lr =
    List.fold_left (fun res r -> apply_trr b r @ res) [] lr
let step_unified_res b lr =
    unify_based_on_iso_res_states (step b lr)
let rec group_based_on_iso_res_states lot = 
    match lot with
        | [] -> []
        | t::rest -> 
        let equal_with_t, rest' = split_into_iso_trans t.rs rest
        in 
            let grouped_rest = group_based_on_iso_res_states rest'
            in 
                [t.rs,t::equal_with_t] @ grouped_rest
let step_grouped_iso_res b lr =
    let raw_result = List.fold_left (fun res r -> apply_trr b r @ res) [] lr
        in  
            let grouped_result = group_based_on_iso_res_states raw_result
            in
                grouped_result
(*
    Takes a pattern and a list of indexed bigraphs.
    Returns a bigraph isomorphic to the pattern with index associated to it and information about whether any bigraph has been found.
    In case of not finding isomorphic bigraph function returns Big.id_eps paired with -1.
*)

let find_iso_indexed_big (patt:Big.t) (loib:(Big.t*int) list) =
    let patt_key = Big.key patt
    in
        List.fold_left 
            (
                fun (res_eq,res_neq,found) (t,i)  -> 
                    if not found && Big.key t = patt_key && Big.equal t patt then
                        (t,i),res_neq,true
                    else
                        res_eq,(t,i)::res_neq,found
            )
            ( (Big.id_eps,-1) ,[],false)
            loib

(*let parfind_iso_indexed_big (patt:Big.t) (loib:(Big.t*int) list) =
    let patt_key = Big.key patt
    and loib_converted = Parmap.L loib
    in
        let eq,neq = Parmap.parmapfold 
            (fun (b,idx)-> (b,idx,(Big.key b)))
            loib_converted
            (
                fun (b,idx,bk) res ->
                    match res with
                    | [],res_neq -> if (bk = patt_key) && (Big.equal patt b ) then 
                                        [b,idx],res_neq
                                    else
                                        [],(b,idx)::res_neq
                    | res_eq,res_neq -> res_eq,(b,idx)::res_neq
            )
            ([],[])
            (
                fun (eq1,neq1) (eq2,neq2) ->
                    match eq1,eq2 with 
                    | [] , [] -> [],neq1@neq2
                    | eq , [] -> eq,neq1@neq2
                    | [] , eq -> eq,neq1@neq2
                    | _, _ -> raise (Invalid_argument "bigraphs not properly indexed!")
            )
        in
            match eq with
            | [] -> (Big.id_eps,-1),neq,false
            | _ -> (List.hd eq),neq,true
*)            

(* reindex_from contains less elements than reindex_of  *)
let filter_and_reindex_duplicates_case1 ~reindex_of:(rof:(Big.t * int) list ) ~reindex_from:(rfr:(Big.t * int) list ) =
    List.fold_left 
    (
        fun (rest_unique,rest_isos) (b_rfr,rfr_idx) -> 
            let (_ ,rof_idx), _,is_found = find_iso_indexed_big b_rfr rof
            in
                if is_found then
                    rest_unique,(rfr_idx,rof_idx)::rest_isos
                else
                    (b_rfr,rfr_idx)::rest_unique,rest_isos
    )
    ([],[])
    rfr
(* reindex_of contains less elements than reindex_from  *)
let filter_and_reindex_duplicates_case2 ~reindex_of:(rof:(Big.t * int) list ) ~reindex_from:(rfr:(Big.t * int) list ) =
    let isos, unique = List.fold_left 
    (
        fun (rest_isos,rest_from) (b_rof,rof_idx) -> 
            let (_ ,rfr_idx), rest_from',is_found = find_iso_indexed_big b_rof rest_from
            in
                if is_found then
                    (rfr_idx,rof_idx)::rest_isos,rest_from'
                else
                    rest_isos,rest_from
    )
    ([],rfr)
    rof
    in
        unique,isos
let filter_and_reindex_duplicatesV2 ~reindex_of:(rof:(Big.t * int) list ) ~reindex_from:(rfr:(Big.t * int) list ) =
    let rfr_count = List.length rfr
    and rof_count = List.length rof
    in
        if rfr_count >= rof_count then filter_and_reindex_duplicates_case2 ~reindex_of:rof ~reindex_from:rfr
        else filter_and_reindex_duplicates_case1 ~reindex_of:rof ~reindex_from:rfr
     
(* 
    Returns all pairs (Big.t * int) from reindex_from which do not exist in reindex_of.
    Additionaly, it returns list of isomorphisms of indexes from rfr to rof for each element of rfr that exists (is isomorphic to any of the elements) in rof.
    Assumption: rof and rfr are grouped by which means there are no pairs of bigraphs that are isomorphic to each other.
*)
(*
let rec filter_and_reindex_duplicates ~reindex_of:(rof:(Big.t * int) list ) ~reindex_from:(rfr:(Big.t * int) list ) =
    match rof with
        | [] -> rfr, []
        | (t,rof_idx)::rest_of -> 
        let (_ ,rfr_idx), rest_from,found = find_iso_indexed_big t rfr
        in 
            let rest_unique,rest_isos = filter_and_reindex_duplicates ~reindex_of:rest_of ~reindex_from:rest_from
            in
                if found then
                    rest_unique,(rfr_idx,rof_idx)::rest_isos
                else
                    rest_unique,rest_isos
*)
(* Wydajność parfilter... jet gorsza od filter... jest gorsza *)
(*
let parfilter_and_reindex_duplicates ~reindex_of:(rof:(Big.t * int) list ) ~reindex_from:(rfr:(Big.t * int) list ) =
    let tmp = Parmap.L rfr
    in
        Parmap.parmapfold
        (
            fun (rfr_b,rfr_idx) ->
                let (_ ,rof_idx), _,found = find_iso_indexed_big rfr_b rof
                in
                    if found then
                        [],[rfr_idx,rof_idx]
                    else
                        [rfr_b,rfr_idx],[]
        )
        tmp
        (
            fun (filtered,iso) (res_filtered,res_iso) ->
                filtered@res_filtered,iso@res_iso
        )
        ([],[])
        (
            fun (res_filtered_part1,res_iso_part1) (res_filtered_part2,res_iso_part2)->
                res_filtered_part1@res_filtered_part2,res_iso_part1@res_iso_part2
        )
*)

(*
    Założenie: indeksacja ci jest od 0 do n-1 (ci to liczba elementow juz indeksowanych)
*)
let regen_indexing (ci:int) (ri:(Big.t * int) list) =
    let indexing = List.mapi (fun i (b,_) -> b,i+ci) ri
    in
        let iso = List.map2 (fun (_,oi) (_,ri) -> (oi,ri)) ri indexing
        in
            indexing,iso
let apply_reindexing loit ridx =
    let tmp = Parmap.L loit
    in
        Parmap.parmap
            (
                fun (t,init_idx,res_idx) ->
                    let res_idx_reindexed = List.find_opt (fun (orig_idx,_) -> orig_idx = res_idx ) ridx
                        in
                            match res_idx_reindexed with
                            | None -> t,init_idx,res_idx
                            | Some (_, res_idx') -> t,init_idx,res_idx'
            )
            tmp
let apply_reindexing_exclude_rest loit ridx =
    let tmp = Parmap.L loit
    in
        Parmap.parfold
            (
                fun (t,init_idx,res_idx) (res_app,res_exc) ->
                    let res_idx_reindexed = List.find_opt (fun (orig_idx,_) -> orig_idx = res_idx ) ridx
                        in
                            match res_idx_reindexed with
                            | None -> res_app,(t,init_idx,res_idx)::res_exc
                            | Some (_, res_idx') -> (t,init_idx,res_idx')::res_app,res_exc
            )
            tmp
            ([],[])
            (
                fun (app_p1,exc_p1) (app_p2,exc_p2) ->
                    app_p1@app_p2,exc_p1@exc_p2
            )        
let initial_indexing (btll:(Big.t * t list) list ) ~(init_state_idx:int) ~(checked_unchecked_sum:int) =
    let tmp = Parmap.L btll
    in
        Parmap.parmapifold
            (
                fun res_state_idx_no_shift (b,tl) ->
                    let init_val_of_res_state_idx = res_state_idx_no_shift+checked_unchecked_sum+1
                    in
                        let indexed_transitions = 
                            List.fold_left (fun res t -> (t,init_state_idx,init_val_of_res_state_idx)::res) [] tl
                        in
                            (b,init_val_of_res_state_idx),indexed_transitions
            )
            tmp
            (
                fun (ib,its) (res_ib,res_its) ->
                    ib::res_ib,its@res_its
            )
            ([],[])
            (
                fun (ibs_rp1,its_rp1) (ibs_rp2,its_rp2) ->
                    ibs_rp1@ibs_rp2,its_rp1@its_rp2
            )
let[@landmark "gen"] _gen_trans_and_unique_states 
    ~(rules:react list) 
    ~(checked:(Big.t*int) list) 
    ~unchecked 
    ~checked_unchecked_sum:(c_uc_sum:int) 
    ~my_state:ms
    ~my_state_idx:(ms_idx:int) 
    ~trans
    ~new_unchecked_states
    ~new_unchecked_states_number
    =
    let res_su = (step_grouped_iso_res ms rules)[@landmark "step"]
    in
        let indexed_res_states, initially_indexed_transitions = (initial_indexing res_su ~init_state_idx:ms_idx  ~checked_unchecked_sum:c_uc_sum)[@landmark "init indexing"]
        in
            let filtered_of_checked,iso_checked = (filter_and_reindex_duplicatesV2 ~reindex_of:checked ~reindex_from:indexed_res_states)[@landmark "filtering of checked"]
            in
                let trans_reindexed_by_checked,trans_unique_p1 = (apply_reindexing_exclude_rest initially_indexed_transitions iso_checked)[@landmark "reindexing 1"]
                and filtered_of_unchecked,iso_unchecked = (filter_and_reindex_duplicatesV2 ~reindex_of:unchecked ~reindex_from:filtered_of_checked)[@landmark "filtering of unchecked"]
                in
                    let trans_reindexed_by_unchecked,trans_unique_p2 = (apply_reindexing_exclude_rest trans_unique_p1 iso_unchecked)[@landmark "reindexing 2"]
                    and filtered_of_results, iso_results = (filter_and_reindex_duplicatesV2 ~reindex_of:new_unchecked_states ~reindex_from:filtered_of_unchecked)[@landmark "filtering current results"]
                    in
                        let trans_reindexed_by_results,trans_unique_p3 = (apply_reindexing_exclude_rest trans_unique_p2 iso_results)[@landmark "reindexing 3"]
                        and my_new_unchecked_states_reindexed,iso_reindexing = (regen_indexing (c_uc_sum+new_unchecked_states_number) filtered_of_results)[@landmark "regen indexing"]
                        in
                            let my_trans = ((apply_reindexing trans_unique_p3 iso_reindexing)@trans_reindexed_by_checked@trans_reindexed_by_unchecked@trans_reindexed_by_results)[@landmark "final trans"]
                            in
                                my_trans@trans, 
                                my_new_unchecked_states_reindexed@new_unchecked_states,
                                ( (List.length my_new_unchecked_states_reindexed)+new_unchecked_states_number )
(*let[@landmark "pargen"] _pargen_of_trans_and_unique_states ~(rules:react list) ~(checked:(Big.t * int) list) ~unchecked =
    let converted_unchecked = Parmap.L unchecked
    and checked_unchecked_sum = List.length checked + List.length unchecked
    in
    Parmap.parfold
        (
            fun (ucs,i) (trans,new_unchecked_states,new_unchecked_states_number) ->
                Unix.sleep 1 ;
                (_gen_trans_and_unique_states 
                    ~rules 
                    ~checked 
                    ~unchecked 
                    ~checked_unchecked_sum 
                    ~my_state:ucs 
                    ~my_state_idx:i 
                    ~trans 
                    ~new_unchecked_states 
                    ~new_unchecked_states_number
                )[@landmark "gen"]
        )
        converted_unchecked
        ([],[],0)
        (
            fun (trans_part1, new_unchecked_part1,new_unchecked_length_part1) (trans_part2, new_unchecked_part2,new_unchecked_length_part2) -> 
                (
                let filtered_part2,iso_part_2_to_1 = filter_and_reindex_duplicatesV2 ~reindex_of:new_unchecked_part1 ~reindex_from:new_unchecked_part2
                and new_length = new_unchecked_length_part1 + new_unchecked_length_part2
                in
                    let trans_part2_reindexed_by_part1,trans_part2_unique = apply_reindexing_exclude_rest trans_part2 iso_part_2_to_1
                    and new_unchecked_part2_reindexed,iso_part2_reindex = regen_indexing (checked_unchecked_sum+new_unchecked_length_part1) filtered_part2
                    in
                        let trans_part2_reindexed_by_shift = apply_reindexing trans_part2_unique iso_part2_reindex
                        in
                            trans_part1@trans_part2_reindexed_by_part1@trans_part2_reindexed_by_shift,new_unchecked_part1@new_unchecked_part2_reindexed,new_length
                )[@landmark "merging"]
        )
        *)
let[@landmark "pargen"] _pargen_of_trans_and_unique_states ~(rules:react list) ~(checked:(Big.t * int) list) ~unchecked =
    let checked_unchecked_sum = List.length checked + List.length unchecked
    in
    List.fold_right
        (
            fun (ucs,i) (trans,new_unchecked_states,new_unchecked_states_number) ->
                _gen_trans_and_unique_states 
                    ~rules 
                    ~checked 
                    ~unchecked 
                    ~checked_unchecked_sum 
                    ~my_state:ucs 
                    ~my_state_idx:i 
                    ~trans 
                    ~new_unchecked_states 
                    ~new_unchecked_states_number
                
        )
        unchecked
        ([],[],0)
        
let rec _parexplore_ss ~(rules:react list) ~(max_steps:int) ~(current_step:int) ~(checked:(Big.t*int) list) ~unchecked =
        if current_step < max_steps then
            match unchecked with
            | [] -> [],checked,[],current_step
            | _ ->
                let res_trans,res_unchecked,_ = _pargen_of_trans_and_unique_states ~rules ~checked ~unchecked
                in
                    let given_transitions,given_unique_states,given_unique_unchecked,last_reached_step = _parexplore_ss ~rules ~max_steps ~current_step:(current_step+1) ~checked:(checked@unchecked) ~unchecked:res_unchecked
                    in
                        res_trans@given_transitions,given_unique_states,given_unique_unchecked,last_reached_step 
        else
            [],checked,unchecked,current_step
let[@landmark "parexplore"] parexplore_ss ~(s0:Big.t) ~(rules:react list) ~(max_steps:int) =
    let checked = []
    and current_step = 0 
    and unchecked = [s0,0]
    in
        _parexplore_ss ~rules:rules ~max_steps ~current_step ~checked ~unchecked

let readlines filename =
    let lines = ref [] in
    let chan = open_in filename in
        try
        while true; do
            lines := input_line chan :: !lines
        done; !lines
        with End_of_file ->
            close_in chan;
            List.rev !lines ;;

let profile () = 
    let s0_to_parse = List.fold_left (fun (t:string) (l:string) -> t^"\n"^l ) "" (readlines "s0v2.txt") 
    and move_lhs_to_parse = List.fold_left (fun (t:string) (l:string) -> t^"\n"^l ) "" (readlines "mov_lhs.txt") 
    and move_rhs_to_parse = List.fold_left (fun (t:string) (l:string) -> t^"\n"^l ) "" (readlines "mov_rhs.txt") 
    and estConn2AF_lhs_to_parse = List.fold_left (fun (t:string) (l:string) -> t^"\n"^l ) "" (readlines "estConn2AF_lhs.txt") 
    and estConn2AF_rhs_to_parse = List.fold_left (fun (t:string) (l:string) -> t^"\n"^l ) "" (readlines "estConn2AF_rhs.txt") 
    and estConn1AF_lhs_to_parse = List.fold_left (fun (t:string) (l:string) -> t^"\n"^l ) "" (readlines "estConn1AF_lhs.txt") 
    and estConn1AF_rhs_to_parse = List.fold_left (fun (t:string) (l:string) -> t^"\n"^l ) "" (readlines "estConn1AF_rhs.txt")
    and breConn_lhs_to_parse = List.fold_left (fun (t:string) (l:string) -> t^"\n"^l ) "" (readlines "breConn_lhs.txt")
    and breConn_rhs_to_parse = List.fold_left (fun (t:string) (l:string) -> t^"\n"^l ) "" (readlines "breConn_rhs.txt")
    in
        let s0 = Big.of_string s0_to_parse
        and mov_lhs = Big.of_string move_lhs_to_parse
        and mov_rhs = Big.of_string move_rhs_to_parse
        and estConn1AF_lhs = Big.of_string estConn1AF_lhs_to_parse
        and estConn1AF_rhs = Big.of_string estConn1AF_rhs_to_parse
        and estConn2AF_lhs = Big.of_string estConn2AF_lhs_to_parse
        and estConn2AF_rhs = Big.of_string estConn2AF_rhs_to_parse
        and breConn_lhs = Big.of_string breConn_lhs_to_parse
        and breConn_rhs = Big.of_string breConn_rhs_to_parse
        and mov_f_rnm = Fun.empty |> Fun.add 0 0 |> Fun.add 1 2 |> Fun.add 2 1
        and estConn2AF_f_rnm = Fun.empty |> Fun.add 0 0 |> Fun.add 1 1 |> Fun.add 2 2 |> Fun.add 3 3
        and estConn1AF_f_rnm = Fun.empty |> Fun.add 0 0 |> Fun.add 1 1 |> Fun.add 2 2
        and breConn_f_rnm = Fun.empty |> Fun.add 0 0 |> Fun.add 1 1
        in
            let mov_react = parse_react "move" ~lhs:mov_lhs ~rhs:mov_rhs ~f_sm:None ~f_rnm:mov_f_rnm
            and estConn1AF_react = parse_react "estConn1AF" ~lhs:estConn1AF_lhs ~rhs:estConn1AF_rhs ~f_sm:None ~f_rnm:estConn1AF_f_rnm
            and estConn2AF_react = parse_react "estConn2AF" ~lhs:estConn2AF_lhs ~rhs:estConn2AF_rhs ~f_sm:None ~f_rnm:estConn2AF_f_rnm
            and breConn_react = parse_react "breConn" ~lhs:breConn_lhs ~rhs:breConn_rhs ~f_sm:None ~f_rnm:breConn_f_rnm 
            in
                let rules = [mov_react;estConn1AF_react;estConn2AF_react;breConn_react]
                and _ = Parmap.set_default_ncores 4
                in
                    let _ = parexplore_ss ~s0 ~rules ~max_steps:300
                    in
                    ()

let () =
    Landmark.start_profiling () ;  
    profile ()


