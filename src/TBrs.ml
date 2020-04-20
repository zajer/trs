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
let step b lr =
    List.fold_left (fun res r -> apply_trr b r @ res) [] lr
let _split_into_iso_trans patt t_mapped transit_fun key_fun iso_fun =
    let patt_transit = transit_fun patt in
    let patt_key = key_fun patt_transit in
            List.fold_left 
            (
                fun  (res_eq,res_neq) (t,k)-> 
                    let checked_transit = transit_fun t.rs in
                        if patt_key = key_fun checked_transit && iso_fun checked_transit patt_transit then
                            (t,k)::res_eq,res_neq
                        else
                            res_eq,(t,k)::res_neq
            )
            ([],[])
            t_mapped;;
let rec _group_based_on_iso_res_states lot transit_fun key_fun iso_fun = 
    match lot with
        | [] -> []
        | (t,k)::rest -> 
        let equal_with_t, rest' = _split_into_iso_trans t.rs rest transit_fun key_fun iso_fun in 
        let grouped_rest = _group_based_on_iso_res_states rest' transit_fun key_fun iso_fun in 
            [(t.rs,k),(t,k)::equal_with_t] |> List.rev_append grouped_rest
let _step_grouped_iso_res state rules transit_fun key_fun iso_fun =
    let raw_result = List.fold_left (fun res r -> apply_trr state r |> List.rev_append res) [] rules in
    let mapped_result = List.map (fun t -> let transit_rs = transit_fun t.rs in t, key_fun transit_rs) raw_result in
    let grouped_result = _group_based_on_iso_res_states mapped_result transit_fun key_fun iso_fun in
        grouped_result
let _gen_semi_grouped_trans_from_states rules states transit_fun key_fun iso_fun =
    List.fold_left 
        (fun logt s -> (_step_grouped_iso_res s rules transit_fun key_fun iso_fun)::logt ) 
        [] 
        states 
    |> List.flatten
let _split_into_iso_trans_list patt gt_mapped transit_fun key_fun iso_fun =
    let patt_transit = transit_fun patt in
    let patt_key = key_fun patt_transit in
        List.fold_left 
            (
                fun  (res_eq,res_neq) ((b,k),tl)-> 
                    let checked_transit = transit_fun b in
                    if patt_key = key_fun checked_transit && iso_fun checked_transit patt_transit then
                        tl::res_eq,res_neq
                    else
                        res_eq,((b,k),tl)::res_neq
            )
            ([],[])
            gt_mapped;;
let rec _merge_iso_groups losgt transit_fun key_fun iso_fun =
    match losgt with
        | [] -> []
        | ((b,k),tl)::rest -> 
            let equal_with_t, rest' = _split_into_iso_trans_list b rest transit_fun key_fun iso_fun
            in 
                let merged_rest = _merge_iso_groups rest' in
                let merged_with_me = (b,k),(tl |> List.rev_append (List.flatten equal_with_t)) in
                merged_with_me :: merged_rest transit_fun key_fun iso_fun
let _map_init_index_of_iso_groups logt =
    List.mapi (fun i ((b,k),tl) -> (b,k,i),List.map (fun (t,k') -> (t,k',i,-1) ) tl ) logt
let _apply_reindexing loit ridx =
    List.map
        (
            fun (t,init_idx,res_idx) ->
                let res_idx_reindexed = List.find_opt (fun (orig_idx,_) -> orig_idx = res_idx ) ridx in
                    match res_idx_reindexed with
                    | None -> t,init_idx,res_idx
                    | Some (_, res_idx') -> t,init_idx,res_idx'
        )
        loit
module KeyMap = Map.Make(struct let compare = Z.compare type t = Z.t end)
let _find_iso_indexed_big patt loib transit_fun iso_fun =
    let patt_transit = transit_fun patt in
        let found,rest,is_found = 
            List.fold_left 
            (
                fun (res_eq,res_neq,found) (b,k,i)  -> 
                    let checked_transit = transit_fun b in
                    if not found && (iso_fun checked_transit patt_transit) then
                        (b,k,i),res_neq,true
                    else
                        res_eq,(b,k,i)::res_neq,found
            )
            ( (Big.id_eps,Z.zero,-1) ,[],false)
            loib
        in
            if not is_found then
                None
            else
                Some (found,rest)
let _filter_and_reindex_duplicates ~filter_of:rof ~filter_from:rfr transit_fun key_fun iso_fun =
    List.fold_left 
    (
        fun (rest_unique,isos) (b_rfr,b_key,rfr_idx) -> 
            let b_rfr_transit = transit_fun b_rfr in
            let b_rfr_key = key_fun b_rfr_transit in
            let b_with_equal_hash = KeyMap.find_opt b_rfr_key rof in
                match b_with_equal_hash with
                | None -> (b_rfr,b_key,rfr_idx)::rest_unique,isos
                | Some l -> 
                    let res = List.find_opt (fun (b,_,_) -> transit_fun b |> iso_fun b_rfr_transit ) l (*_find_iso_indexed_big b_rfr l transit_fun iso_fun *) (* nie zmniejszam zbioru przeszukiwan! *)
                    in
                        match res with
                        | None -> (b_rfr,b_key,rfr_idx)::rest_unique,isos
                        | Some (_,_,rof_idx) -> rest_unique,(rfr_idx,rof_idx)::isos
    )
    ([],[])
    rfr
let _apply_reindexing_exclude_rest loit ridx =
    List.fold_left
        (
            fun (res_app,res_exc) (t,res_key,init_idx,res_idx) ->
                let res_idx_reindexed = List.find_opt (fun (orig_idx,_) -> orig_idx = res_idx ) ridx in
                        match res_idx_reindexed with
                        | None -> res_app,(t,res_key,init_idx,res_idx)::res_exc
                        | Some (_, res_idx') -> (t,res_key,init_idx,res_idx')::res_app,res_exc
        )
        ([],[])
        loit
let _regen_indexing shift indexed_states_to_regen =
    let indexing = List.mapi (fun i (b,k,_) -> b,k,i+shift) indexed_states_to_regen in
    let iso = List.map2 (fun (_,_,oi) (_,_,ri) -> (oi,ri)) indexed_states_to_regen indexing 
    in
        indexing,iso
let _apply_reindexing loit ridx =
    List.map
        (
            fun (t,res_key,init_idx,res_idx) ->
                let res_idx_reindexed = List.find_opt (fun (orig_idx,_) -> orig_idx = res_idx ) ridx
                    in
                        match res_idx_reindexed with
                        | None -> t,res_key,init_idx,res_idx
                        | Some (_, res_idx') -> t,res_key,init_idx,res_idx'
        )
        loit
let _gen_unique_states ~grouped_indexed_trans ~known_unique_states ~new_unchecked_propositions c_uc_sum transit_fun key_fun iso_fun = 
    let filtered_of_all,iso_all = _filter_and_reindex_duplicates ~filter_of:known_unique_states ~filter_from:new_unchecked_propositions transit_fun key_fun iso_fun in 
    let reindexed_by_all, my_new_unchecked = _apply_reindexing_exclude_rest grouped_indexed_trans iso_all in
    let new_unchecked_states_reindexed,iso_reindexing = _regen_indexing (c_uc_sum) filtered_of_all
    in
        let new_trans = (_apply_reindexing my_new_unchecked iso_reindexing) |> List.rev_append reindexed_by_all
        in
        new_trans, 
        new_unchecked_states_reindexed,
        (List.length new_unchecked_states_reindexed);;
let _gen_trans_and_unique_states rules ~checked ~unchecked checked_unchecked_sum transit_fun key_fun iso_fun =
    (* let checked_unchecked_sum = List.length checked + List.length unchecked
    and *)
    let unchecked_without_key_and_idx = List.map (fun (b,_,_) -> b) unchecked 
    and known_unique_states = List.fold_left 
        (
            fun map (b,k,i) -> 
            match KeyMap.find_opt k map with
            | None -> KeyMap.add k [(b,k,i)] map
            | Some l -> KeyMap.add k ((b,k,i)::l) map
        )
        checked
        unchecked in
    let semi_grouped_trans = _gen_semi_grouped_trans_from_states rules unchecked_without_key_and_idx transit_fun key_fun iso_fun in
    let grouped_trans = _merge_iso_groups semi_grouped_trans transit_fun key_fun iso_fun in
    let new_unchecked_propositions,initially_indexed_trans = _map_init_index_of_iso_groups grouped_trans |> List.split in
    let new_trans,new_states,num_of_new_states = _gen_unique_states ~grouped_indexed_trans:(initially_indexed_trans |> List.flatten) ~known_unique_states ~new_unchecked_propositions checked_unchecked_sum transit_fun key_fun iso_fun in
        new_trans,new_states,num_of_new_states,known_unique_states
let rec _parexplore_ss ~rules ~(max_steps:int) ~(current_step:int) ~checked ~unchecked c_us_sum transit_fun key_fun iso_fun =
        if current_step < max_steps then
            match unchecked with
            | [] -> [],checked,[],current_step
            | _ ->
                let res_trans,res_unchecked,num_of_new_unchecked_states,new_checked = _gen_trans_and_unique_states rules ~checked ~unchecked c_us_sum transit_fun key_fun iso_fun in
                let given_transitions,given_unique_states,given_unique_unchecked,last_reached_step = _parexplore_ss ~rules ~max_steps ~current_step:(current_step+1) ~checked:new_checked ~unchecked:res_unchecked (c_us_sum+num_of_new_unchecked_states) transit_fun key_fun iso_fun in
                    res_trans@given_transitions,given_unique_states,given_unique_unchecked,last_reached_step 
        else
            [],checked,unchecked,current_step
let _iso d1 d2 = 
    let g1 = Digraph.dig_2_graph d1 
    and g2 = Digraph.dig_2_graph d2
    in
        Onauty.Iso.are_digraphs_iso ~check_colors:true g1 g2
let _final_mapping_of_states los= List.map (fun (b,_,i) -> b,i) los
let parexplore_ss ?(tools = Digraph.big_2_dig,Digraph.hash_graph,_iso ) (s0:Big.t) (rules:react list) (max_steps:int) =
    let transit_fun, key_fun, iso_fun = tools in
    let s0_k = transit_fun s0 |> key_fun in
    let checked = KeyMap.empty 
    and current_step = 0
    and unchecked = [s0,s0_k,0]
    and c_us_sum = 1 in
    let trans,cs_map,ucs,nos = _parexplore_ss ~rules:rules ~max_steps ~current_step ~checked ~unchecked c_us_sum transit_fun key_fun iso_fun in
    let _,cs = KeyMap.bindings cs_map |> List.split in
        List.map (fun (t,_,isi,rsi) -> t,isi,rsi) trans ,
        _final_mapping_of_states (List.flatten cs) ,
        _final_mapping_of_states ucs,
        nos

