open Bigraph
type react = { label:string; lhs:Big.t; rhs:Big.t; f_sm:Fun.t option; f_rnm:Fun.t}
type t = { is:Big.t; rs:Big.t ; rf:Fun.t ; p:Iso.t ; rl:string}
module KeyMap = Map.Make(struct let compare = Z.compare type t = Z.t end)
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
            (String.concat "\n" [init_state;res_state;residue_fun;participants]);;
let _REACT_LABEL_HEADER = "react label"
let _STATE_INDEX_HEADER = "state index"
let _STATE_HEADER = "state representation"
let _INIT_STATE_INDEX_HEADER = "init state idx"
let _RES_STATE_INDEX_HEADER = "res state idx"
let _PARTICIPANT_HEADER = "init state 2 react_lhs iso"
let _RESIDUE_HEADER = "residue of init in res state"
let _RES_STATE_HEADER = "res state actual representation"
let trans_header = [_INIT_STATE_INDEX_HEADER;_RES_STATE_INDEX_HEADER;_REACT_LABEL_HEADER;_PARTICIPANT_HEADER;_RESIDUE_HEADER;_RES_STATE_HEADER] 
and states_header = [_STATE_INDEX_HEADER;_STATE_HEADER] 
let transistions_to_losl its = 
    let trans_rest = List.fold_left 
        (
            fun res (t,ii,ri) -> 
                let isi = string_of_int ii
                and rsi = string_of_int ri
                and rl = t.rl
                and p = (Iso.to_string t.p)
                and rf = (Fun.to_string t.rf)
                and rs = (Big.to_string t.rs)
                in
                    let new_row = [isi;rsi;rl;p;rf;rs]
                    in
                        [new_row]@res
        ) 
        [] 
        its
        in
            trans_rest
let states_to_losl ius =
    let states_rest = List.fold_left
    (
        fun res (b,i) ->
            let state = Big.to_string b
            and index = string_of_int i
            in
                let new_row = [index;state]
                in
                    [new_row]@res
    )
    []
    ius
    in
        states_rest   
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
let _split_into_iso_trans_no_key_checks patt t_mapped transit_fun _ iso_fun =
    let patt_transit = transit_fun patt in
        List.fold_left 
        (
            fun  (res_eq,res_neq) (t,k)-> 
                let checked_transit = transit_fun t.rs in
                    if iso_fun checked_transit patt_transit then
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
let rec _group_based_on_iso_res_states_no_key_checks lot transit_fun key_fun iso_fun = 
    match lot with
        | [] -> []
        | (t,k)::rest -> 
        let equal_with_t, rest' = _split_into_iso_trans_no_key_checks t.rs rest transit_fun key_fun iso_fun in 
        let grouped_rest = _group_based_on_iso_res_states_no_key_checks rest' transit_fun key_fun iso_fun in 
            [(t.rs,k),(t,k)::equal_with_t] |> List.rev_append grouped_rest
let _group_based_on_iso_res_statesV2 lot transit_fun key_fun iso_fun =
    let kp = List.fold_left 
        (
            fun map (b,k) -> 
            match KeyMap.find_opt k map with
            | None -> KeyMap.add k [(b,k)] map
            | Some l -> KeyMap.add k ((b,k)::l) map
        )
        KeyMap.empty
        lot in
    let tmp_res = List.fold_left 
        (
            fun res (_,sub_lobi) -> 
                (_group_based_on_iso_res_states_no_key_checks sub_lobi transit_fun key_fun iso_fun) :: res
        )
        []
        (KeyMap.bindings kp) in
    List.flatten tmp_res
let _step_grouped_iso_res (state,idx) rules transit_fun key_fun iso_fun =
    let raw_result = List.fold_left (fun res r -> apply_trr state r |> List.rev_append res) [] rules in
    let mapped_with_key_result = List.map (fun t -> let transit_rs = transit_fun t.rs in t, key_fun transit_rs) raw_result in
    let grouped_result = _group_based_on_iso_res_statesV2 mapped_with_key_result transit_fun key_fun iso_fun in
    let init_indexed_result = List.map (fun ((b,k),(tl)) -> (b,k),List.map (fun (t,k) -> t,k,idx) tl ) grouped_result in
        init_indexed_result
let _gen_semi_grouped_trans_from_states rules states transit_fun key_fun iso_fun =
    List.fold_left 
        (
            fun logt (s,i) -> (_step_grouped_iso_res (s,i) rules transit_fun key_fun iso_fun )::logt 
        ) 
        [] 
        states 
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
    List.mapi (fun i ((b,k),tl) -> (b,k,i),List.map (fun (t,k',isi) -> (t,k',isi,i) ) tl ) logt
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
let _filter_and_reindex_duplicates ~filter_of:rof ~filter_from:rfr transit_fun _ iso_fun =
    List.fold_left 
    (
        fun (rest_unique,isos) (b_rfr,b_key,rfr_idx) -> 
            let b_rfr_transit = transit_fun b_rfr in
            let b_with_equal_hash = KeyMap.find_opt b_key rof in
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
let _filter_and_reindex_duplicatesV2 ~filter_of:rof ~filter_from:rfr transit_fun _ iso_fun =
        let converted = List.map
        (
            fun (b_rfr,b_key,rfr_idx) ->
                let b_rfr_transit = transit_fun b_rfr in
                let b_with_equal_hash = KeyMap.find_opt b_key rof in
                    match b_with_equal_hash with
                    | None -> ( Some (b_rfr,b_key,rfr_idx), None)
                    | Some l -> 
                        let res = List.find_opt (fun (b,_,_) -> transit_fun b |> iso_fun b_rfr_transit ) l (*_find_iso_indexed_big b_rfr l transit_fun iso_fun *) (* nie zmniejszam zbioru przeszukiwan! *)
                        in
                            match res with
                            | None -> ( Some (b_rfr,b_key,rfr_idx) ,None )
                            | Some (_,_,rof_idx) -> ( None , Some (rfr_idx,rof_idx) )
        )
        rfr |>
        List.fold_left (
            fun (unique_res,iso_res) (unique,iso)-> 
                match unique,iso with 
                | Some s, None -> s::unique_res,iso_res
                | None , Some i -> unique_res,i::iso_res
                | None, None -> failwith "filter_and_reindes-None None"
                | Some _, Some _ -> failwith "filter_and_reindes-Some Some"
        )
        ([],[]) in
        converted
        
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
    let filtered_of_all,iso_all = _filter_and_reindex_duplicatesV2 
        ~filter_of:known_unique_states 
        ~filter_from:new_unchecked_propositions 
        transit_fun 
        key_fun 
        iso_fun 
    in 
    let trans_reindexed_by_all, trans_to_new_unchecked = _apply_reindexing_exclude_rest grouped_indexed_trans iso_all in
    let new_unchecked_states_reindexed,iso_reindexing = _regen_indexing (c_uc_sum) filtered_of_all
    in
        let new_trans = (_apply_reindexing trans_to_new_unchecked iso_reindexing) |> List.rev_append trans_reindexed_by_all
        in
        new_trans, 
        new_unchecked_states_reindexed,
        (List.length new_unchecked_states_reindexed);;
let _split_into_iso_bigs (patt,patt_key,patt_idx,patt_res_idx) lo_big_key_idx transit_fun key_fun iso_fun=
    let patt_transit = transit_fun patt in
        List.fold_left 
            (
                fun  (res_eq,res_neq,isos) (b,k,idx,res_idx)-> 
                    let checked_transit = transit_fun b in
                    if patt_key = key_fun checked_transit && iso_fun checked_transit patt_transit then
                        (b,k,idx,res_idx)::res_eq,res_neq,(res_idx,patt_res_idx,idx,patt_idx)::isos
                    else
                        res_eq,(b,k,idx,res_idx)::res_neq,isos
            )
            ([],[],[])
            lo_big_key_idx;;
let _split_into_iso_bigs_no_key_checks (patt,_,patt_idx,patt_res_idx) lo_big_key_idx transit_fun _ iso_fun=
let patt_transit = transit_fun patt in
    List.fold_left 
        (
            fun  (res_eq,res_neq,isos) (b,k,idx,res_idx)-> 
                let checked_transit = transit_fun b in
                if iso_fun checked_transit patt_transit then
                    (b,k,idx,res_idx)::res_eq,res_neq,(res_idx,patt_res_idx,idx,patt_idx)::isos
                else
                    res_eq,(b,k,idx,res_idx)::res_neq,isos
        )
        ([],[],[])
        lo_big_key_idx;;
let rec _merge_iso_bigs_and_reindex lobi transit_fun key_fun iso_fun =
    match lobi with
        | [] -> [],[]
        | patt::rest -> 
            let _, rest',isos = _split_into_iso_bigs patt rest transit_fun key_fun iso_fun
            in 
                let unique_rest,isos_rest = _merge_iso_bigs_and_reindex rest' transit_fun key_fun iso_fun in
                (patt :: unique_rest),isos::isos_rest
let rec _merge_iso_bigs_and_reindex_no_key_checks lobi transit_fun key_fun iso_fun =
    match lobi with
        | [] -> [],[]
        | patt::rest -> 
            let _, rest',isos = _split_into_iso_bigs_no_key_checks patt rest transit_fun key_fun iso_fun
            in 
                let unique_rest,isos_rest = _merge_iso_bigs_and_reindex_no_key_checks rest' transit_fun key_fun iso_fun in
                (patt :: unique_rest),isos::isos_rest
let _merge_iso_bigs_and_reindex_no_key_checks_const_stack lobi transit_fun key_fun iso_fun =
    match lobi with
    | [] -> [],[]
    | patt::_ -> 
        let left_to_merge = ref lobi in
        let curr_patt = ref patt in
        let res_merged = ref [] in
        let res_isos = ref [] in
        while !left_to_merge <> [] do
            let _, rest',isos = _split_into_iso_bigs_no_key_checks !curr_patt !left_to_merge transit_fun key_fun iso_fun in
            res_merged := !curr_patt :: !res_merged;
            res_isos := isos :: !res_isos;
            left_to_merge := rest';
            curr_patt := if List.length rest' > 0 then List.hd rest' else !curr_patt
        done ;
        !res_merged,!res_isos
let _merge_iso_bigs_and_reindexV2 lobi transit_fun key_fun iso_fun =
    let kp = List.fold_left 
        (
            fun map (b,k,res_idx,state_idx) -> 
            match KeyMap.find_opt k map with
            | None -> KeyMap.add k [(b,k,res_idx,state_idx)] map
            | Some l -> KeyMap.add k ((b,k,res_idx,state_idx)::l) map
        )
        KeyMap.empty
        lobi in
    let tmp_res = List.fold_left 
        (
            fun res (_,sub_lobi) -> 
                (_merge_iso_bigs_and_reindex_no_key_checks_const_stack sub_lobi transit_fun key_fun iso_fun) :: res
        )
        []
        (KeyMap.bindings kp) in
    List.fold_left 
        (
            fun (states_res,isos_res) (part_states_res,part_isos_res) -> 
                List.append states_res part_states_res, List.append isos_res part_isos_res 
        ) 
        ([],[]) 
        tmp_res
let _chunk_array max_length arr = 
    let arr_length = Array.length arr in
    let num_of_chunks = (arr_length / max_length) +1 in
    if num_of_chunks = 1 then
        [arr]
    else
        (
            List.init num_of_chunks 
            (
                fun i ->
                    if i < num_of_chunks -1 then
                        Array.sub arr (max_length*i) (max_length)
                    else
                        Array.sub arr (max_length*i) (arr_length - max_length*i)
            )
        )
let _loa2lol loa =
    List.map (fun arr -> Array.to_list arr) loa
let _merge_iso_bigs_and_reindexV3 lobi transit_fun key_fun iso_fun =
    let size_of_chunk = 100 in
    let kp = List.fold_left 
        (
            fun map (b,k,res_idx,state_idx) -> 
            match KeyMap.find_opt k map with
            | None -> KeyMap.add k [(b,k,res_idx,state_idx)] map
            | Some l -> KeyMap.add k ((b,k,res_idx,state_idx)::l) map
        )
        KeyMap.empty
        lobi in
    let tmp_res = List.map
        (
            fun (_,sub_lobi) -> 
                let sub_lobi_array = Array.of_list sub_lobi in
                let loa = _chunk_array size_of_chunk sub_lobi_array in
                let lol = _loa2lol loa in
                let part_res = List.fold_left 
                (
                    fun (merged_states_with_same_key,isos) sub_lobi_chunk ->
                        let new_merged_states,new_isos = _merge_iso_bigs_and_reindex_no_key_checks_const_stack (List.rev_append sub_lobi_chunk merged_states_with_same_key) transit_fun key_fun iso_fun in
                        new_merged_states,List.rev_append isos new_isos
                        
                ) ([], []) lol in
                part_res
        )
        (KeyMap.bindings kp) in
    List.fold_left 
        (
            fun (states_res,isos_res) (part_states_res,part_isos_res) -> 
                List.append states_res part_states_res, List.append isos_res part_isos_res 
        ) 
        ([],[]) 
        tmp_res
let _apply_reindexing_extended ridx loit  =
    List.map
        (
            fun (t,res_key,isi,rsi,trans_res_idx) ->
                let res_idx_reindexed = List.find_opt (fun (orig_res_idx,_,orig_idx,_) -> orig_idx = rsi && orig_res_idx = trans_res_idx ) ridx in
                match res_idx_reindexed with
            | None -> t,res_key,isi,rsi,trans_res_idx
            | Some (_,trans_res_idx',_,rsi') -> t,res_key,isi,rsi',trans_res_idx'
        )
        loit
let _regen_indexing_extended shift indexed_states_to_regen =
    let indexing = List.mapi (fun i (b,k,_,_) -> b,k,i+shift) indexed_states_to_regen in
    let iso = List.map2 (fun (_,_,oi,res_idx) (_,_,ri) -> (res_idx,res_idx,oi,ri)) indexed_states_to_regen indexing 
    in
        indexing,iso
let _gen_unique_statesV2 ~grouped_isi_indexed_trans ~known_unique_states c_uc_sum transit_fun key_fun iso_fun = 
    let trans_and_state_props = List.mapi
    (
    fun res_idx semi_grouped_list ->
            let local_new_unchecked_propositions,locally_initially_indexed_trans = _map_init_index_of_iso_groups semi_grouped_list |> List.split in
            let local_new_trans,local_new_states,_ = _gen_unique_states
                ~grouped_indexed_trans:(locally_initially_indexed_trans |> List.flatten) 
                ~known_unique_states 
                ~new_unchecked_propositions:local_new_unchecked_propositions
                c_uc_sum
                transit_fun 
                key_fun 
                iso_fun in
            let local_new_trans_res_idx = List.map (fun (t,k,isi,rsi) -> t,k,isi,rsi,res_idx ) local_new_trans
            and local_new_states_res_idx = List.map (fun (b,k,i) -> b,k,i,res_idx ) local_new_states in
            (local_new_trans_res_idx,local_new_states_res_idx)
    ) 
    grouped_isi_indexed_trans in
    let trans,states_unmerged = List.split trans_and_state_props |> (fun (t,s) -> t|>List.flatten, s|> List.flatten) in
    let merged_states,isos_merge = _merge_iso_bigs_and_reindexV2 states_unmerged transit_fun key_fun iso_fun |> (fun (ss,isos) -> ss, List.flatten isos ) in
    let final_states,isos_regen = _regen_indexing_extended c_uc_sum merged_states in
    let trans_tmp1 = _apply_reindexing_extended isos_merge trans in
    let trans_tmp2 = _apply_reindexing_extended isos_regen trans_tmp1 in
    let final_trans = List.map (fun (t,k,isi,rsi,_) -> t,k,isi,rsi) trans_tmp2 in
    final_trans,final_states,List.length merged_states
let _gen_trans_and_unique_states rules ~checked ~unchecked checked_unchecked_sum transit_fun key_fun iso_fun =
    (* let checked_unchecked_sum = List.length checked + List.length unchecked
    and *)
    let unchecked_without_key = List.map (fun (b,_,i) -> b,i ) unchecked 
    and known_unique_states = List.fold_left 
        (
            fun map (b,k,i) -> 
            match KeyMap.find_opt k map with
            | None -> KeyMap.add k [(b,k,i)] map
            | Some l -> KeyMap.add k ((b,k,i)::l) map
        )
        checked
        unchecked in
    let semi_grouped_trans = _gen_semi_grouped_trans_from_states 
        rules 
        unchecked_without_key 
        transit_fun 
        key_fun 
        iso_fun in
    let grouped_trans = _merge_iso_groups (semi_grouped_trans |> List.flatten) transit_fun key_fun iso_fun in
    let new_unchecked_propositions,initially_indexed_trans = _map_init_index_of_iso_groups grouped_trans |> List.split in
    let new_trans,new_states,num_of_new_states = _gen_unique_states 
        ~grouped_indexed_trans:(initially_indexed_trans |> List.flatten) 
        ~known_unique_states 
        ~new_unchecked_propositions 
        checked_unchecked_sum 
        transit_fun 
        key_fun 
        iso_fun in
        new_trans,new_states,num_of_new_states,known_unique_states
let _generic_gen_trans_and_unique_statesV2 fun_gen_semi_grouped_trans_from_states fun_gen_unique_states rules ~checked ~unchecked checked_unchecked_sum transit_fun key_fun iso_fun =
    let unchecked_without_key = List.map (fun (b,_,i) -> b,i ) unchecked 
    and known_unique_states = List.fold_left 
        (
            fun map (b,k,i) -> 
            match KeyMap.find_opt k map with
            | None -> KeyMap.add k [(b,k,i)] map
            | Some l -> KeyMap.add k ((b,k,i)::l) map
        )
        checked
        unchecked in
    let semi_grouped_trans = fun_gen_semi_grouped_trans_from_states 
        rules 
        unchecked_without_key 
        transit_fun 
        key_fun 
        iso_fun in
    let new_trans,new_states,num_of_new_states = fun_gen_unique_states
        ~grouped_isi_indexed_trans:semi_grouped_trans
        ~known_unique_states  
        checked_unchecked_sum 
        transit_fun 
        key_fun 
        iso_fun in
        new_trans,new_states,num_of_new_states,known_unique_states
let rec _generic_explore_ss fun_gen_trans_and_unique_states rules ~(max_steps:int) ~(current_step:int) ~checked ~unchecked c_us_sum transit_fun key_fun iso_fun =
    if current_step < max_steps then
        match unchecked with
        | [] -> [],checked,[],current_step
        | _ ->
            let res_trans,res_unchecked,num_of_new_unchecked_states,new_checked = fun_gen_trans_and_unique_states rules ~checked ~unchecked c_us_sum transit_fun key_fun iso_fun in
            let given_transitions,given_unique_states,given_unique_unchecked,last_reached_step = _generic_explore_ss fun_gen_trans_and_unique_states rules ~max_steps ~current_step:(current_step+1) ~checked:new_checked ~unchecked:res_unchecked (c_us_sum+num_of_new_unchecked_states) transit_fun key_fun iso_fun in
                res_trans::given_transitions,given_unique_states,given_unique_unchecked,last_reached_step 
    else
        [],checked,unchecked,current_step
let _generic_explore_ss_const_stack fun_gen_trans_and_unique_states rules ~(max_steps:int) ~(current_step:int) ~checked ~unchecked c_us_sum transit_fun key_fun iso_fun =
    let curr_step_ref = ref current_step 
    and curr_unchecked_ref = ref unchecked
    and curr_checked_ref = ref checked
    and res_trans = ref [] 
    and num_of_checked_and_unchecked_ref = ref c_us_sum in
    while !curr_step_ref < max_steps && !curr_unchecked_ref <> [] do
        let new_trans,new_unchecked,num_of_new_unchecked_states,new_checked = fun_gen_trans_and_unique_states rules ~checked:!curr_checked_ref ~unchecked:!curr_unchecked_ref !num_of_checked_and_unchecked_ref transit_fun key_fun iso_fun in
        curr_unchecked_ref := new_unchecked;
        curr_checked_ref := new_checked;
        num_of_checked_and_unchecked_ref := (!num_of_checked_and_unchecked_ref+num_of_new_unchecked_states);
        curr_step_ref := ( !curr_step_ref + 1);
        res_trans := new_trans :: !res_trans 
    done;
        !res_trans,!curr_checked_ref,!curr_unchecked_ref,!curr_step_ref
let _append_trans_csv ?(first_time=false) trans file =
    let out_channel = open_out_gen [Open_creat; Open_append] 666 file |> Csv.to_channel in
    let transitions = transistions_to_losl trans in
    let content = if first_time then trans_header :: transitions else transitions in
    Csv.output_all out_channel content;
    Csv.close_out out_channel
let _unmap_key_of_result_state trans =
    List.map (fun (t,_,isi,rsi) -> t,isi,rsi) trans
let _generic_explore_ss_const_stack_slim fun_gen_trans_and_states rules ~(max_steps:int) ~(current_step:int) ~checked ~unchecked c_us_sum transit_fun key_fun iso_fun trans_file =
    let curr_step_ref = ref current_step 
    and curr_unchecked_ref = ref unchecked
    and curr_checked_ref = ref checked
    and res_trans_count = ref 0  
    and num_of_checked_and_unchecked_ref = ref c_us_sum in
    while !curr_step_ref < max_steps && !curr_unchecked_ref <> [] do
        let new_trans,new_unchecked,num_of_new_unchecked_states,new_checked = fun_gen_trans_and_states rules ~checked:!curr_checked_ref ~unchecked:!curr_unchecked_ref !num_of_checked_and_unchecked_ref transit_fun key_fun iso_fun in
        curr_unchecked_ref := new_unchecked;
        curr_checked_ref := new_checked;
        num_of_checked_and_unchecked_ref := (!num_of_checked_and_unchecked_ref+num_of_new_unchecked_states);
        curr_step_ref := ( !curr_step_ref + 1);
        _append_trans_csv ~first_time:(!curr_step_ref = 0 ) (new_trans |> _unmap_key_of_result_state ) trans_file ;
        res_trans_count := !res_trans_count + List.length new_trans
    done;
        !res_trans_count,!curr_checked_ref,!curr_unchecked_ref,!curr_step_ref
let _iso d1 d2 = 
    let g1 = Digraph.dig_2_graph d1 
    and g2 = Digraph.dig_2_graph d2
    in
        Onauty.Iso.are_digraphs_iso ~check_colors:true g1 g2
let _final_unmapping_of_states los= List.map (fun (b,_,i) -> b,i) los
let _generic_explore_ss_facade fun_explore_ss tools (s0:Big.t) (rules:react list) (max_steps:int) =
    let transit_fun, key_fun, iso_fun = tools in
    let s0_k = transit_fun s0 |> key_fun in
    let checked = KeyMap.empty 
    and current_step = 0
    and unchecked = [s0,s0_k,0]
    and c_us_sum = 1 in
    let trans,cs_map,ucs,nos = fun_explore_ss rules ~max_steps ~current_step ~checked ~unchecked c_us_sum transit_fun key_fun iso_fun in
    let _,cs = KeyMap.bindings cs_map |> List.split in
        List.map (fun (t,_,isi,rsi) -> t,isi,rsi) (trans|>List.flatten) ,
        _final_unmapping_of_states (List.flatten cs) ,
        _final_unmapping_of_states ucs,
        nos
let _generic_explore_ss_slim_facade fun_explore_ss trans_file_name tools s0 rules max_steps =
    let transit_fun, key_fun, iso_fun = tools in
    let s0_k = transit_fun s0 |> key_fun in
    let checked = KeyMap.empty 
    and current_step = 0
    and unchecked = [s0,s0_k,0]
    and c_us_sum = 1 in
    let num_of_trans,cs_map,ucs,nos = fun_explore_ss rules ~max_steps ~current_step ~checked ~unchecked c_us_sum transit_fun key_fun iso_fun trans_file_name in
    let _,cs = KeyMap.bindings cs_map |> List.split in
        num_of_trans ,
        _final_unmapping_of_states (List.flatten cs) ,
        _final_unmapping_of_states ucs,
        nos
let explore_ss ?(tools = Digraph.big_2_dig,Digraph.hash_graph,_iso ) (s0:Big.t) (rules:react list) (max_steps:int) =
    let main_fun = _generic_gen_trans_and_unique_statesV2 _gen_semi_grouped_trans_from_states _gen_unique_statesV2 |> _generic_explore_ss in
        _generic_explore_ss_facade main_fun tools s0 rules max_steps
let explore_ss_const_explo_stack ?(tools = Digraph.big_2_dig,Digraph.hash_graph,_iso ) (s0:Big.t) (rules:react list) (max_steps:int) =
    let main_fun = _generic_gen_trans_and_unique_statesV2 _gen_semi_grouped_trans_from_states _gen_unique_statesV2 |> _generic_explore_ss in
        _generic_explore_ss_facade main_fun tools s0 rules max_steps
let explore_ss_slim ?(trans_file_name=(string_of_float (Unix.time ()))^"csv" ) ?(tools = Digraph.big_2_dig,Digraph.hash_graph,_iso ) (s0:Big.t) (rules:react list) (max_steps:int) =
    let main_fun = _generic_gen_trans_and_unique_statesV2 _gen_semi_grouped_trans_from_states _gen_unique_statesV2 |> _generic_explore_ss_const_stack_slim in
        _generic_explore_ss_slim_facade main_fun trans_file_name tools s0 rules max_steps
let _pargen_semi_grouped_trans_from_states rules states transit_fun key_fun iso_fun =
    Parmap.parfold 
        (
            fun (s,i) logt -> (_step_grouped_iso_res (s,i) rules transit_fun key_fun iso_fun )::logt 
        )  
        (Parmap.L states)
        []
        (fun logt1 logt2 -> List.rev_append logt1 logt2)
let _parmap_init_index_of_iso_groups logt =
    Parmap.parmapi (fun i ((b,k),tl) -> (b,k,i),List.map (fun (t,k',isi) -> (t,k',isi,i) ) tl ) (Parmap.L logt)
let _parfilter_and_reindex_duplicates ~filter_of:rof ~filter_from:rfr transit_fun _ iso_fun =
    Parmap.parfold 
    (
        fun (b_rfr,b_key,rfr_idx) (rest_unique,isos) -> 
            let b_rfr_transit = transit_fun b_rfr in
            let b_with_equal_hash = KeyMap.find_opt b_key rof in
                match b_with_equal_hash with
                | None -> (b_rfr,b_key,rfr_idx)::rest_unique,isos
                | Some l -> 
                    let res = List.find_opt (fun (b,_,_) -> transit_fun b |> iso_fun b_rfr_transit ) l (*_find_iso_indexed_big b_rfr l transit_fun iso_fun *) (* nie zmniejszam zbioru przeszukiwan! *)
                    in
                        match res with
                        | None -> (b_rfr,b_key,rfr_idx)::rest_unique,isos
                        | Some (_,_,rof_idx) -> rest_unique,(rfr_idx,rof_idx)::isos
    )
    (Parmap.L rfr)
    ([],[])
    (fun (filtered1,iso1) (filtered2,iso2) -> List.rev_append filtered1 filtered2,List.rev_append iso1 iso2 )
let _pargen_unique_states ~grouped_indexed_trans ~known_unique_states ~new_unchecked_propositions c_uc_sum transit_fun key_fun iso_fun = 
    let filtered_of_all,iso_all = _parfilter_and_reindex_duplicates 
        ~filter_of:known_unique_states 
        ~filter_from:new_unchecked_propositions 
        transit_fun 
        key_fun 
        iso_fun 
    in 
    let reindexed_by_all, my_new_unchecked = _apply_reindexing_exclude_rest grouped_indexed_trans iso_all in
    let new_unchecked_states_reindexed,iso_reindexing = _regen_indexing (c_uc_sum) filtered_of_all
    in
        let new_trans = (_apply_reindexing my_new_unchecked iso_reindexing) |> List.rev_append reindexed_by_all
        in
        new_trans, 
        new_unchecked_states_reindexed,
        (List.length new_unchecked_states_reindexed);;

let _parreindex_results results shift = 
    Parmap.parmapi 
    (fun i (a,b) -> List.map (fun (x,y,z,w,_) -> x,y,z,w,i+shift ) a, List.map (fun (x,y,z,_) -> x,y,z,i+shift) b ) (Parmap.L results)
let _parmerge_iso_bigs_and_reindexV2 lobi transit_fun key_fun iso_fun =
    let kp = List.fold_left 
        (
            fun map (b,k,res_idx,state_idx) -> 
            match KeyMap.find_opt k map with
            | None -> KeyMap.add k [(b,k,res_idx,state_idx)] map
            | Some l -> KeyMap.add k ((b,k,res_idx,state_idx)::l) map
        )
        KeyMap.empty
        lobi in
    let tmp_res = Parmap.parfold
        (
            fun (_,sub_lobi) res  -> 
                (_merge_iso_bigs_and_reindex sub_lobi transit_fun key_fun iso_fun) :: res
        )
        (Parmap.L (KeyMap.bindings kp) ) 
        [] 
        (
            fun tmp_res_part1 tmp_res_part2 -> List.rev_append tmp_res_part1 tmp_res_part2
        ) in
    List.fold_left 
        (
            fun (states_res,isos_res) (part_states_res,part_isos_res) -> 
                List.append states_res part_states_res, List.append isos_res part_isos_res 
        ) 
        ([],[]) 
        tmp_res
    
let _pargen_unique_statesV2 ~grouped_isi_indexed_trans ~known_unique_states c_uc_sum transit_fun key_fun iso_fun = 
    let grouped_isi_indexed_trans_arr = Array.of_list grouped_isi_indexed_trans in
    let trans_and_state_props = Parmap.parmapi 
    (
    fun res_idx _ ->
            let semi_grouped_list = Array.get grouped_isi_indexed_trans_arr res_idx in
            let local_new_unchecked_propositions,locally_initially_indexed_trans = _map_init_index_of_iso_groups semi_grouped_list |> List.split in
            let local_new_trans,local_new_states,_ = _gen_unique_states
                ~grouped_indexed_trans:(locally_initially_indexed_trans |> List.flatten) 
                ~known_unique_states 
                ~new_unchecked_propositions:local_new_unchecked_propositions
                c_uc_sum
                transit_fun 
                key_fun 
                iso_fun in
            let local_new_trans_res_idx = List.map (fun (t,k,isi,rsi) -> t,k,isi,rsi,res_idx ) local_new_trans
            and local_new_states_res_idx = List.map (fun (b,k,i) -> b,k,i,res_idx ) local_new_states in
            (local_new_trans_res_idx,local_new_states_res_idx)
    ) 
    (Parmap.A (Array.init (Array.length grouped_isi_indexed_trans_arr) (fun _ -> ()) ) ) in
    let trans,states_unmerged = List.split trans_and_state_props |> (fun (t,s) -> t|>List.flatten, s|> List.flatten) in
    let merged_states,isos_merge = _merge_iso_bigs_and_reindexV3 states_unmerged transit_fun key_fun iso_fun |> (fun (ss,isos) -> ss, List.flatten isos ) in
    let final_states,isos_regen = _regen_indexing_extended c_uc_sum merged_states in
    let trans_tmp1 = _apply_reindexing_extended isos_merge trans in
    let trans_tmp2 = _apply_reindexing_extended isos_regen trans_tmp1 in
    let final_trans = List.map (fun (t,k,isi,rsi,_) -> t,k,isi,rsi) trans_tmp2 in
    final_trans,final_states,List.length merged_states
let _pargen_unique_statesV2' ~grouped_isi_indexed_trans ~known_unique_states c_uc_sum transit_fun key_fun iso_fun = 
    let trans_and_state_props = Parmap.parmapi 
    (
    fun res_idx semi_grouped_list ->
            let local_new_unchecked_propositions,locally_initially_indexed_trans = _map_init_index_of_iso_groups semi_grouped_list |> List.split in
            let local_new_trans,local_new_states,_ = _gen_unique_states
                ~grouped_indexed_trans:(locally_initially_indexed_trans |> List.flatten) 
                ~known_unique_states 
                ~new_unchecked_propositions:local_new_unchecked_propositions
                c_uc_sum
                transit_fun 
                key_fun 
                iso_fun in
            let local_new_trans_res_idx = List.map (fun (t,k,isi,rsi) -> t,k,isi,rsi,res_idx ) local_new_trans
            and local_new_states_res_idx = List.map (fun (b,k,i) -> b,k,i,res_idx ) local_new_states in
            (local_new_trans_res_idx,local_new_states_res_idx)
    )
    (Parmap.L grouped_isi_indexed_trans) in
    let trans,states_unmerged = List.split trans_and_state_props |> (fun (t,s) -> t|>List.flatten, s|> List.flatten) in
    let merged_states,isos_merge = _merge_iso_bigs_and_reindexV3 states_unmerged transit_fun key_fun iso_fun |> (fun (ss,isos) -> ss, List.flatten isos ) in
    let final_states,isos_regen = _regen_indexing_extended c_uc_sum merged_states in
    let trans_tmp1 = _apply_reindexing_extended isos_merge trans in
    let trans_tmp2 = _apply_reindexing_extended isos_regen trans_tmp1 in
    let final_trans = List.map (fun (t,k,isi,rsi,_) -> t,k,isi,rsi) trans_tmp2 in
    final_trans,final_states,List.length merged_states
let _pargen_unique_statesV3 ~grouped_isi_indexed_trans ~known_unique_states c_uc_sum transit_fun key_fun iso_fun = 
    let trans_and_state_props = List.mapi 
    (
    fun res_idx semi_grouped_list ->
            let local_new_unchecked_propositions,locally_initially_indexed_trans = _map_init_index_of_iso_groups semi_grouped_list |> List.split in
            let local_new_trans,local_new_states,_ = _gen_unique_states
                ~grouped_indexed_trans:(locally_initially_indexed_trans |> List.flatten) 
                ~known_unique_states 
                ~new_unchecked_propositions:local_new_unchecked_propositions
                c_uc_sum
                transit_fun 
                key_fun 
                iso_fun in
            let local_new_trans_res_idx = List.map (fun (t,k,isi,rsi) -> t,k,isi,rsi,res_idx ) local_new_trans
            and local_new_states_res_idx = List.map (fun (b,k,i) -> b,k,i,res_idx ) local_new_states in
            (local_new_trans_res_idx,local_new_states_res_idx)
    ) 
    grouped_isi_indexed_trans in
    let trans,states_unmerged = List.split trans_and_state_props |> (fun (t,s) -> t|>List.flatten, s|> List.flatten) in
    let merged_states,isos_merge = _merge_iso_bigs_and_reindexV2 states_unmerged transit_fun key_fun iso_fun |> (fun (ss,isos) -> ss, List.flatten isos ) in
    let final_states,isos_regen = _regen_indexing_extended c_uc_sum merged_states in
    let trans_tmp1 = _apply_reindexing_extended isos_merge trans in
    let trans_tmp2 = _apply_reindexing_extended isos_regen trans_tmp1 in
    let final_trans = List.map (fun (t,k,isi,rsi,_) -> t,k,isi,rsi) trans_tmp2 in
    final_trans,final_states,List.length merged_states
let _pargen_trans_and_unique_states rules ~checked ~unchecked checked_unchecked_sum transit_fun key_fun iso_fun =
    (* let checked_unchecked_sum = List.length checked + List.length unchecked
    and *)
    let unchecked_without_key = List.map (fun (b,_,i) -> b,i ) unchecked
    and known_unique_states = List.fold_left 
        (
            fun map (b,k,i) -> 
            match KeyMap.find_opt k map with
            | None -> KeyMap.add k [(b,k,i)] map
            | Some l -> KeyMap.add k ((b,k,i)::l) map
        )
        checked
        unchecked in
    let semi_grouped_trans = _pargen_semi_grouped_trans_from_states 
        rules 
        unchecked_without_key 
        transit_fun 
        key_fun 
        iso_fun in
    let grouped_trans = _merge_iso_groups (semi_grouped_trans |> List.flatten) transit_fun key_fun iso_fun in
    let new_unchecked_propositions,initially_indexed_trans = _parmap_init_index_of_iso_groups grouped_trans |> List.split in
    let new_trans,new_states,num_of_new_states = _pargen_unique_states 
        ~grouped_indexed_trans:(initially_indexed_trans |> List.flatten) 
        ~known_unique_states 
        ~new_unchecked_propositions 
        checked_unchecked_sum 
        transit_fun 
        key_fun 
        iso_fun in
        new_trans,new_states,num_of_new_states,known_unique_states
let _pargen_trans_and_unique_statesV2 rules ~checked ~unchecked checked_unchecked_sum transit_fun key_fun iso_fun =
    let unchecked_without_key = List.map (fun (b,_,i) -> b,i ) unchecked
    and known_unique_states = List.fold_left 
        (
            fun map (b,k,i) -> 
            match KeyMap.find_opt k map with
            | None -> KeyMap.add k [(b,k,i)] map
            | Some l -> KeyMap.add k ((b,k,i)::l) map
        )
        checked
        unchecked in
    let semi_grouped_trans = _pargen_semi_grouped_trans_from_states 
        rules 
        unchecked_without_key 
        transit_fun 
        key_fun 
        iso_fun in
    let new_trans,new_states,num_of_new_states = _pargen_unique_statesV2' 
        ~grouped_isi_indexed_trans:semi_grouped_trans
        ~known_unique_states  
        checked_unchecked_sum 
        transit_fun 
        key_fun 
        iso_fun in
        new_trans,new_states,num_of_new_states,known_unique_states
let parexplore_ss ?(tools = Digraph.big_2_dig,Digraph.hash_graph,_iso ) (s0:Big.t) (rules:react list) (max_steps:int) =
    let main_fun = _generic_explore_ss _pargen_trans_and_unique_statesV2 in
        _generic_explore_ss_facade main_fun tools s0 rules max_steps
let parexplore_ss_const_explo_stack ?(tools = Digraph.big_2_dig,Digraph.hash_graph,_iso ) (s0:Big.t) (rules:react list) (max_steps:int) =
    let main_fun = _generic_explore_ss_const_stack _pargen_trans_and_unique_statesV2 in
        _generic_explore_ss_facade main_fun tools s0 rules max_steps
let parexplore_ss_slim ?(trans_file_name= (string_of_float (Unix.time ()))^"csv" ) ?(tools = Digraph.big_2_dig,Digraph.hash_graph,_iso ) (s0:Big.t) (rules:react list) (max_steps:int) =
    let main_fun = _generic_explore_ss_const_stack_slim _pargen_trans_and_unique_statesV2 in
        _generic_explore_ss_slim_facade main_fun trans_file_name tools s0 rules max_steps