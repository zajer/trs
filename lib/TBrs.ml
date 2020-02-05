open Bigraph
type react = { label:string; lhs:Big.t; rhs:Big.t; f_sm:Fun.t option; f_rnm:Fun.t}
type trans = { init_state:Big.t; res_state:Big.t ; residue:Fun.t ; participants:Iso.t ; react_label:string}
let trans_to_string t =
    let init_state_label = "Init state:"
    and res_state_label = "Res state:"
    and residue_fun_label = "Residue fun:"
    and participant_label = "Participants:"
    in
        let init_state = init_state_label^"\n"^(Big.to_string t.init_state)
        and res_state = res_state_label^"\n"^(Big.to_string t.res_state)
        and residue_fun = residue_fun_label^"\n"^(Fun.to_string t.residue)
        and participants = participant_label^"\n"^(Iso.to_string t.participants)
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
        { init_state=b; res_state=res_b;residue=res_f;participants=res_iso; react_label=r.label}
let apply_trr (b:Big.t) (r:react) =
    let occs = Big.occurrences ~target:b ~pattern:r.lhs
    in  
        List.fold_left (fun res occ -> apply_trr_with_occ b r occ :: res) [] occs
let translate_trans ~(output_res_state:Big.t) ~(translated:trans) =
    let translation = TBig.translate_equal ~from_b:translated.res_state ~to_b:output_res_state
    in
        let res_residue_fun = Utils.transform_fun_dom translated.residue translation
        in
            {
                init_state=translated.init_state;
                res_state=output_res_state; 
                residue=res_residue_fun;
                participants=translated.participants;
                react_label=translated.react_label
            }      
let split_into_iso_trans (patt:Big.t) (rest:trans list) =
    let patt_key = Big.key patt
    in
        List.fold_right 
            (
                fun t (res_eq,res_neq) -> 
                    if Big.key t.res_state = patt_key && Big.equal t.res_state patt then
                            t::res_eq,res_neq
                    else
                        res_eq,t::res_neq
            )
            rest
            ([],[])
let translate_all ors ttl =
    List.fold_right (fun t res -> translate_trans ~translated:t ~output_res_state:ors::res) ttl []
let translate_all_iso_trans (patt:Big.t) (all:trans list) =
    let eq,neq = split_into_iso_trans patt all    
    in
        let teq = translate_all patt eq
        in
            teq,neq
let rec unify_based_on_iso_res_states lot = 
    match lot with
    | [] -> []
    | t::rest -> 
        let merged_with_t, rest' = translate_all_iso_trans t.res_state rest
        in 
            let merged_with_rest = unify_based_on_iso_res_states rest'
            in 
                [t.res_state,t::merged_with_t] @ merged_with_rest
let step b lr =
    List.fold_left (fun res r -> apply_trr b r @ res) [] lr
let step_unified_res b lr =
    unify_based_on_iso_res_states (step b lr)
let rec group_based_on_iso_res_states lot = 
    match lot with
        | [] -> []
        | t::rest -> 
        let equal_with_t, rest' = split_into_iso_trans t.res_state rest
        in 
            let grouped_rest = group_based_on_iso_res_states rest'
            in 
                [t.res_state,t::equal_with_t] @ grouped_rest
let step_grouped_iso_res b lr =
    let raw_result = List.fold_left (fun res r -> apply_trr b r @ res) [] lr
        in  
            let grouped_result = group_based_on_iso_res_states raw_result
            in
                grouped_result
let equal_state_from_checked state checked = 
    let state_key = Big.key state 
    in
        List.fold_left 
            (
                fun (res_big,res_i) ic -> 
                if not res_i && Big.key ic = state_key && Big.equal state ic then
                    ic,true
                else
                    res_big,res_i
            )
            (Big.id_eps,false)
            checked
let group_with_checked su checked =
    List.fold_left 
    (
        fun (res_unified,res_unique) (res_big, tl) ->
            let from_checked, does_exist = equal_state_from_checked res_big checked 
                in
                    if does_exist then
                        [from_checked, tl]@res_unified,res_unique
                    else
                        res_unified ,[res_big, tl]@res_unique
    )
    ([],[])
    su
let split_into_iso_bigs (patt:Big.t) (rest:Big.t list) =
    let patt_key = Big.key patt
    in
        List.fold_right 
            (
                fun t (res_eq,res_neq) -> 
                    if Big.key t = patt_key && Big.equal t patt then
                            t::res_eq,res_neq
                    else
                        res_eq,t::res_neq
            )
            rest
            ([],[])
let rec filter_iso_dupl ~filter_of:x ~filter_from:y = 
    match x with
        | [] -> y
        | t::rest_of -> 
        let _, rest_from = split_into_iso_bigs t y
        in 
            filter_iso_dupl ~filter_of:rest_of ~filter_from:rest_from
let rec _explore_ss ~(rules:react list) ~(max_steps:int) ~(current_step:int) ~(checked:Big.t list) ~(unchecked:Big.t list) =
        if current_step < max_steps then
            match unchecked with
            | [] -> [],checked,current_step
            | s::rest -> 
                let res_su = step_grouped_iso_res s rules 
                in
                    let unified_with_checked,unique = group_with_checked res_su (s::checked) 
                    in 
                        let part_new_unchecked, part_result1  = List.split unique
                        and _ , part_result2 = List.split unified_with_checked
                        in
                            let part_result = List.concat part_result1 @ List.concat part_result2
                            in
                                let new_checked = s::checked
                                and new_unchecked = rest@(filter_iso_dupl ~filter_of:rest ~filter_from:part_new_unchecked)
                                and new_current_step = current_step + 1
                                in
                                    let given_transitions,given_unique_states,last_reached_step = _explore_ss ~rules ~max_steps ~current_step:new_current_step ~checked:new_checked ~unchecked:new_unchecked
                                    in
                                        part_result@given_transitions,given_unique_states,last_reached_step
        else
            [],checked,current_step
let explore_ss ~(s0:Big.t) ~(rules:react list) ~(max_steps:int) =
    let checked = []
    and unchecked = [s0]
    and current_step = 0 
    in
        _explore_ss ~rules ~max_steps ~current_step ~checked ~unchecked 
let parapply_trr (b:Big.t) (r:react) noc =
    let occs = Big.occurrences ~target:b ~pattern:r.lhs
    in  
        let par_occs = Parmap.L occs
        in
            Parmap.parfold (fun occ res -> apply_trr_with_occ b r occ :: res) par_occs [] (fun part_res1 part_res2 -> part_res1@part_res2) ~ncores:noc
let _pargen_of_trans_and_unique_states ~(rules:react list) ~(checked:Big.t list) ~unchecked =
    let converted_unchecked = Parmap.L unchecked
    in
    Parmap.parfold
        (
            fun ucs (trans,new_unchecked_states) ->
                let res_su = step_grouped_iso_res ucs rules
                in
                    let unified_with_checked,unique = group_with_checked res_su (ucs::checked) 
                    in
                        let new_unchecked_filtered_of_checked, part_result1  = List.split unique
                        and _ , part_result2 = List.split unified_with_checked
                        in
                            let part_result = List.concat part_result1 @ List.concat part_result2
                            in
                                let filtered_of_checked_and_current_unchecked = filter_iso_dupl ~filter_of:unchecked ~filter_from:new_unchecked_filtered_of_checked
                                in
                                    let filtered_of_current_results = filter_iso_dupl ~filter_of:new_unchecked_states ~filter_from:filtered_of_checked_and_current_unchecked
                                    in
                                        part_result@trans,filtered_of_current_results@new_unchecked_states
        )
        converted_unchecked
        ([],[])
        (
            fun (trans_part1, new_unchecked_part1) (trans_part2, new_unchecked_part2) -> 
                let trans_res = trans_part1@trans_part2
                and filtered_part2 = filter_iso_dupl ~filter_of:new_unchecked_part1 ~filter_from:new_unchecked_part2
                in
                    trans_res,new_unchecked_part1@filtered_part2

        )
let rec _parexplore_ss ~(rules:react list) ~(max_steps:int) ~(current_step:int) ~(checked:Big.t list) ~unchecked =
        if current_step < max_steps then
            match unchecked with
            | [] -> [],checked,current_step
            | _ ->
                let res_trans,res_unchecked = _pargen_of_trans_and_unique_states ~rules ~checked ~unchecked
                in
                    let given_transitions,given_unique_states,last_reached_step = _parexplore_ss ~rules ~max_steps ~current_step:(current_step+1) ~checked:(checked@unchecked) ~unchecked:res_unchecked
                    in
                        res_trans@given_transitions,given_unique_states,last_reached_step
                
        else
            [],checked,current_step
let parexplore_ss ~(s0:Big.t) ~(rules:react list) ~(max_steps:int) =
    let checked = []
    and current_step = 0 
    and unchecked = [s0]
    in
        _parexplore_ss ~rules:rules ~max_steps ~current_step ~checked ~unchecked
let rec _norm_ss trans unique_states = 
    match unique_states with
    | [] -> []
    | us::rest_states ->
        let normlaised,rest_trans = translate_all_iso_trans us trans
        in
            normlaised@_norm_ss rest_trans rest_states
let norm_ss trans unique_states =
    _norm_ss trans unique_states
let parse_trans_unsafe ~(init:Big.t) ~(result:Big.t) (part:Iso.t) (residue:Fun.t) label = 
    let result = {init_state=init ; res_state=result ; participants=part ; residue=residue ; react_label=label}
    in
        result
let parnorm_ss trans unique_states = 
    let pus = Parmap.L unique_states
    in
        Parmap.parfold 
            (fun us res -> 
                let part_res,_ = translate_all_iso_trans us trans
                in
                    part_res@res
            ) 
            pus 
            [] 
            (fun pr1 pr2 -> pr1@pr2)
let find_equal_state_index_by_structure s lois =
    let _, idx = List.fold_left (fun (res_flag,res_idx) (cs,i) -> if not res_flag && cs = s then true,i else false,res_idx) (false,-1) lois
    in
        match idx with
        | -1 -> raise (invalid_arg "equal state not found!")
        | _ -> idx
let index_transitions_by_structure transitions indexed_unique_states =
    List.map
        (fun t ->  
            let idx_of_init = find_equal_state_index_by_structure t.init_state indexed_unique_states
            and idx_of_res = find_equal_state_index_by_structure t.res_state indexed_unique_states
            in
                (t,idx_of_init,idx_of_res)
        )  
        transitions
let parindex_transitions_by_physical_address transitions indexed_unique_states =
    Parmap.parmap
        (fun t ->  
            let idx_of_init = find_equal_state_index_by_structure t.init_state indexed_unique_states
            and idx_of_res = find_equal_state_index_by_structure t.res_state indexed_unique_states
            in
                (t,idx_of_init,idx_of_res)
        )  
        transitions
let explore_ss_and_index ~(s0:Big.t) ~(rules:react list) ~(max_steps:int) =
    let checked = []
    and unchecked = [s0]
    and current_step = 0 
    in
        let (raw_result,unique_states,performed_steps) = _explore_ss ~rules ~max_steps ~current_step ~checked ~unchecked 
        in
            let normalized_result = norm_ss raw_result unique_states
            and indexed_unique_states = List.mapi (fun i s -> (s,i)) unique_states
            in
                index_transitions_by_structure normalized_result indexed_unique_states,indexed_unique_states,performed_steps
let parexplore_ss_and_index ~(s0:Big.t) ~(rules:react list) ~(max_steps:int) =
    let checked = []
    and current_step = 0 
    and unchecked = [s0]
    in
        let (raw_result,unique_states,performed_steps) = _parexplore_ss ~rules:rules ~max_steps ~current_step ~checked ~unchecked
        in
        let normalized_result = parnorm_ss raw_result unique_states
            and indexed_unique_states = List.mapi (fun i s -> (s,i)) unique_states
            in
                let normalized_parseq = Parmap.L normalized_result
                in
                parindex_transitions_by_physical_address normalized_parseq indexed_unique_states,indexed_unique_states,performed_steps