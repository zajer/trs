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
                res_state=translated.res_state; 
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
let rec _parexplore_ss ~(rules:react list) ~(max_steps:int) ~(current_step:int) ~(checked:Big.t list) ~(unchecked:Big.t list) =
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
                                    let given_transitions,given_unique_states,last_reached_step = _parexplore_ss ~rules ~max_steps ~current_step:new_current_step ~checked:new_checked ~unchecked:new_unchecked
                                    in
                                        part_result@given_transitions,given_unique_states,last_reached_step
        else
            [],checked,current_step
let parexplore_ss ~(s0:Big.t) ~(rules:react list) ~(max_steps:int) ~ncores:_ =
    let checked = []
    and unchecked = [s0]
    and current_step = 0 
    and _ = Parmap.L rules
    in
        _parexplore_ss ~rules:rules ~max_steps ~current_step ~checked ~unchecked