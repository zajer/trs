open Bigraph
type react = { label:string; lhs:Big.t; rhs:Big.t; f_sm:Fun.t option; f_rnm:Fun.t}
type t = { is:Big.t; rs:Big.t ; rf:Fun.t ; p:Iso.t ; rl:string}
let trans_to_string t =
    let init_state_label = "Init state:"
    and res_state_label = "Res state:"
    and residue_fun_label = "Residue fun:"
    and participant_label = "Participants:"
    in
        let init_state = init_state_label^"\n"^(Big.to_string t.rs)
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
        List.fold_right 
            (
                fun t (res_eq,res_neq) -> 
                    if Big.key t.rs = patt_key && Big.equal t.rs patt then
                            t::res_eq,res_neq
                    else
                        res_eq,t::res_neq
            )
            rest
            ([],[])
let translate_all ors ttl =
    List.fold_right (fun t res -> translate_trans ~translated:t ~output_res_state:ors::res) ttl []
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
