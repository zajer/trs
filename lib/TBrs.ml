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
let rec translate_all_iso_trans (patt:Big.t) (rest:trans list) = 
    match rest with 
    | [] -> [],[]
    | t2c::rest' -> 
        if Big.equal patt t2c.res_state then
            let eq_translated,neq = translate_all_iso_trans patt rest'
            in translate_trans ~translated:t2c ~output_res_state:patt::eq_translated,neq
        else
            let eq_translated,neq = translate_all_iso_trans patt rest'
            in eq_translated,t2c::neq
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
    let raw_result = List.fold_left (fun res r -> apply_trr b r @ res) [] lr
    in  
        let unified_result = unify_based_on_iso_res_states raw_result
        in
            unified_result
let does_state_exist_in_checked state checked =
    List.exists (fun ic -> Big.equal ic state) checked
let get_equal_state_from_checked state checked = 
    List.fold_left 
        (
            fun res ic -> 
                if Big.equal res Big.id_eps then
                    if Big.equal state ic then
                        ic
                    else
                        res
                else
                    res  
        )
        Big.id_eps
        checked
let unify_with_checked su checked =
    List.fold_left 
    (
        fun (res_unique,res_unified) (res_big, tl) ->
            let does_exist = does_state_exist_in_checked res_big checked
                in
                    if does_exist then
                        let from_checked = get_equal_state_from_checked res_big checked 
                        in
                            let unified_part_res, _ = translate_all_iso_trans from_checked tl
                            in
                               res_unique,[from_checked, unified_part_res]@res_unified
                    else
                        [res_big, tl]@res_unique,res_unified 
    )
    ([],[])
    su
let rec _explore_ss ~(rules:react list) ~(max_steps:int) ~(current_step:int) ~(checked:Big.t list) ~(unchecked:Big.t list) =
        match unchecked with
        | [] -> [],checked,current_step
        | s::rest -> 
            let res_su = step_unified_res s rules 
            in
                let unieque,unified_with_checked = unify_with_checked res_su checked  
                in 
                    let part_new_unchecked, part_result1  = List.split unieque
                    and _ , part_result2 = List.split unified_with_checked
                    in
                        let part_result = List.concat part_result1 @ List.concat part_result2
                        in
                            if current_step < max_steps then
                                let new_checked = s::checked
                                and new_unchecked = rest@part_new_unchecked
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
