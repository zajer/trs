open Bigraph
type react = { label:string; lhs:Big.t; rhs:Big.t; f_sm:Fun.t option; f_rnm:Fun.t}
type trans = { res_state:Big.t ; residue:Fun.t ; participants:Iso.t ; react_label:string}
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
    and is_label_not_empty = l = ""
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
        {res_state=res_b;residue=res_f;participants=res_iso; react_label=r.label}
let apply_trr (b:Big.t) (r:react) =
    let occs = Big.occurrences ~target:b ~pattern:r.lhs
    in  
        List.fold_left (fun res occ -> apply_trr_with_occ b r occ :: res) [] occs
let translate_iso_trans ~(from_t:trans) ~(to_t:trans) =
    let translation = TBig.translate_equal ~from_b:from_t.res_state ~to_b:to_t.res_state
    in
        let res_residue_fun = Utils.transform_fun_dom from_t.residue translation
        in
            {
                res_state=to_t.res_state; 
                residue=res_residue_fun;
                participants=from_t.participants;
                react_label=from_t.react_label
            }
let rec translate_all_iso_trans (patt:trans) (rest:trans list) = 
    match rest with 
    | [] -> [],[]
    | t2c::rest' -> 
        if Big.equal patt.res_state t2c.res_state then
            let eq_translated,neq = translate_all_iso_trans patt rest'
            in translate_iso_trans ~from_t:t2c ~to_t:patt::eq_translated,neq
        else
            let eq_translated,neq = translate_all_iso_trans patt rest'
            in eq_translated,t2c::neq
let rec unify_based_on_iso_res_states lot = 
    match lot with
    | [] -> []
    | t::rest -> 
        let merged_with_t, rest' = translate_all_iso_trans t rest
        in 
            let merged_with_rest = unify_based_on_iso_res_states rest'
            in 
                merged_with_t @ merged_with_rest
let step b lr =
    let raw_result = List.fold_left (fun res r -> apply_trr b r @ res) [] lr
    in  
        let unified_result = unify_based_on_iso_res_states raw_result
        in
            unified_result

