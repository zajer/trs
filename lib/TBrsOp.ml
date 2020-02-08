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
(*
    Przyjmuje wzorzec i pogrupowaną indeksowaną listę dwugrafów (loib).
    Zwraca izomorficzny do wzorca dwugraf z loib wraz indeksem do niego przypisanym oraz informację czy jakikolwiek izomorficzny dwugraf został znaleziony.
    Jeżeli nie znaleziono izomorficznego dwugrafu to jako dwugraf zwracana jest tożsamość eps i indeks -1.
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
(* 
    Zwraca wszystkie pary (Big.t * int) z reindex_from, które nie występują w reindex_of. 
    Dodatkowo zwraca izomorfizm indeksów z rfr na rof dla elementów rfr, które występują w rof.
    Założenia 1: rof i rfr są pogrupowane tzn. nie ma dwóch izomorficznych dwugrafów na żadnej liście, które miałyby różne indeksy.
    Uproszczając: na żadnej liście nie ma dwóch izomorficznych do siebie dwugrafów.
*)
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
let _gen_trans_and_unique_states 
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
    let res_su = step_grouped_iso_res ms rules
    in
        let indexed_res_states, initially_indexed_transitions = initial_indexing res_su ~init_state_idx:ms_idx  ~checked_unchecked_sum:c_uc_sum
        in
            let filtered_of_checked,iso_checked = filter_and_reindex_duplicates ~reindex_of:checked ~reindex_from:indexed_res_states 
            in
                let trans_reindexed_by_checked = apply_reindexing initially_indexed_transitions iso_checked
                and filtered_of_unchecked,iso_unchecked = filter_and_reindex_duplicates ~reindex_of:unchecked ~reindex_from:filtered_of_checked
                in
                    let trans_reindexed_by_unchecked = apply_reindexing trans_reindexed_by_checked iso_unchecked
                    and filtered_of_results, iso_results = filter_and_reindex_duplicates ~reindex_of:new_unchecked_states ~reindex_from:filtered_of_unchecked
                    in
                        let trans_reindexed_by_results = apply_reindexing trans_reindexed_by_unchecked iso_results
                        and my_new_unchecked_states_reindexed,iso_reindexing = regen_indexing (c_uc_sum+new_unchecked_states_number) filtered_of_results
                        in
                            let my_trans = apply_reindexing trans_reindexed_by_results iso_reindexing
                            in
                                my_trans@trans, 
                                my_new_unchecked_states_reindexed@new_unchecked_states,
                                (List.length my_new_unchecked_states_reindexed)
let _pargen_of_trans_and_unique_states ~(rules:react list) ~(checked:(Big.t * int) list) ~unchecked =
    let converted_unchecked = Parmap.L unchecked
    and checked_unchecked_sum = List.length checked + List.length unchecked
    in
    Parmap.parfold
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
        converted_unchecked
        ([],[],0)
        (
            fun (trans_part1, new_unchecked_part1,new_unchecked_length_part1) (trans_part2, new_unchecked_part2,new_unchecked_length_part2) -> 
                let filtered_part2,iso_part_2_to_1 = filter_and_reindex_duplicates ~reindex_of:new_unchecked_part1 ~reindex_from:new_unchecked_part2
                and new_length = new_unchecked_length_part1 + new_unchecked_length_part2
                in
                    let trans_part2_reindexed_by_part1,trans_part2_unique = apply_reindexing_exclude_rest trans_part2 iso_part_2_to_1
                    and new_unchecked_part2_reindexed,iso_part2_reindex = regen_indexing (checked_unchecked_sum+new_unchecked_length_part1) filtered_part2
                    in
                        let trans_part2_reindexed_by_shift = apply_reindexing trans_part2_unique iso_part2_reindex
                        in
                            trans_part1@trans_part2_reindexed_by_part1@trans_part2_reindexed_by_shift,new_unchecked_part1@new_unchecked_part2_reindexed,new_length
        )
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
let parexplore_ss ~(s0:Big.t) ~(rules:react list) ~(max_steps:int) =
    let checked = []
    and current_step = 0 
    and unchecked = [s0,0]
    in
        _parexplore_ss ~rules:rules ~max_steps ~current_step ~checked ~unchecked
        

