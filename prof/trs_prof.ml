open Bigraph
open Tracking_bigraph

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
let [@landmark] is_residual_node_mapping_function_correct f_rnm ~(lhs:Big.t) ~(rhs:Big.t) =
    let is_frnm_not_exceeding = IntSet.max_elt (Fun.dom f_rnm) <= Some rhs.p.n && IntSet.max_elt (Fun.codom f_rnm) <= Some lhs.p.n
    in
        is_frnm_not_exceeding
let [@landmark] parse_react l ~(lhs:Big.t) ~(rhs:Big.t) ~(f_sm:Fun.t option) ~(f_rnm:Fun.t) =
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
let [@landmark] apply_trr_with_occ (b:Big.t) (r:react) (lhs_occ:Big.occ) =
    let res_b,res_f = TBig.rewrite lhs_occ ~target:b ~r0:r.lhs ~r1:r.rhs ~f_s:r.f_sm ~f_r1_r0:r.f_rnm
    and res_iso = match lhs_occ with | iso, _, _ -> iso
    in
        { is=b; rs=res_b;rf=res_f;p=res_iso; rl=r.label}
let [@landmark] apply_trr (b:Big.t) (r:react) =
    let occs = Big.occurrences ~target:b ~pattern:r.lhs
    in  
        List.fold_left (fun res occ -> apply_trr_with_occ b r occ :: res) [] occs
let [@landmark] translate_trans ~(output_res_state:Big.t) ~(translated:t) =
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
open Onauty  
let [@landmark] split_into_iso_trans (patt:Big.t) (rest:t list) =
    let patt_dig = Digraph.big_2_dig patt
    in
    let patt_key = Digraph.hash_graph patt_dig
    and patt_graph = Dig2graph.dig_2_graph patt_dig
    and eq = Iso.are_digraphs_iso
    in
        List.fold_left 
            (
                fun  (res_eq,res_neq) t-> 
                    let checked_dig = Digraph.big_2_dig t.rs
                    in
                        let checked_graph = Dig2graph.dig_2_graph checked_dig
                        in
                            if (Digraph.hash_graph checked_dig = patt_key)[@landmark "key_check"] && (eq checked_graph patt_graph)[@landmark "equality_check"] then
                                    t::res_eq,res_neq
                            else
                                res_eq,t::res_neq
            )
            ([],[])
            rest
let translate_all ors ttl =
    List.fold_left (fun res t -> translate_trans ~translated:t ~output_res_state:ors::res) [] ttl
let [@landmark] translate_all_iso_trans (patt:Big.t) (all:t list) =
    let eq,neq = split_into_iso_trans patt all    
    in
        let teq = translate_all patt eq
        in
            teq,neq
let [@landmark] rec unify_based_on_iso_res_states lot = 
    match lot with
    | [] -> []
    | t::rest -> 
        let merged_with_t, rest' = translate_all_iso_trans t.rs rest
        in 
            let merged_with_rest = unify_based_on_iso_res_states rest'
            in 
                [t.rs,t::merged_with_t] @ merged_with_rest
let [@landmark] rec group_based_on_iso_res_states lot = 
    match lot with
        | [] -> []
        | t::rest -> 
        let equal_with_t, rest' = split_into_iso_trans t.rs rest
        in 
            let grouped_rest = group_based_on_iso_res_states rest'
            in 
                [t.rs,t::equal_with_t] @ grouped_rest
let [@landmark] split_into_iso_groups_of_trans (patt:Big.t) (rest:(Big.t * t list) list) =
    let patt_dig = Digraph.big_2_dig patt
    in
    let patt_key = Digraph.hash_graph patt_dig
    and patt_graph = Dig2graph.dig_2_graph patt_dig
    and eq = Iso.are_digraphs_iso
    in
        List.fold_left 
            (
                fun  (res_eq,res_neq) (b,tl)-> 
                    let checked_dig = Digraph.big_2_dig b
                    in
                        let checked_graph = Dig2graph.dig_2_graph checked_dig
                        in
                            if (Digraph.hash_graph checked_dig = patt_key)[@landmark "key_check"] && (eq checked_graph patt_graph)[@landmark "equality_check"] then
                                    (b,tl)::res_eq,res_neq
                            else
                                res_eq,(b,tl)::res_neq
            )
            ([],[])
            rest
let [@landmark] rec merge_grouped_based_on_iso_res_states lot = 
    match lot with
        | [] -> []
        | (b,tl)::rest -> 
        let equal_with_t, rest' = split_into_iso_groups_of_trans b rest in
        let equal_with_t_conv = List.map (fun (_,tl) -> tl) equal_with_t |> List.flatten in 
            let grouped_rest = merge_grouped_based_on_iso_res_states rest'
            in 
                [b,tl@equal_with_t_conv] @ grouped_rest
let [@landmark] rec group_based_on_iso_res_statesV2 aot =
    let aot_l = Array.length aot in
    if aot_l > 200 then
    (
        let pivot_point =  aot_l / 2 in
        let sub_aot1 = Array.sub aot 0 pivot_point
        and sub_aot2 = Array.sub aot pivot_point (aot_l - pivot_point) in
        let res1 = group_based_on_iso_res_statesV2 sub_aot1
        and res2 = group_based_on_iso_res_statesV2 sub_aot2 in
        merge_grouped_based_on_iso_res_states res1@res2
    )
    else
        group_based_on_iso_res_states (Array.to_list aot)


let [@landmark] split_into_iso_trans_indexed (patt:Big.t) (rest:(t*int*int) list) =
    let patt_dig = Digraph.big_2_dig patt
    and eq = Iso.are_digraphs_iso
    in
    let patt_key = Digraph.hash_graph patt_dig
    and patt_graph = Dig2graph.dig_2_graph patt_dig
    in
        List.fold_left 
            (
                fun  (res_eq,res_neq) (t,i1,i2)-> 
                    let checked_dig = Digraph.big_2_dig t.rs
                    in
                    let checked_graph = Dig2graph.dig_2_graph checked_dig
                    in
                    if (Digraph.hash_graph checked_dig = patt_key)[@landmark "key_check"] && (eq checked_graph patt_graph)[@landmark "equality_check"] then
                        (t,i1,i2)::res_eq,res_neq
                    else
                        res_eq,(t,i1,i2)::res_neq
            )
            ([],[])
            rest
let [@landmark] rec group_indexed_based_on_iso_res_states lot = 
    match lot with
        | [] -> []
        | (t,i1,i2)::rest -> 
            let equal_with_t, rest' = split_into_iso_trans_indexed t.rs rest
            in 
                let grouped_rest = group_indexed_based_on_iso_res_states rest'
                in 
                    [t.rs,(t,i1,i2)::equal_with_t] @ grouped_rest
let [@landmark] find_previous_iso_res_trans_opt aot i_fin rs =
    let found_idx = ref (-1) 
    and is_found = ref false
    and patt_dig = Digraph.big_2_dig rs
    and eq = Iso.are_digraphs_iso
    in
    let patt_key = Digraph.hash_graph patt_dig
    and patt_graph = Dig2graph.dig_2_graph patt_dig
    in
        Array.iteri 
            (
                fun i_curr (t_ch,_,_) -> 
                    let checked_dig = Digraph.big_2_dig t_ch.rs
                    in
                        let checked_graph = Dig2graph.dig_2_graph checked_dig
                        in
                            if not !is_found && i_curr < i_fin && (Digraph.hash_graph checked_dig = patt_key)[@landmark "key_check"] && (eq checked_graph patt_graph)[@landmark "equality_check"] then
                            (
                                found_idx := i_curr;
                                is_found := true
                            )
            )
            aot;
            if !is_found then
                Some !found_idx
            else
                None
let [@landmark] map_trans_to_previous_found aot =
    Array.mapi
        (
            fun i (t_m,isi_m,rsi_m) ->
                let iso_idx_opt = find_previous_iso_res_trans_opt aot i t_m.rs
                in
                match iso_idx_opt with
                | None -> i,t_m,isi_m,rsi_m
                | Some iso_idx -> iso_idx,t_m,isi_m,rsi_m
        )
        aot
let [@landmark] split_into_eq_mapped_trans patt aomt =
    let patt_idx,_,_,_ = patt
    in
    List.fold_left 
            (
                fun  (res_eq,res_neq) (idx,t,i1,i2)-> 
                    if patt_idx = idx then
                        (t,i1,i2)::res_eq,res_neq
                    else
                        res_eq,(idx,t,i1,i2)::res_neq
            )
            ([],[])
            aomt
let [@landmark] rec group_mapped_trans aomt =
    match aomt with
        | [] -> []
        | mtrans::rest -> 
        let equal_with_t, rest' = split_into_eq_mapped_trans mtrans rest
        in 
            let grouped_rest = group_mapped_trans rest'
            and _,trans,isi,rsi = mtrans
            in 
                [trans.rs,(trans,isi,rsi)::equal_with_t] @ grouped_rest

let [@landmark] group_indexed_based_on_iso_res_statesV2 lot =
    let mapped_aot = Array.of_list lot |> map_trans_to_previous_found
    in
        group_mapped_trans (Array.to_list mapped_aot)
let [@landmark] step b lr =
    List.fold_left (fun res r -> apply_trr b r @ res) [] lr
let [@landmark] step_grouped_iso_res b lr =
    let raw_result = List.fold_left (fun res r -> apply_trr b r @ res) [] lr
        in  
            let grouped_result = group_based_on_iso_res_statesV2 (raw_result |> Array.of_list)
            in
                grouped_result

let [@landmark] find_iso_indexed_big (patt:Big.t) (loib:(Big.t*int) list) =
    let patt_dig = Digraph.big_2_dig patt
    and eq = Iso.are_digraphs_iso
    in
    let patt_key = Digraph.hash_graph patt_dig
    and patt_graph = Dig2graph.dig_2_graph patt_dig
    in
        List.fold_left 
            (
                fun (res_eq,res_neq,found) (t,i)  -> 
                    let checked_dig = Digraph.big_2_dig t
                    in
                    let checked_graph = Dig2graph.dig_2_graph checked_dig
                    in
                    if not found && (Digraph.hash_graph checked_dig = patt_key) [@landmark "key_check"]&& (eq checked_graph patt_graph)[@landmark "equality_check"] then
                        (t,i),res_neq,true
                    else
                        res_eq,(t,i)::res_neq,found
            )
            ( (Big.id_eps,-1) ,[],false)
            loib
     
(* reindex_from contains less elements than reindex_of  *)
let [@landmark] filter_and_reindex_duplicates_case1 ~reindex_of:(rof:(Big.t * int) list ) ~reindex_from:(rfr:(Big.t * int) list ) =
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
let [@landmark] filter_and_reindex_duplicates_case2 ~reindex_of:(rof:(Big.t * int) list ) ~reindex_from:(rfr:(Big.t * int) list ) =
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
let [@landmark] filter_and_reindex_duplicatesV2 ~reindex_of:(rof:(Big.t * int) list ) ~reindex_from:(rfr:(Big.t * int) list ) =
    let rfr_count = List.length rfr
    and rof_count = List.length rof
    in
        if rfr_count >= rof_count then filter_and_reindex_duplicates_case2 ~reindex_of:rof ~reindex_from:rfr
        else filter_and_reindex_duplicates_case1 ~reindex_of:rof ~reindex_from:rfr
module HashMap = Map.Make(struct
    let compare = Z.compare
    type t = Z.t
  end)
let [@landmark] filter_and_reindex_duplicatesV3 ~reindex_of:(rof:(Big.t * int) list ) ~reindex_from:(rfr:(Big.t * int) list ) =
    let rof_mapped = List.map 
        (
        fun (b,i) -> 
                let dig = Digraph.big_2_dig b 
                in
                Digraph.hash_graph dig,b,i
        )
        rof
    in
        let rof_map = List.fold_left 
            (
                fun map (h,b,i) -> 
                match HashMap.find_opt h map with
                | None -> HashMap.add h [(b,i)] map
                | Some l -> HashMap.add h ((b,i)::l) map
            )
            HashMap.empty
            rof_mapped
        in
        List.fold_left 
        (
            fun (rest_unique,rest_isos) (b_rfr,rfr_idx) -> 
                let b_rfr_hash = Digraph.big_2_dig b_rfr |> Digraph.hash_graph
                in
                let b_with_equal_hash = HashMap.find_opt b_rfr_hash rof_map
                in
                    match b_with_equal_hash with
                    | None -> (b_rfr,rfr_idx)::rest_unique,rest_isos
                    | Some l -> 
                        let (_ ,rof_idx), _,is_found = find_iso_indexed_big b_rfr l
                        in
                            if is_found then
                                rest_unique,(rfr_idx,rof_idx)::rest_isos
                            else
                                (b_rfr,rfr_idx)::rest_unique,rest_isos
        )
        ([],[])
        rfr
    
let [@landmark] regen_indexing (ci:int) (ri:(Big.t * int) list) =
    let indexing = List.mapi (fun i (b,_) -> b,i+ci) ri
    in
        let iso = List.map2 (fun (_,oi) (_,ri) -> (oi,ri)) ri indexing
        in
            indexing,iso
let [@landmark] apply_reindexing loit ridx =
    List.map
        (
            fun (t,init_idx,res_idx) ->
                let res_idx_reindexed = List.find_opt (fun (orig_idx,_) -> orig_idx = res_idx ) ridx
                    in
                        match res_idx_reindexed with
                        | None -> t,init_idx,res_idx
                        | Some (_, res_idx') -> t,init_idx,res_idx'
        )
        loit
let [@landmark] apply_reindexing_exclude_rest loit ridx =
        List.fold_right
            (
                fun (t,init_idx,res_idx) (res_app,res_exc) ->
                    let res_idx_reindexed = List.find_opt (fun (orig_idx,_) -> orig_idx = res_idx ) ridx
                        in
                            match res_idx_reindexed with
                            | None -> res_app,(t,init_idx,res_idx)::res_exc
                            | Some (_, res_idx') -> (t,init_idx,res_idx')::res_app,res_exc
            )
            loit
            ([],[])        
let [@landmark] initial_indexing (btll:(Big.t * t list) list ) ~(init_state_idx:int) ~(checked_unchecked_sum:int) =
        let mapped = List.mapi
            (
                fun res_state_idx_no_shift (b,tl) ->
                    let init_val_of_res_state_idx = res_state_idx_no_shift+checked_unchecked_sum+1
                    in
                        let indexed_transitions = 
                            List.fold_left (fun res t -> (t,init_state_idx,init_val_of_res_state_idx)::res) [] tl
                        in
                            (b,init_val_of_res_state_idx),indexed_transitions
            )
            btll
        in
        List.fold_right
        (
            fun (ib,its) (res_ib,res_its) ->
                ib::res_ib,its@res_its
        )
        mapped
        ([],[])
let [@landmark] initially_index_trans init_idx trans =
    List.map 
    (
        fun t -> t,init_idx,-1
    )
    trans    
let [@landmark] _gen_trans_and_init_index rules unchecked =
    List.fold_left 
    (
    fun res_trans (uncheck_state,us_idx) ->
        step uncheck_state rules |> initially_index_trans us_idx |> List.rev_append res_trans
    )
    []
    unchecked
let [@landmark] _gen_unique_states grouped_indexed_trans ~checked ~unchecked ~new_unchecked_propositions c_uc_sum = 
    let filtered_of_all,iso_all = filter_and_reindex_duplicatesV3 ~reindex_of:(checked@unchecked) ~reindex_from:new_unchecked_propositions
    in 
        let reindexed_by_all, my_new_unchecked = apply_reindexing_exclude_rest grouped_indexed_trans iso_all
        in
            let my_new_unchecked_states_reindexed,iso_reindexing = regen_indexing (c_uc_sum) filtered_of_all
            in
                let my_trans = (apply_reindexing my_new_unchecked iso_reindexing)@reindexed_by_all
                (*and _ = "new unchecked propositions length:"^(string_of_int (List.length new_unchecked_propositions)) |> print_endline
                and _ = "my new unchecked length:"^(string_of_int (List.length my_new_unchecked_states_reindexed )) |> print_endline*)
                in
                my_trans, 
                my_new_unchecked_states_reindexed,
                (List.length my_new_unchecked_states_reindexed);;
let [@landmark] _gen_trans_and_unique_states 
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
    (*and _ = "liczba sprawdzonych, teraz sprawdzanych i nowych niesprawdzonych:"^(string_of_int (List.length (checked@unchecked@new_unchecked_states))) |> print_endline*)
    in
        let indexed_res_states, initially_indexed_transitions = initial_indexing res_su ~init_state_idx:ms_idx  ~checked_unchecked_sum:c_uc_sum
        in
        let filtered_of_all,iso_all = filter_and_reindex_duplicatesV2 ~reindex_of:(checked@unchecked@new_unchecked_states) ~reindex_from:indexed_res_states 
        in 
            let reindexed_by_all, my_new_unchecked = apply_reindexing_exclude_rest initially_indexed_transitions iso_all
            in
                let my_new_unchecked_states_reindexed,iso_reindexing = regen_indexing (c_uc_sum+new_unchecked_states_number) filtered_of_all
                in
                    let my_trans = (apply_reindexing my_new_unchecked iso_reindexing)@reindexed_by_all
                    in
        (*
            let filtered_of_checked,iso_checked = filter_and_reindex_duplicatesV2 ~reindex_of:checked ~reindex_from:indexed_res_states 
            in
                let trans_reindexed_by_checked,trans_unique_p1 = apply_reindexing_exclude_rest initially_indexed_transitions iso_checked
                and filtered_of_unchecked,iso_unchecked = filter_and_reindex_duplicatesV2 ~reindex_of:unchecked ~reindex_from:filtered_of_checked
                in
                    let trans_reindexed_by_unchecked,trans_unique_p2 = apply_reindexing_exclude_rest trans_unique_p1 iso_unchecked
                    and filtered_of_results, iso_results = filter_and_reindex_duplicatesV2 ~reindex_of:new_unchecked_states ~reindex_from:filtered_of_unchecked
                    in
                        let trans_reindexed_by_results,trans_unique_p3 = apply_reindexing_exclude_rest trans_unique_p2 iso_results
                        and my_new_unchecked_states_reindexed,iso_reindexing = regen_indexing (c_uc_sum+new_unchecked_states_number) filtered_of_results
                        in
                            let my_trans = (apply_reindexing trans_unique_p3 iso_reindexing)@trans_reindexed_by_checked@trans_reindexed_by_unchecked@trans_reindexed_by_results
                            in*)
                                my_trans@trans, 
                                my_new_unchecked_states_reindexed@new_unchecked_states,
                                ( (List.length my_new_unchecked_states_reindexed)+new_unchecked_states_number )
let [@landmark] _pargen_of_trans_and_unique_states ~(rules:react list) ~(checked:(Big.t * int) list) ~unchecked =
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
        ([],[],0);;
let [@landmark] _pargen_of_trans_and_unique_statesV2 ~(rules:react list) ~(checked:(Big.t * int) list) ~unchecked =
    let checked_unchecked_sum = List.length checked + List.length unchecked
    and initially_indexed_trans = _gen_trans_and_init_index rules unchecked
    in
        let new_unchecked_propositions,grouped_trans = group_indexed_based_on_iso_res_states initially_indexed_trans |> List.mapi (fun i (b,tl) -> (b,i),tl) |> List.split
        in
        _gen_unique_states (grouped_trans |> List.flatten) ~checked ~unchecked ~new_unchecked_propositions checked_unchecked_sum;;
let [@landmark] split_into_iso_trans_list (patt:Big.t) (rest:(Big.t * t list) list) =
    let patt_dig = Digraph.big_2_dig patt
    and eq = Iso.are_digraphs_iso
    in
    let patt_key = Digraph.hash_graph patt_dig
    and patt_graph = Dig2graph.dig_2_graph patt_dig
    in
        List.fold_left 
            (
                fun  (res_eq,res_neq) (b,tl)-> 
                    let checked_dig = Digraph.big_2_dig b
                    in
                    let checked_graph = Dig2graph.dig_2_graph checked_dig
                    in
                    if (Digraph.hash_graph checked_dig = patt_key)[@landmark "key_check"] && (eq checked_graph patt_graph)[@landmark "equality_check"] then
                        tl::res_eq,res_neq
                    else
                        res_eq,(b,tl)::res_neq
            )
            ([],[])
            rest;;
let [@landmark] rec merge_iso_groups logt =
    match logt with
        | [] -> []
        | (b,tl)::rest -> 
            let equal_with_t, rest' = split_into_iso_trans_list b rest
            in 
                let grouped_rest = merge_iso_groups rest'
                in
                let my_res = b,(tl@(List.flatten equal_with_t))
                in
                my_res :: grouped_rest


let [@landmark] _pargen_of_trans_and_unique_statesV3 ~(rules:react list) ~(checked:(Big.t * int) list) ~unchecked =
    let checked_unchecked_sum = List.length checked + List.length unchecked
    and grouped_trans = List.fold_left (fun logt (s,_) -> (step_grouped_iso_res s rules)::logt ) [] unchecked |> List.flatten
    in
        let new_unchecked_propositions,initially_indexed_trans = merge_iso_groups grouped_trans |> List.mapi (fun i (b,tl) -> (b,i),List.map (fun t -> t,i,-1) tl ) |> List.split
        in
                _gen_unique_states (initially_indexed_trans |> List.flatten) ~checked ~unchecked ~new_unchecked_propositions checked_unchecked_sum;;
let rec _parexplore_ss ~(rules:react list) ~(max_steps:int) ~(current_step:int) ~(checked:(Big.t*int) list) ~unchecked =
        if current_step < max_steps then
            match unchecked with
            | [] -> [],checked,[],current_step
            | _ ->
                let res_trans,res_unchecked,_ = _pargen_of_trans_and_unique_statesV3 ~rules ~checked ~unchecked
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
        
        open Bigraph

let s0_to_parse =
"
{(0, AL:0),(1, AF:4),(2, UAV:1),(3, AF:4),(4, AF:4),(5, UAV:1),(6, AF:4),(7, UAV:1),(8, AF:4),(9, AF:4),(10, AF:4),(11, AF:4),(12, AF:4),(13, AF:4),(14, AF:4),(15, AF:4)}
1 16 0
1000000000000000
0101101011111111
0010000000000000
0000000000000000
0000000000000000
0000010000000000
0000000000000000
0000000100000000
0000000000000000
0000000000000000
0000000000000000
0000000000000000
0000000000000000
0000000000000000
0000000000000000
0000000000000000
0000000000000000
({}, {}, {(1, 1)})
({}, {}, {(1, 1)})
({}, {}, {(1, 1), (3, 1)})
({}, {}, {(1, 1), (8, 1)})
({}, {}, {(2, 1)})
({}, {}, {(3, 1)})
({}, {}, {(3, 1), (4, 1)})
({}, {}, {(3, 1), (9, 1)})
({}, {}, {(4, 1)})
({}, {}, {(4, 1), (6, 1)})
({}, {}, {(4, 1), (10, 1)})
({}, {}, {(5, 1)})
({}, {}, {(6, 1)})
({}, {}, {(6, 1)})
({}, {}, {(6, 1), (11, 1)})
({}, {}, {(7, 1)})
({}, {}, {(8, 1)})
({}, {}, {(8, 1), (9, 1)})
({}, {}, {(8, 1), (12, 1)})
({}, {}, {(9, 1), (10, 1)})
({}, {}, {(9, 1), (13, 1)})
({}, {}, {(10, 1), (11, 1)})
({}, {}, {(10, 1), (14, 1)})
({}, {}, {(11, 1)})
({}, {}, {(11, 1), (15, 1)})
({}, {}, {(12, 1)})
({}, {}, {(12, 1)})
({}, {}, {(12, 1), (13, 1)})
({}, {}, {(13, 1)})
({}, {}, {(13, 1), (14, 1)})
({}, {}, {(14, 1)})
({}, {}, {(14, 1), (15, 1)})
({}, {}, {(15, 1)})
({}, {}, {(15, 1)})
"
let move_lhs_to_parse =
"
{(0, AF:4),(1, UAV:1),(2, AF:4)}
1 3 2
10100
01010
00000
00001
({}, {}, {(0, 1), (2, 1)})
({}, {}, {(1, 1)})
({}, {b1}, {(0, 1)})
({}, {b2}, {(2, 1)})
({}, {l1}, {(0, 1)})
({}, {r2}, {(2, 1)})
({}, {t1}, {(0, 1)})
({}, {t2}, {(2, 1)})
"
let move_rhs_to_parse =
"
{(0, AF:4),(1, AF:4),(2, UAV:1)}
1 3 2
11000
00010
00101
00000
({}, {}, {(0, 1), (1, 1)})
({}, {}, {(2, 1)})
({}, {b1}, {(0, 1)})
({}, {b2}, {(1, 1)})
({}, {l1}, {(0, 1)})
({}, {r2}, {(1, 1)})
({}, {t1}, {(0, 1)})
({}, {t2}, {(1, 1)})
"
let estConn2AF_lhs_to_parse =
"
{(0, AF:4),(1, UAV:1),(2, AF:4),(3, UAV:1)}
1 4 2
101000
010010
000000
000101
000000
({}, {}, {(0, 1), (2, 1)})
({}, {}, {(1, 1)})
({}, {b1}, {(0, 1)})
({}, {b2}, {(2, 1)})
({}, {c2}, {(3, 1)})
({}, {l1}, {(0, 1)})
({}, {r2}, {(2, 1)})
({}, {t1}, {(0, 1)})
({}, {t2}, {(2, 1)})
"
let estConn2AF_rhs_to_parse =
"
{(0, AF:4),(1, UAV:1),(2, AF:4),(3, UAV:1)}
1 4 2
101000
010010
000000
000101
000000
({}, {}, {(0, 1), (2, 1)})
({}, {b1}, {(0, 1)})
({}, {b2}, {(2, 1)})
({}, {c2}, {(1, 1), (3, 1)})
({}, {l1}, {(0, 1)})
({}, {r2}, {(2, 1)})
({}, {t1}, {(0, 1)})
({}, {t2}, {(2, 1)})
"
let estConn1AF_lhs_to_parse =
"
{(0, AF:4),(1, UAV:1),(2, UAV:1)}
1 3 1
1000
0111
0000
0000
({}, {}, {(1, 1)})
({}, {b1}, {(0, 1)})
({}, {c2}, {(2, 1)})
({}, {l1}, {(0, 1)})
({}, {r1}, {(0, 1)})
({}, {t1}, {(0, 1)})
"
let estConn1AF_rhs_to_parse = 
"
{(0, AF:4),(1, UAV:1),(2, UAV:1)}
1 3 1
1000
0111
0000
0000
({}, {b1}, {(0, 1)})
({}, {c2}, {(1, 1), (2, 1)})
({}, {l1}, {(0, 1)})
({}, {r1}, {(0, 1)})
({}, {t1}, {(0, 1)})
"

let s0 = Big.of_string s0_to_parse
let mov_lhs = Big.of_string move_lhs_to_parse
let mov_rhs = Big.of_string move_rhs_to_parse
let estConn1AF_lhs = Big.of_string estConn1AF_lhs_to_parse
let estConn1AF_rhs = Big.of_string estConn1AF_rhs_to_parse
let estConn2AF_lhs = Big.of_string estConn2AF_lhs_to_parse
let estConn2AF_rhs = Big.of_string estConn2AF_rhs_to_parse
let mov_f_rnm = Fun.empty |> Fun.add 0 0 |> Fun.add 1 2 |> Fun.add 2 1
let estConn2AF_f_rnm = Fun.empty |> Fun.add 0 0 |> Fun.add 1 1 |> Fun.add 2 2 |> Fun.add 3 3
let estConn1AF_f_rnm = Fun.empty |> Fun.add 0 0 |> Fun.add 1 1 |> Fun.add 2 2

let mov_react = parse_react "move" ~lhs:mov_lhs ~rhs:mov_rhs ~f_sm:None ~f_rnm:mov_f_rnm
let estConn1AF_react = parse_react "estConn1AF" ~lhs:estConn1AF_lhs ~rhs:estConn1AF_rhs ~f_sm:None ~f_rnm:estConn1AF_f_rnm
let estConn2AF_react = parse_react "estConn2AF" ~lhs:estConn2AF_lhs ~rhs:estConn2AF_rhs ~f_sm:None ~f_rnm:estConn2AF_f_rnm
let rules = [mov_react;estConn1AF_react;estConn2AF_react];;

Landmark.start_profiling ();;
Curl.global_init ( Curl.CURLINIT_GLOBALALL );;
let tl,ss,uss,ms = parexplore_ss ~s0 ~rules ~max_steps:300;;
Curl.global_cleanup ();;
print_endline ("Number of transitions:" ^ ( string_of_int (List.length tl) ) );
print_endline ("Number of checked unique states:" ^ ( string_of_int (List.length ss) ) );;
print_endline ("Number of unchecked unique states:" ^ ( string_of_int (List.length uss) ) );;
(*
let keys = Hashtbl.create 30;;
List.iter 
    (fun (s,_) -> 
        
        (Hashtbl.add keys (Big.key s) s)
    ) 
    (ss@uss);;
let num_of_keys = Hashtbl.length keys;;
"Number of big keys "^(string_of_int num_of_keys) |> print_endline;;
let ks = Hashtbl.to_seq_keys keys ;;
Seq.iter 
    (
        fun k -> 
            "Key:"^(string_of_int k) |> print_endline; 
            "Num of bindings:"^(string_of_int (List.length (Hashtbl.find_all keys k))) |> print_endline
    )
    ks
    ;;
*)
(*
List.iter 
    (fun (s,_) -> 
        
        "Key:\n"^(string_of_int (Big.key s)) |> print_endline; 
        "Hash:\n"^(Z.to_string (Digraph.big_2_dig s |> Digraph.hash_graph)) |> print_endline; 
        "Big:\n"^(Big.to_string s) |> print_endline
        
    ) 
    (ss@uss);;
*)