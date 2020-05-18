open Bigraph
(*
let react_label_header = "react label"
let state_index_header = "state index"
let state_header = "state representation"
let init_state_index_header = "init state idx"
let res_state_index_header = "res state idx"
let participant_header = "init state 2 react_lhs iso"
let residue_header = "residue of init in res state"
let res_state = "res state actual representation"
*)
let timestamp_string () =
    string_of_float (Unix.time ())

let transistions_to_sll its = 
    let trans_rest = List.fold_left 
        (
            fun res (t,ii,ri) -> 
                let isi = string_of_int ii
                and rsi = string_of_int ri
                and rl = t.TBrs.rl
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
let states_to_sll ius =
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

let export_ss_csv its ius =
    let trans_header = TBrs.trans_header  
    and states_header = TBrs.states_header in
    let transitions = trans_header :: transistions_to_sll its
    and states = states_header :: states_to_sll ius
    and timestamp = timestamp_string ()
    in
        Csv.save ("transitions_"^(timestamp)^".csv") transitions;
        Csv.save ("states_"^(timestamp)^".csv") states
        
let append_trans_csv ?(first_time=false) trans file =
    let trans_header = TBrs.trans_header in
    let transitions = transistions_to_sll trans in
    let content = if first_time then trans_header :: transitions else transitions in
    Csv.save file content
