open Bigraph
let react_label_header = "react label"
let state_index_header = "state index"
let state_header = "state representation"
let init_state_index_header = "init state idx"
let res_state_index_header = "res state idx"
let participant_header = "init state 2 react_lhs iso"
let residue_header = "residue of init in res state"

let timestamp_string () =
    string_of_float (Unix.time ())

let transistions_to_sll its = 
    let trans_header = [init_state_index_header;res_state_index_header;react_label_header;participant_header;residue_header]
    in
        let trans_rest = List.fold_left 
            (
                fun res (t,ii,ri) -> 
                    let isi = string_of_int ii
                    and rsi = string_of_int ri
                    and rl = t.TBrs.rl
                    and p = (Iso.to_string t.p)
                    and rf = (Fun.to_string t.rf)
                    in
                        let new_row = [isi;rsi;rl;p;rf]
                        in
                            [new_row]@res
            ) 
            [] 
            its
            in
                [trans_header]@trans_rest
let states_to_sll ius =
    let states_header = [state_index_header;state_header]
    in
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
            [states_header]@states_rest

let export_ss_csv its ius =
    let transitions = transistions_to_sll its
    and states = states_to_sll ius
    and timestamp = timestamp_string ()
    in
        Csv.save ("transitions_"^(timestamp)^".csv") transitions;
        Csv.save ("states_"^(timestamp)^".csv") states

