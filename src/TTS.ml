open Bigraph

type trans_raw = { is:Big.t; os:Big.t ; rf:Fun.t ; p:Iso.t ; rl:string}
type trans_exported = { in_state_idx:int;out_state_idx:int; react_label:string;participants:Iso.t;residue:Fun.t;actual_out_state:Big.t }
type state = { bigraph:Big.t;index:int }
let trans_to_string t =
  let init_state_label = "Input state:"
  and res_state_label = "Output state:"
  and residue_fun_label = "Residue fun:"
  and participant_label = "Participants fun:"
  in
      let init_state = init_state_label^"\n"^(Big.to_string t.is)
      and res_state = res_state_label^"\n"^(Big.to_string t.os)
      and residue_fun = residue_fun_label^"\n"^(Fun.to_string t.rf)
      and participants = participant_label^"\n"^(Iso.to_string t.p)
      in
          (String.concat "\n" [init_state;res_state;residue_fun;participants]);;
let _REACT_LABEL_HEADER = "react label"
let _STATE_INDEX_HEADER = "state index"
let _STATE_REPRESENTATION_HEADER = "state representation"
let _INPUT_STATE_INDEX_HEADER = "input state idx"
let _OUTPUT_STATE_INDEX_HEADER = "output state idx"
let _PARTICIPANTS_HEADER = "react lhs node -> input state node"
let _RESIDUE_HEADER = "output state node -> input state node"
let _REAL_OUTPUT_STATE_REPRESENTATION_HEADER = "output state actual representation"
let _trans_header = [_INPUT_STATE_INDEX_HEADER;_OUTPUT_STATE_INDEX_HEADER;_REACT_LABEL_HEADER;_PARTICIPANTS_HEADER;_RESIDUE_HEADER;_REAL_OUTPUT_STATE_REPRESENTATION_HEADER] 
and _states_header = [_STATE_INDEX_HEADER;_STATE_REPRESENTATION_HEADER] 
let transistions_to_losl its = 
  let trans_rest = List.fold_left 
      (
          fun res (t,ii,ri) -> 
              let isi = string_of_int ii
              and rsi = string_of_int ri
              and rl = t.rl
              and p = (Iso.to_string t.p)
              and rf = (Fun.to_string t.rf)
              and rs = (Big.to_string t.os)
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

let _default_file_name () = 
  ( ( string_of_float (Unix.time ()) )^".csv")
let export_ss_csv ?(trans_file_name= "trans_"^_default_file_name () ) ?(states_file_name = "states_"^_default_file_name () ) its ius =
  let trans_header = _trans_header  
  and states_header = _states_header in
  let transitions = trans_header :: transistions_to_losl its
  and states = states_header :: states_to_losl ius
  in
      Csv.save trans_file_name transitions;
      Csv.save states_file_name states
let append_trans_csv ?(first_time=false) trans file =
  let out_channel = open_out_gen [Open_creat; Open_append] 0o666 file |> Csv.to_channel in
  let transitions = transistions_to_losl trans in
  let content = if first_time then _trans_header :: transitions else transitions in
  Csv.output_all out_channel content;
  Csv.close_out out_channel
let save_states_csv states file =
  let out_channel = open_out_gen [Open_creat; Open_append] 0o666 file |> Csv.to_channel in
  let states_string = states_to_losl states in
  let content = _states_header :: states_string in
  Csv.output_all out_channel content;
  Csv.close_out out_channel