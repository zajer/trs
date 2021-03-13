open Bigraph

type trans_raw = { is:Big.t; os:Big.t ; rf:Fun.t ; p:Iso.t ; rl:string}
type trans_exported = { in_state_idx:int;out_state_idx:int; react_label:string;participants:Iso.t;residue:Fun.t;actual_out_state:Big.t }
type state = { bigraph:Big.t;index:int }
let raw_trans_to_string t =
  let init_state_label = "Input state:"
  and res_state_label = "Output state:"
  and residue_fun_label = "Residue fun:"
  and participant_label = "Participants fun:"
  and react_label = "React label:"
  in
      let init_state = init_state_label^"\n"^(Big.to_string t.is)
      and res_state = res_state_label^"\n"^(Big.to_string t.os)
      and residue_fun = residue_fun_label^"\n"^(Fun.to_string t.rf)
      and participants = participant_label^"\n"^(Iso.to_string t.p)
      and react = react_label^"\n"^(t.rl)
      in
          (String.concat "\n" [init_state;res_state;residue_fun;participants;react]);;
let exported_trans_to_string t =
  let init_state_label = "Input state idx:"
  and res_state_label = "Output state idx:"
  and residue_fun_label = "Residue fun:"
  and participant_label = "Participants fun:"
  and react_label = "React label:"
  in
      let init_state = init_state_label^" "^( string_of_int t.in_state_idx)
      and res_state = res_state_label^" "^( string_of_int t.out_state_idx)
      and react = react_label^" "^(t.react_label)
      and residue_fun = residue_fun_label^" "^(Fun.to_string t.residue)
      and participants = participant_label^" "^(Iso.to_string t.participants)
      in
          (String.concat "||" [init_state;res_state;react;participants;residue_fun;]);;
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
let _list_of_string_to_2_tuple_of_strings los =
  if List.length los <> 2 then
    raise (Invalid_argument "A valid row has to have exactly two columns")
  else
    (
      let bigraph_str = List.nth los 0 
      and idx_str = List.nth los 1 in
      bigraph_str,idx_str
    )
let _parse_single_exported_state = 
  fun los -> 
    let idx_str,bigraph_str = _list_of_string_to_2_tuple_of_strings los in
    {bigraph=Big.of_string bigraph_str;index=(int_of_string idx_str)}
let import_states file_name =
  let states_as_string_lists = Csv.load file_name |> List.tl in
    List.map 
    ( 
      _parse_single_exported_state
    )
    states_as_string_lists
let parimport_states file_name =
  let states_as_string_lists = Csv.load file_name |> List.tl in
    Parmap.parmap 
    ( 
      _parse_single_exported_state
    )
    (Parmap.L states_as_string_lists)
let _list_of_string_to_6_tuple_of_strings los =
  if List.length los <> 6 then
    raise (Invalid_argument "A valid row has to have exactly five columns")
  else
    (
      let in_state_idx_str = List.nth los 0
      and out_state_idx_str = List.nth los 1
      and react_label_str = List.nth los 2
      and participants_str = List.nth los 3
      and residue_str = List.nth los 4
      and actual_out_state_str = List.nth los 5 in
      in_state_idx_str,out_state_idx_str,react_label_str,participants_str,residue_str,actual_out_state_str
    )
let _parse_single_exported_transition = 
  fun los -> 
    let in_state_idx_str,out_state_idx_str,react_label,participants_str,residue_str,actual_out_state_str = _list_of_string_to_6_tuple_of_strings los in
      let in_state_idx = int_of_string in_state_idx_str
      and out_state_idx = int_of_string out_state_idx_str
      and participants = Utils.iso_as_string_to_iso participants_str
      and residue = Utils.fun_as_string_to_fun residue_str
      and actual_out_state = Big.of_string actual_out_state_str in
      { in_state_idx;out_state_idx;react_label;participants;residue;actual_out_state}
let import_transitions file_name = 
  let transitions_as_string_lists = Csv.load file_name |> List.tl in
  List.map
    (
      _parse_single_exported_transition
    )
    transitions_as_string_lists
let parimport_transitions file_name = 
  let transitions_as_string_lists = Csv.load file_name |> List.tl in
  Parmap.parmap
    (
      _parse_single_exported_transition
    )
    (Parmap.L transitions_as_string_lists)