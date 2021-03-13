open Bigraph
open Tracking_bigraph
open TTS_tests_data
open OUnit2
let _compare_states_lists esl rsl = 
  List.for_all ( fun es -> List.exists (fun rs -> Big.equal es.TTS.bigraph rs.TTS.bigraph && es.index = rs.index ) rsl ) esl
let _compare_transitions_lists esl rsl = 
  List.for_all 
  ( fun es -> List.exists 
    (
      fun rs -> 
        let input_state_idx_cond = es.TTS.in_state_idx = rs.TTS.in_state_idx 
        and output_state_idx_cond = es.TTS.out_state_idx = rs.out_state_idx 
        and react_label_cond = es.TTS.react_label = rs.react_label
        and participants_cond = Iso.equal es.TTS.participants rs.participants
        and residue_cond = Fun.equal es.TTS.residue rs.residue
        and actual_output_state_cond = es.TTS.actual_out_state = rs.actual_out_state
        in
        input_state_idx_cond && output_state_idx_cond && react_label_cond && participants_cond && residue_cond && actual_output_state_cond
    ) 
    rsl 
  ) 
  esl
let test_states_import_1 _ =
  let expected_state_1 = { TTS.index=0; bigraph=(import_states_1_expected_big_0|> Big.of_string) }
  and expected_state_2 = { TTS.index=1; bigraph=(import_states_1_expected_big_1|> Big.of_string) }
  in
  let imported_states = TTS.import_states "states.csv"
  and expcted_states = [expected_state_1;expected_state_2]
  in
  assert_equal ~msg:"There should be exactly two states imported" 2 (List.length expcted_states);
  assert_equal ~msg:"Not all expected states are within the imported ones" ~cmp:_compare_states_lists expcted_states imported_states
let test_transitions_import_1 _ =
  let expected_transition = 
    { 
      TTS.in_state_idx=0;
      out_state_idx=1;
      react_label="my_react";
      participants=(Iso.of_list [(0,0);(1,1)]);
      residue = (Fun.of_list [(0,0);(1,1);(3,1)]);
      actual_out_state = (Big.of_string import_states_1_expected_big_1)
    }
  in
  let imported_transitions = TTS.import_transitions "transitions.csv" 
  and expected_transitions = [expected_transition] 
  in
  assert_equal ~msg:"There should be one imported transition" 1 (List.length imported_transitions);
  assert_equal 
    ~msg:"Imported transition do not match with the expected"
    ~printer:(fun tl -> List.fold_left (fun accu t -> accu^(TTS.exported_trans_to_string t)^"\n" ) "" tl )
    ~cmp:_compare_transitions_lists expected_transitions imported_transitions
let suite =
  "TTS tests" >::: [
    "Test import states 1">:: test_states_import_1;
    "Test import transitions 1">:: test_transitions_import_1;
]

let () =
  run_test_tt_main suite
  