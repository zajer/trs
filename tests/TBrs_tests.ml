open OUnit2

open Bigraph
open Tracking_bigraph
module Digraph_TRS_gen = TBrs.Make(Tools.DigraphTools)

let test_parexplore_ss_1 _ =
    let s0_to_parse ="{(0, A:0),(1, A:0),(2, B:0),(3, B:0)}\n0 4 0\n0010\n0001\n0000\n0000"
    and r0_to_parse ="{(0, A:0),(1, A:0),(2, B:0)}\n1 3 2\n11000\n00110\n00001\n00000"
    and r1_to_parse ="{(0, A:0),(1, A:0),(2, B:0)}\n1 3 2\n11000\n00010\n00101\n00000"
    in
        let s0 = Big.of_string s0_to_parse
        and lhs = Big.of_string r0_to_parse
        and rhs = Big.of_string r1_to_parse
        and f_rnm = Fun.empty |> Fun.add 0 0
        in
            let react = TBrs.parse_react "yolo" ~lhs ~rhs ~f_rnm ~f_sm:None
            in
                (*let tl,ss,uss,_ = TBrs.parexplore_ss s0 [react] 10*)
                let tl,ss,uss,_ = Digraph_TRS_gen.parexplore_ss s0 [react] 10
                in
                    List.iteri
                        (
                            fun _ (t,ii,ri) -> 
                                let init_state_according_to_index,_ = List.find ( fun (_,i) -> if i = ii then true else false ) (ss@uss) 
                                and res_state_according_to_index,_ = List.find ( fun (_,i) -> if i = ri then true else false ) (ss@uss)
                                in
                                    let is_init_in_trans_iso_to_indexed = Big.equal init_state_according_to_index (t.Trans.is)
                                    and  is_res_in_trans_iso_to_indexed = Big.equal res_state_according_to_index (t.Trans.os)
                                    in
                                        assert_equal true (is_init_in_trans_iso_to_indexed && is_res_in_trans_iso_to_indexed )
                        ) 
                        tl
let test_parexplore_ss_2 _ =
    let s0_to_parse ="{(0, A:0),(1, A:0),(2, B:0),(3, C:0)}\n0 4 0\n0010\n0001\n0000\n0000\n"
    and r0_to_parse ="{(0, A:0)}\n1 1 1\n10\n01"
    and r1_to_parse ="{(0, A:0),(1, X:0)}\n1 2 1\n100\n011\n000"
    in
        let s0 = Big.of_string s0_to_parse
        and lhs = Big.of_string r0_to_parse
        and rhs = Big.of_string r1_to_parse
        and f_rnm = Fun.empty |> Fun.add 0 0
        in
            let react = TBrs.parse_react "yolo" ~lhs ~rhs ~f_rnm ~f_sm:None
            in
                let tl,ss,uss,_ = Digraph_TRS_gen.parexplore_ss s0 [react] 3
                in
                    List.iteri
                        (
                            fun i (t,ii,ri) -> 
                                let init_state_according_to_index,_ = List.find ( fun (_,i) -> if i = ii then true else false ) (ss@uss)
                                and res_state_according_to_index,_ = List.find ( fun (_,i) -> if i = ri then true else false ) (ss@uss)
                                in
                                    let is_init_in_trans_iso_to_indexed = Big.equal init_state_according_to_index (t.Trans.is)
                                    and is_res_in_trans_iso_to_indexed = Big.equal res_state_according_to_index (t.Trans.os)
                                    in
                                        if not (is_init_in_trans_iso_to_indexed && is_res_in_trans_iso_to_indexed ) then
                                        (
                                        "Result "^(string_of_int i)^": "^(string_of_bool (is_init_in_trans_iso_to_indexed && is_res_in_trans_iso_to_indexed)) |> print_endline;
                                        "Result components, init:"^(string_of_bool is_init_in_trans_iso_to_indexed)^" , res:"^(string_of_bool is_res_in_trans_iso_to_indexed) |> print_endline;
                                        "Actual transition input state:\n"^(Big.to_string (t.Trans.is)) |> print_endline;
                                        "Indexed transition input state:\n"^(Big.to_string (init_state_according_to_index)) |> print_endline;
                                        "Actual transition output state:\n"^(Big.to_string (t.Trans.os)) |> print_endline;
                                        "Indexed transition output state:\n"^(Big.to_string (res_state_according_to_index)) |> print_endline;                 
                                        );
                                        assert_equal true (is_init_in_trans_iso_to_indexed && is_res_in_trans_iso_to_indexed )
                        ) 
                        tl
let test_parexplore_ss_3 _ =
    let s0_to_parse ="{(0, A:0),(1, A:0),(2, B:0),(3, C:0)}\n0 4 0\n0010\n0001\n0000\n0000\n"
    and r0_to_parse ="{(0, A:0)}\n1 1 1\n10\n01"
    and r1_to_parse ="{(0, A:0),(1, X:0)}\n1 2 1\n100\n011\n000"
    in
        let s0 = Big.of_string s0_to_parse
        and lhs = Big.of_string r0_to_parse
        and rhs = Big.of_string r1_to_parse
        and f_rnm = Fun.empty |> Fun.add 0 0
        in
            let react = TBrs.parse_react "yolo" ~lhs ~rhs ~f_rnm ~f_sm:None
            in
                let tl,ss,uss,_ = Digraph_TRS_gen.parexplore_ss s0 [react] 5
                in
                    List.iteri
                        (
                            fun i (t,ii,ri) -> 
                                let init_state_according_to_index,_ = List.find ( fun (_,i) -> if i = ii then true else false ) (ss@uss)
                                and res_state_according_to_index,_ = List.find ( fun (_,i) -> if i = ri then true else false ) (ss@uss)
                                in
                                    let is_init_in_trans_iso_to_indexed = Big.equal init_state_according_to_index (t.Trans.is)
                                    and is_res_in_trans_iso_to_indexed = Big.equal res_state_according_to_index (t.Trans.os)
                                    in
                                        if not (is_init_in_trans_iso_to_indexed && is_res_in_trans_iso_to_indexed ) then
                                        (
                                        "Result "^(string_of_int i)^": "^(string_of_bool (is_init_in_trans_iso_to_indexed && is_res_in_trans_iso_to_indexed)) |> print_endline;
                                        "Result components, init:"^(string_of_bool is_init_in_trans_iso_to_indexed)^" , res:"^(string_of_bool is_res_in_trans_iso_to_indexed) |> print_endline;
                                        "Actual transition input state:\n"^(Big.to_string (t.Trans.is)) |> print_endline;
                                        "Indexed transition input state:\n"^(Big.to_string (init_state_according_to_index)) |> print_endline;
                                        "Actual transition output state:\n"^(Big.to_string (t.Trans.os)) |> print_endline;
                                        "Indexed transition output state:\n"^(Big.to_string (res_state_according_to_index)) |> print_endline;                  
                                        );
                                        assert_equal true (is_init_in_trans_iso_to_indexed && is_res_in_trans_iso_to_indexed )
                        ) 
                        tl
let test_parexplore_ss_4 _ =
    let s0_to_parse ="{(0, A:0),(1, A:0),(2, B:0),(3, C:0)}\n0 4 0\n0010\n0001\n0000\n0000\n"
    and r0_to_parse ="{(0, A:0)}\n1 1 1\n10\n01"
    and r1_to_parse ="{(0, A:0),(1, X:0)}\n1 2 1\n100\n011\n000"
    in
        let s0 = Big.of_string s0_to_parse
        and lhs = Big.of_string r0_to_parse
        and rhs = Big.of_string r1_to_parse
        and f_rnm = Fun.empty |> Fun.add 0 0
        in
            let react = TBrs.parse_react "yolo" ~lhs ~rhs ~f_rnm ~f_sm:None
            in
                let tl,ss,uss,_ = Digraph_TRS_gen.parexplore_ss s0 [react] 9
                in
                    List.iteri
                        (
                            fun i (t,ii,ri) -> 
                                let init_state_according_to_index,_ = List.find ( fun (_,i) -> if i = ii then true else false ) (ss@uss)
                                and res_state_according_to_index,_ = List.find ( fun (_,i) -> if i = ri then true else false ) (ss@uss)
                                in
                                    let is_init_in_trans_iso_to_indexed = Big.equal init_state_according_to_index (t.Trans.is)
                                    and is_res_in_trans_iso_to_indexed = Big.equal res_state_according_to_index (t.Trans.os)
                                    in
                                        if not (is_init_in_trans_iso_to_indexed && is_res_in_trans_iso_to_indexed ) then
                                        (
                                        "Result "^(string_of_int i)^": "^(string_of_bool (is_init_in_trans_iso_to_indexed && is_res_in_trans_iso_to_indexed)) |> print_endline;
                                        "Result components, init:"^(string_of_bool is_init_in_trans_iso_to_indexed)^" , res:"^(string_of_bool is_res_in_trans_iso_to_indexed) |> print_endline;
                                        "Actual transition input state:\n"^(Big.to_string (t.Trans.is)) |> print_endline;
                                        "Indexed transition input state:\n"^(Big.to_string (init_state_according_to_index)) |> print_endline;
                                        "Actual transition output state:\n"^(Big.to_string (t.Trans.os)) |> print_endline;
                                        "Indexed transition output state:\n"^(Big.to_string (res_state_according_to_index)) |> print_endline;                    
                                        );
                                        assert_equal true (is_init_in_trans_iso_to_indexed && is_res_in_trans_iso_to_indexed )
                        ) 
                        tl
let test_parexplore_ss_5 _ =
    let s0_to_parse ="{(0, A:0),(1, A:0),(2, B:0),(3, C:0)}\n0 4 0\n0010\n0001\n0000\n0000\n"
    and r0_to_parse ="{(0, A:0)}\n1 1 1\n10\n01"
    and r1_to_parse ="{(0, A:0),(1, X:0)}\n1 2 1\n100\n011\n000"
    in
        let s0 = Big.of_string s0_to_parse
        and lhs = Big.of_string r0_to_parse
        and rhs = Big.of_string r1_to_parse
        and f_rnm = Fun.empty |> Fun.add 0 0
        in
            let react = TBrs.parse_react "yolo" ~lhs ~rhs ~f_rnm ~f_sm:None
            in
                let tl,ss,uss,_ = Digraph_TRS_gen.parexplore_ss s0 [react] 15
                in
                    List.iteri
                        (
                            fun i (t,ii,ri) -> 
                                let init_state_according_to_index,_ = List.find ( fun (_,i) -> if i = ii then true else false ) (ss@uss)
                                and res_state_according_to_index,_ = List.find ( fun (_,i) -> if i = ri then true else false ) (ss@uss)
                                in
                                    let is_init_in_trans_iso_to_indexed = Big.equal init_state_according_to_index (t.Trans.is)
                                    and is_res_in_trans_iso_to_indexed = Big.equal res_state_according_to_index (t.Trans.os)
                                    in
                                        if not (is_init_in_trans_iso_to_indexed && is_res_in_trans_iso_to_indexed ) then
                                        (
                                        "Result "^(string_of_int i)^": "^(string_of_bool (is_init_in_trans_iso_to_indexed && is_res_in_trans_iso_to_indexed)) |> print_endline;
                                        "Result components, init:"^(string_of_bool is_init_in_trans_iso_to_indexed)^" , res:"^(string_of_bool is_res_in_trans_iso_to_indexed) |> print_endline;
                                        "Actual transition input state:\n"^(Big.to_string (t.Trans.is)) |> print_endline;
                                        "Indexed transition input state:\n"^(Big.to_string (init_state_according_to_index)) |> print_endline;
                                        "Actual transition output state:\n"^(Big.to_string (t.Trans.os)) |> print_endline;
                                        "Indexed transition output state:\n"^(Big.to_string (res_state_according_to_index)) |> print_endline;            
                                        );
                                        assert_equal true (is_init_in_trans_iso_to_indexed && is_res_in_trans_iso_to_indexed )
                        ) 
                        tl

let suite =
  "TBrs tests" >::: [
    "Parexplore ss 1">:: test_parexplore_ss_1;
    "Parexplore ss 2">:: test_parexplore_ss_2;
    "Parexplore ss 3">:: test_parexplore_ss_3;
    "Parexplore ss 4">:: test_parexplore_ss_4;
    "Parexplore ss 5">:: test_parexplore_ss_5;
]

let () =
    run_test_tt_main suite
    