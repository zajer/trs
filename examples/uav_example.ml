open Bigraph
open Tracking_bigraph

let readlines filename =
    let lines = ref [] in
    let chan = open_in filename in
        try
        while true; do
            lines := input_line chan :: !lines
        done; !lines
        with End_of_file ->
            close_in chan;
            List.rev !lines ;;

let readfile filename = 
    let lines = readlines filename
    in
    List.fold_left (fun (t:string) (l:string) -> t^"\n"^l ) "" lines ;;
(*Change a map file to one of the uav_example_map_AxB_Cus.txt files for a different scenario. *)
let s0_to_parse = readfile "uav_example_map_4x3_3us.txt"
let move_lhs_to_parse = readfile "uav_example_mov_lhs.txt"
let move_rhs_to_parse = readfile "uav_example_mov_rhs.txt"
let estConn2AF_lhs_to_parse = readfile "uav_example_estConn2AF_lhs.txt"
let estConn2AF_rhs_to_parse = readfile "uav_example_estConn2AF_rhs.txt"
let estConn1AF_lhs_to_parse = readfile "uav_example_estConn1AF_lhs.txt"
let estConn1AF_rhs_to_parse = readfile "uav_example_estConn1AF_rhs.txt"
let breConn_lhs_to_parse = readfile "uav_example_breConn_lhs.txt"
let breConn_rhs_to_parse = readfile "uav_example_breConn_rhs.txt"

let s0 = Big.of_string s0_to_parse
let mov_lhs = Big.of_string move_lhs_to_parse
let mov_rhs = Big.of_string move_rhs_to_parse
let estConn1AF_lhs = Big.of_string estConn1AF_lhs_to_parse
let estConn1AF_rhs = Big.of_string estConn1AF_rhs_to_parse
let estConn2AF_lhs = Big.of_string estConn2AF_lhs_to_parse
let estConn2AF_rhs = Big.of_string estConn2AF_rhs_to_parse
let breConn_lhs = Big.of_string breConn_lhs_to_parse
let breConn_rhs = Big.of_string breConn_rhs_to_parse
let mov_f_rnm = Fun.empty |> Fun.add 0 0 |> Fun.add 1 2 |> Fun.add 2 1
let estConn2AF_f_rnm = Fun.empty |> Fun.add 0 0 |> Fun.add 1 1 |> Fun.add 2 2 |> Fun.add 3 3
let estConn1AF_f_rnm = Fun.empty |> Fun.add 0 0 |> Fun.add 1 1 |> Fun.add 2 2
let breConn_f_rnm = Fun.empty |> Fun.add 0 0 |> Fun.add 1 1
let mov_react = TBrs.parse_react "move" ~lhs:mov_lhs ~rhs:mov_rhs ~f_sm:None ~f_rnm:mov_f_rnm
let estConn1AF_react = TBrs.parse_react "estConn1AF" ~lhs:estConn1AF_lhs ~rhs:estConn1AF_rhs ~f_sm:None ~f_rnm:estConn1AF_f_rnm
let estConn2AF_react = TBrs.parse_react "estConn2AF" ~lhs:estConn2AF_lhs ~rhs:estConn2AF_rhs ~f_sm:None ~f_rnm:estConn2AF_f_rnm
let breConn_react = TBrs.parse_react "breConn" ~lhs:breConn_lhs ~rhs:breConn_rhs ~f_sm:None ~f_rnm:breConn_f_rnm 
let rules = [mov_react;estConn1AF_react;estConn2AF_react;breConn_react];;
Parmap.set_default_ncores 4

let tl,ss,uss,ms = TBrs.parexplore_ss ~s0 ~rules ~max_steps:300;;

print_endline ("Number of transitions:" ^ ( string_of_int (List.length tl) ) );
print_endline ("Number of unique states:" ^ ( string_of_int (List.length ss) ) );;

RExp.export_ss_csv tl (ss@uss);;
(*
    Uncomment the below to perform corretness tests. 
    It checks whether all result states are actually unique up to isomorphism
    and if all transitions' init and result states are indexed properly.
*)
(*
List.iteri
    (
        fun i (t,ii,ri) -> 
            let init_state_according_to_index,_ = List.find ( fun (_,i) -> if i = ii then true else false ) (ss@uss)
            and res_state_according_to_index,_ = List.find ( fun (_,i) -> if i = ri then true else false ) (ss@uss)
            in
                let is_init_in_trans_iso_to_indexed = Big.equal init_state_according_to_index (t.TBrs.is)
                and is_res_in_trans_iso_to_indexed = Big.equal res_state_according_to_index (t.TBrs.rs)
                in
                    if not (is_init_in_trans_iso_to_indexed && is_res_in_trans_iso_to_indexed ) then
                    (
                    "Result "^(string_of_int i)^": "^(string_of_bool (is_init_in_trans_iso_to_indexed && is_res_in_trans_iso_to_indexed)) |> print_endline;
                    "Result components, init:"^(string_of_bool is_init_in_trans_iso_to_indexed)^" , res:"^(string_of_bool is_res_in_trans_iso_to_indexed) |> print_endline;
                    "Actual transition init state:\n"^(Big.to_string (t.TBrs.is)) |> print_endline;
                    "Indexed transition init state:\n"^(Big.to_string (init_state_according_to_index)) |> print_endline;
                    "Actual transition result state:\n"^(Big.to_string (t.TBrs.rs)) |> print_endline;
                    "Indexed transition result state:\n"^(Big.to_string (res_state_according_to_index)) |> print_endline;                 
                    exit 1
                    )
    ) 
    tl;;

print_endline "All results are indexed properly" ;;

let rec check_equals_among_results uss = 
    match uss with
    | [] -> ();
    | (us,idx)::rouss -> 
        List.iter 
            (
                fun (cs,cidx) -> 
                    if Big.equal us cs then  
                    (
                        print_endline ("Results indexed as idx1="^(string_of_int idx)^" idx2="^(string_of_int cidx)^" are isomorphic!");
                        exit 1
                    )
                    else
                        ()
            )
            rouss;
            check_equals_among_results rouss;;

check_equals_among_results (ss@uss);;

print_endline "There are no isomorphic elements inside result lists"
*)