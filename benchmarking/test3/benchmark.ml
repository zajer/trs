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
let s0_to_parse = readfile "uav_example_map_3x3_3us.txt"
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
let mov_react_trs = TBrs.parse_react "move" ~lhs:mov_lhs ~rhs:mov_rhs ~f_sm:None ~f_rnm:mov_f_rnm
let estConn1AF_react_trs = TBrs.parse_react "estConn1AF" ~lhs:estConn1AF_lhs ~rhs:estConn1AF_rhs ~f_sm:None ~f_rnm:estConn1AF_f_rnm
let estConn2AF_react_trs = TBrs.parse_react "estConn2AF" ~lhs:estConn2AF_lhs ~rhs:estConn2AF_rhs ~f_sm:None ~f_rnm:estConn2AF_f_rnm
let breConn_react_trs = TBrs.parse_react "breConn" ~lhs:breConn_lhs ~rhs:breConn_rhs ~f_sm:None ~f_rnm:breConn_f_rnm 
let rules = [mov_react_trs;estConn1AF_react_trs;estConn2AF_react_trs;breConn_react_trs];;

let mov_react_brs = Brs.parse_react ~name:"move" ~lhs:mov_lhs ~rhs:mov_rhs None |> Option.get
let estConn1AF_react_brs = Brs.parse_react ~name:"estConn1AF" ~lhs:estConn1AF_lhs ~rhs:estConn1AF_rhs None|> Option.get
let estConn2AF_react_brs = Brs.parse_react ~name:"estConn2AF" ~lhs:estConn2AF_lhs ~rhs:estConn2AF_rhs None|> Option.get
let breConn_react_brs = Brs.parse_react ~name:"breConn" ~lhs:breConn_lhs ~rhs:breConn_rhs None|> Option.get


let pclass = Brs.P_class [mov_react_brs;estConn1AF_react_brs;estConn2AF_react_brs;breConn_react_brs];;

let explore_classic () = 
    try 
        let _,s = Brs.bfs ~s0 ~priorities:[pclass] ~predicates:[] ~max:64 ~iter_f:(fun _ _ -> () ) in s
    with
    | Brs.DEADLOCK (_,s,_) -> s
    | Brs.MAX (_,s) -> s;;

let explore_with_tracking () = 
    let start_time = Sys.time()
    and t,cs,us,_ = TBrs.explore_ss s0 rules 300
    and finish_time = Sys.time()
    in 
        t,cs,us,finish_time -. start_time

let s = explore_classic () ;;

"Number of found states by bigraph library:"^string_of_int s.states |> print_endline;
"Number of transitions by bigraph library:"^string_of_int s.trans |> print_endline;
"Time took by bigraph library :"^string_of_float s.time |> print_endline


let t,cs,us,time = explore_with_tracking ();;

"Number of found states by tracking_bigraph library:"^string_of_int (List.length (cs@us)) |> print_endline;
"Number of transitions by tracking_bigraph library:"^string_of_int (List.length t) |> print_endline;
"Time took by tracking_bigraph library :"^string_of_float time |> print_endline


