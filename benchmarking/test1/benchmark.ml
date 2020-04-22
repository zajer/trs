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

let s0_to_parse = readfile "s0.txt"
let mov_lhs_to_parse = readfile "mov_lhs.txt"
let mov_rhs_to_parse = readfile "mov_rhs.txt"
let estConn_lhs_to_parse = readfile "estConn_lhs.txt"
let estConn_rhs_to_parse = readfile "estConn_rhs.txt"

let s0 = Big.of_string s0_to_parse
let mov_lhs = Big.of_string mov_lhs_to_parse
let mov_rhs = Big.of_string mov_rhs_to_parse
let estConn_lhs = Big.of_string estConn_lhs_to_parse
let estConn_rhs = Big.of_string estConn_rhs_to_parse

let mov_f_rnm = Fun.empty |> Fun.add 0 0 |> Fun.add 1 2 |> Fun.add 2 1
let estConn2AF_f_rnm = Fun.empty |> Fun.add 0 0 |> Fun.add 1 1 |> Fun.add 2 2 |> Fun.add 3 3

let mov_rea_brs = Brs.parse_react ~name:"mov" ~lhs:mov_lhs ~rhs:mov_rhs None |> Option.get
let estConn_rea_brs = Brs.parse_react ~name:"mov" ~lhs:estConn_lhs ~rhs:estConn_rhs None |> Option.get

let pclass = Brs.P_class [mov_rea_brs;estConn_rea_brs] 

let explore_classic () = 
    try 
        let _,s = Brs.bfs ~s0 ~priorities:[pclass] ~predicates:[] ~max:100000 ~iter_f:(fun _ _ -> () ) in s
    with
    | Brs.DEADLOCK (_,s,_) -> s;;
(*
let s = explore_classic () ;;

"Number of found states by bigraph library:"^string_of_int s.states |> print_endline;
"Number of transitions by bigraph library:"^string_of_int s.trans |> print_endline;
"Time took by bigraph library :"^string_of_float s.time |> print_endline
*)

let mov_rea_tbrs = TBrs.parse_react "move" ~lhs:mov_lhs ~rhs:mov_rhs ~f_sm:None ~f_rnm:mov_f_rnm
let estConn_rea_tbrs = TBrs.parse_react "estConn2AF" ~lhs:estConn_lhs ~rhs:estConn_rhs ~f_sm:None ~f_rnm:estConn2AF_f_rnm
let rules = [mov_rea_tbrs;estConn_rea_tbrs]
let explore_with_tracking () = 
    let _ = Parmap.set_default_ncores 4
    and start_time = Sys.time()
    and t,cs,us,_ = TBrs.explore_ss s0 rules 100000 
    and finish_time = Sys.time()
    in 
        t,cs,us,finish_time -. start_time

let t,cs,us,time = explore_with_tracking () ;;
"Number of found states by tracking_bigraph library:"^string_of_int (List.length (cs@us)) |> print_endline;
"Number of transitions by tracking_bigraph library:"^string_of_int (List.length t) |> print_endline;
"Time took by tracking_bigraph library :"^string_of_float time |> print_endline
