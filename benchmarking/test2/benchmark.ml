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
let r0_lhs_to_parse = readfile "r0_lhs.txt"
let r0_rhs_to_parse = readfile "r0_rhs.txt"

let s0 = Big.of_string s0_to_parse
let r0_lhs = Big.of_string r0_lhs_to_parse
let r0_rhs = Big.of_string r0_rhs_to_parse

let f_rnm = Fun.empty |> Fun.add 0 0;;

let r0_rea_brs = Brs.parse_react ~name:"mov" ~lhs:r0_lhs ~rhs:r0_rhs None |> Option.get;;

let pclass = Brs.P_class [r0_rea_brs] 

let explore_classic () = 
    try 
        let _,s = Brs.bfs ~s0 ~priorities:[pclass] ~predicates:[] ~max:64 ~iter_f:(fun _ _ -> () ) in s
    with
    | Brs.DEADLOCK (_,s,_) -> s
    | Brs.MAX (_,s) -> s;;

let s = explore_classic () ;;

"Number of found states by bigraph library:"^string_of_int s.states |> print_endline;
"Number of transitions by bigraph library:"^string_of_int s.trans |> print_endline;
"Time took by bigraph library :"^string_of_float s.time |> print_endline


let r0_rea_tbrs = TBrs.parse_react "move" ~lhs:r0_lhs ~rhs:r0_rhs ~f_sm:None ~f_rnm:f_rnm

let rules = [r0_rea_tbrs]
let explore_with_tracking () = 
    let start_time = Sys.time()
    and t,cs,us,_ = TBrs.explore_ss s0 rules 10
    and finish_time = Sys.time()
    in 
        t,cs,us,finish_time -. start_time

let t,cs,us,time = explore_with_tracking () ;;
"Number of found states by tracking_bigraph library:"^string_of_int (List.length (cs@us)) |> print_endline;
"Number of transitions by tracking_bigraph library:"^string_of_int (List.length t) |> print_endline;
"Time took by tracking_bigraph library :"^string_of_float time |> print_endline
