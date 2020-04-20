open Bigraph
open Tracking_bigraph


let init_state_to_parse = 
"
{(0, A:1),(1, B:0),(2, B:0),(3, A:1)}
0 4 0
0110
0000
0000
0000
({}, {}, {(0, 1), (3, 1)})
"
let init_state = Big.of_string init_state_to_parse

let lhs_to_parse =
"
{(0, A:1),(1, B:0),(2, A:1)}
0 3 2
01010
00000
00001
({}, {}, {(0, 1), (2, 1)})
"
let rhs_to_parse =
"
{(0, A:1),(1, B:0),(2, A:1)}
0 3 2
00010
00000
01001
({}, {}, {(0, 1), (2, 1)})
"
let lhs = Big.of_string lhs_to_parse
let rhs = Big.of_string rhs_to_parse

let res_map = Fun.empty |> Fun.add 0 2 |> Fun.add 1 1 |> Fun.add 2 0

let rule = TBrs.parse_react "move" ~lhs ~rhs ~f_sm:None ~f_rnm:res_map;;

Parmap.set_default_ncores 4

let transitions,checked_states,unchecked_states,used_steps = TBrs.parexplore_ss init_state [rule] 777;;


RExp.export_ss_csv transitions (checked_states@unchecked_states)


