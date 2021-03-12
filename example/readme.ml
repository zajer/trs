open Bigraph
open Tracking_bigraph
let s0_to_parse =
"
{(0, A:1),(1, C:1)}
0 2 0
00
00
({}, {}, {(0, 1)})
({}, {}, {(1, 1)})
"
let r_lhs_to_parse =
"
{(0, A:1),(1, C:1)}
0 2 0
00
00
({}, {}, {(0, 1)})
({}, {}, {(1, 1)})
"
let r_rhs_to_parse =
"
{(0, X:1),(1, C:1),(2, B:1),(3, C:1)}
0 4 0
0000
0000
0000
0000
({}, {}, {(0, 1), (2, 1)})
({}, {}, {(1, 1), (3, 1)})
"
let s0 = Big.of_string s0_to_parse
let r_lhs = Big.of_string r_lhs_to_parse
let r_rhs = Big.of_string r_rhs_to_parse
let fun_residue = Fun.of_list [(0,0);(1,1);(3,1)]
let react = TBrs.parse_react "my_react" ~lhs:r_lhs ~rhs:r_rhs ~f_sm:None ~f_rnm:fun_residue
module Gen = TBrs.Make(Tools.DigraphTools);;

let trans,checked,unchecked,steps = Gen.explore_ss s0 [react] 777;;
TTS.export_ss_csv ~trans_file_name:"transitions.csv" ~states_file_name:"states.csv" trans (checked@unchecked);
Printf.printf 
  "
  %d states discovered in %d steps\n 
  %d of these states are checked (i.e. every possible reaction rule has been applied to it)\n
  %d of these states are unchecked\n" (List.length (checked@unchecked)) steps (List.length checked) (List.length unchecked)