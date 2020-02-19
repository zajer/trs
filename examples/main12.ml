open Bigraph
open Tracking_bigraph

let s0_to_parse =
"
{(0, A:0),(1, A:0),(2, B:0),(3, C:0)}
0 4 0
0010
0001
0000
0000
"
let r0_to_parse =
"
{(0, A:0)}
1 1 1
10
01
"
let r1_to_parse =
"
{(0, A:0),(1, X:0)}
1 2 1
100
011
000
"
let s0'_to_parse =
"
{(0, A:0),(1, A:0),(2, B:0),(3, B:0)}
0 4 0
0010
0001
0000
0000
"
let r0'_to_parse =
"
{(0, A:0),(1, A:0),(2, B:0)}
1 3 2
11000
00110
00001
00000
"
let r1'_to_parse =
"
{(0, A:0),(1, A:0),(2, B:0)}
1 3 2
11000
00010
00101
00000
"

let s0 = Big.of_string s0_to_parse
let lhs = Big.of_string r0_to_parse
let rhs = Big.of_string r1_to_parse
let f_rnm = Fun.empty |> Fun.add 0 0
let react = TBrs.parse_react "yolo" ~lhs ~rhs ~f_rnm ~f_sm:None;;

let tl,ss,uss,ms = TBrs.parexplore_ss ~s0 ~rules:[react] ~max_steps:9;;

RExp.export_ss_csv tl (ss@uss)