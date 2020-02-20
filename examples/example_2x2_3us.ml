open Bigraph
open Tracking_bigraph

let s0_to_parse =
"
{(0, AF:4),(1, UAV:1),(2, AF:4),(3, UAV:1),(4, AF:4),(5, UAV:1),(6, AF:4)}
1 7 0
1010101
0100000
0000000
0001000
0000000
0000010
0000000
0000000
({}, {}, {(0, 1)})
({}, {}, {(0, 1)})
({}, {}, {(0, 1), (2, 1)})
({}, {}, {(0, 1), (4, 1)})
({}, {}, {(1, 1)})
({}, {}, {(2, 1)})
({}, {}, {(2, 1)})
({}, {}, {(2, 1), (6, 1)})
({}, {}, {(3, 1)})
({}, {}, {(4, 1)})
({}, {}, {(4, 1)})
({}, {}, {(4, 1), (6, 1)})
({}, {}, {(5, 1)})
({}, {}, {(6, 1)})
({}, {}, {(6, 1)})
"
let move_lhs_to_parse =
"
{(0, AF:4),(1, UAV:1),(2, AF:4)}
1 3 2
10100
01010
00000
00001
({}, {}, {(0, 1), (2, 1)})
({}, {}, {(1, 1)})
({}, {b1}, {(0, 1)})
({}, {b2}, {(2, 1)})
({}, {l1}, {(0, 1)})
({}, {r2}, {(2, 1)})
({}, {t1}, {(0, 1)})
({}, {t2}, {(2, 1)})
"
let move_rhs_to_parse =
"
{(0, AF:4),(1, AF:4),(2, UAV:1)}
1 3 2
11000
00010
00101
00000
({}, {}, {(0, 1), (1, 1)})
({}, {}, {(2, 1)})
({}, {b1}, {(0, 1)})
({}, {b2}, {(1, 1)})
({}, {l1}, {(0, 1)})
({}, {r2}, {(1, 1)})
({}, {t1}, {(0, 1)})
({}, {t2}, {(1, 1)})
"
let estConn2AF_lhs_to_parse =
"
{(0, AF:4),(1, UAV:1),(2, AF:4),(3, UAV:1)}
1 4 2
101000
010010
000000
000101
000000
({}, {}, {(0, 1), (2, 1)})
({}, {}, {(1, 1)})
({}, {b1}, {(0, 1)})
({}, {b2}, {(2, 1)})
({}, {c2}, {(3, 1)})
({}, {l1}, {(0, 1)})
({}, {r2}, {(2, 1)})
({}, {t1}, {(0, 1)})
({}, {t2}, {(2, 1)})
"
let estConn2AF_rhs_to_parse =
"
{(0, AF:4),(1, UAV:1),(2, AF:4),(3, UAV:1)}
1 4 2
101000
010010
000000
000101
000000
({}, {}, {(0, 1), (2, 1)})
({}, {b1}, {(0, 1)})
({}, {b2}, {(2, 1)})
({}, {c2}, {(1, 1), (3, 1)})
({}, {l1}, {(0, 1)})
({}, {r2}, {(2, 1)})
({}, {t1}, {(0, 1)})
({}, {t2}, {(2, 1)})
"
let estConn1AF_lhs_to_parse =
"
{(0, AF:4),(1, UAV:1),(2, UAV:1)}
1 3 1
1000
0111
0000
0000
({}, {}, {(1, 1)})
({}, {b1}, {(0, 1)})
({}, {c2}, {(2, 1)})
({}, {l1}, {(0, 1)})
({}, {r1}, {(0, 1)})
({}, {t1}, {(0, 1)})
"
let estConn1AF_rhs_to_parse = 
"
{(0, AF:4),(1, UAV:1),(2, UAV:1)}
1 3 1
1000
0111
0000
0000
({}, {b1}, {(0, 1)})
({}, {c2}, {(1, 1), (2, 1)})
({}, {l1}, {(0, 1)})
({}, {r1}, {(0, 1)})
({}, {t1}, {(0, 1)})
"

let breConn_lhs_to_parse = 
"
{(0, UAV:1),(1, UAV:1)}
2 2 0
10
01
00
00
({}, {c1}, {(0, 1), (1, 1)})
"
let breConn_rhs_to_parse =
"
{(0, UAV:1),(1, UAV:1)}
2 2 0
10
01
00
00
({}, {}, {(1, 1)})
({}, {c1}, {(0, 1)})
"

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

RExp.export_ss_csv tl (ss@uss)