open Bigraph
open Tracking_bigraph
let s0_to_parse = 
"
{(0, A:2),(1, A:2),(2, A:2),(3, A:2),(4, U:0)}
0 5 0
00000
00000
00001
00000
00000
({}, {}, {(0, 1), (1, 1)})
({}, {}, {(0, 1), (2, 1)})
({}, {}, {(1, 1), (3, 1)})
({}, {}, {(3, 1), (2, 1)})
"
let lhs_to_parse = 
"
{(0, A:2),(1, A:2),(2, U:0)}
1 3 0
110
001
000
000
({}, {}, {(0, 1), (1, 1)})
({}, {a}, {(0, 1)})
({}, {d}, {(1, 1)})
"
let rhs_to_parse = 
"
{(0, A:2),(1, A:2)}
1 2 0
11
00
00
({}, {}, {(0, 1), (1, 1)})
({}, {a}, {(0, 1)})
({}, {d}, {(1, 1)})
"
let s0 = Big.of_string s0_to_parse
let lhs = Big.of_string lhs_to_parse
let rhs = Big.of_string rhs_to_parse
let f = Fun.empty |> Fun.add 0 0 |> Fun.add 1 1  
let occs = Big.occurrences ~target:s0 ~pattern:lhs 
let oc1 = List.hd occs

let (res_big,res_fun) = TBig.rewrite oc1 ~target:s0 ~r0:lhs ~r1:rhs ~f_s:None ~f_r1_r0:f;;
print_endline (Fun.to_string res_fun)