open Bigraph
open Tracking_bigraph

let s_to_parse =
"
{(0, A:0),(1, B:0),(2, C:0),(3, D:0),(4, E:0)}
0 5 0
01100
00010
00001
00000
00000
"

let r0_to_parse =
"
{(0, A:0),(1, B:0),(2, C:0)}
1 3 2
10000
01100
00010
00001
"

let r0'_to_parse =
"
{(0, B:0)}
1 1 1
10
01
"

let r1_to_parse =
"
{(0, A:0),(1, B:0),(2, C:0)}
1 3 4
1000000
0110000
0001010
0000101
"

let r1'_to_parse =
"
{(0, B:0)}
1 1 2
100
011
"

let s = Big.of_string s_to_parse
let lhs1 = Big.of_string r0_to_parse
let rhs1 = Big.of_string r1_to_parse
let lhs2 = Big.of_string r0'_to_parse
let rhs2 = Big.of_string r1'_to_parse
let fs1 = Fun.empty |> Fun.add 0 0 |> Fun.add 1 1 |> Fun.add 2 1 |> Fun.add 3 0
let fs2 = Fun.empty |> Fun.add 0 0 |> Fun.add 1 0
let tau1 = Fun.empty |> Fun.add 0 0 |> Fun.add 1 1 |> Fun.add 2 2
let tau2 = Fun.empty |> Fun.add 0 0 

let lhs = lhs2
let rhs = rhs2
let fs = fs2
let tau = tau2


let occs = Big.occurrences ~target:s ~pattern:lhs
let oc1 = List.hd occs

let (res_big,res_fun) = TBig.rewrite oc1 ~target:s ~r0:lhs ~r1:rhs ~f_s:(Some fs) ~f_r1_r0:tau;;

print_newline () ;
print_endline "init_big:";
print_endline (Big.to_string s);
print_endline "res_big:";
print_endline (Big.to_string res_big);
print_endline "res fun:";
print_endline (Fun.to_string res_fun)