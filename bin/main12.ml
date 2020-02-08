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

let magic x par =
    let y = Big.of_string
    (*"{(0, A:0),(1, X:0),(2, A:0),(3, X:0),(4, X:0),(5, X:0),(6, X:0),(7, B:0),(8, C:0)}\n0 9 0\n010011101\n000000000\n000100010\n000000000\n000000000\n000000000\n000000000\n000000000\n000000000"*)
    "{(0, A:0),(1, X:0),(2, A:0),(3, X:0),(4, X:0),(5, X:0),(6, X:0),(7, X:0),(8, X:0),(9, X:0),(10, X:0),(11, B:0),(12, C:0)}\n0 13 0\n0100011101110\n0000000000000\n0001100010001\n0000000000000\n0000000000000\n0000000000000\n0000000000000\n0000000000000\n0000000000000\n0000000000000\n0000000000000\n0000000000000\n0000000000000"
    in
        let found = List.fold_left 
            (
                fun res (b,ri)-> if Big.equal b y then ri::res else res
            )
            []
            x
        in
            print_endline (par^"Znaleziono "^(string_of_int (List.length found))^" wystąpień złotego dwugrafu");
            List.iteri 
                (
                    fun i idx -> 
                        ((string_of_int i)^" wystąpienie wskazuje na idx:"^(string_of_int idx)) |> print_endline
                )
                found;;

magic (ss@uss) "hehe"
(*
print_endline ("Liczba przejść:" ^ ( string_of_int (List.length tl) ) );

print_endline ("Liczba unikalnych stanów:" ^ ( string_of_int (List.length (ss@uss)) ) );
print_newline ();
List.iteri 
    (
        fun i (b,idx) -> 
            print_endline ("Stan:"^(string_of_int i));
            print_endline ((Big.to_string b));
            print_endline ("Indeks:"^(string_of_int idx));
    ) 
    (ss@uss);
  

print_newline ();
List.iteri 
    (
        fun i (t,ii,ri) -> 
        print_endline ("\nPrzejście:"^(string_of_int i));
        print_endline ((TBrsOp.trans_to_string t));
        print_endline ("From idx:"^(string_of_int ii));
        print_endline ("To idx:"^(string_of_int ri));
    ) 
    tl;

*)