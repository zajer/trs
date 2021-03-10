let test_rewrite_1_no_eta_s0 = 
"{(0, A:2),(1, A:2),(2, A:2),(3, A:2),(4, U:0)}
0 5 0
00000
00000
00001
00000
00000
({}, {}, {(0, 1), (1, 1)})
({}, {}, {(0, 1), (2, 1)})
({}, {}, {(1, 1), (3, 1)})
({}, {}, {(3, 1), (2, 1)})"
let test_rewrite_1_no_eta_redex = 
"{(0, A:2),(1, A:2),(2, U:0)}
1 3 0
110
001
000
000
({}, {}, {(0, 1), (1, 1)})
({}, {a}, {(0, 1)})
({}, {d}, {(1, 1)})"
let test_rewrite_1_no_eta_reactum = 
"{(0, A:2),(1, A:2)}
1 2 0
11
00
00
({}, {}, {(0, 1), (1, 1)})
({}, {a}, {(0, 1)})
({}, {d}, {(1, 1)})"
let test_rewrite_2_3_eta_s0 =
"{(0, A:0),(1, B:0),(2, C:0),(3, D:0),(4, E:0)}
0 5 0
01100
00010
00001
00000
00000"
let test_rewrite_2_eta_redex = 
"{(0, A:0),(1, B:0),(2, C:0)}
1 3 2
10000
01100
00010
00001"
let test_rewrite_2_eta_reactum = 
"{(0, A:0),(1, B:0),(2, C:0)}
1 3 4
1000000
0110000
0001010
0000101"
let test_rewrite_2_eta_expected_result =
"{(0, A:0),(1, B:0),(2, C:0),(3, D:0),(4, E:0),(5, E:0),(6, D:0)}
0 7 0
0110000
0001010
0000101
0000000
0000000
0000000
0000000"
let test_rewrite_3_eta_redex =
"{(0, B:0)}
1 1 1
10
01"
let test_rewrite_3_eta_reactum = 
"{(0, B:0)}
1 1 2
100
011"
let test_rewrite_3_eta_expected_result =
"{(0, A:0),(1, B:0),(2, D:0),(3, D:0),(4, C:0),(5, E:0)}
0 6 0
010010
001100
000000
000000
000001
000000"
let test_rewrite_4_no_eta_s0 = 
"{(0, A:0),(1, B:0),(2, C:0),(3, D:0),(4, E:0)}
0 5 0
01100
00010
00001
00000
00000"
let test_rewrite_4_no_eta_redex = 
"{(0, A:0)}
1 1 1
10
01"
let test_rewrite_4_no_eta_reactum =
"{(0, A:0),(1, X:0)}
1 2 1
110
001
000"
let test_rewrite_4_no_eta_expected_result =
"{(0, A:0),(1, X:0),(2, B:0),(3, C:0),(4, D:0),(5, E:0)}
0 6 0
001100
000000
000010
000001
000000
000000"
let test_rewrite_5_eta_s0 =
"{(0, A:0),(1, B:0)}
0 2 0
01
00"
let test_rewrite_5_eta_redex =
"{(0, A:0)}
1 1 1
10
01"
let test_rewrite_5_eta_reactum =
"{(0, A:0),(1, X:0)}
1 2 2
1100
0011
0000"
let test_rewrite_5_eta_result_expected =
"{(0, A:0),(1, X:0),(2, B:0),(3, B:0)}
0 4 0
0011
0000
0000
0000"