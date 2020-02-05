open OUnit2

open Bigraph
open Tracking_bigraph

let test_norm_ss_1 _ =
  let us1 = Big.of_string "{(0, A:0),(1, B:0),(2, C:0)}\n0 3 0\n010\n001\n000"
  in
    let is11 = Big.of_string "{(0, C:0),(1, A:0),(2, B:0)}\n0 3 0\n000\n001\n100"
    and is12 = Big.of_string "{(0, C:0),(1, B:0),(2, A:0)}\n0 3 0\n000\n100\n010"
    and is13 = Big.of_string "{(0, B:0),(1, C:0),(2, A:0)}\n0 3 0\n010\n000\n100"
    in
      let t_us1_is11_residue = Fun.empty |> Fun.add 0 2 |> Fun.add 1 0 |> Fun.add 2 1
      and t_us1_is12_residue = Fun.empty |> Fun.add 0 2 |> Fun.add 1 1 |> Fun.add 2 0
      and t_us1_is13_residue = Fun.empty |> Fun.add 0 1 |> Fun.add 1 2 |> Fun.add 2 0
    in
      let t111 = TBrs.parse_trans_unsafe ~init:us1 ~result:is11 Iso.empty t_us1_is11_residue ""
      and t112 = TBrs.parse_trans_unsafe ~init:us1 ~result:is12 Iso.empty t_us1_is12_residue ""
      and t113 = TBrs.parse_trans_unsafe ~init:us1 ~result:is13 Iso.empty t_us1_is13_residue ""
      in
        let rt = TBrs.norm_ss [t111;t112;t113] [us1]
        and expected_residue = Fun.of_list [(0,0);(1,1);(2,2)]
        in
          List.iter 
          (fun (t:TBrs.trans) ->
            let t_res_s = t.res_state
            and t_res_f = t.residue
            in
              assert_equal us1 t_res_s;
              assert_equal ~cmp:(fun r1 r2 -> Fun.equal r1 r2) expected_residue t_res_f
          ) rt
let test_norm_ss_2 _ =
  let us1 = Big.of_string "{(0, A:0),(1, B:0),(2, C:0)}\n0 3 0\n010\n001\n000"
  and us2 = Big.of_string "{(0, X:0),(1, Y:0),(2, Z:0)}\n0 3 0\n010\n001\n000"
  in
    let is11 = Big.of_string "{(0, C:0),(1, A:0),(2, B:0)}\n0 3 0\n000\n001\n100"
    and is12 = Big.of_string "{(0, C:0),(1, B:0),(2, A:0)}\n0 3 0\n000\n100\n010"
    and is21 = Big.of_string "{(0, Z:0),(1, X:0),(2, Y:0)}\n0 3 0\n000\n001\n100"
    and is22 = Big.of_string "{(0, Z:0),(1, Y:0),(2, X:0)}\n0 3 0\n000\n100\n010"
    in
      let t_us1_is11_residue = Fun.empty |> Fun.add 0 2 |> Fun.add 1 0 |> Fun.add 2 1
      and t_us1_is12_residue = Fun.empty |> Fun.add 0 2 |> Fun.add 1 1 |> Fun.add 2 0
      and t_us2_is21_residue = Fun.empty |> Fun.add 0 2 |> Fun.add 1 0 |> Fun.add 2 1
      and t_us2_is22_residue = Fun.empty |> Fun.add 0 2 |> Fun.add 1 1 |> Fun.add 2 0
    in
      let t111 = TBrs.parse_trans_unsafe ~init:us1 ~result:is11 Iso.empty t_us1_is11_residue ""
      and t112 = TBrs.parse_trans_unsafe ~init:us1 ~result:is12 Iso.empty t_us1_is12_residue ""
      and t221 = TBrs.parse_trans_unsafe ~init:us2 ~result:is21 Iso.empty t_us2_is21_residue ""
      and t222 = TBrs.parse_trans_unsafe ~init:us2 ~result:is22 Iso.empty t_us2_is22_residue ""
      in
        let rt = TBrs.norm_ss [t111;t112;t221;t222] [us1;us2]
        and expected_residue = Fun.of_list [(0,0);(1,1);(2,2)]
        in
          List.iter 
          (fun (t:TBrs.trans) ->
            let t_res_s = t.res_state
            and t_res_f = t.residue
            in
              assert_equal true (us1 = t_res_s || us2 = t_res_s);
              assert_equal ~cmp:(fun r1 r2 -> Fun.equal r1 r2) expected_residue t_res_f
          ) rt
let test_norm_ss_3 _ =
  let us1 = Big.of_string "{(0, A:0),(1, B:0),(2, C:0)}\n0 3 0\n010\n001\n000"
  and us2 = Big.of_string "{(0, X:0),(1, Y:0),(2, Z:0),(3, W:0)}\n0 4 0\n0100\n0010\n0001\n0000"
  in
    let is21 = Big.of_string "{(0, W:0),(1, Z:0),(2, Y:0),(3, X:0)}\n0 4 0\n0000\n1000\n0100\n0010"
    and is22 = Big.of_string "{(0, Z:0),(1, X:0),(2, W:0),(3, Y:0)}\n0 4 0\n0010\n0001\n0000\n1000"
    in
      let t_us1_is21_residue = Fun.empty |> Fun.add 3 0 |> Fun.add 2 0 |> Fun.add 0 1
      and t_us1_is22_residue = Fun.empty |> Fun.add 1 0 |> Fun.add 3 0 |> Fun.add 2 1
    in
      let t121 = TBrs.parse_trans_unsafe ~init:us1 ~result:is21 Iso.empty t_us1_is21_residue ""
      and t122 = TBrs.parse_trans_unsafe ~init:us1 ~result:is22 Iso.empty t_us1_is22_residue ""
      in
        let _ = Parmap.set_default_ncores 2
        and rt = TBrs.parnorm_ss [t121;t122] [us1;us2]
        and expected_residue = Fun.of_list [(0,0);(1,0);(3,1)]
        in
          List.iter 
          (fun (t:TBrs.trans) ->
            let t_res_s = t.res_state
            and t_res_f = t.residue
            in
              assert_equal us2 t_res_s;
              assert_equal ~cmp:(fun r1 r2 -> Fun.equal r1 r2) expected_residue t_res_f
          ) rt
let test_parnorm_ss_1 _ =
  let us1 = Big.of_string "{(0, A:0),(1, B:0),(2, C:0)}\n0 3 0\n010\n001\n000"
  in
    let is11 = Big.of_string "{(0, C:0),(1, A:0),(2, B:0)}\n0 3 0\n000\n001\n100"
    and is12 = Big.of_string "{(0, C:0),(1, B:0),(2, A:0)}\n0 3 0\n000\n100\n010"
    and is13 = Big.of_string "{(0, B:0),(1, C:0),(2, A:0)}\n0 3 0\n010\n000\n100"
    in
      let t_us1_is11_residue = Fun.empty |> Fun.add 0 2 |> Fun.add 1 0 |> Fun.add 2 1
      and t_us1_is12_residue = Fun.empty |> Fun.add 0 2 |> Fun.add 1 1 |> Fun.add 2 0
      and t_us1_is13_residue = Fun.empty |> Fun.add 0 1 |> Fun.add 1 2 |> Fun.add 2 0
    in
      let t111 = TBrs.parse_trans_unsafe ~init:us1 ~result:is11 Iso.empty t_us1_is11_residue ""
      and t112 = TBrs.parse_trans_unsafe ~init:us1 ~result:is12 Iso.empty t_us1_is12_residue ""
      and t113 = TBrs.parse_trans_unsafe ~init:us1 ~result:is13 Iso.empty t_us1_is13_residue ""
      in
        let _ = Parmap.set_default_ncores 2
        and rt = TBrs.parnorm_ss [t111;t112;t113] [us1]
        and expected_residue = Fun.of_list [(0,0);(1,1);(2,2)]
        in
          List.iter 
          (fun (t:TBrs.trans) ->
            let t_res_s = t.res_state
            and t_res_f = t.residue
            in
              assert_equal us1 t_res_s;
              assert_equal ~cmp:(fun r1 r2 -> Fun.equal r1 r2) expected_residue t_res_f
          ) rt
let test_parnorm_ss_2 _ =
  let us1 = Big.of_string "{(0, A:0),(1, B:0),(2, C:0)}\n0 3 0\n010\n001\n000"
  and us2 = Big.of_string "{(0, X:0),(1, Y:0),(2, Z:0)}\n0 3 0\n010\n001\n000"
  in
    let is11 = Big.of_string "{(0, C:0),(1, A:0),(2, B:0)}\n0 3 0\n000\n001\n100"
    and is12 = Big.of_string "{(0, C:0),(1, B:0),(2, A:0)}\n0 3 0\n000\n100\n010"
    and is21 = Big.of_string "{(0, Z:0),(1, X:0),(2, Y:0)}\n0 3 0\n000\n001\n100"
    and is22 = Big.of_string "{(0, Z:0),(1, Y:0),(2, X:0)}\n0 3 0\n000\n100\n010"
    in
      let t_us1_is11_residue = Fun.empty |> Fun.add 0 2 |> Fun.add 1 0 |> Fun.add 2 1
      and t_us1_is12_residue = Fun.empty |> Fun.add 0 2 |> Fun.add 1 1 |> Fun.add 2 0
      and t_us2_is21_residue = Fun.empty |> Fun.add 0 2 |> Fun.add 1 0 |> Fun.add 2 1
      and t_us2_is22_residue = Fun.empty |> Fun.add 0 2 |> Fun.add 1 1 |> Fun.add 2 0
    in
      let t111 = TBrs.parse_trans_unsafe ~init:us1 ~result:is11 Iso.empty t_us1_is11_residue ""
      and t112 = TBrs.parse_trans_unsafe ~init:us1 ~result:is12 Iso.empty t_us1_is12_residue ""
      and t221 = TBrs.parse_trans_unsafe ~init:us2 ~result:is21 Iso.empty t_us2_is21_residue ""
      and t222 = TBrs.parse_trans_unsafe ~init:us2 ~result:is22 Iso.empty t_us2_is22_residue ""
      in
        let _ = Parmap.set_default_ncores 2
        and rt = TBrs.norm_ss [t111;t112;t221;t222] [us1;us2]
        and expected_residue = Fun.of_list [(0,0);(1,1);(2,2)]
        in
          List.iter 
          (fun (t:TBrs.trans) ->
            let t_res_s = t.res_state
            and t_res_f = t.residue
            in
              assert_equal true (us1 = t_res_s || us2 = t_res_s);
              assert_equal ~cmp:(fun r1 r2 -> Fun.equal r1 r2) expected_residue t_res_f
          ) rt
let test_parnorm_ss_3 _ =
  let us1 = Big.of_string "{(0, A:0),(1, B:0),(2, C:0)}\n0 3 0\n010\n001\n000"
  and us2 = Big.of_string "{(0, X:0),(1, Y:0),(2, Z:0),(3, W:0)}\n0 4 0\n0100\n0010\n0001\n0000"
  in
    let is21 = Big.of_string "{(0, W:0),(1, Z:0),(2, Y:0),(3, X:0)}\n0 4 0\n0000\n1000\n0100\n0010"
    and is22 = Big.of_string "{(0, Z:0),(1, X:0),(2, W:0),(3, Y:0)}\n0 4 0\n0010\n0001\n0000\n1000"
    in
      let t_us1_is21_residue = Fun.empty |> Fun.add 3 0 |> Fun.add 2 0 |> Fun.add 0 1
      and t_us1_is22_residue = Fun.empty |> Fun.add 1 0 |> Fun.add 3 0 |> Fun.add 2 1
    in
      let t121 = TBrs.parse_trans_unsafe ~init:us1 ~result:is21 Iso.empty t_us1_is21_residue ""
      and t122 = TBrs.parse_trans_unsafe ~init:us1 ~result:is22 Iso.empty t_us1_is22_residue ""
      in
        let rt = TBrs.norm_ss [t121;t122] [us1;us2]
        and expected_residue = Fun.of_list [(0,0);(1,0);(3,1)]
        in
          List.iter 
          (fun (t:TBrs.trans) ->
            let t_res_s = t.res_state
            and t_res_f = t.residue
            in
              assert_equal us2 t_res_s;
              assert_equal ~cmp:(fun r1 r2 -> Fun.equal r1 r2) expected_residue t_res_f
          ) rt


let suite =
  "TBrs tests" >::: [
    "Norm ss 1">:: test_norm_ss_1;
    "Norm ss 2">:: test_norm_ss_2;
    "Norm ss 3">:: test_norm_ss_3;
    "Parnorm ss 1">:: test_parnorm_ss_1;
    "Parnorm ss 2">:: test_parnorm_ss_2;
    "Parnorm ss 3">:: test_parnorm_ss_3;
]

let () =
  run_test_tt_main suite