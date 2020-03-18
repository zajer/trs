open OUnit2
open Bigraph
open Tracking_bigraph.Utils
let test_transform_fun_codom_1 _ = 
  let f = Fun.empty |> Fun.add 0 0 |> Fun.add 1 1  
  and i = Iso.empty |> Iso.add 0 4 |> Iso.add 1 3
  and exp_res = Fun.empty |> Fun.add 0 4 |> Fun.add 1 3
  in
    let res = transform_fun_codom f i
    in
    assert_equal exp_res res
let test_transform_fun_codom_2 _ = 
let f = Fun.empty |> Fun.add 1 2 |> Fun.add 7 5  
and i = Iso.empty |> Iso.add 2 4 |> Iso.add 5 13
and exp_res = Fun.empty |> Fun.add 1 4 |> Fun.add 7 13
in
  let res = transform_fun_codom f i
  in
  assert_equal exp_res res
let test_transform_fun_dom_1 _ = 
let f = Fun.empty |> Fun.add 0 0 |> Fun.add 1 1  
and i = Iso.empty |> Iso.add 0 4 |> Iso.add 1 3
and exp_res = Fun.empty |> Fun.add 4 0 |> Fun.add 3 1
in
  let res = transform_fun_dom f i
  in
  assert_equal exp_res res
let test_transform_fun_dom_2 _ = 
let f = Fun.empty |> Fun.add 1 2 |> Fun.add 7 5  
and i = Iso.empty |> Iso.add 1 4 |> Iso.add 7 13
and exp_res = Fun.empty |> Fun.add 4 2 |> Fun.add 13 5
in
  let res = transform_fun_dom f i
  in
  assert_equal exp_res res
let test_shift_iso_codom_1 _ =
  let iso = Iso.empty |> Iso.add 0 0 |> Iso.add 1 1
  and shift = 1
  and exp_res = Iso.empty |> Iso.add 0 1 |> Iso.add 1 2
  in
    let res = shift_iso_codom iso shift
    in
      assert_equal exp_res res

let suite =
  "Utils tests" >::: [
    "Transform codom 1">:: test_transform_fun_codom_1;
    "Transform codom 2">:: test_transform_fun_codom_2;
    "Transform dom 1">:: test_transform_fun_dom_1;
    "Transform dom 2">:: test_transform_fun_dom_2;
    "Shift codom 1">:: test_shift_iso_codom_1;
  ]
let () =
  Py.initialize ~version:3 ();
  run_test_tt_main suite