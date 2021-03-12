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
let test_iso_as_string_to_iso_1 _ =
  let to_convert = "{(3,4),(1,2),(7,7)}"
  and expected_result = [(3,4);(1,2);(7,7)] |> Iso.of_list in
  let parsed_iso = iso_as_string_to_iso to_convert in
  assert_equal 
    ~msg:"Parsed iso is not equal to expected" 
    ~printer:( fun iso -> Iso.to_string iso ) 
    ~cmp:(fun iso1 iso2 -> Iso.equal iso1 iso2) 
    expected_result 
    parsed_iso
let test_iso_as_string_to_iso_2 _ =
  let to_convert = "{ (3 , 4), (1 ,2) ,(7,7) , (8, 9) } "
  and expected_result = [(3,4);(1,2);(7,7);(8,9)] |> Iso.of_list in
  let parsed_iso = iso_as_string_to_iso to_convert in
  assert_equal 
    ~msg:"Parsed iso is not equal to expected" 
    ~printer:( fun iso -> Iso.to_string iso ) 
    ~cmp:(fun iso1 iso2 -> Iso.equal iso1 iso2) 
    expected_result 
    parsed_iso
let test_fun_as_string_to_fun_1 _ =
  let to_convert = "{(3,4),(1,2),(7,7)}"
  and expected_result = [(3,4);(1,2);(7,7)] |> Fun.of_list in
  let parsed_iso = fun_as_string_to_fun to_convert in
  assert_equal 
    ~msg:"Parsed fun is not equal to expected" 
    ~printer:( fun func -> Fun.to_string func ) 
    ~cmp:(fun fun1 fun2 -> Fun.equal fun1 fun2) 
    expected_result 
    parsed_iso
let test_fun_as_string_to_fun_2 _ =
  let to_convert = "{ (3 , 4), (1 ,2) ,(7,7) , (8, 9) } "
  and expected_result = [(3,4);(1,2);(7,7);(8,9)]  |> Fun.of_list in
  let parsed_iso = fun_as_string_to_fun to_convert in
  assert_equal 
    ~msg:"Parsed fun is not equal to expected" 
    ~printer:( fun func -> Fun.to_string func ) 
    ~cmp:(fun fun1 fun2 -> Fun.equal fun1 fun2) 
    expected_result 
    parsed_iso
let test_fun_as_string_to_fun_3 _ =
  let to_convert = "{(3,4),(1,2),(7,7),(5,7)}"
  and expected_result = [(3,4);(1,2);(7,7);(5,7)] |> Fun.of_list in
  let parsed_iso = fun_as_string_to_fun to_convert in
  assert_equal 
    ~msg:"Parsed fun is not equal to expected" 
    ~printer:( fun func -> Fun.to_string func ) 
    ~cmp:(fun fun1 fun2 -> Fun.equal fun1 fun2) 
    expected_result 
    parsed_iso
let suite =
  "Utils tests" >::: [
    "Transform codom 1">:: test_transform_fun_codom_1;
    "Transform codom 2">:: test_transform_fun_codom_2;
    "Transform dom 1">:: test_transform_fun_dom_1;
    "Transform dom 2">:: test_transform_fun_dom_2;
    "Shift codom 1">:: test_shift_iso_codom_1;
    "Converting iso as string to iso 1" >:: test_iso_as_string_to_iso_1;
    "Converting iso as string to iso 2" >:: test_iso_as_string_to_iso_2;
    "Converting fun as string to fun 1" >:: test_fun_as_string_to_fun_1;
    "Converting fun as string to fun 2" >:: test_fun_as_string_to_fun_2;
    "Converting fun as string to fun 3" >:: test_fun_as_string_to_fun_3

  ]
let () =
  run_test_tt_main suite