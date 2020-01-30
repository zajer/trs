open OUnit2
open Bigraph
open Tracking_bigraph

let test_prepare_fun_of_residue_1 _ =
  let i_t2c = Iso.empty |> Iso.add 0 0 |> Iso.add 1 1 
  and i_p2t = Iso.empty |> Iso.add 0 2 |> Iso.add 1 3 |> Iso.add 2 4
  and i_t2d = Iso.empty |> Iso.add 5 0 |> Iso.add 6 1 
  and f_r1_in_r0 = Fun.empty |> Fun.add 0 0 |> Fun.add 1 2
  and c_n_n = 2
  and r1_n_n = 2
  and d_n_n = 3
  in
    let exp_res = Fun.empty |> 
      Fun.add 0 0 |> 
      Fun.add 1 1 |> 
      Fun.add 2 2 |> 
      Fun.add 3 4 |> 
      Fun.add 4 5 |> 
      Fun.add 5 6
    and res = TBig.prepare_basic_fun_of_residue ~c_n_n ~r1_n_n ~d_n_n ~iso_p2t_n:i_p2t ~iso_t2c_n:i_t2c ~iso_t2d_n:i_t2d f_r1_in_r0
    in
      assert_equal ~cmp:(fun x y -> Fun.equal x y) exp_res res

let suite =
  "TBig tests" >::: [
    "Prepare function of residue 1">:: test_prepare_fun_of_residue_1;
]

let () =
  run_test_tt_main suite
