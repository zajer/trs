open Bigraph

let transform_fun_codom f i = 
  let id_dom = IntSet.fold (fun i res -> Iso.add i i res) (Fun.dom f) Iso.empty
  in
    Fun.transform ~iso_dom:id_dom ~iso_codom:i f
let transform_fun_dom f i = 
    let id_codom = IntSet.fold (fun i res -> Iso.add i i res) (Fun.codom f) Iso.empty
    in
      Fun.transform ~iso_dom:i ~iso_codom:id_codom f
let transform_iso_dom ~transformed:i_2transform ~applied:i_2apply =
  let id_codom = List.fold_left (fun res i -> Iso.add i i res) Iso.empty (Iso.codom i_2transform)
    in
      Iso.transform ~iso_dom:i_2apply ~iso_codom:id_codom i_2transform
let shift_iso_codom i c =
  Iso.fold (fun i_c i_a res-> Iso.add i_c (i_a+c) res ) i Iso.empty
let iso_apply i e =
  Option.get (Iso.apply i e)
let flat_isos_into_rel il = 
  let common_source = List.fold_left (fun acc i -> IntSet.union acc (IntSet.of_list (Iso.dom i))  ) IntSet.empty il
  in
    let lop = IntSet.fold 
      (fun x res -> 
        (
          x, 
          (List.fold_left 
            (
              fun part_res i ->  
                if Iso.mem x i then
                  (iso_apply i x)::part_res
                else
                  part_res
            )
            []
            il 
          ) 
        )::res 
      ) 
      common_source 
      []
    in
    Rel.of_list lop
let transform_rel_codom r i =
  Rel.fold (fun x is res -> Rel.add x (IntSet.apply i is) res ) r Rel.empty
let transform_rel_dom r i =
  Rel.fold 
    (fun x is res -> 
      if Iso.mem x i then
        Rel.add (iso_apply i x) is res 
      else
        res
    ) 
    r 
    Rel.empty
let merge_rel_with_iso r i =
  Iso.fold (fun i1 i2 res -> Rel.add i1 (IntSet.singleton i2) res ) i r
let _str_to_list_of_int_pairs str =
  let pairs_regex = "\\([0-9]+\\s*,\\s*[0-9]+\\)" |> Str.regexp
  and single_number_regex = "[0-9]+" |> Str.regexp in
  let list_of_pairs_as_str = Str.split pairs_regex str in
  List.map 
    (fun pair_as_str -> 
      let values = Str.split single_number_regex pair_as_str |> List.map (fun s -> int_of_string s) in
      assert (List.length values = 2) ;
      (List.nth values 0 ),(List.nth values 1)
    )
    list_of_pairs_as_str
let iso_as_string_to_iso iso_as_str =
  _str_to_list_of_int_pairs iso_as_str |> Iso.of_list
let fun_as_string_to_fun iso_as_str =
  _str_to_list_of_int_pairs iso_as_str |> Fun.of_list