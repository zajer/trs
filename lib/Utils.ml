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