open Bigraph

let big_nodes_2_dig_nodes ns = 
    Nodes.fold (fun i n res-> (i,Ctrl.to_string n)::res ) ns []
let big_hedges_2_dig_nodes ~nohe ~non =
    List.init nohe (fun i -> i+non,"HE")
let big_hedges_2_dig_nodes_adv hedges ~non = 
    let res,_ = Link.Lg.fold 
        (
            fun hedg (res_list,curr_idx) -> 
                let node = (curr_idx+non,"HE-C:"^(Link.Ports.cardinal hedg.p |> string_of_int) )
                in 
            node::res_list,(curr_idx+1)
        )
        hedges
        ([],0)
    in
    res
let big_place_2_dig_edges p =
    Sparse.fold 
    (fun f t loe -> 
        (*"from:"^(string_of_int f) |> print_endline ;
        "to:"^(string_of_int t) |> print_endline ;*)
        (f,t)::loe 
    )
    p.Place.nn
    []
let big_link_2_dig_edges (l:Link.Lg.t) non =
    let loe,_ = Link.Lg.fold 
    (
        fun edg (loe,edge_as_node_id) -> 
        let ploe =Link.Ports.fold 
            (fun n _ ploe -> (n, edge_as_node_id)::ploe ) 
            edg.p
            []
        in
        ploe@loe,(edge_as_node_id+1)
    )
    l
    ([],non)
    in
    loe

type nt = int*string

module NS = Set.Make( 
    struct
    let compare = (fun (i1,_) (i2,_)  -> Stdlib.compare i1 i2)
    type t = nt
    end )
type t = NS.t*Bigraph.Sparse.t
let big_2_dig (b:Big.t) =
    let non = Nodes.size b.n
    and nohe = Link.Lg.cardinal b.l
    in
        (*let ns = (big_nodes_2_dig_nodes b.n)@(big_hedges_2_dig_nodes ~nohe ~non)*)
        let ns = (big_nodes_2_dig_nodes b.n)@(big_hedges_2_dig_nodes_adv b.l ~non)
        and es = (big_place_2_dig_edges b.p)@(big_link_2_dig_edges b.l non)
        in
            let adj_part = Sparse.make (non+nohe) (non+nohe) |> Sparse.add_list
            and ns = NS.of_list ns
            in
            ns,adj_part es

let hash_string str =
    let digest = (Digest.string str)
    in
        let digest_bytes = Bytes.of_string digest
        
        in
            let digF8i64 = Bytes.get_int64_ne digest_bytes 0
            and digL8i64 = Bytes.get_int64_ne digest_bytes 8
            
            in
                let digF8 =  (Z.of_int64 digF8i64) 
                and digL8 = Z.shift_left (Z.of_int64 digL8i64) 64
                in
                    Z.add digF8 digL8

let hash_string_512 str =
    let digest = Sha512.string str
    in
    let digest_bin = Sha512.to_bin digest
    in
        let res = Z.of_bits digest_bin
        in
        (*(Sha512.to_hex digest ) |> print_endline;
        "Big_hex:"^(Z.to_bits res |> Hex.of_string |> Hex.show )  |> print_endline ;*)
        res
let average_of_chl sum num_of_chl =
    Z.fdiv sum num_of_chl
let hash_hash hsh =
    hash_string (Z.to_string hsh)
let hash_of_single_node node children flag=
    let my_hash = hash_string node
    and hash_of_children = hash_hash children
    in
        if flag > 0 then (
        "my hash="^(Z.to_string my_hash) |> print_endline;
        "chl hash="^(Z.to_string hash_of_children) |> print_endline;
        "res hash="^(Z.to_string (Z.add my_hash hash_of_children )) |> print_endline);
        (*let my_res = Z.add my_hash hash_of_children
        in
        hash_hash my_res*)
        Z.add my_hash hash_of_children

let rec hash_of_node node_id nodes adj_mx =
    let children = Sparse.chl adj_mx node_id
    and flag = if node_id = -1 then 1 else 0
    and _,node_to_hash = NS.find (node_id,"") nodes
    in
        let num_of_chl = IntSet.cardinal children
        in
            if flag > 0 then "Liczba nastepnikow dla node_id:"^(string_of_int node_id)^" jest rowna="^(string_of_int num_of_chl) |> print_endline;
            if num_of_chl = 0 then
                    hash_of_single_node node_to_hash Z.zero flag
            else
                let part_ress = Hashtbl.create num_of_chl
                in
                let children_hash = IntSet.fold 
                    (
                        fun child_id sum-> 
                            let chl_hash = hash_of_node child_id nodes adj_mx
                            in
                                Hashtbl.add part_ress child_id chl_hash;
                                if flag > 0 then "part res dla node_id="^(string_of_int node_id)^" :"^(Z.to_string chl_hash) |> print_endline;
                                Z.add chl_hash sum
                        
                    )
                    children
                Z.zero (*|> average_of_chl (Z.of_int num_of_chl)*)
                (*in
                let children_hash = IntSet.fold 
                    (
                        fun child_id sum -> 
                            let hash_of_child = Hashtbl.find part_ress child_id
                            in
                                let div_between_avg = Z.min hash_of_child avg_among_children
                                in
                                Z.add sum div_between_avg
                                
                    )
                    children
                Z.zero*)
                in
                    hash_of_single_node node_to_hash children_hash flag

let hash_graph (nodes,adj_mx) =
    let orpans = Sparse.orphans adj_mx
    in
        if IntSet.cardinal orpans <> 1 then
            failwith "Tylko jeden orphan"
        else
            let root_id = Option.get (IntSet.min_elt orpans )
            in
            hash_of_node root_id nodes adj_mx
            
