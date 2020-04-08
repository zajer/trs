open Digraph
open Bigraph
let nodes_to_json ns = 
    NS.fold 
        (
            fun (i,ndsc) res -> 
                let j_node = `List [ `Int i ; `String ndsc ]
                in
                j_node::res
        ) 
        ns 
        []
    
let edges_to_json es =
    Sparse.fold (fun f t res -> `List [ `Int f; `Int t ] :: res ) es []

let dig_to_json g =
    let j_nodes = nodes_to_json g.nodes
    and j_edges = edges_to_json g.edges
    in
        `Assoc 
        [
            ("nodes", `List j_nodes); ("edges", `List j_edges)
        ]