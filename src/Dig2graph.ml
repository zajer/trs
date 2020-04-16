open Onauty
open Bigraph
let dig_2_graph (d:Digraph.graph) =
    let non = Digraph.NS.cardinal d.nodes
    and edges = Sparse.fold (fun f t res -> (f,t)::res) d.edges []
    in
        let result_no_color = Graph.empty () |> Graph.add_vertices non |> Graph.add_conns edges
        in
            Digraph.NS.fold 
                (fun (vid,color) res_graph -> Graph.color_vertex color vid res_graph ) 
                d.nodes
                result_no_color