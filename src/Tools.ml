module type ToolsBoilerplate = sig
  type t
  val convert : Bigraph.Big.t -> t
  val hash : t -> Z.t
  val are_isomorphic : t -> t -> bool
end

module DigraphTools =
  struct
  type t = Digraph.t
  let convert = Digraph.big_2_dig
  let hash = Digraph.hash_graph
  let are_isomorphic = Digraph.are_digraphs_iso
end