(lang dune 2.0)
(name tracking_bigraph)
(version 0.7.0)
(generate_opam_files true)

(source (github zajer/trs))
(license BSD-2-Clause)
(authors "Piotr Cybulski <pikus3@list.pl>")
(maintainers "Piotr Cybulski <pikus3@list.pl>")
(homepage "https://github.com/zajer/trs")
(bug_reports "https://github.com/zajer/trs/issues")

(package
  (name tracking_bigraph)
  (synopsis "An OCaml library for Tracking Reactive Systems")
  (description "
    Tracking_bigraph is an addon to the OCaml library \"bigraph\". 
    It allows designing and evaluating bigraphical reactive systems with nodes tracking between state transitions. 
    Additionally it allows to export calculated state space to a file. 
    It also tries to parallelize some of computations.")
  (tags ("bigraph" "tracking" "trs" "brs") )
  (depends
    (dune (and :build (>= 2.0.0)))
    bigraph
    parmap
    csv
    onauty
    zarith
    (ounit2 :with-test)
  )
)
