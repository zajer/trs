(lang dune 2.0)
(name tracking_bigraph)
(version 0.3.1)
(generate_opam_files true)

(source (uri https://github.com/zajer/trs))
(license BSD-2-Clause)
(authors "Piotr Cybulski <pikus3@list.pl>")
(maintainers "Piotr Cybulski <pikus3@list.pl>")

(package
  (name tracking_bigraph)
  (synopsis "An OCaml library for Tracking Reactive Systems")
  (description "Tracking_bigraph is an addon to the OCaml library \"bigraph\" made by Michele Sevegnani. It allows designing and evaluating bigraphical reactive systems with nodes tracking (hence the tracking reactive systems name comes from). Additionally it allows for export of calculated state space to a file. It also tries to parallelize some of computations.")
  (tags ("bigraph" "tracking" "trs" "brs") )
  (depends
    (dune (and :build (>= 2.0.0)))
    bigraph
    parmap
    csv
  )
)
