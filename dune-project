(lang dune 2.0)
(name tracking_bigraph)
(version 0.1)
(generate_opam_files true)

(source (uri https://github.com/zajer/trs))
(license BSD-2-Clause)
(authors "Piotr Cybulski <pikus3@list.pl>")
(maintainers "Piotr Cybulski <pikus3@list.pl>")

(package
  (name tracking_bigraph)
  (synopsis "An OCaml library for Tracking Reactive Systems")
  (description "A description")
  (tags ("bigraph" "tracking" "trs" "brs") )
  (depends
    (dune (and :build (>= 2.0.0)))
    bigraph
    parmap
    csv
  )
)
