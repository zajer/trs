(lang dune 2.0)
(name my_super_name)
(version 0.0.0)
(generate_opam_files true)

(source (uri http://www.google.com))
(license BSD-2-Clause)
(authors "Bruce Wayne")
(maintainers "bruce.wayne@gotham.com")
(homepage "http://www.google.com")
(documentation "http://www.google.com")

(package
  (name my_super_name)
  (synopsis "Summary")
  (description "A description")
  (tags ("yolo" "swag"))
  (depends
    (dune (and :build (>= 2.0.0)))
    (odoc :with-doc)))
  
