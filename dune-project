(lang dune 3.19)

(name ocaml_sat)

(generate_opam_files true)

(source
 (github username/reponame))

(authors "Author Name <author@example.com>")

(using menhir 2.1)

(maintainers "Maintainer Name <maintainer@example.com>")

(license LICENSE)

(documentation https://url/to/documentation)

(package
 (name ocaml_sat)
 (synopsis "A short synopsis")
 (description "A longer description")
 (depends ocaml)
 (tags
  ("add topics" "to describe" your project)))

; See the complete stanza docs at https://dune.readthedocs.io/en/stable/reference/dune-project/index.html
