(lang dune 3.10)

(using menhir 2.1)

(name aml)

(source
 (github johnyob/aml))

(authors "Alistair O'Brien")

(maintainers "ajo41@cam.ac.uk")

(license GPL-3.0-only)

(generate_opam_files true)

(package
 (name aml)
 (depends ocaml dune core core_unix ppx_jane fmt menhir grace))
