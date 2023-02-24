(lang dune 3.6)

(generate_opam_files true)

(name BitvectorMK)

(package
 (name BitvectorMK)
 (depends
  ctypes-foreign
  z3
  ppx_fail
  GT
  ppx_inline_test
  ppx_expect
  OCanren
  ;
  ))
