(lang dune 3.5)

(generate_opam_files true)

(name bitvector-mk)

(package
 (name bitvector-mk)
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
