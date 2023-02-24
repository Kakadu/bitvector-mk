(lang dune 3.4)

(generate_opam_files true)

(name bitvector-mk)

(package
 (name bitvector-mk)
 (depends
  ctypes-foreign
  z3
  ppx_fail
  res
  GT
  ppx_inline_test
  ppx_expect
  OCanren
  ;
  ))
