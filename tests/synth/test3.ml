open Synth
open OCanren
open Types

let bv_size = 3

let hint ans_var =
  fresh (ph0 ph1 ph2 ph3 a b)
    (a === Types.(T.var !!"a"))
    (b === Types.(T.var !!"b"))
    (ph0 === Ph.le __ a)
    (ph1 === Ph.le __ a)
    (ph2 === Ph.le __ __)
    (ph3 === Ph.le __ a)
    (ans_var === Ph.(not (conj_list (list_take bv_size [ ph0; ph1; ph2; ph3 ]))))

let () = test bv_size Inhabit_ph.evalo Algebra.ex4 ~hint
