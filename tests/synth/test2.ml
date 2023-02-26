open Synth
open OCanren
open Types

let bv_size = 2

let () =
  let hint ans_var =
    fresh
      (ph0 ph1 ph2 ph3 a b l0 r0 l1 r1 l2 r2 ans_var2 o3 l3 r3)
      (a === Types.(T.var !!"a"))
      (b === Types.(T.var !!"b"))
      (* (ph0 === Types.Ph.le b a) *)
      (* (ph1 === Types.Ph.le (Types.T.shl b (Types.T.const @@ BV.build_num 1)) a) *)
      (* (ph2 === Types.Ph.le (Types.T.shl b (Types.T.const @@ BV.build_num 2)) a) *)
      (* (ph3 === Types.Ph.le (Types.T.shl b (Types.T.const @@ BV.build_num 3)) a) *)
      (* (ph0 === Types.Ph.le l0 a) *)
      (* (ph1 === Types.Ph.le l1 a) *)
      (* (ph2 === Types.Ph.le l2 a) *)
      (* (ph3 === Types.Ph.le l3 a) *)
      (* (ph2 === Types.Ph.le (Types.T.shl b l2) a) *)
      (* (ph3 === Types.Ph.le (Types.T.shl l3 (Types.T.const @@ BV.build_num 3)) a) *)
      (* (ph3 === Types.Ph.le (Types.T.shl b r3) a) *)
      (* (fresh (u v) (r3 =/= Types.T.op !!Types.T.Shl u v)) *)
      (* (fresh v (r3 === Types.T.const v)) *)
      (* (ph0 === Types.Ph.op !!Types.Ph.Le l0 r0)
         (ph1 === Types.Ph.op !!Types.Ph.Le l1 r1)
         (ph2 === Types.Ph.op !!Types.Ph.Le l2 r2)
         (ph3 === Types.Ph.op !!Types.Ph.Le l3 r3) *)
      (ans_var
      === Ph.(not (conj_list (list_take bv_size [ ph0; ph1; ph2; ph3 ]))))
  in

  test bv_size Inhabit_ph.evalo Algebra.ex4 ~hint
