open EvalPh
open OCanren
open Tester

let __ =
  let runR = Tester.runR (GT.show Ph.ground) (GT.show Ph.logic) in

  let (module BV) = Bv.create 4 in
  let evalo = EvalPh.evalo (module BV) in

  runR q qh (REPR (evalo Env.(cons !!"x" (BV.build_num 15) empty)));

  1
