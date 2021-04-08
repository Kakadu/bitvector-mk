open EvalPh
open OCanren

let __ =
  let runR = Tester.runR (GT.show Ph.ground) (GT.show Ph.logic) in
  1
