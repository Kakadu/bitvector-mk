open OCanren
open Tester
open EvalPh

let __ =
  let (module BV) = Bv.create 4 in
  let runBV =
    Tester.runR Bv.Repr.reify (GT.show Bv.Repr.g) (GT.show Bv.Repr.l)
  in
  let runR = Tester.runR Ph.reify (GT.show Ph.ground) (GT.show Ph.logic) in
  let runS = Tester.run_exn (GT.show GT.string) in
  let runT = Tester.runR T.reify (GT.show T.ground) (GT.show T.logic) in
  let evalo = EvalPh.evalo (module BV) in
  let _ = runT in
  let _ = runR in
  let _ = runS in
  let _ = runBV in
  let _ = evalo in

  let forallo relo =
    let p = 1 lsl BV.width in
    let rec loop n acc =
      if n >= p then acc else loop (1 + n) (acc &&& relo (BV.build_num n))
    in
    loop 0 success
  in
  let _ = forallo in

  (*
  runBV (-1) q qh (REPR (fun q -> q === BV.build_num 15 &&& BV.leo q q));
  runBV (-1) q qh (REPR (fun q -> q === BV.build_num 15 &&& BV.lto q q));
  runBV (-1) q qh (REPR (fun q -> BV.lshiftr1 (BV.build_num 15) q));
  runBV (-1) q qh (REPR (fun q -> BV.lto (BV.build_num 15) (BV.build_num 7)));
  runBV (-1) q qh
    (REPR (fun q -> fresh t (BV.lshiftr1 (BV.build_num 15) t) (BV.lto q t))); *)

  (* runBV (-1) q qh (REPR (fun q -> BV.lto (BV.build_num 1) (BV.build_num 0)));

     runBV (-1) q qh (REPR (fun q -> BV.lto (BV.build_num 1) (BV.build_num 0)));
  *)
  runR 15 q qh
    (REPR
       (fun q ->
         evalo (Env.cons !!"x" (T.const @@ BV.build_num 15) Env.empty) q));

  (*
  runS 1 q qh
    (REPR
       (fun s ->
         s === !!"tautology"
         &&& forallo (fun q ->
                 fresh rez (BV.addo q q rez) (BV.multo q (BV.build_num 2) rez))));
*)

  (*
  runBV 15 q qh
    (REPR
       (fun q ->
         fresh (r1 r2) (r1 =/= r2) (BV.addo q q r1)
           (BV.multo q (BV.build_num 2) r2)));
 *)
  (* runBV 15 q qh (REPR (fun q -> BV.multo (BV.build_num 1) (BV.build_num 2) q)); *)

  (* runBV 15 q qh (REPR (fun q -> BV.addo (BV.build_num 1) (BV.build_num 1) q)); *)

  (* runBV 15 q qh (REPR (fun q -> q === BV.build_num 1)); *)
  ()
