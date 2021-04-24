open OCanren
open Tester
open Types

let debug_n : Bv.Repr.n -> (int logic Std.List.logic list -> goal) -> goal =
 fun n -> debug_var n (fun a b -> OCanren.Std.List.reify OCanren.reify b a)

let trace_bv n fmt =
  debug_n n (function
    | [ n ] ->
        Format.printf "%s: %s\n%!" (Format.asprintf fmt) (Bv.Repr.show_logic n);
        success
    | _ -> assert false)

let __ =
  let (module BV) = Bv.create 4 in
  let runBV =
    Tester.runR Bv.Repr.reify (GT.show Bv.Repr.g) (GT.show Bv.Repr.l)
  in
  let runF = Tester.runR Ph.reify (GT.show Ph.ground) (GT.show Ph.logic) in
  let runS = Tester.run_exn (GT.show GT.string) in
  let runT = Tester.runR T.reify (GT.show T.ground) (GT.show T.logic) in
  let evalo = EvalPh0.evalo (module BV) in
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
  runF 35 q qh
    (REPR
       (fun q ->
         fresh is_tauto
           (EvalPh0.evalo_helper
              (module BV)
              (Env.cons !!"x" (T.const @@ BV.build_num 15) Env.empty)
              q is_tauto)));

  (*
  runS 1 q qh
    (REPR
       (fun s ->
         s === !!"tautology"
         &&& forallo (fun q ->
                 fresh rez (BV.addo q q rez) (BV.multo q (BV.build_num 2) rez))));
*)

  (* runS 1 q qh
     (REPR
        (fun s ->
          s === !!"tautology"
          &&& evalo Env.empty
                Ph.(le (T.const @@ BV.build_num 1) (T.const @@ BV.build_num 2))));
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
  runF 30 q qh
    (REPR
       (fun f ->
         fresh (v1 v2 env)
           (env === Env.cons !!"x" v1 (Env.cons !!"y" v2 Env.empty))
           (forallo (fun q -> EvalPh0.evalo (module BV) env f))));

  (* runBV (-1) qr qrh (REPR (fun q r -> BV.leo q r)); *)
  ()

let __ () =
  let (module BV) = Bv.create 4 in
  let runBV =
    Tester.runR Bv.Repr.reify (GT.show Bv.Repr.g) (GT.show Bv.Repr.l)
  in
  let runF = Tester.runR Ph.reify (GT.show Ph.ground) (GT.show Ph.logic) in
  let runS = Tester.run_exn (GT.show GT.string) in
  let runT = Tester.runR T.reify (GT.show T.ground) (GT.show T.logic) in
  let evalo = EvalPh0.evalo (module BV) in
  let _ = runT in
  let _ = runF in
  let _ = runR in
  let _ = runS in
  let _ = runBV in
  let _ = evalo in

  let _same_answer_count : State.t Stream.t -> _ -> bool =
   fun s1 s2 ->
    let n1 = OCanren.Stream.take s1 in
    let n2 = OCanren.Stream.take s2 in
    n1 = n2
  in
  let _stream_is_singleton ss =
    match OCanren.Stream.take ~n:2 ss with [ x ] -> true | _ -> false
  in

  let ph =
    let (module I : Algebra.INPUT) = Algebra.ex4 in
    let (module T), (module P) = Types.to_mk (module BV) in
    let module MkEncoded = I (T) (P) in
    Option.get MkEncoded.answer
  in

  let count = Bv.int_pow 2 BV.width - 1 in
  for i = 1 to count - 1 do
    for j = 1 to count - 1 do
      let myenv =
        Env.cons !!"x" (T.const @@ BV.build_num i)
        @@ Env.cons !!"y" (T.const @@ BV.build_num j) Env.empty
      in
      let s =
        OCanren.(run q) (fun _ -> EvalPh0.evalo (module BV) myenv ph) Fun.id
      in
      if not (_stream_is_singleton s) then
        Format.eprintf "no answer for i=%d, j=%d\n%!" i j
      else ()
    done
  done;
  ()

let __ () =
  let (module BV) = Bv.create 4 in
  let runBV =
    Tester.runR Bv.Repr.reify (GT.show Bv.Repr.g) (GT.show Bv.Repr.l)
  in
  let runF = Tester.runR Ph.reify (GT.show Ph.ground) (GT.show Ph.logic) in
  let runS = Tester.run_exn (GT.show GT.string) in
  let runT = Tester.runR T.reify (GT.show T.ground) (GT.show T.logic) in
  let evalo = EvalPh0.evalo (module BV) in
  let _ = runT in
  let _ = runF in
  let _ = runR in
  let _ = runS in
  let _ = runBV in
  let _ = evalo in

  let module Term = struct
    type t = Bv.Repr.g

    type ground = Bv.Repr.g

    let ground = Bv.Repr.g

    type logic = Bv.Repr.l

    let logic = Bv.Repr.l

    let reify = Bv.Repr.reify
  end in
  let module Ph = struct
    type 'a t = Op of 'a * 'a [@@deriving gt ~options:{ show }]

    type ground = Term.ground t [@@deriving gt ~options:{ show }]

    type logic = Term.logic t OCanren.logic [@@deriving gt ~options:{ show }]

    module Ops = Fmap (struct
      type nonrec 'a t = 'a t

      let fmap f (Op (x, y)) = Op (f x, f y)
    end)

    let op l r = inj @@ Ops.distrib (Op (l, r))

    let reify env = Ops.reify Term.reify env
  end in
  let termo t1 t2 =
    fresh () (t1 === t2)
      (conde
         [ t1 === BV.build_num 1; t1 === BV.build_num 2; t1 === BV.build_num 3 ])
  in
  let rec pho ph rez =
    fresh (l r l2 r2)
      (ph === Ph.op l r)
      (termo l l2)
      (* (trace_bv l "l=") *)
      (termo r r2)
      (* (trace_bv r "r=") *)
      (BV.compare_helper l2 r2 rez)
  in
  let runF = Tester.runR Ph.reify (GT.show Ph.ground) (GT.show Ph.logic) in
  runF (-1) q qh (REPR (fun q -> pho q !!Bv.LT));
  runF (-1) q qh (REPR (fun q -> pho q !!Bv.EQ));
  runF (-1) q qh (REPR (fun q -> pho q !!Bv.GT));
  ()
