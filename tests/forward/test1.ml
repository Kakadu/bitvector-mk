open OCanren
open Types

let bv_size = 2

let run_bool eta =
  Tester.run_r OCanren.reify (GT.show OCanren.logic (GT.show GT.bool)) eta

open Tester

let () =
  let (module BV) = Bv.create bv_size in
  let run_term eta = Tester.run_r T.reify T.show_logic eta in
  let run_bv n = run_r Bv.Repr.reify Bv.Repr.show_logic n in
  [%tester run_bv (-1) (fun q -> q === BV.build_num 0)];
  [%tester run_bv (-1) (fun q -> q === BV.build_num 1)];
  [%tester run_bv (-1) (fun q -> q === BV.build_num 2)];
  [%tester run_bv (-1) (fun q -> q === BV.build_num 3)];
  let env =
    Types.Env.inject @@ Types.Env.embed
    @@ List.map (fun (a, b) -> (a, BV.of_int b)) [ ("x", 1); ("x2", 2) ]
  in

  let _x = T.var !!"x" in
  let _a = T.var !!"a" in
  let _b = T.var !!"b" in
  let _x2 = T.var !!"x2" in
  let _1 = T.const (BV.build_num 1) in
  let _2 = T.const (BV.build_num 2) in
  let _3 = T.const (BV.build_num 3) in

  [%tester
    run_bool (-1) (fun rez ->
        Inhabit_ph.evalo (module BV) env (Ph.not (Ph.le _1 _x2)) rez)];
  [%tester
    run_bool (-1) (fun rez ->
        fresh ()
          (* (trace_env env "initial env") *)
          (Inhabit_ph.evalo (module BV) env (Ph.le (T.shl _1 _x) _x) rez))];
  [%tester
    run_bool (-1) (fun rez ->
        fresh ()
          (* (trace_env env "initial env") *)
          (Inhabit_ph.evalo (module BV) env (Ph.le _2 _x) rez))];
  [%tester
    run_term (-1) (fun rez ->
        fresh ()
          (* (trace_env env "initial env") *)
          (Inhabit_ph.termo (module BV) env (T.shl _1 _x) rez))];
  [%tester
    run_bool (-1) (fun rez ->
        Inhabit_ph.evalo (module BV) env (Ph.le _x _3) rez)];
  [%tester
    run_bool (-1) (fun rez ->
        Inhabit_ph.evalo (module BV) env (Ph.le _x _3) rez)];
  let ( ** ) name v = Std.pair !!name (T.const (BV.inj_int v)) in
  [%tester
    run_bool 10 (fun rez ->
        fresh (ph env)
          (env === Std.List.list [ "b" ** 0b10; "a" ** 0b11 ])
          (ph === Ph.conj2 (Ph.le _1 _a) (Ph.le _1 _b))
          (* (ph === Ph.le _1 _b) *)
          (* (rez === !!true) *)
          (Inhabit_ph.evalo (module BV) env ph rez))];
  ()
