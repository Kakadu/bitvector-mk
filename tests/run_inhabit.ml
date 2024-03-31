open OCanren
open Inhabit_ph
open Types

let ans_count = ref 20

let () =
  Arg.parse []
    (fun str -> ans_count := try int_of_string str with Failure _ -> 20)
    ""

let run_ph eta =
  Tester.run_r Ph.reify (Format.asprintf "%a" Ph.PPNew.my_logic_pp) eta

let bv_size = 4

let _ =
  let open Tester in
  let ((module BV) as bv) = Bv.create bv_size in

  (* let env =
       Types.Env.inject @@ Types.Env.embed
       @@ List.map (fun (a, b) -> (a, BV.of_int b)) [ ("x", 1) ]
     in *)
  let ( ** ) name v = Std.pair !!name (T.const (BV.inj_int v)) in
  [%tester
    run_ph !ans_count (fun ph ->
        let open Std in
        fresh (env rez)
          (* (env === pair !!"x" __ % (pair !!"y" __ % nil ())) *)
          (env === Std.list Fun.id [ "x" ** 1; "y" ** 1 ])
          (rez === !!true) (evalo bv env ph rez))]
