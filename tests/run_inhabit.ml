open OCanren
open Inhabit_ph
open Types

let run_ph eta =
  Tester.run_r Ph.reify (Format.asprintf "%a" Ph.PPNew.my_logic_pp) eta

let bv_size = 4

let _ =
  let open Tester in
  let ((module BV) as bv) = Bv.create bv_size in
  let env =
    Types.Env.inject @@ Types.Env.embed
    @@ List.map (fun (a, b) -> (a, BV.of_int b)) [ ("x", 1) ]
  in

  [%tester run_ph 20 (fun ph -> evalo bv env ph !!true)]
