[@@@ocaml.warning "-33"]

open Synth
open OCanren
open Types

let bv_size = 3
let () = test bv_size Inhabit_ph.evalo Algebra.ex2
