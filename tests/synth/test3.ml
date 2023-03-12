open Synth
open OCanren
open Types

let () = Gc.set { (Gc.get ()) with Gc.verbose = 0x400 }
let bv_size = 3

let hint ans_var =
  fresh (ph0 ph1 ph2 ph3 a b)
    (a === Types.(T.var !!"a"))
    (b === Types.(T.var !!"b"))
    (ph0 === Ph.le __ __)
    (ph1 === Ph.le __ __)
    (ph2 === Ph.le __ __)
    (ph3 === Ph.le __ __)
    (ans_var === Ph.(not (conj_list (list_take bv_size [ ph0; ph1; ph2; ph3 ]))))

let () =
  let rec loop n =
    Thread.delay (float_of_int n *. 60.);
    Format.printf "Synthesis is running for %d minutes...\n%!" n;
    loop (n + 1)
  in
  Thread.create loop 0 |> ignore

let () = test bv_size Inhabit_ph.evalo Algebra.ex4 ~hint
