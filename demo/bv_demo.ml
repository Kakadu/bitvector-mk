open OCanren
open OCanren.Std
open Tester
open Bv

let __ _freeVars =
  let (module M) = create 2 in
  let open M in
  let runL n = runR M.reify show show_logic n in

  (* runL 5 qrs qrsh (REPR (fun q r s -> pluso q r s )); *)
  (* runL (-1) qr qrh (REPR (fun q r -> pluso q r (build_num 7))); *)
  (* runL (-1) q qh (REPR (fun q -> pluso (build_num 0) (build_num 0) q)); *)
  runL (-1) q qh (REPR (fun q -> pluso (build_num 1) (build_num 1) q));
  (* runL (-1) q qh (REPR (fun q -> pluso (build_num 1) (build_num 0) q)); *)
  ()

(*
let _freeVars =
  let (module M) = create 2 in
  let open M in
  let runL n = runR M.reify show show_logic n in

  runL (-1) q qh (REPR (fun r -> addero 1 !!1 (!< !!0) (!< !!0) r));
  ()
*)

let __ _freeVars =
  let (module M) = create 2 in
  let open M in
  let runL n = runR M.reify show show_logic n in

  (* runL 1 q qh (REPR (fun q -> q === build_num 1));
     runL 1 q qh (REPR (fun q -> q === build_num 2));
     runL 1 q qh (REPR (fun q -> q === build_num 3));

     runL (-1) q qh (REPR (fun q -> pluso q (build_num 3) (build_num 1)));
     runL (-1) q qh (REPR (fun q -> pluso (build_num 1) (build_num 2) q));
     runL 5 qrs qrsh (REPR (fun q r s -> pluso q r s)); *)
  runL 5 q qh (REPR (fun q -> minuso (build_num 2) (build_num 1) q));
  (* runL (-1) q qh (REPR (fun q -> pluso (build_num 3) q (build_num 1))); *)
  (* runL (-1) q qh (REPR (fun q -> pluso (build_num 3) (build_num 2) q)); *)
  ()

let __ _freeVars =
  let (module M) = create 3 in
  let open M in
  let runL n = runR M.reify show show_logic n in

  (*
  runL 1 q qh (REPR (fun q -> q === build_num 1));
  runL 1 q qh (REPR (fun q -> q === build_num 2));
  runL 1 q qh (REPR (fun q -> q === build_num 3));
  runL 1 q qh (REPR (fun q -> q === build_num 4));
  runL 1 q qh (REPR (fun q -> q === build_num 5)); *)

  (* runL (-1) q qh (REPR (fun q -> pluso (build_num 3) q (build_num 5))); *)
  runL (-1) q qh (REPR (fun q -> pluso (build_num 3) (build_num 2) q));
  runL 5 q qh (REPR (fun q -> minuso (build_num 3) (build_num 2) q));
  ()

let __ _shifts =
  let (module M) = create 4 in
  let open M in
  let runL n = runR M.reify show show_logic n in

  runL 5 q qh (REPR (fun q -> shiftl (build_num 5) q));
  runL 5 q qh (REPR (fun q -> shiftl (build_num 10) q));

  runL 5 q qh (REPR (fun q -> q === build_num 9));
  runL 5 q qh (REPR (fun q -> rotl (build_num 9) q));
  runL 5 q qh (REPR (fun q -> q === build_num 8));
  runL 5 q qh (REPR (fun q -> rotr (build_num 8) q));
  runL 5 q qh (REPR (fun q -> q === build_num 3));
  runL 5 q qh (REPR (fun q -> rotr (build_num 3) q));
  ()

let _mults =
  let (module M) = create 2 in
  let open M in
  let runL n = runR M.reify show_binary show_logic n in

  (* runL 5 q qh (REPR (fun q -> multo (build_num 2) (build_num 2) q)); *)
  (* runL 5 q qh (REPR (fun q -> multo (build_num 2) (build_num 0) q)); *)
  (* runL 5 q qh (REPR (fun q -> multo (build_num 0) (build_num 2) q)); *)
  (* runL 5 q qh (REPR (fun q -> multo (build_num 2) (build_num 1) q)); *)
  runL 5 q qh (REPR (fun q -> mul2 (build_num 1) q));
  runL 5 q qh (REPR (fun q -> mul2 (build_num 2) q));
  runL 5 q qh (REPR (fun q -> mul2 (build_num 3) q));

  runL 5 q qh (REPR (fun q -> multo (build_num 2) (build_num 2) q));

  runL (-1) qrs qrsh (REPR (fun q r s -> multo q r s));
  ()
