open OCanren
open OCanren.Std
open Tester
open Bv
open Bv.Repr

let __ _freeVars =
  let (module M) = create 2 in
  let open M in
  let runL n = runR reify show show_logic n in

  (* runL 5 qrs qrsh (REPR (fun q r s -> addo q r s )); *)
  (* runL (-1) qr qrh (REPR (fun q r -> addo q r (build_num 7))); *)
  (* runL (-1) q qh (REPR (fun q -> addo (build_num 0) (build_num 0) q)); *)
  runL (-1) q qh (REPR (fun q -> addo (build_num 1) (build_num 1) q));
  (* runL (-1) q qh (REPR (fun q -> addo (build_num 1) (build_num 0) q)); *)
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
  let runL n = runR reify show show_logic n in

  (* runL 1 q qh (REPR (fun q -> q === build_num 1));
     runL 1 q qh (REPR (fun q -> q === build_num 2));
     runL 1 q qh (REPR (fun q -> q === build_num 3));

     runL (-1) q qh (REPR (fun q -> addo q (build_num 3) (build_num 1)));
     runL (-1) q qh (REPR (fun q -> addo (build_num 1) (build_num 2) q));
     runL 5 qrs qrsh (REPR (fun q r s -> addo q r s)); *)
  runL 5 q qh (REPR (fun q -> subo (build_num 2) (build_num 1) q));
  (* runL (-1) q qh (REPR (fun q -> addo (build_num 3) q (build_num 1))); *)
  (* runL (-1) q qh (REPR (fun q -> addo (build_num 3) (build_num 2) q)); *)
  ()

let __ _freeVars =
  let (module M) = create 3 in
  let open M in
  let runL n = runR reify show show_logic n in

  (*
  runL 1 q qh (REPR (fun q -> q === build_num 1));
  runL 1 q qh (REPR (fun q -> q === build_num 2));
  runL 1 q qh (REPR (fun q -> q === build_num 3));
  runL 1 q qh (REPR (fun q -> q === build_num 4));
  runL 1 q qh (REPR (fun q -> q === build_num 5)); *)

  (* runL (-1) q qh (REPR (fun q -> addo (build_num 3) q (build_num 5))); *)
  runL (-1) q qh (REPR (fun q -> addo (build_num 3) (build_num 2) q));
  runL 5 q qh (REPR (fun q -> subo (build_num 3) (build_num 2) q));
  ()

let __ _shifts =
  let (module M) = create 4 in
  let open M in
  let runL n = runR reify show show_logic n in

  runL 5 q qh (REPR (fun q -> shiftl1 (build_num 5) q));
  runL 5 q qh (REPR (fun q -> shiftl1 (build_num 10) q));

  runL 5 q qh (REPR (fun q -> q === build_num 9));
  runL 5 q qh (REPR (fun q -> rotl (build_num 9) q));
  runL 5 q qh (REPR (fun q -> q === build_num 8));
  runL 5 q qh (REPR (fun q -> rotr (build_num 8) q));
  runL 5 q qh (REPR (fun q -> q === build_num 3));
  runL 5 q qh (REPR (fun q -> rotr (build_num 3) q));
  ()

let __ _mults =
  let (module M) = create 2 in
  let open M in
  let runL n = runR reify show_binary show_logic n in

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

let __ _shifts =
  let (module M) = create 4 in
  let open M in
  let runL n = runR reify show_binary show_logic n in

  runL (-1) qr qrh (REPR (shiftlo (build_num 1)));

  runL (-1) qr qrh (REPR (fun q r -> shiftlo q r (build_num 1)));

  runL 50 qr qrh (REPR (fun q r -> lshiftro q r (build_num 0)));

  (* runL 50 qr qrh (REPR (fun q r -> lando q (build_num 3) (build_num 3))); *)

  (* runL 50 qr qrh (REPR (fun q r -> lando q (build_num 3) r)); *)
  runL (-1) q qh (REPR (fun q -> shiftlo (build_num 1) (build_num 3) q));
  runL (-1) q qh (REPR (fun q -> lto (build_num 0) (build_num 4)));
  runL (-1) q qh (REPR (fun q -> shiftlo (build_num 5) (build_num 0) q));
  runL (-1) q qh (REPR (fun q -> leo (build_num 4) (build_num 0)));
  runL (-1) q qh (REPR (fun q -> leo (build_num 1) (build_num 3)));

  (* runL 50 q qh (REPR (fun q -> lando (build_num 15) (build_num 15) q)); *)
  (* runL (-1) q qh (REPR (fun q -> leo (build_num 1) (build_num 2))); *)
  (* runL (-1) q qh (REPR (fun q -> lto (build_num 4) (build_num 3))); *)

  (* runL (-1) qr qrh (REPR (fun q r -> shiftl1 (build_num 1) r &&& shiftl1 r q)); *)
  ()

let _shifts =
  let (module M) = create 4 in
  let open M in
  let runL n = runR reify show_binary show_logic n in

  runL (-1) qr qrh
    (REPR
       (fun q r ->
         fresh verdict (verdict === !!GT) (compare_helper q r verdict)));

  ()
