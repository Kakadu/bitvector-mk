open OCanren
open Tester
open Bv
open Bv.Repr

let __ _freeVars =
  let (module M) = create 2 in
  let open M in
  let runL n = run_r reify show_logic n in

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
  let runL n = run_r reify show_logic n in

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
  let runL n = run_r reify show_logic n in

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
  let runL n = run_r reify show_logic n in

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
  let runL n = run_r reify show_logic n in

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

let _shifts =
  let (module M) = create 4 in
  let open M in
  let runL n = run_r reify show_logic n in

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
  runL (-1) q qh (REPR (fun q -> shiftlo (build_num 4) (build_num 4) q));

  (* runL 50 q qh (REPR (fun q -> lando (build_num 15) (build_num 15) q)); *)
  (* runL (-1) q qh (REPR (fun q -> leo (build_num 1) (build_num 2))); *)
  (* runL (-1) q qh (REPR (fun q -> lto (build_num 4) (build_num 3))); *)

  (* runL (-1) qr qrh (REPR (fun q r -> shiftl1 (build_num 1) r &&& shiftl1 r q)); *)
  ()

let __ _shifts =
  let (module M) = create 4 in
  let open M in
  let runL n = run_r reify show_logic n in

  runL (-1) qr qrh
    (REPR
       (fun q r ->
         fresh verdict (verdict === !!GT) (compare_helper q r verdict)));

  ()

let run_cmp n = run_r OCanren.reify (GT.show OCanren.logic (GT.show Bv.cmp_t)) n

let _ =
  let (module M) = create 3 in
  let open M in
  let run_bv n = run_r Bv.Repr.reify Bv.Repr.show_logic n in
  [%tester
    run_cmp (-1) (fun verdict ->
        fresh q
          (shiftlo (build_num 1) (build_num 1) q)
          (compare_helper q (build_num 1) verdict))];

  [%tester run_bv (-1) (fun q -> shiftlo (build_num 1) (build_num 1) q)];
  [%tester run_bv (-1) (fun q -> shiftlo (build_num 1) (build_num 2) q)];

  ()

let _1 _ =
  let (module M) = create 2 in
  let open M in
  let run_bv n = run_r Bv.Repr.reify Bv.Repr.show_logic n in
  [%tester run_bv (-1) (fun q -> q === build_num 0)];
  [%tester run_bv (-1) (fun q -> q === build_num 1)];
  [%tester run_bv (-1) (fun q -> q === build_num 2)];
  [%tester run_bv (-1) (fun q -> q === build_num 3)];
  ()
