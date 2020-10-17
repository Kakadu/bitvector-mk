module M = struct
  open Z3

  let c = mk_context []

  let s = Solver.mk_simple_solver c

  let ex1 () =
    let xr = Symbol.mk_string c "x" in
    let yr = Symbol.mk_string c "y" in
    let open Expr in
    let open BitVector in
    let x = mk_const c xr 64 in
    let y = mk_const c yr 64 in
    [
      (* (assert (not (= (bvand (bvnot x) (bvnot y)) (bvnot (bvor x y))))) *)
      Boolean.mk_not c
      @@ Boolean.mk_eq c
           (mk_and c (mk_not c x) (mk_not c y))
           (mk_not c @@ mk_or c x y);
    ]

  let () =
    let open Solver in
    Solver.reset s;
    let es = ex1 () in
    List.iter (fun s -> Format.printf "%s\n%!" (Expr.to_string s)) es;
    match Solver.check s es with
    | UNSATISFIABLE -> Format.printf "unsat\n%!"
    | SATISFIABLE -> Format.printf "sat\n%!"
    | UNKNOWN -> Format.printf "unk\n%!"

  let () =
    let open Solver in
    Solver.reset s;
    (* (simplify (bvmul #x07 #x03)) ; multiplication *)
    let e =
      let open BitVector in
      mk_mul c
        (Expr.mk_numeral_int c 7 (BitVector.mk_sort c 32))
        (Expr.mk_numeral_int c 3 (BitVector.mk_sort c 32))
    in
    print_endline (Expr.to_string e);

    let e2 = Expr.simplify e None in
    print_endline (Expr.to_string e2)
end
