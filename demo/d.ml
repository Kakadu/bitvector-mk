let () = Printf.printf "\n\n%!"

module M = struct
  open Z3

  let c = mk_context []

  let s = Solver.mk_simple_solver c

  let run es =
    match Solver.check s es with
    | UNSATISFIABLE -> Format.printf "unsat\n%!"
    | UNKNOWN -> Format.printf "unk\n%!"
    | SATISFIABLE -> (
        Format.printf "sat\n%!";
        match Solver.get_model s with
        | None -> Format.printf "no model\n%!"
        | Some m -> Format.printf "%s\n%!" (Model.to_string m) )

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

  let __ () =
    let open Solver in
    Solver.reset s;
    let es = ex1 () in
    List.iter (fun s -> Format.printf "%s\n%!" (Expr.to_string s)) es;
    run es

  let __ () =
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

  let __ () =
    let open Z3 in
    let open Solver in
    let open Z3.Arithmetic in
    Solver.reset s;
    let ctx = c in

    let is = Integer.mk_sort ctx in
    let types = [ is; is; is ] in
    let names =
      [
        Symbol.mk_string ctx "x_0";
        Symbol.mk_string ctx "x_1";
        Symbol.mk_string ctx "x_2";
      ]
    in
    let vars =
      [
        Quantifier.mk_bound ctx 2 (List.nth types 0);
        Quantifier.mk_bound ctx 2 (List.nth types 1);
        Quantifier.mk_bound ctx 2 (List.nth types 2);
      ]
    in
    let xs =
      [
        Integer.mk_const ctx (List.nth names 0);
        Integer.mk_const ctx (List.nth names 1);
        Integer.mk_const ctx (List.nth names 2);
      ]
    in

    let body_vars =
      Boolean.mk_and ctx
        [
          Boolean.mk_eq ctx
            (Arithmetic.mk_add ctx
               [ List.nth vars 0; Integer.mk_numeral_i ctx 1 ])
            (Integer.mk_numeral_i ctx 2);
          Boolean.mk_eq ctx
            (Arithmetic.mk_add ctx
               [ List.nth vars 1; Integer.mk_numeral_i ctx 2 ])
            (Arithmetic.mk_add ctx
               [ List.nth vars 2; Integer.mk_numeral_i ctx 3 ]);
        ]
    in
    let body_const =
      Boolean.mk_and ctx
        [
          Boolean.mk_eq ctx
            (Arithmetic.mk_add ctx
               [ List.nth xs 0; Integer.mk_numeral_i ctx 1 ])
            (Integer.mk_numeral_i ctx 2);
          Boolean.mk_eq ctx
            (Arithmetic.mk_add ctx
               [ List.nth xs 1; Integer.mk_numeral_i ctx 2 ])
            (Arithmetic.mk_add ctx
               [ List.nth xs 2; Integer.mk_numeral_i ctx 3 ]);
        ]
    in

    let x =
      Quantifier.mk_forall ctx types names body_vars (Some 1) [] []
        (Some (Symbol.mk_string ctx "Q1"))
        (Some (Symbol.mk_string ctx "skid1"))
    in
    Printf.printf "Quantifier X: %s\n" (Quantifier.to_string x);
    run [ Quantifier.expr_of_quantifier x ];

    Solver.reset s;
    let y =
      Quantifier.mk_forall_const ctx xs body_const (Some 1) [] []
        (Some (Symbol.mk_string ctx "Q2"))
        (Some (Symbol.mk_string ctx "skid2"))
    in
    Printf.printf "Quantifier Y: %s\n" (Quantifier.to_string y);
    run [ Quantifier.expr_of_quantifier y ];

    if Boolean.is_true (Quantifier.expr_of_quantifier x) then assert false
    else if Boolean.is_false (Quantifier.expr_of_quantifier x) then assert false
    else if Expr.is_const (Quantifier.expr_of_quantifier x) then assert false

  (* unreachable *)

  let __ () =
    let open Solver in
    let open Z3.Arithmetic in
    Solver.reset s;
    let e =
      let xr = Symbol.mk_string c "x" in
      let yr = Symbol.mk_string c "y" in
      let x = Integer.mk_const c xr in
      let y = Integer.mk_const c yr in
      (* let x = FuncDecl.mk_func_decl c xr [] (Integer.mk_sort c) in
         let y = FuncDecl.mk_func_decl c yr [] (Integer.mk_sort c) in *)
      (* let types = [ Integer.mk_sort c; Integer.mk_sort c ] in *)
      (* Boolean.mk_not c
         @@ *)
      Quantifier.expr_of_quantifier
        (Quantifier.mk_forall_const c [ x; y ]
           (* (mk_gt c (FuncDecl.apply y []) (FuncDecl.apply x [])) *)
           (mk_gt c y x)
           (* (Some 2)  *)
           None [] []
           (* (Some (Symbol.mk_string c "Q2"))
              (Some (Symbol.mk_string c "skid2")) *)
           None None)
    in
    print_endline (Expr.to_string e);
    run [ e ]

  let __ () =
    let open Solver in
    Solver.reset s;
    let e =
      let xr = Symbol.mk_string c "x" in
      let yr = Symbol.mk_string c "y" in

      let mk_const, mk_sort, mk_gt =
        if true then
          ( (fun c n -> BitVector.mk_const c n 4),
            (fun c -> BitVector.mk_sort c 4),
            BitVector.mk_ugt )
        else
          (* Normal numbers will not finish *)
          ( Arithmetic.Integer.mk_const,
            Arithmetic.Integer.mk_sort,
            Arithmetic.mk_gt )
      in
      let x = mk_const c xr in
      let y = mk_const c yr in
      Quantifier.expr_of_quantifier
        (Quantifier.mk_forall_const c [ x ]
           ( Quantifier.mk_exists_const c [ y ] (mk_gt c y x) None [] [] None
               None
           |> Z3.Quantifier.expr_of_quantifier )
           None [] [] None None)
    in
    print_endline (Expr.to_string e);
    run [ e ]

  let () =
    let open Solver in
    Solver.reset s;
    let e =
      let xr = Symbol.mk_string c "x" in

      let mk_const, mk_sort, mk_gt =
        ( (fun c n -> BitVector.mk_const c n 4),
          (fun c -> BitVector.mk_sort c 4),
          BitVector.mk_ugt )
      in

      let x = mk_const c xr in
      Quantifier.expr_of_quantifier
        (Quantifier.mk_forall_const c [ x ]
           (mk_gt c x (Expr.mk_numeral_string c "1" (BitVector.mk_sort c 4)))
           None [] [] None None)
    in
    print_endline (Expr.to_string e);
    run [ e ]
end
