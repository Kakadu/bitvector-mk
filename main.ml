open Format
open OCanren
open Types

[%%define TRACE]

(* [%%undef TRACE] *)

let rec inhabito term r =
  conde
    [
      fresh (a b) (r === Ph.eq a b) (term a) (term b);
      fresh (a b) (r === Ph.lt a b) (term a) (term b);
      fresh (a b) (r === Ph.le a b) (term a) (term b);
      fresh (a b) (r === Ph.conj a b) (inhabito term a) (inhabito term b);
      fresh (a b) (r === Ph.disj a b) (inhabito term a) (inhabito term b);
      fresh a (r === Ph.not a) (inhabito term a);
    ]

let __ () =
  let on_ground x = Format.asprintf "%a" (GT.fmt Ph.ground) x in
  let _on_logic x = GT.show Ph.logic x in
  let open OCanren in
  let open Tester in
  (* runR Ph.reify on_ground on_logic 20 q qh ("", fun q -> inhabito q) *)
  run_exn on_ground 20 q qh
    ("", fun q -> inhabito (inhabito_term (fun _ -> failure)) q)

module MyQueue : sig
  type t

  val enqueue : t -> Env.ground -> unit

  val create : unit -> t

  val get : t -> int -> Env.ground * Env.injected

  val size : t -> int

  val report_queue_stats : t -> unit
end = struct
  module Arr = Res.Array

  (* WE should save models and evaluations of the original formula in them *)
  type t = { arr : (Env.ground * Env.injected) Arr.t; count : int ref }

  (* [%%define CHECK_DUPLICATES] *)

  (* [%%undef CHECK_DUPLICATES] *)

  exception Duplicate

  let enqueue : t -> Env.ground -> unit =
   fun ({ arr } as q) ex ->
    try
      Arr.iter (fun (el, _) -> if el = ex then raise Duplicate) arr;

      (* Doc doesn't say explicitly but
         it seems that it is adding new element to the end *)
      Arr.add_one arr (ex, Env.inject ex)
    with Duplicate -> incr q.count

  let create () : t = { arr = Arr.empty (); count = ref 0 }

  let get { arr } = Arr.get arr

  (* let clear q = q := [] *)

  let size { arr } = Arr.length arr

  [%%if defined TRACE]

  let report_queue_stats q =
    Format.printf "Queue contains %d examples\n%!" (size q);
    Format.printf "There were %d duplicate examples\n%!" !(q.count)

  [%%else]

  let report_queue_stats _ = ()

  [%%endif]
end

[%%if defined TRACE]

let trace_on_success q solver_count =
  MyQueue.report_queue_stats q;
  Format.printf "Solver called %d times\n%!" (solver_count ())

let trace_intermediate_candidate =
  match Sys.getenv "MKTRACE" with
  | exception Not_found -> fun _ -> ()
  | _ -> fun q -> Format.printf "@[Query:@ @[%s@]@]\n%!" (Z3.Expr.to_string q)

let trace_new_example =
  match Sys.getenv "MKTRACE" with
  | exception Not_found -> fun _ _ -> ()
  | _ ->
      fun env sz ->
        Format.printf "next model is = '%s'\n%!" (Env.show env);
        Format.printf "Examples count  = %d\n%!" sz

[%%else]

let trace_on_success _ = ()

let trace_intermediate_candidate _ = ()

let trace_new_example _ _ = ()

[%%endif]

let test (evalo : (module Bv.S) -> _) m =
  let ctx = Z3.mk_context [] in
  let solver = Z3.Solver.mk_simple_solver ctx in

  let run_solver, solver_count =
    let c = ref 0 in
    let run ph =
      incr c;
      Z3.Solver.check solver [ ph ]
    in
    let count () = !c in
    (run, count)
  in

  let (module T), (module P) = Algebra.to_z3 ctx in
  let (module I : Algebra.INPUT) = m in
  let module Z3Encoded = I (T) (P) in
  Format.printf "%s\n%!" Z3Encoded.info;
  Format.printf "%s\n%!" (Z3.Expr.to_string Z3Encoded.ph);
  let free = Algebra.freevars m in

  (* let __ () =
       Format.printf "Free vars: ";
       Algebra.SS.iter (Format.printf "%s ") free;
       Format.printf "\n%!";
       assert (not (Algebra.SS.is_empty free))
     in *)
  (*
  (* varo is required for inhabito *)
  let varo : _ -> OCanren.goal =
    match Algebra.SS.to_seq free |> List.of_seq with
    | [] -> fun _ -> failure
    | h :: tl ->
        List.fold_left
          (fun relo name q -> conde [ q === !!name; relo q ])
          (fun q -> q === !!h)
          tl
  in *)
  let (module F : Algebra.FORMULA_Z3) = Algebra.z3_of_formula ctx in
  let (module BV) = Bv.create 4 in

  let check_cand candidate =
    let q = F.(not (iff candidate Z3Encoded.ph)) in
    trace_intermediate_candidate candidate;
    run_solver q
  in

  let _ =
    match Z3Encoded.answer with
    | None -> ()
    | Some answ -> (
        match check_cand answ with
        | Z3.Solver.UNKNOWN -> assert false
        | Z3.Solver.SATISFIABLE -> failwith "Proposed answer is not an answer"
        | Z3.Solver.UNSATISFIABLE ->
            Format.printf "Predefined answers fits!\n%!")
  in

  let ex_storage, myenqueue =
    let _eval m =
      match Z3.Model.eval m Z3Encoded.ph false with
      | None -> failwith "should not happen"
      | Some e when not (Z3.Expr.is_const e) -> failwith "Got not a constant "
      | Some e ->
          printf "Model evaluation result is : %s\n%!" (Z3.Expr.to_string e);
          42
    in

    let q = MyQueue.create () in
    let myenqueue model =
      let env =
        Algebra.SS.fold
          (fun name acc ->
            let eans = Z3.Model.eval model (T.var name) true |> Option.get in
            let estr = Z3.Expr.to_string eans in
            try
              Scanf.sscanf estr "#x%X" (fun n ->
                  (* failwith estr; *)
                  Std.List.Cons ((name, Types.T.Const (BV.of_int n)), acc))
            with Scanf.Scan_failure s as e ->
              Format.eprintf "Error while parsing a string '%s'\n%!" estr;
              raise e)
          free Std.List.Nil
      in

      trace_new_example env (1 + MyQueue.size q);

      MyQueue.enqueue q env
    in

    (* let's create a 1st example by querying any model *)
    let () =
      match run_solver Z3Encoded.ph with
      | Z3.Solver.UNKNOWN -> failwith "Solver should not return UNKNOWN result"
      | UNSATISFIABLE -> failwith "Initial formula is unsat"
      | SATISFIABLE ->
          let model = Z3.Solver.get_model solver |> Option.get in
          myenqueue model
    in
    (q, myenqueue)
  in

  let on_ground ~span:_ x = Format.asprintf "%a" (GT.fmt Ph.ground) x in
  let on_logic ~span:_ x = Format.asprintf "%a" (GT.fmt Ph.logic) x in
  let open OCanren in
  let open Mytester in
  let goal ans_var =
    let loop () =
      let rec helper i =
        if i >= MyQueue.size ex_storage then
          (* let () = Format.printf "i is >= %d\n%!" (MyQueue.size ex_storage) in *)
          success
        else
          let _g, env0 = MyQueue.get ex_storage i in
          (* Format.printf "Testing example: '%a'\n%!" EvalPh.Env.pp _g; *)
          evalo (module BV) env0 ans_var &&& helper (1 + i)
      in
      helper 0
    in
    let _enough_variables q =
      let rec collect_in_term2 acc : Types.T.logic -> _ =
        GT.foldl OCanren.logic
          (GT.transform Types.T.t (fun _ ->
               object
                 inherit
                   [_, _, _, _, _] Types.T.foldl_t_t
                     collect_in_term2
                     (fun acc _ -> acc)
                     (fun acc -> function
                       | Value x -> Algebra.SS.add x acc
                       | Var _ -> assert false)
                     (fun _ _ -> failwith "should not happen")
               end))
          acc
      in
      let rec collect_in_ph acc : Types.Ph.logic -> _ =
        GT.foldl OCanren.logic
          (GT.transform Types.Ph.t (fun _ ->
               object
                 inherit
                   [_, _, _, _] Types.Ph.foldl_t_t
                     collect_in_ph collect_in_term2
                     (fun _ _ -> failwith "should not happen")
               end))
          acc
      in

      debug_var q (flip Ph.reify) (fun p ->
          let p : Types.Ph.logic =
            match p with [ h ] -> h | _ -> assert false
          in

          let cur_vars = collect_in_ph Algebra.SS.empty p in
          if Algebra.SS.equal cur_vars free then success else failure)
    in
    let cutter q =
      debug_var q (flip Ph.reify) (fun p ->
          let p = match p with [ h ] -> h | _ -> assert false in

          (* There we should encode logic formula p to SMT and check that
              not (I <=> p) is unsat
          *)
          let candidate = Ph.to_smt_logic_exn ctx p in

          let q = F.(not (iff candidate Z3Encoded.ph)) in
          trace_intermediate_candidate candidate;
          match run_solver q with
          | Z3.Solver.UNKNOWN ->
              failwith "Solver should not return UNKNOWN result"
          | UNSATISFIABLE ->
              trace_on_success ex_storage solver_count;
              success
          | SATISFIABLE ->
              let model = Z3.Solver.get_model solver |> Option.get in
              myenqueue model;
              failure)
    in
    fresh () (loop ())
      (* TODO: removing constraint below leads to more examples
         FIX: do not add duplicate examples.
      *)
      (* (enough_variables ans_var) *)
      (cutter ans_var)
  in
  runR Ph.reify on_ground on_logic 1 q qh ("", goal)

let () = test EvalPh0.evalo Algebra.ex4
