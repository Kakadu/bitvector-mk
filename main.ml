open Format
open OCanren
open EvalPh

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

(* let () = Format.printf "%s %d\n%!" __FILE__ __LINE__ *)

let trace_intermediate_candidate =
  match Sys.getenv "MKTRACE" with
  | exception Not_found -> fun _ -> ()
  | _ ->
      fun q ->
        let () = Format.printf "@[Query:@ @[%s@]@]\n%!" (Z3.Expr.to_string q) in
        ()

module MyQueue : sig
  type t

  val enqueue : t -> Z3.Model.model -> unit

  val create : (Z3.Model.model -> int) -> t

  val size : t -> int
end = struct
  module Arr = Res.Array

  type model = Z3.Model.model

  (* WE should save models and evaluations of the original formula in them *)
  type t = (model -> int) * (model * int) Arr.t

  let enqueue : t -> model -> unit =
   fun (f, arr) m ->
    (* Doc doesn't say explicitly but
       it seems that it is adding new element to the end *)
    Arr.add_one arr (m, f m)

  let create f : t = (f, Arr.empty ())

  let clear q = q := []

  let size (_, arr) = Arr.length arr
end

let test m =
  let ctx = Z3.mk_context [] in
  let solver = Z3.Solver.mk_simple_solver ctx in

  let (module T), (module P) = S.to_z3 ctx in
  let (module I : S.INPUT) = m in
  let module Z3Encoded = I (T) (P) in
  Format.printf "%s\n%!" Z3Encoded.info;
  Format.printf "%s\n%!" (Z3.Expr.to_string Z3Encoded.ph);
  let free = S.freevars m in
  let () =
    Format.printf "Free vars: ";
    S.SS.iter (Format.printf "%s ") free;
    Format.printf "\n%!";
    assert (not (S.SS.is_empty free))
  in
  let varo : _ -> OCanren.goal =
    match S.SS.to_seq free |> List.of_seq with
    | [] -> fun _ -> failure
    | h :: tl ->
        List.fold_left
          (fun relo name q -> conde [ q === !!name; relo q ])
          (fun q -> q === !!h)
          tl
  in

  let ex_storage =
    let eval m =
      match Z3.Model.eval m Z3Encoded.ph false with
      | None -> failwith "should not happen"
      | Some e when not (Z3.Expr.is_const e) -> failwith "Got not a constant "
      | Some e ->
          printf "Model evaluation result is : %s\n%!" (Z3.Expr.to_string e);
          42
    in

    MyQueue.create eval
  in

  let on_ground x = Format.asprintf "%a" (GT.fmt Ph.ground) x in
  let on_logic x = Format.asprintf "%a" (GT.fmt Ph.logic) x in
  let open OCanren in
  let open Tester in
  let goal q =
    let cutter q =
      debug_var q (flip Ph.reify) (fun p ->
          let p = match p with [ h ] -> h | _ -> assert false in
          (* There we should encode logic formula p to SMT and check that
              not (I <=> p) is unsat
          *)
          let candidate = Ph.to_smt_logic_exn ctx p in
          let (module F : S.FORMULA_Z3) = S.z3_of_formula ctx in
          let q = F.(not (iff candidate Z3Encoded.ph)) in
          trace_intermediate_candidate candidate;
          match Z3.Solver.check solver [ q ] with
          | Z3.Solver.UNKNOWN ->
              failwith "Solver should not return UNKNOWN result"
          | UNSATISFIABLE -> success
          | SATISFIABLE ->
              let model = Z3.Solver.get_model solver |> Option.get in
              MyQueue.enqueue ex_storage model;
              success)
    in
    fresh () (inhabito (inhabito_term varo) q) (cutter q)
  in
  runR Ph.reify on_ground on_logic 2 q qh ("", goal)

let () = test S.ex6
