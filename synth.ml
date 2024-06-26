open Format
open OCanren
open Types
(*
   module Options = struct
     type options = { mutable max_answers : int }

     let max { max_answers } = max_answers
     let set_max o n = o.max_answers <- n
     let create () = { max_answers = 1 }
   end

   let options = Options.create ()

   let () =
     Arg.parse
       [ ("-max", Arg.Int (Options.set_max options), "maximum answers count") ]
       (fun _ -> Printf.printf "anonymous arguments not supported\n")
       "usage" *)

[%%define TRACE]

(* [%%undef TRACE] *)
(*
let rec inhabito term r =
  conde
    [
      fresh (a b) (r === Ph.eq a b) (term a) (term b);
      fresh (a b) (r === Ph.lt a b) (term a) (term b);
      fresh (a b) (r === Ph.le a b) (term a) (term b);
      fresh (a b) (r === Ph.conj2 a b) (inhabito term a) (inhabito term b);
      fresh (a b) (r === Ph.disj2 a b) (inhabito term a) (inhabito term b);
      fresh a (r === Ph.not a) (inhabito term a);
    ]
 *)
(* let __ () =
   let on_ground x = Format.asprintf "%a" (GT.fmt Ph.ground) x in
   let _on_logic x = GT.show Ph.logic x in
   let open OCanren in
   let open Tester in
   (* runR Ph.reify on_ground on_logic 20 q qh ("", fun q -> inhabito q) *)
   run_exn on_ground 20 q qh
     ("", fun q -> inhabito (inhabito_term (fun _ -> failure)) q)
*)
module MyQueue : sig
  type t

  val enqueue : t -> Env.ground -> bool -> unit
  val create : unit -> t
  val get : t -> int -> Env.ground * Env.injected * bool
  val size : t -> int
  val report_queue_stats : t -> unit
  val pp : Format.formatter -> t -> unit
end = struct
  module Arr = Res.Array

  (* WE should save models and evaluations of the original formula in them *)
  type t = { arr : (Env.ground * Env.injected * bool) Arr.t; count : int ref }

  (* [%%define CHECK_DUPLICATES] *)

  (* [%%undef CHECK_DUPLICATES] *)

  exception Duplicate

  let enqueue : t -> Env.ground -> _ -> unit =
   fun ({ arr } as q) ex v ->
    try
      Arr.iter (fun (el, _, _) -> if el = ex then raise Duplicate) arr;

      (* Doc doesn't say explicitly but
         it seems that it is adding new element to the end *)
      Arr.add_one arr (ex, Env.inject ex, v)
    with Duplicate -> incr q.count

  let create () : t = { arr = Arr.empty (); count = ref 0 }

  let get { arr } idx =
    (* Format.eprintf "idx = %d, length = %d\n%!" idx (Arr.length arr); *)
    assert (idx < Arr.length arr);
    Arr.get arr idx

  (* let clear q = q := [] *)

  let size { arr } = Arr.length arr

  let pp ppf { arr } =
    Format.set_geometry ~margin:1000 ~max_indent:(1000 - 1);
    Format.fprintf ppf "@[<h>{|";
    Arr.iter
      (fun (env, _, b) ->
        if b then Format.fprintf ppf "@[%a@]@ " Env.pp env
        else Format.fprintf ppf "@[(not %a)@ " Env.pp env)
      arr;
    Format.fprintf ppf "]}@]"

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
  | exception Not_found -> fun _ _ _ -> ()
  | _ ->
      fun env sz v ->
        Format.printf "next model is = '%s' with value %b\n%!" (Env.show env) v;
        Format.printf "Examples count  = %d\n%!" sz

[%%else]

let trace_on_success _ = ()
let trace_intermediate_candidate _ = ()
let trace_new_example _ _ _ = ()

[%%endif]

let rec list_take n = function
  | xs when n < 0 -> xs
  | _ when n = 0 -> []
  | h :: tl -> h :: list_take (n - 1) tl
  | [] -> []

let _enough_variables free q =
  let rec collect_in_term2 acc : Types.T.logic -> _ =
    GT.foldl OCanren.logic
      (GT.transform Types.T.t (fun _ ->
           object
             inherit
               [_, _, _, _, _, _] Types.T.foldl_t_t
                 collect_in_term2
                 (fun acc _ -> acc)
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
               [_, _, _, _, _, _] Types.Ph.foldl_t_t
                 collect_in_ph collect_in_ph_list
                 (fun acc _ -> acc)
                 collect_in_term2
                 (fun _ _ -> failwith "should not happen")
           end))
      acc
  and collect_in_ph_list acc = GT.foldl Std.List.logic collect_in_ph acc in

  debug_var q Ph.reify (fun p ->
      let p : Types.Ph.logic = match p with [ h ] -> h | _ -> assert false in

      let cur_vars = collect_in_ph Algebra.SS.empty p in
      if Algebra.SS.equal cur_vars free then success else failure)

let test ?(n = 1) bv_size (evalo : (module Bv.S) -> _ -> Ph.injected -> _) ?hint
    m =
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

  let (module T), (module P) = Algebra.to_z3 bv_size ctx in
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
  let (module F : Algebra.FORMULA_Z3) = Algebra.z3_of_formula bv_size ctx in
  let ((module BV) as bv) = Bv.create bv_size in

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
            Format.printf
              "Predefined answers fits by the opinon of SMT solver!\n%!")
  in

  let apply_model ph ~model =
    match Z3.Model.eval model ph true with
    | None -> failwith "should not happen"
    | Some e when Z3.Boolean.is_true e -> true
    | Some e when Z3.Boolean.is_false e -> false
    | Some e when not (Z3.Expr.is_const e) -> (
        match run_solver e with
        | Z3.Solver.UNKNOWN ->
            failwith "Solver should not return UNKNOWN result"
        | UNSATISFIABLE -> false
        | SATISFIABLE -> true)
    | Some e ->
        printf "Model evaluation result is : %s\n%!" (Z3.Expr.to_string e);
        failwith "not implemented"
  in

  let q = MyQueue.create () in
  let ex_storage, myenqueue, _pack_of_cut_examples =
    let _eval m =
      match Z3.Model.eval m Z3Encoded.ph false with
      | None -> failwith "should not happen"
      | Some e when not (Z3.Expr.is_const e) -> failwith "Got not a constant "
      | Some e ->
          printf "Model evaluation result is : %s\n%!" (Z3.Expr.to_string e);
          42
    in
    let cutted = ref (Z3.Boolean.mk_true ctx) in

    let myenqueue model b =
      let env : Types.Env.ground =
        Algebra.SS.fold
          (fun name acc ->
            let eans = Z3.Model.eval model (T.var name) true |> Option.get in
            let estr = Z3.Expr.to_string eans in
            try
              let wrap n = (name, Types.T.Const (BV.of_int n)) :: acc in
              let scanf_bin s =
                if s.[0] = '#' && s.[1] = 'b' then
                  let len = String.length s in
                  let rec loop acc i =
                    if i >= len then acc
                    else if s.[i] = '0' then loop (acc * 2) (i + 1)
                    else if s.[i] = '1' then loop ((acc * 2) + 1) (i + 1)
                    else assert false
                  in
                  loop 0 2
                else failwith "Bad argument"
              in
              if String.starts_with ~prefix:"#b" estr then wrap (scanf_bin estr)
              else Scanf.sscanf estr "#x%X" wrap
            with Scanf.Scan_failure s as e ->
              Format.eprintf "Error while parsing a string '%s'\n%!" estr;
              raise e)
          free []
      in

      trace_new_example env (1 + MyQueue.size q) b;

      MyQueue.enqueue q env b
    in

    (* let's create a 1st example by querying any model *)
    let () =
      match run_solver Z3Encoded.ph with
      | Z3.Solver.UNKNOWN -> failwith "Solver should not return UNKNOWN result"
      | UNSATISFIABLE -> failwith "Initial formula is unsat"
      | SATISFIABLE ->
          let model = Z3.Solver.get_model solver |> Option.get in
          myenqueue model (apply_model Z3Encoded.ph ~model);
          Format.printf "starting example = %a\n%!" MyQueue.pp q
    in
    let () =
      let module P = Algebra.EnrichFormula (P) in
      let manual_answers =
        [ (* [ ("b", 9); ("a", 8) ];  *)
          (* [ ("b", 0); ("a", 8) ]  *) ]
      in

      manual_answers
      |> List.iter (fun env ->
             let genv =
               Types.Env.embed @@ List.map (fun (a, b) -> (a, BV.of_int b)) env
             in
             let envf =
               List.fold_left
                 (fun acc (x, v) -> P.(acc && T.var x == T.const_int v))
                 P.true_ env
             in
             let ph0 = P.conj envf Z3Encoded.ph in
             Format.printf "%s\n%!" (Z3.Expr.to_string ph0);
             let ans =
               match run_solver ph0 with
               | Z3.Solver.UNKNOWN ->
                   failwith "Solver should not return UNKNOWN result"
               | UNSATISFIABLE -> false
               | SATISFIABLE ->
                   (* let model = Z3.Solver.get_model solver |> Option.get in
                      Format.printf "Got a model that should be empty : `%s`\n"
                        (Z3.Model.to_string model); *)
                   true
             in
             MyQueue.enqueue q genv ans)
    in

    (q, myenqueue, cutted)
  in

  let on_ground ~span:_ x = Format.asprintf "%a" (GT.fmt Ph.ground) x in
  let on_logic ~span:_ x = Format.asprintf "%a" Ph.PPNew.my_logic_pp x in
  let open OCanren in
  let open Mytester in
  let goal ans_var =
    let cutter q do_cont =
      debug_var ans_var Ph.reify (function
        | [ p ] ->
            Format.printf "Current candidate = %a\n%!" Ph.PPNew.my_logic_pp p;
            success
        | _ -> assert false)
      &&& debug_var q Ph.reify (fun p ->
              let p = match p with [ h ] -> h | _ -> assert false in
              try
                (* There we should encode logic formula p to SMT and check that
                    not (I <=> p) is unsat
                *)
                Format.printf
                  "encoding to SMT a formula: \027[%dm`%a`\027[0m\n%!" 32
                  Ph.PPNew.my_logic_pp p;
                Format.printf "examples = %a\n%!" MyQueue.pp ex_storage;

                let candidate = Ph.to_smt_logic_exn bv_size ctx p in

                let q = F.(not (iff candidate Z3Encoded.ph)) in
                trace_intermediate_candidate candidate;
                match run_solver q with
                | Z3.Solver.UNKNOWN ->
                    failwith "Solver should not return UNKNOWN result"
                | UNSATISFIABLE ->
                    Format.eprintf "%s %d\n%!" __FILE__ __LINE__;
                    trace_on_success ex_storage solver_count;
                    do_cont === !!false
                | SATISFIABLE ->
                    let model = Z3.Solver.get_model solver |> Option.get in
                    myenqueue model (apply_model ~model Z3Encoded.ph);
                    Format.eprintf "New example added. Queue size = %d\n%!"
                      (MyQueue.size ex_storage);
                    do_cont === !!true
              with HasFreeVars s ->
                Format.eprintf "Got a phormula with free variables: `%s`\n%!" s;
                failure)
    in
    let loop =
      let rec helper i =
        let size = MyQueue.size ex_storage in
        if i >= size then
          (* let () = Format.printf "(i=%d) is >= %d\n%!" i size in *)
          Fresh.one (fun repeat ->
              cutter ans_var repeat
              &&& disj_2nd_strict
                    (repeat === !!true
                    &&& debug_var !!1 OCanren.reify (function _ ->
                            assert (i < MyQueue.size ex_storage);
                            success)
                    &&& delay (fun () -> kont i))
                    (repeat === !!false))
        else fresh () (kont i)
      and kont i =
        let _g, env0, is_true = MyQueue.get ex_storage i in
        (* Format.printf "Testing example: '%a'\n%!" EvalPh.Env.pp _g; *)
        evalo bv env0 ans_var !!is_true
        (* &&& EvalPh0.trace_bool !!is_true "evalo said" *)
        (* &&& EvalPh0.trace_ph ans_var "\t\tcurrent answer after %d example(s)"
              (1 + i) *)
        &&& delay (fun () -> helper (1 + i))
      in
      helper
    in
    (match hint with None -> success | Some h -> h ans_var) &&& loop 0
  in
  run_r Ph.reify on_logic n q qh ("", goal)
