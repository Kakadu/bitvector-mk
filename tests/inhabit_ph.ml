open Types
open OCanren

type trace_cfg = { mutable trace_order : bool }

let trace_cfg = { trace_order = false }
let set_trace_order flg = trace_cfg.trace_order <- flg

let trace_line { Lexing.pos_fname; Lexing.pos_lnum } =
  debug_var !!1 (Fun.flip OCanren.prj_exn) (function
    | [ q ] ->
        Format.printf "%s %d\n%!" pos_fname pos_lnum;
        success
    | _ -> failwith "Will not happen")

let trace_helper reifier pp bv fmt =
  Format.kasprintf
    (fun msg ->
      debug_var bv (Fun.flip reifier) (function
        | [ q ] ->
            Format.printf "%s: %a\n%!" msg pp q;
            success
        | _ -> failwith "Will not happen"))
    fmt

let trace_bv eta = trace_helper Bv.Repr.reify Bv.Repr.pp_logic eta
let trace_ph eta = trace_helper Types.Ph.reify Types.Ph.PPNew.my_logic_pp eta
let trace_term eta = trace_helper Types.T.reify Types.T.PPNew.my_logic_pp eta
let trace_env eta = trace_helper Types.Env.reify Types.Env.pp_logic eta

let rec evalo bv_impl env ph is_tauto =
  let (module BV : Bv.S) = bv_impl in
  conde
    [
      (* ph === Ph.true_ &&& (!!true === is_tauto); *)
      fresh (a b a2 b2 h1 h2 cmp_rez)
        (ph === Ph.le a b)
        (a =/= b)
        (Std.pair a b =/= Std.pair (T.const __) (T.const __))
        (* (trace_term a "a") *)
        (* (trace_term b "b") *)
        (termo bv_impl env a (T.const a2))
        (termo bv_impl env b (T.const b2))
        (* (trace_bv a2 "Left  part of <=") *)
        (* (trace_bv b2 "Right part of <=") *)
        (conde
           [
             cmp_rez === !!Bv.GT &&& (is_tauto === !!false);
             cmp_rez =/= !!Bv.GT &&& (is_tauto === !!true);
           ])
        (* (trace_line [%here]) *)
        (BV.compare_helper a2 b2 cmp_rez)
      (* (trace_line [%here]) *);
      fresh () (ph === Ph.conj (Std.nil ())) failure;
      fresh (a b h tl arez)
        (ph === Ph.conj (Std.List.cons h tl))
        (tl === Std.List.cons __ __)
        (h =/= Ph.conj __)
        (* (cut_bad_syntax `Conj h) *)
        (* (trace_ph_list Std.(h % tl) "conjuncts") *)
        (* (trace_int !!__LINE__ "call evalo on 1st conjunct") *)
        (* (trace_ph h "head = ")  *)
        (evalo bv_impl env h arez)
        (* (trace_bool arez "1st conjunct done") *)
        (conde
           [
             arez === !!true
             (* &&& trace_line [%here] *)
             &&& conj_list_evalo bv_impl env ~prev:h tl is_tauto;
             arez === !!false &&& trace_line [%here] &&& (is_tauto === !!false);
           ]);
      fresh (prev rez)
        (ph === Ph.not prev)
        (prev =/= Ph.not __)
        (conde
           [
             is_tauto === !!true &&& (rez === !!false);
             is_tauto === !!false &&& (rez === !!true);
           ])
        (evalo bv_impl env prev rez);
    ]

and disj_list_evalo bv_impl env ~prev phs is_tauto =
  conde
    [
      (* multiple disjunction shoould evaluate end of conjucts as true.
         It is not related to evaluation of empty disjunction *)
      phs === Std.nil () &&& (is_tauto === !!false);
      fresh (h tl arez)
        (phs === Std.List.cons h tl)
        (h =/= prev)
        (h =/= Ph.disj __)
        (OCanren.structural (Std.pair prev h) (Std.Pair.reify Ph.reify Ph.reify)
           (function
          | Var _ -> failwiths "should not happen"
          | Value (a, b) -> (
              match GT.compare Ph.logic a b with
              | LT | EQ -> true
              | _ ->
                  if trace_cfg.trace_order then
                    Format.printf
                      "comparsion have filtered out '%a' and '%a'\n%!"
                      Ph.PPNew.my_logic_pp a Ph.PPNew.my_logic_pp b;
                  false)))
        (evalo bv_impl env h arez)
        (conde
           [
             arez === !!false
             &&& disj_list_evalo bv_impl env ~prev:h tl is_tauto;
             arez === !!true &&& (is_tauto === !!true);
           ]);
    ]

and conj_list_evalo bv_impl env ~prev phs is_tauto =
  conde
    [
      (* multiple conjunction shoould evaluate end of conjucts as true.
         It is not related to evaluation of empty conjunction *)
      phs === Std.nil () &&& (is_tauto === !!true);
      fresh (h tl arez)
        (phs === Std.List.cons h tl)
        (h =/= prev)
        (h =/= Ph.conj __)
        (* (trace_line [%here]) *)
        (fresh vvv
           (* forbid 'prev&h' be ' c1 <= vvv & c2 <= vvv' *)
           (Std.pair prev h
           =/= Std.pair (Ph.le (T.const __) vvv) (Ph.le (T.const __) vvv)))
        (* (trace_line [%here]) *)
        (OCanren.structural (Std.pair prev h) (Std.Pair.reify Ph.reify Ph.reify)
           (function
          | Var _ -> failwiths "should not happen"
          | Value (a, b) -> (
              match GT.compare Ph.logic a b with
              | LT | EQ -> true
              | _ ->
                  if trace_cfg.trace_order then
                    Format.printf
                      "comparsion have filtered out '%a' and '%a'\n%!"
                      Ph.PPNew.my_logic_pp a Ph.PPNew.my_logic_pp b;
                  false)))
        (* (trace_line [%here]) *)
        (* (trace_ph h "conj_list_evalo: 'evalo h' ") *)
        (evalo bv_impl env h arez)
        (conde
           [
             arez === !!true &&& conj_list_evalo bv_impl env ~prev:h tl is_tauto;
             arez === !!false &&& (is_tauto === !!false);
           ]);
    ]

(*
and evalo_list bv_impl op prev env phs is_tauto =
  let make_decision arez h tl =
    match op with
    | `Conj ->
        conde
          [
            arez === !!true &&& evalo_list bv_impl op h env tl is_tauto;
            arez === !!false &&& (is_tauto === !!false);
          ]
    | `Disj ->
        conde
          [
            arez === !!false &&& evalo_list bv_impl op h env tl is_tauto;
            arez === !!true &&& (is_tauto === !!true);
          ]
  in
  conde
    [
      (phs === Std.nil ()
      &&& match op with `Conj -> success | `Disj -> failure);
      fresh (h tl arez)
        (phs === Std.(h % tl))
        (h =/= prev)
        (* (cut_bad_syntax op h) *)
        (OCanren.structural (Std.pair prev h) (Std.Pair.reify Ph.reify Ph.reify)
           (function
          | Var _ -> failwiths "should not happen"
          | Value (a, b) -> (
              match GT.compare Ph.logic a b with
              | LT | EQ -> true
              | _ ->
                  Format.printf "comparsion said (not<=): %a and %a\n%!"
                    Ph.PPNew.my_logic_pp a Ph.PPNew.my_logic_pp b;
                  false)))
        (evalo bv_impl env h arez) (make_decision arez h tl);
    ]
*)

and termo bv_impl env (t : T.injected) (rez : T.injected) =
  let (module BV : Bv.S) = bv_impl in
  (* let wrap_binop ?(cstr = fun _ _ -> success) top bvop =
       fresh (l r l2 r2 r0)
         (t === top l r)
         (cstr l r)
         (rez === T.const r0)
         (termo bv_impl env l (T.const l2))
         (termo bv_impl env r (T.const r2))
         (bvop l2 r2 r0)
     in *)
  conde
    [
      fresh v
        (t === T.var v)
        (Types.Env.lookupo v env rez)
        (* (trace_term rez "after lookup") *)
        (* (trace_env env "in the env") *)
        success;
      conde
        (List.map
           (fun n -> t === rez &&& (t === T.const (BV.build_num n)))
           [ 1; 2; 3 ]);
      (* t === rez &&& (t === T.const (BV.build_num 1));
         t === rez &&& (t === T.const (BV.build_num 2));
         t === rez &&& (t === T.const (BV.build_num 3)); *)
      fresh (l r r0 l2 r2)
        (t === T.shl l r)
        (rez === T.const r0)
        (Std.pair l r =/= Std.pair (T.const __) (T.const __))
        (termo bv_impl env l (T.const l2))
        (termo bv_impl env r (T.const r2))
        (BV.shiftlo l2 r2 r0)
      (* ~cstr:(fun a b ->
         structural (Std.pair a b) (Std.Pair.reify T.reify T.reify) (function
           | Value (Value (T.Const _), Value (T.Const _)) -> false
           | _ -> true)); *);
    ]

(* let run_ph eta =
     Tester.run_r Ph.reify (Format.asprintf "%a" Ph.PPNew.my_logic_pp) eta

   let _ =
     let open Tester in
     let ((module BV) as bv) = Bv.create 4 in
     let env =
       Types.Env.inject @@ Types.Env.embed
       @@ List.map (fun (a, b) -> (a, BV.of_int b)) [ ("x", 1) ]
     in

     [%tester run_ph 20 (fun ph -> evalo (Bv.create 4) env ph !!true)]
*)
