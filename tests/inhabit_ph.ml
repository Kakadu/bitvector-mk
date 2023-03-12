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

(* TODO(Kakadu): represent variable names as integers *)
let terms_tbl : OCanren.tbl = Hashtbl.create 10

let evalo bv_impl =
  let (module BV : Bv.S) = bv_impl in
  let bv_iconst_1 = BV.build_num 1 in
  let bv_iconst_2 = BV.build_num 2 in
  let bv_iconst_3 = BV.build_num 3 in

  let rec evalo env ph is_tauto =
    conde
      [
        (* ph === Ph.true_ &&& (!!true === is_tauto); *)
        fresh (a b a2 b2 h1 h2 cmp_rez)
          (ph === Ph.le a b)
          (a =/= b)
          (Std.pair a b =/= Std.pair (T.const __) (T.const __))
          (* (trace_term a "a") *)
          (* (trace_term b "b") *)
          (termo env a (T.const a2))
          (termo env b (T.const b2))
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
          (fresh (u v) (tl === Std.List.cons u v))
          (h =/= Ph.conj __)
          (* (cut_bad_syntax `Conj h) *)
          (* (trace_ph_list Std.(h % tl) "conjuncts") *)
          (* (trace_int !!__LINE__ "call evalo on 1st conjunct") *)
          (* (trace_ph h "head = ")  *)
          (debug_var is_tauto (Fun.flip OCanren.reify) (function
            | [] | _ :: _ :: _ -> failwith "should not happen"
            | [ Value true ] ->
                (* evaluation when phormula should be true *)
                fresh () (evalo env h is_tauto)
                  (conj_list_evalo env ~prev:h tl is_tauto)
            | [ Value false ] ->
                (* evaluation when phormula should be false  *)
                conde
                  [
                    evalo env h is_tauto;
                    conj_list_evalo env ~prev:h tl is_tauto;
                  ]
            | [ Var _ ] ->
                (* synthesis *)
                fresh () (evalo env h arez)
                  (conde
                     [
                       arez === !!true
                       &&& conj_list_evalo env ~prev:h tl is_tauto;
                       arez === !!false
                       &&& trace_line [%here]
                       &&& (is_tauto === !!false);
                     ])));
        fresh (prev rez)
          (ph === Ph.not prev)
          (prev =/= Ph.not __)
          (conde
             [
               is_tauto === !!true &&& (rez === !!false);
               is_tauto === !!false &&& (rez === !!true);
             ])
          (evalo env prev rez);
      ]
  and termo env (t : T.injected) (rez : T.injected) =
    conde
      [
        fresh v (t === T.var v) (Types.Env.lookupo v env rez)
        (* (trace_term rez "after lookup") *)
        (* (trace_env env "in the env") *);
        conde
          [
            t === rez &&& (t === T.const bv_iconst_1);
            t === rez &&& (t === T.const bv_iconst_2);
            t === rez &&& (t === T.const bv_iconst_3);
          ];
        fresh (l r r0 l2 r2)
          (t === T.shl l r)
          (rez === T.const r0)
          (Std.pair l r =/= Std.pair (T.const __) (T.const __))
          (termo env l (T.const l2))
          (termo env r (T.const r2))
          (BV.shiftlo l2 r2 r0)
        (* ~cstr:(fun a b ->
           structural (Std.pair a b) (Std.Pair.reify T.reify T.reify) (function
             | Value (Value (T.Const _), Value (T.Const _)) -> false
             | _ -> true)); *);
      ]
  and conj_list_evalo env ~prev phs is_tauto =
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
          (* Not yet expressible *)
          (*
        (fresh www
           (* forbid 'prev&h' to be 'c1 <= www & c2 <= www' *)
           (Std.pair prev h
           =/= Std.pair (Ph.le (T.const __) www) (Ph.le (T.const __) www)))
        (fresh www
           (* forbid 'prev&h' to be 'www <= c1 & www <= c2' *)
           (Std.pair prev h
           =/= Std.pair (Ph.le www (T.const __)) (Ph.le www (T.const __))))
        *)
          (OCanren.structural (Std.pair prev h)
             (Std.Pair.reify Ph.reify Ph.reify) (function
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
          (* (trace_ph h "conj_list_evalo: 'evalo h' ") *)
          (evalo env h arez)
          (conde
             [
               fresh () (arez === !!true)
                 (conj_list_evalo env ~prev:h tl is_tauto)
                 (* (fresh www
                       (* forbid 'prev&h' to be 'c1 <= www & c2 <= www' *)
                       (Std.pair prev h
                       =/= Std.pair (Ph.le (T.const __) www) (Ph.le (T.const __) www)
                       ))
                    (fresh www
                       (* forbid 'prev&h' to be 'www <= c1 & www <= c2' *)
                       (Std.pair prev h
                       =/= Std.pair (Ph.le www (T.const __)) (Ph.le www (T.const __))
                       )) *)
                 success;
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
  in
  evalo
(* and disj_list_evalo bv_impl env ~prev phs is_tauto =
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
     ] *)
