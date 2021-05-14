open OCanren
open Types

let debug_n : Bv.Repr.n -> (int logic Std.List.logic list -> goal) -> goal =
 fun n -> debug_var n (fun a b -> OCanren.Std.List.reify OCanren.reify b a)

let trace_my show n fmt =
  debug_n n (function
    | [ n ] ->
        Format.printf "%s: %s\n%!" (Format.asprintf fmt) (show n);
        success
    | _ -> assert false)

let trace_n n fmt = trace_my Bv.Repr.show_logic n fmt

let trace_bool n fmt =
  debug_var n (flip OCanren.reify) (function
    | [ b ] ->
        Format.printf "%s: %s\n%!" (Format.asprintf fmt)
          (GT.show logic (GT.show GT.bool) b);
        success
    | _ -> assert false)

let trace_ph : Types.Ph.injected -> _ -> _ =
 fun n fmt ->
  debug_var n (flip Ph.reify) (function
    | [ f ] ->
        Format.printf "%s: %a\n%!" (Format.asprintf fmt) Ph.PPNew.my_logic_pp f;
        success
    | _ -> assert false)

let trace_ph_list n fmt =
  debug_var n
    (flip (Std.List.reify Ph.reify))
    (function
      | [] -> success
      | [ f ] ->
          Format.printf "%s: %s\n%!" (Format.asprintf fmt)
            (GT.show Std.List.logic (GT.show Ph.logic) f);
          success
      | _ -> assert false)

let trace_cmp n fmt =
  (* trace_my
     (GT.show Std.List.logic (GT.show OCanren.logic (GT.show Bv.cmp_t)))
     n fmt *)
  debug_var n
    (fun a b -> OCanren.reify b a)
    (function
      | [ n ] ->
          Format.printf "%s: %s\n%!" (Format.asprintf fmt)
            ((GT.show OCanren.logic (GT.show Bv.cmp_t)) n);
          success
      | _ -> assert false)

let trace_int n fmt =
  debug_var n
    (fun a b -> OCanren.reify b a)
    (function
      | [ n ] ->
          Format.printf "%s: %s\n%!" (Format.asprintf fmt)
            (GT.show OCanren.logic (GT.show GT.int) n);
          success
      | _ -> assert false)

let evalo_helper bv_impl : Env.injected -> Ph.injected -> _ -> goal =
  let (module BV : Bv.S) = bv_impl in
  let cut_bad_syntax op ph =
    (* no conjunction inside conjunction and no disjunction inside disjunction *)
    match op with
    | `Conj ->
        structural ph Ph.reify (function
          | Value (Not (Value True)) | Value True | Value (Conj _) -> false
          | _ -> true)
    | `Disj ->
        structural ph Ph.reify (function Value (Disj _) -> false | _ -> true)
  in
  let rec evalo_list op prev env phs is_tauto =
    let make_decision arez h tl =
      match op with
      | `Conj ->
          conde
            [
              arez === !!true &&& evalo_list op h env tl is_tauto;
              arez === !!false &&& (is_tauto === !!false);
            ]
      | `Disj ->
          conde
            [
              arez === !!false &&& evalo_list op h env tl is_tauto;
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
          (OCanren.structural (Std.pair prev h)
             (Std.Pair.reify Ph.reify Ph.reify) (function
            | Var _ -> failwiths "should not happen"
            | Value (a, b) -> (
                match GT.compare Ph.logic a b with
                | LT | EQ -> true
                | _ ->
                    Format.printf "comparsion said (not<=): %a and %a\n%!"
                      Ph.PPNew.my_logic_pp a Ph.PPNew.my_logic_pp b;
                    false)))
          (evalo env h arez) (make_decision arez h tl);
      ]
  and evalo env ph is_tauto =
    conde
      [
        (* ph === Ph.true_ &&& (!!true === is_tauto); *)
        fresh (a b a2 b2 h1 h2 cmp_rez)
          (ph === Ph.le a b)
          (a =/= b)
          (structural (Std.pair a b) (Std.Pair.reify T.reify T.reify) (function
            | Value (Value (T.Const _), Value (T.Const _)) -> false
            | _ -> true))
          (termo env a (T.const a2))
          (termo env b (T.const b2))
          (conde
             [
               cmp_rez === !!Bv.GT &&& (is_tauto === !!false);
               cmp_rez =/= !!Bv.GT &&& (is_tauto === !!true);
             ])
          (BV.compare_helper a2 b2 cmp_rez);
        fresh () (ph === Ph.conj (Std.nil ())) failure;
        fresh (a b h tl arez)
          (ph === Ph.conj Std.(h % tl))
          (cut_bad_syntax `Conj h)
          (* (trace_ph_list Std.(h % tl) "conjuncts") *)
          (* (trace_int !!__LINE__ "call evalo on 1st conjunct") *)
          (* (trace_ph h "head = ")  *)
          (evalo env h arez)
          (* (trace_bool arez "1st conjunct done") *)
          (conde
             [
               arez === !!true
               (* &&& trace_int !!__LINE__ "call evalo_list" *)
               &&& evalo_list `Conj h env tl is_tauto;
               arez === !!false &&& (is_tauto === !!false);
             ]);
        fresh (prev rez)
          (ph === Ph.not prev)
          (conde
             [
               is_tauto === !!true &&& (rez === !!false);
               is_tauto === !!false &&& (rez === !!true);
             ])
          (evalo env prev rez);
      ]
  and termo env (t : T.injected) (rez : T.injected) =
    let wrap_binop ?(cstr = fun _ _ -> success) top bvop =
      fresh (l r l2 r2 r0)
        (t === top l r)
        (cstr l r)
        (rez === T.const r0)
        (termo env l (T.const l2))
        (termo env r (T.const r2))
        (bvop l2 r2 r0)
    in
    conde
      [
        conde
          (List.map
             (fun n -> t === rez &&& (t === T.const (BV.build_num n)))
             [ 1; 2; 3 ]);
        (* t === rez &&& (t === T.const (BV.build_num 1));
           t === rez &&& (t === T.const (BV.build_num 2));
           t === rez &&& (t === T.const (BV.build_num 3)); *)
        fresh v (t === T.var v) (Env.lookupo v env rez);
        wrap_binop T.shl BV.shiftlo ~cstr:(fun a b ->
            structural (Std.pair a b) (Std.Pair.reify T.reify T.reify) (function
              | Value (Value (T.Const _), Value (T.Const _)) -> false
              | _ -> true));
      ]
  in
  evalo
