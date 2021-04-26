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
  (* N.B. Environment never changes *)
  let (module BV : Bv.S) = bv_impl in
  (* op = `Conj | `Disj
      prev = first operand
  *)
  let rec evalo_list _op _prev env phs is_tauto =
    let make_decision arez h tl =
      match _op with
      | `Conj ->
          conde
            [
              arez === !!true &&& evalo_list _op h env tl is_tauto;
              arez === !!false &&& (is_tauto === !!false);
            ]
      | `Disj ->
          conde
            [
              arez === !!false &&& evalo_list _op h env tl is_tauto;
              arez === !!true &&& (is_tauto === !!true);
            ]
    in
    conde
      [
        (phs === Std.nil ()
        &&& match _op with `Conj -> success | `Disj -> failure);
        fresh (h tl arez)
          (phs === Std.(h % tl))
          (evalo env h arez) (make_decision arez h tl);
      ]
  and evalo env ph is_tauto =
    conde
      [
        ph === Ph.true_ &&& (!!true === is_tauto);
        (* fresh (a b r) (ph === Ph.eq a b) (termo env a r) (termo env b r); *)
        (* fresh (a b a2 b2)
           (ph === Ph.lt a b)
           (termo env a (T.const a2))
           (termo env b (T.const b2))
           (BV.lto a2 b2); *)
        fresh (a b a2 b2 h1 h2 cmp_rez)
          (ph === Ph.le a b)
          (a =/= b) (* (trace_int !!__LINE__ "Ph.le gave result") *)
          (structural (Std.pair a b) (Std.Pair.reify T.reify T.reify) (function
            | Value (Value (T.Const _), Value (T.Const _)) -> false
            | _ -> true))
          (termo env a (T.const a2))
          (* (trace_int !!__LINE__ "termo a gave result") *)
          (termo env b (T.const b2))
          (* (trace_int !!__LINE__ "termo b gave result") *)
          (conde
             [
               cmp_rez === !!Bv.GT &&& (is_tauto === !!false);
               cmp_rez =/= !!Bv.GT &&& (is_tauto === !!true);
             ])
          (* (trace_int !!__LINE__ "<= gave result") *)
          (* (trace_n a2 "a2") (trace_n b2 "b2") *)
          (* (trace_cmp cmp_rez " === cmp_rez") *)
          (BV.compare_helper a2 b2 cmp_rez)
          (* (trace_int !!__LINE__ "`compare_helper` gave result") *)
          (* (trace_n a2 "a2") *)
          (* (trace_n b2 "b2") *)
          success;
        fresh () (ph === Ph.conj (Std.nil ())) (is_tauto === !!true);
        fresh (a b h tl xs arez)
          (ph === Ph.conj xs)
          (xs =/= Std.nil ())
          (xs === Std.(h % tl))
          (h =/= Ph.not Ph.true_)
          (evalo env h arez)
          (conde
             [
               arez === !!true &&& evalo_list `Conj h env tl is_tauto;
               arez === !!false &&& (is_tauto === !!false);
             ]);
        fresh (a nrez)
          (ph === Ph.not a)
          (structural a Ph.reify (function
            | Value (Ph.Not _) -> false
            | _ -> true))
          (evalo env a nrez)
          (conde
             [
               nrez === !!true &&& (is_tauto === !!false);
               nrez === !!false &&& (is_tauto === !!true);
             ]);
      ]
  and termo env (t : T.injected) (rez : T.injected) =
    let wrap_binop ?(cstr = fun _ _ -> success) top bvop =
      fresh (l r l2 r2 r0 h1 h2)
        (t === top l r)
        (* (Std.pair l r =/= Std.pair (T.const h1) (T.const h2)) *)
        (cstr l r)
        (rez === T.const r0)
        (termo env l (T.const l2))
        (termo env r (T.const r2))
        (bvop l2 r2 r0)
    in
    let wrap_uop ?(cstr = fun _ -> success) uop bvop =
      fresh (l l2 r0)
        (t === uop l)
        (cstr l)
        (rez === T.const r0)
        (termo env l (T.const l2))
        (bvop l2 r0)
    in
    let rec not_in_envo t env =
      conde
        [
          env === Env.empty;
          fresh (v t0 env0)
            (env === Env.cons v t0 env0)
            (t0 =/= t) (not_in_envo t env0);
        ]
    in
    conde
      [
        fresh v
          (t === T.var v)
          (* (trace_int !!__LINE__ "line") *)
          (Env.lookupo v env rez);
        fresh () (t === rez)
          (conde
             (List.map (fun n -> t === T.const (BV.build_num n)) [ 1; 2; 3 ]));
        (* wrap_binop T.mul BV.multo; *)
        (* wrap_binop T.add BV.addo; *)
        (* wrap_binop T.sub BV.subo; *)
        (* wrap_uop T.lshiftr1 BV.lshiftr1; *)
        wrap_binop T.shl BV.shiftlo ~cstr:(fun a b ->
            structural (Std.pair a b) (Std.Pair.reify T.reify T.reify) (function
              | Value (Value (T.Const _), Value (T.Const _)) -> false
              | _ -> true));
        (*
          ~cstr:(fun in_ ->
            (* let (_ : int) = OCanren.structural in *)
            OCanren.structural in_ T.reify (fun xx ->
                match xx with Value (T.Shl1 _) -> false | _ -> true))
                *)
        (* TODO: divo *)
      ]
  in
  evalo

let evalo bv env ph = evalo_helper bv env ph !!true
