open OCanren
open Types

let evalo bv_impl : Env.injected -> Ph.injected -> goal =
  let (module BV : Bv.S) = bv_impl in
  let rec evalo env ph =
    conde
      [
        ph === Ph.true_;
        (* fresh (a b r) (ph === Ph.eq a b) (termo env a r) (termo env b r); *)
        (* fresh (a b a2 b2)
           (ph === Ph.lt a b)
           (termo env a (T.const a2))
           (termo env b (T.const b2))
           (BV.lto a2 b2); *)
        fresh (a b a2 b2 h1 h2)
          (ph === Ph.le a b)
          (* (Std.pair a b =/= Std.pair (T.const h1) (T.const h2)) *)
          (termo env a (T.const a2))
          (termo env b (T.const b2))
          (structural (Std.pair a b) (Std.Pair.reify T.reify T.reify) (function
            | Value (Value (T.Const _), Value (T.Const _)) -> false
            | _ -> true))
          (BV.leo a2 b2);
        fresh (a b)
          (ph === Ph.conj a b)
          (a =/= Ph.not Ph.true_)
          (b =/= Ph.not Ph.true_)
          (a =/= Ph.true_) (b =/= Ph.true_) (evalo env a) (evalo env b);
        (* fresh (a b) (ph === Ph.disj a b) (evalo env a) (evalo env b); *)
        fresh a
          (ph === Ph.not a)
          (structural a Ph.reify (function
            | Value (Ph.Not _) -> false
            | _ -> true))
          (evalo env a);
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
    conde
      [
        fresh v (t === T.var v) (Env.lookupo v env rez);
        conde @@ List.map (fun n -> t === T.const (BV.build_num n)) [ 1; 2; 3 ];
        (* wrap_binop T.mul BV.multo; *)
        (* wrap_binop T.add BV.addo; *)
        (* wrap_binop T.sub BV.subo; *)
        (* wrap_uop T.lshiftr1 BV.lshiftr1; *)
        wrap_binop T.shl BV.shiftlo ~cstr:(fun a b ->
            structural (Std.pair a b) (Std.Pair.reify T.reify T.reify) (function
              | Value (Value (T.Const _), Value (T.Const _)) -> false
              | _ -> true));
        (* wrap_uop T.shiftl1 BV.shiftl1 *)
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
