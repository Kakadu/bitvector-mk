open OCanren

let flip f a b = f b a

module N = struct
  type ground = Bv.Repr.g

  type nonrec logic = Bv.Repr.l

  type nonrec injected = Bv.Repr.injected

  let ground = Bv.Repr.g

  let logic = Bv.Repr.l

  let reify env x = Bv.Repr.reify env x

  let one : injected =
    let open OCanren in
    Std.(!<(!!1))

  let zero : injected =
    let open OCanren in
    Std.(!<(!!0))

  let int_of_ground (xs : Bv.Repr.g) =
    let _, ans =
      GT.foldl OCanren.Std.List.ground
        (fun (base, acc) n ->
          if n = 1 then (base * 2, base + acc) else (base * 2, acc))
        (1, 0) xs
    in
    ans

  let ground =
    {
      ground with
      GT.plugins =
        object
          method show n = string_of_int @@ int_of_ground n

          method gmap = ground.GT.plugins#gmap

          method fmt ppf n = Format.pp_print_int ppf (int_of_ground n)
        end;
    }

  let to_smt ctx xs : Z3.Expr.expr =
    let (module T), _ = S.to_z3 ctx in

    (* let b = Buffer.create 20 in *)
    (* Buffer.add_string b "#x";
       let () =
         List.fold_right
           (fun n () -> Buffer.add_char b (if n then '1' else '0'))
           xs ()
       in
       T.const_s (Buffer.contents b) *)
    T.const_s @@ string_of_int @@ int_of_ground xs

  let to_smt_logic_exn ctx (xs : Bv.Repr.l) : Z3.Expr.expr =
    let (module T), _ = S.to_z3 ctx in
    (* let b = Buffer.create 20 in *)
    (* Buffer.add_string b "#x"; *)
    let acc = ref 0 in
    let module L = OCanren.Std.List in
    let rec iter base = function
      | OCanren.Value (L.Cons (OCanren.Var _, _))
      | Value (L.Cons (_, OCanren.Var _))
      | Var _ ->
          assert false
      | Value (L.Cons (Value n, tl)) ->
          (* Buffer.add_char b (if n then '1' else '0'); *)
          acc := !acc + if n = 1 then base else 0;
          iter (base * 2) tl
      | Value L.Nil -> ()
    in
    iter 1 xs;
    (* T.const_s (Buffer.contents b) *)
    T.const_s (string_of_int !acc)
end

module T = struct
  type ('self, 'int, 'varname) t =
    | Const of 'int
    | Var of 'varname
    | Shl of 'self * 'self
    | Lshr of 'self * 'self
    | Land of 'self * 'self
    | Lor of 'self * 'self
    | Mul of 'self * 'self
    | Add of 'self * 'self
    | Sub of 'self * 'self
  [@@deriving gt ~options:{ show; fmt; gmap }]

  open OCanren

  module E = Fmap3 (struct
    type nonrec ('a, 'b, 'c) t = ('a, 'b, 'c) t

    let fmap eta = GT.gmap t eta
  end)

  type ground = (ground, N.ground, GT.string) t
  [@@deriving gt ~options:{ show; fmt; gmap }]

  type logic = (logic, N.logic, GT.string OCanren.logic) t OCanren.logic
  [@@deriving gt ~options:{ show; fmt; gmap }]

  type nonrec injected = (ground, logic) injected

  let rec reify env x = E.reify reify N.reify OCanren.reify env x

  let const (x : Bv.Repr.injected) : injected = inj @@ E.distrib @@ Const x

  let var s = inj @@ E.distrib @@ Var s

  let shl a b : injected = inj @@ E.distrib @@ Shl (a, b)

  let lshr a b : injected = inj @@ E.distrib @@ Lshr (a, b)

  let land_ a b = inj @@ E.distrib @@ Land (a, b)

  let lor_ a b = inj @@ E.distrib @@ Lor (a, b)

  let mul a b = inj @@ E.distrib @@ Mul (a, b)

  let add a b = inj @@ E.distrib @@ Add (a, b)

  let sub a b = inj @@ E.distrib @@ Sub (a, b)

  let pp_ground : Format.formatter -> ground -> unit =
    let rec helper ppf = function
      | Const n -> GT.fmt Bv.Repr.g ppf n
      | Var s -> Format.pp_print_string ppf s
      | Add (l, r) -> Format.fprintf ppf "(bvadd %a %a)" helper l helper r
      | Sub (l, r) -> Format.fprintf ppf "(bvsub %a %a)" helper l helper r
      | Mul (l, r) -> Format.fprintf ppf "(bvmul %a %a)" helper l helper r
      | Land (l, r) -> Format.fprintf ppf "(bvand %a %a)" helper l helper r
      | Lor (l, r) -> Format.fprintf ppf "(bvor %a %a)" helper l helper r
      | Shl (l, r) -> Format.fprintf ppf "(bvshl %a %a)" helper l helper r
      | Lshr (l, r) -> Format.fprintf ppf "(bvlshr %a %a)" helper l helper r
    in
    helper

  let ground =
    {
      ground with
      GT.plugins =
        object
          method show = GT.show ground

          method fmt = pp_ground

          method gmap = GT.gmap ground
        end;
    }

  let to_smt ctx : ground -> _ =
    let (module T), (module P) = S.to_z3 ctx in
    let rec helper = function
      | Const n -> N.to_smt ctx n
      | Var s -> T.var s
      | Add (l, r) -> T.add (helper l) (helper r)
      | Sub (l, r) -> T.sub (helper l) (helper r)
      | Mul (l, r) -> T.mul (helper l) (helper r)
      | Shl (l, r) -> T.shl (helper l) (helper r)
      | Lshr (l, r) -> T.lshr (helper l) (helper r)
      | Land (l, r) -> T.land_ (helper l) (helper r)
      | Lor (l, r) -> T.lor_ (helper l) (helper r)
    in
    helper

  let to_smt_logic_exn ctx : logic -> _ =
    let (module T), _ = S.to_z3 ctx in
    let rec helper : logic -> _ = function
      | Value (Var (OCanren.Var _)) | Var _ -> failwith "logic inside"
      | Value (Const n) -> N.to_smt_logic_exn ctx n
      | Value (Var (OCanren.Value s)) -> T.var s
      | Value (Add (l, r)) -> T.add (helper l) (helper r)
      | Value (Sub (l, r)) -> T.sub (helper l) (helper r)
      | Value (Mul (l, r)) -> T.mul (helper l) (helper r)
      | Value (Shl (l, r)) -> T.shl (helper l) (helper r)
      | Value (Lshr (l, r)) -> T.shl (helper l) (helper r)
      | Value (Land (l, r)) -> T.land_ (helper l) (helper r)
      | Value (Lor (l, r)) -> T.lor_ (helper l) (helper r)
    in
    helper
end

let rec inhabito_term varo =
  let rec helper (rez : T.injected) =
    let open OCanren in
    conde
      [
        fresh x (rez === T.const x) (inhabito_const x);
        fresh n (rez === T.var n) (varo n);
        fresh (l r) (rez === T.land_ l r) (helper l) (helper r);
        fresh (l r) (rez === T.lor_ l r) (helper l) (helper r);
        fresh (l r) (rez === T.mul l r) (helper l) (helper r);
        fresh (l r) (rez === T.sub l r) (helper l) (helper r);
        fresh (l r) (rez === T.add l r) (helper l) (helper r);
        fresh (l r) (rez === T.shl l r) (helper l) (helper r);
        fresh (l r) (rez === T.lshr l r) (helper l) (helper r);
      ]
  in
  helper

and inhabito_const r =
  let open OCanren in
  conde [ r === N.one; r === N.zero ]

let __ () =
  let on_ground x = Format.asprintf "%a" (GT.fmt T.ground) x in
  let open OCanren in
  let open Tester in
  run_exn on_ground 20 q qh ("", inhabito_term (fun q -> q === !!"a"))

module Ph = struct
  type ('self, 'term) t =
    | Conj of 'self * 'self
    | Disj of 'self * 'self
    | Not of 'self
    | Eq of 'term * 'term
    | Lt of 'term * 'term
    | Le of 'term * 'term
  [@@deriving gt ~options:{ show; fmt; gmap }]

  open OCanren

  module E = Fmap2 (struct
    type nonrec ('a, 'b) t = ('a, 'b) t

    let fmap eta = GT.gmap t eta
  end)

  type ground = (ground, T.ground) t
  [@@deriving gt ~options:{ show; fmt; gmap }]

  type logic = (logic, T.logic) t OCanren.logic
  [@@deriving gt ~options:{ show; fmt; gmap }]

  let rec reify env x = E.reify reify T.reify env x

  let eq a b = inj @@ E.distrib @@ Eq (a, b)

  let lt a b = inj @@ E.distrib @@ Lt (a, b)

  let le a b = inj @@ E.distrib @@ Le (a, b)

  let conj a b = inj @@ E.distrib @@ Conj (a, b)

  let disj a b = inj @@ E.distrib @@ Disj (a, b)

  let not a = inj @@ E.distrib @@ Not a

  let pp_ground : Format.formatter -> ground -> unit =
    let rec helper ppf : ground -> _ = function
      | Eq (l, r) ->
          Format.fprintf ppf "(= %a %a)" (GT.fmt T.ground) l (GT.fmt T.ground) r
      | Le (l, r) ->
          Format.fprintf ppf "(<= %a %a)" (GT.fmt T.ground) l (GT.fmt T.ground)
            r
      | Lt (l, r) ->
          Format.fprintf ppf "(< %a %a)" (GT.fmt T.ground) l (GT.fmt T.ground) r
      | Conj (l, r) -> Format.fprintf ppf "(and %a %a)" helper l helper r
      | Disj (l, r) -> Format.fprintf ppf "(or %a %a)" helper l helper r
      | Not l -> Format.fprintf ppf "(not %a)" helper l
    in
    helper

  let ground =
    {
      ground with
      GT.plugins =
        object
          method show = GT.show ground

          method fmt = pp_ground

          method gmap = GT.gmap ground
        end;
    }

  let to_smt ctx gr =
    let term = T.to_smt ctx in
    let _, (module P) = S.to_z3 ctx in

    let rec helper = function
      | Eq (l, r) -> P.eq (term l) (term r)
      | Le (l, r) -> P.le (term l) (term r)
      | Lt (l, r) -> P.lt (term l) (term r)
      | Conj (l, r) -> P.conj (helper l) (helper r)
      | Disj (l, r) -> P.disj (helper l) (helper r)
      | Not l -> P.not (helper l)
    in
    helper gr

  let to_smt_logic_exn ctx : logic -> Z3.Expr.expr =
    let term = T.to_smt_logic_exn ctx in
    let _, (module P) = S.to_z3 ctx in

    let rec helper = function
      | Var _ -> failwith "free vars inside"
      | Value (Eq (l, r)) -> P.eq (term l) (term r)
      | Value (Le (l, r)) -> P.le (term l) (term r)
      | Value (Lt (l, r)) -> P.lt (term l) (term r)
      | Value (Conj (l, r)) -> P.conj (helper l) (helper r)
      | Value (Disj (l, r)) -> P.disj (helper l) (helper r)
      | Value (Not l) -> P.not (helper l)
    in
    helper
end

let evalo bv_impl inhabito =
  let (module BV : Bv.S) = bv_impl in
  let rec evalo ph =
    conde
      [
        fresh (a b r) (ph === Ph.eq a b) (termo a r) (termo b r);
        fresh (a b a2 b2)
          (ph === Ph.lt a b)
          (termo a a2) (termo b b2) (BV.lto a2 b2);
        fresh (a b a2 b2)
          (ph === Ph.le a b)
          (termo a a2) (termo b b2) (BV.leo a2 b2);
        fresh (a b) (ph === Ph.conj a b) (inhabito termo a) (inhabito termo b);
        fresh (a b) (ph === Ph.disj a b) (inhabito termo a) (inhabito termo b);
        fresh a (ph === Ph.not a) (inhabito termo a);
      ]
  and termo t rez =
    conde
      [
        fresh (l r) (t === T.mul l r) (BV.multo l r rez);
        fresh (l r) (t === T.add l r) (BV.addo l r rez);
        fresh (l r) (t === T.sub l r) (BV.subo l r rez);
        fresh (l r) (t === T.lor_ l r) (BV.loro l r rez);
        fresh (l r) (t === T.land_ l r) (BV.lando l r rez);
        fresh (l r t2 l2 r2)
          (t === T.lshr l r)
          (termo t t2) (termo l l2) (termo r r2) (BV.lshiftro l r t2);
        fresh (l r t2 l2 r2) (t === T.lshl l r) (BV.lshiftl l r rez);
        fresh (l r) (t === T.var s) (BV.lshiftl l r rez);
      ]
  in
  evalo
