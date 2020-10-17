module N = struct
  type ground = GT.bool OCanren.Std.List.ground
  [@@deriving gt ~options:{ show; fmt; gmap }]

  type nonrec logic = GT.bool OCanren.logic OCanren.Std.List.logic
  [@@deriving gt ~options:{ show; fmt; gmap }]

  type nonrec injected = (ground, logic) OCanren.injected

  let reify env x = OCanren.Std.List.reify OCanren.reify env x

  let one : injected =
    let open OCanren in
    Std.(!<(!!true))

  let zero : injected =
    let open OCanren in
    Std.(!<(!!false))
end

module T = struct
  type ('self, 'int) t =
    | Const of 'int
    | Mul of 'self * 'self
    | Add of 'self * 'self
  [@@deriving gt ~options:{ show; fmt; gmap }]

  open OCanren

  module E = Fmap2 (struct
    type nonrec ('a, 'b) t = ('a, 'b) t

    let fmap eta = GT.gmap t eta
  end)

  type ground = (ground, N.ground) t
  [@@deriving gt ~options:{ show; fmt; gmap }]

  type logic = (logic, N.logic) t OCanren.logic
  [@@deriving gt ~options:{ show; fmt; gmap }]

  type nonrec injected = (ground, logic) injected

  let rec reify env x = E.reify reify N.reify env x

  let const (x : N.injected) : injected = inj @@ E.distrib @@ Const x

  let mul a b = inj @@ E.distrib @@ Mul (a, b)

  let add a b = inj @@ E.distrib @@ Add (a, b)

  let pp_ground : Format.formatter -> ground -> unit =
    let rec helper ppf = function
      | Const n -> GT.fmt N.ground ppf n
      | Add (l, r) -> Format.fprintf ppf "(bvadd %a %a)" helper l helper r
      | Mul (l, r) -> Format.fprintf ppf "(bvmul %a %a)" helper l helper r
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
end

let rec inhabito_term r =
  let open OCanren in
  conde
    [
      fresh x (r === T.const x) (inhabito_const x);
      fresh (l r) (r === T.mul l r) (inhabito_term l) (inhabito_term r);
      fresh (l r) (r === T.add l r) (inhabito_term l) (inhabito_term r);
    ]

and inhabito_const r =
  let open OCanren in
  conde [ r === N.one; r === N.zero ]

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
end

open OCanren

let rec inhabito r =
  conde
    [
      fresh (a b) (r === Ph.eq a b) (inhabito_term a) (inhabito_term b);
      fresh (a b) (r === Ph.lt a b) (inhabito_term a) (inhabito_term b);
      fresh (a b) (r === Ph.le a b) (inhabito_term a) (inhabito_term b);
      fresh (a b) (r === Ph.conj a b) (inhabito a) (inhabito b);
      fresh (a b) (r === Ph.disj a b) (inhabito a) (inhabito b);
      fresh a (r === Ph.not a) (inhabito a);
    ]

let () =
  let on_ground x = Format.asprintf "%a" (GT.fmt Ph.ground) x in
  let on_logic x = GT.show Ph.logic x in
  let open OCanren in
  let open Tester in
  (* runR Ph.reify on_ground on_logic 20 q qh ("", fun q -> inhabito q) *)
  run_exn on_ground 20 q qh ("", fun q -> inhabito q)
