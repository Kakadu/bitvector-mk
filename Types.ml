open OCanren

let flip f a b = f b a

let failwiths ppf = Format.kasprintf failwith ppf

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
    let (module T), _ = Algebra.to_z3 ctx in

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
    let (module T), _ = Algebra.to_z3 ctx in
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

exception HasFreeVars of string Lazy.t

module T = struct
  type op = Shl | Lshr | Land | Lor | Mul | Add | Sub
  [@@deriving gt ~options:{ show; fmt; gmap; foldl }]

  type ('self, 'op, 'int, 'varname) t =
    | Const of 'int
    | Var of 'varname
    (* | Shl1 of 'self
       | Lshr1 of 'self *)
    | Binop of 'op * 'self * 'self
  [@@deriving gt ~options:{ show; fmt; gmap; foldl }]

  open OCanren

  module E = Fmap4 (struct
    type nonrec ('a, 'b, 'c, 'd) t = ('a, 'b, 'c, 'd) t

    let fmap eta = GT.gmap t eta
  end)

  type ground = (ground, op, N.ground, GT.string) t
  [@@deriving gt ~options:{ show; fmt; gmap }]

  type logic =
    (logic, op OCanren.logic, N.logic, GT.string OCanren.logic) t OCanren.logic
  [@@deriving gt ~options:{ show; fmt; gmap; foldl }]

  type nonrec injected = (ground, logic) injected

  let rec reify env x = E.reify reify OCanren.reify N.reify OCanren.reify env x

  let const (x : Bv.Repr.injected) : injected = inj @@ E.distrib @@ Const x

  let var s : injected = inj @@ E.distrib @@ Var s

  (* let shiftl1 a : injected = inj @@ E.distrib @@ Shl1 a

     let lshiftr1 a : injected = inj @@ E.distrib @@ Lshr1 a
  *)
  let land_ a b = inj @@ E.distrib @@ Binop (!!Land, a, b)

  let lor_ a b = inj @@ E.distrib @@ Binop (!!Lor, a, b)

  let mul a b = inj @@ E.distrib @@ Binop (!!Mul, a, b)

  let add a b = inj @@ E.distrib @@ Binop (!!Add, a, b)

  let sub a b = inj @@ E.distrib @@ Binop (!!Sub, a, b)

  let shl a b = inj @@ E.distrib @@ Binop (!!Shl, a, b)

  let lshr a b = inj @@ E.distrib @@ Binop (!!Lshr, a, b)

  let inj =
    let of_op = function
      | Add -> add
      | Sub -> sub
      | Mul -> mul
      | Land -> land_
      | Lor -> lor_
      | Shl -> shl
      | Lshr -> lshr
    in
    let rec helper = function
      | Const n -> const (Bv.Repr.inj n)
      | Var s -> var !!s
      | Binop (op, l, r) -> of_op op (helper l) (helper r)
      (* | Shl1 l -> shiftl1 (helper l)
         | Lshr1 l -> lshiftr1 (helper l) *)
    in
    helper

  let pp : Format.formatter -> ground -> unit =
    let pp_op ppf = function
      | Add -> Format.fprintf ppf "bvadd"
      | Sub -> Format.fprintf ppf "bvsub"
      | Mul -> Format.fprintf ppf "bvmul"
      | Land -> Format.fprintf ppf "bvand"
      | Lor -> Format.fprintf ppf "bvor"
      | Shl -> Format.fprintf ppf "bvshl"
      | Lshr -> Format.fprintf ppf "bvlshr"
    in
    let rec helper ppf = function
      | Const n -> Format.fprintf ppf "%s" (Bv.Repr.show_binary n)
      | Var s -> Format.pp_print_string ppf s
      | Binop (op, l, r) ->
          Format.fprintf ppf "(%a %a %a)" pp_op op helper l helper r
      (* | Shl (l, r) -> Format.fprintf ppf "(bvshl %a %a)" helper l helper r
         | Lshr (l, r) -> Format.fprintf ppf "(bvlshr %a %a)" helper l helper r *)
    in
    helper

  let ground =
    {
      ground with
      GT.plugins =
        object
          method show = GT.show ground

          method fmt = pp

          method gmap = GT.gmap ground
        end;
    }

  let to_smt ctx : ground -> _ =
    let (module T), (module P) = Algebra.to_z3 ctx in
    (* TODO: maybe returned T should already be enriched *)
    let module T = Algebra.EnrichTerm (T) in
    let on_op = function
      | Add -> T.add
      | Sub -> T.sub
      | Mul -> T.mul
      | Shl -> T.shl
      | Lshr -> T.lshr
      | Land -> T.land_
      | Lor -> T.lor_
    in

    let rec helper = function
      | Const n -> N.to_smt ctx n
      | Var s -> T.var s
      | Binop (op, l, r) -> on_op op (helper l) (helper r)
      (* | Shl (l, r) -> T.shl (helper l) (helper r)
         | Lshr (l, r) -> T.lshr (helper l) (helper r) *)
    in
    helper

  type ctx = CtxConj | CtxDisj | CtxAny

  let to_smt_logic_exn ctx : logic -> _ =
   fun root ->
    let (module T), _ = Algebra.to_z3 ctx in
    let module T = Algebra.EnrichTerm (T) in
    let on_op = function
      | Add -> T.add
      | Sub -> T.sub
      | Mul -> T.mul
      | Shl -> T.shl
      | Lshr -> T.lshr
      | Land -> T.land_
      | Lor -> T.lor_
    in
    let rec helper : logic -> _ = function
      | Value (Binop (Var _, _, _)) ->
          (* failwiths "logic inside %s %d: " __FILE__ __LINE__ *)
          raise (HasFreeVars (lazy ""))
      | Value (Var (OCanren.Var _)) ->
          (* failwiths "logic inside %s %d" __FILE__ __LINE__ *)
          raise (HasFreeVars (lazy ""))
      | Var _ ->
          (* failwiths "logic inside %s %d: `%s`" __FILE__ __LINE__
             (GT.show logic root); *)
          raise (HasFreeVars (lazy ""))
      | Value (Const n) -> N.to_smt_logic_exn ctx n
      | Value (Var (OCanren.Value s)) -> T.var s
      | Value (Binop (Value op, l, r)) -> on_op op (helper l) (helper r)
      (* | Value (Shl (l, r)) -> T.shl (helper l) (helper r)
         | Value (Lshr (l, r)) -> T.lshr (helper l) (helper r) *)
    in

    helper root
end

(*
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
        fresh (l r) (rez === T.shiftl1 l) (helper l) (helper r);
        fresh (l r) (rez === T.lshiftr1 l) (helper l) (helper r);
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
 *)

module Ph = struct
  type binop = Eq | Lt | Le
  [@@deriving gt ~options:{ show; fmt; gmap; foldl }]

  type ('self, 'selflist, 'binop, 'term) t =
    | True
    | Conj of 'selflist
    | Disj of 'selflist
    | Not of 'self
    | Op of 'binop * 'term * 'term
  [@@deriving gt ~options:{ show; fmt; gmap; foldl }]

  open OCanren

  module E = Fmap4 (struct
    type nonrec ('a, 'b, 'c, 'd) t = ('a, 'b, 'c, 'd) t

    let fmap eta = GT.gmap t eta
  end)

  type ground = (ground, ground Std.List.ground, binop, T.ground) t
  [@@deriving gt ~options:{ show; fmt; gmap }]

  type logic =
    (logic, logic Std.List.logic, binop OCanren.logic, T.logic) t OCanren.logic
  [@@deriving gt ~options:{ show; fmt; gmap; foldl }]

  type nonrec injected = (ground, logic) injected

  let rec reify env =
    E.reify reify (Std.List.reify reify) OCanren.reify T.reify env

  let true_ : injected = inj @@ E.distrib True

  let eq a b = inj @@ E.distrib @@ Op (!!Eq, a, b)

  let lt a b = inj @@ E.distrib @@ Op (!!Lt, a, b)

  let le a b = inj @@ E.distrib @@ Op (!!Le, a, b)

  let conj2 a (b : injected) = inj @@ E.distrib @@ Conj Std.(a % (b % nil ()))

  let conj_list xs : injected = inj @@ E.distrib @@ Conj (Std.list Fun.id xs)

  let conj xs = inj @@ E.distrib @@ Conj xs

  let disj2 a (b : injected) = inj @@ E.distrib @@ Disj Std.(a % (b % nil ()))

  let disj a b = inj @@ E.distrib @@ Disj Std.(a % (b % nil ()))

  let disj_list xs : injected = inj @@ E.distrib @@ Disj (Std.list Fun.id xs)

  let not a = inj @@ E.distrib @@ Not a

  let pp_ground : Format.formatter -> ground -> unit =
    let pp_binop ppf = function
      | Eq -> Format.fprintf ppf "="
      | Lt -> Format.fprintf ppf "<"
      | Le -> Format.fprintf ppf "<="
    in
    let rec helper ppf : ground -> _ = function
      | True -> Format.fprintf ppf "(= #x1 #x1)"
      | Op (op, l, r) ->
          Format.fprintf ppf "(%a %a %a)" pp_binop op (GT.fmt T.ground) l
            (GT.fmt T.ground) r
      | Conj xs ->
          Format.fprintf ppf "(and";
          GT.foldl Std.List.ground
            (fun () x -> Format.fprintf ppf " %a" helper x)
            () xs;
          Format.fprintf ppf ") "
      | Disj xs ->
          Format.fprintf ppf "(or";
          GT.foldl Std.List.ground
            (fun () x -> Format.fprintf ppf " %a" helper x)
            () xs;
          Format.fprintf ppf ") "
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
    let _, (module P) = Algebra.to_z3 ctx in

    let rec helper = function
      | True -> P.true_
      | Op (Eq, l, r) -> P.eq (term l) (term r)
      | Op (Le, l, r) -> P.le (term l) (term r)
      | Op (Lt, l, r) -> P.lt (term l) (term r)
      | Conj (l, r) -> P.conj (helper l) (helper r)
      | Disj (l, r) -> P.disj (helper l) (helper r)
      | Not l -> P.not (helper l)
    in
    helper gr

  let to_smt_logic_exn ctx : logic -> Z3.Expr.expr =
    let term = T.to_smt_logic_exn ctx in
    let _, (module P) = Algebra.to_z3 ctx in

    let rec helper : logic -> _ = function
      | Value (Op (Var _, _, _)) | Var _ -> raise (HasFreeVars (lazy ""))
      | Value True -> P.true_
      | Value (Op (Value Eq, l, r)) -> P.eq (term l) (term r)
      | Value (Op (Value Le, l, r)) -> P.le (term l) (term r)
      | Value (Op (Value Lt, l, r)) -> P.lt (term l) (term r)
      | Value (Conj xs) -> helper_list P.conj ~on_empty:(P.not P.true_) xs
      | Value (Disj xs) -> helper_list P.disj ~on_empty:P.true_ xs
      | Value (Not l) -> P.not (helper l)
    and helper_list ~on_empty op = function
      | Var _ -> raise (HasFreeVars (lazy ""))
      | Value (Std.List.Cons (e, tl)) ->
          op (helper e) (helper_list ~on_empty op tl)
      | Value Std.List.Nil -> on_empty
    in
    helper
end

(* TODO: Here environment containts terms but in practice it's likely that we will need only constants *)
module Env = struct
  type ground = (string * T.ground) Std.List.ground

  type logic = (string OCanren.logic * T.logic) OCanren.logic Std.List.logic

  type injected = (ground, logic) OCanren.injected

  let reify env : injected -> logic =
    Std.List.reify (Std.Pair.reify OCanren.reify T.reify) env

  let empty : injected = Std.nil ()

  let cons name t : injected -> injected = Std.List.cons (Std.Pair.pair name t)

  let conso name t (tail : injected) (env : injected) = env === cons name t tail

  let rec lookupo name (env : injected) rez =
    conde
      [
        fresh (k1 v1 e1) (conso k1 v1 e1 env)
          (conde
             [
               k1 === name &&& (rez === v1); k1 =/= name &&& lookupo name e1 rez;
             ]);
        env === empty &&& failure;
      ]

  let inject : ground -> injected =
    let rec helper = function
      | Std.List.Nil -> Std.nil ()
      | Cons ((s, t), tl) -> cons !!s (T.inj t) (helper tl)
    in
    helper

  let pp ppf (xs : ground) =
    Format.fprintf ppf "[ ";
    (* let (_ : int) = GT.foldl Std.List.ground in *)
    GT.foldl Std.List.ground
      (fun () (name, t) -> Format.fprintf ppf "%s -> %a; " name T.pp t)
      () xs;
    Format.fprintf ppf "]"

  let show = Format.asprintf "%a" pp
end

(* ********************************************************************* *)

let mk_of_term (module BV : Bv.S) =
  let module Ans = struct
    type t = T.injected

    type rez = t

    let finish = Fun.id

    let var s : t = T.var !!s

    let const n = T.const (BV.build_num n)

    let const_s s : t = T.const (BV.build_num @@ int_of_string s)

    let land_ = T.land_

    let lor_ = T.lor_

    let shl = T.shl

    let lshr = T.lshr

    let add = T.add

    let sub = T.sub

    let mul = T.mul
  end in
  (module Ans : Algebra.TERM with type t = T.injected)

let mk_of_formula =
  let module P = struct
    open Z3

    type rez = Ph.injected

    type t = Conjs of rez list | Disjs of rez list | Final of rez

    let finish = function
      | Final x -> x
      | Disjs xs -> Ph.disj_list xs
      | Conjs xs -> Ph.conj_list xs

    type term = T.injected

    let true_ = Final Ph.true_

    let iff a b = failwiths "not implemented %s %d" __FILE__ __LINE__

    let not f = Final (Ph.not (finish f))

    let conj x y =
      match (x, y) with
      | Conjs xs, Conjs ys -> Conjs (List.append xs ys)
      | Final x, Conjs xs | Conjs xs, Final x -> Conjs (x :: xs)
      | _, _ -> Final (Ph.conj2 (finish x) (finish y))

    let disj x y =
      match (x, y) with
      | Disjs xs, Disjs ys -> Disjs (List.append xs ys)
      | Final x, Disjs xs | Disjs xs, Final x -> Disjs (x :: xs)
      | _, _ -> Final (Ph.disj2 (finish x) (finish y))

    let eq x y = Final (Ph.eq x y)

    let le x y = Final (Ph.le x y)

    let lt x y = Final (Ph.lt x y)

    let forall name f =
      Format.eprintf "forall is not supported\n%s %d" __FILE__ __LINE__;
      f

    let exists name f =
      Format.eprintf "exists is not supported\n%s %d" __FILE__ __LINE__;
      f
  end in
  (module P : Algebra.FORMULA
    with type rez = Ph.injected
     and type term = T.injected)

let to_mk :
    (module Bv.S) ->
    (module Algebra.TERM with type t = T.injected)
    * (module Algebra.FORMULA
         with type rez = Ph.injected
          and type term = T.injected) =
 fun ctx -> (mk_of_term ctx, mk_of_formula)
