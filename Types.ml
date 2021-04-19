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

module T = struct
  type ('self, 'int, 'varname) t =
    | Const of 'int
    | Var of 'varname
    | Shl1 of 'self
    | Lshr1 of 'self
    | Land of 'self * 'self
    | Lor of 'self * 'self
    | Mul of 'self * 'self
    | Add of 'self * 'self
    | Sub of 'self * 'self
  [@@deriving gt ~options:{ show; fmt; gmap; foldl }]

  open OCanren

  module E = Fmap3 (struct
    type nonrec ('a, 'b, 'c) t = ('a, 'b, 'c) t

    let fmap eta = GT.gmap t eta
  end)

  type ground = (ground, N.ground, GT.string) t
  [@@deriving gt ~options:{ show; fmt; gmap }]

  type logic = (logic, N.logic, GT.string OCanren.logic) t OCanren.logic
  [@@deriving gt ~options:{ show; fmt; gmap; foldl }]

  type nonrec injected = (ground, logic) injected

  let rec reify env x = E.reify reify N.reify OCanren.reify env x

  let const (x : Bv.Repr.injected) : injected = inj @@ E.distrib @@ Const x

  let var s : injected = inj @@ E.distrib @@ Var s

  let shiftl1 a : injected = inj @@ E.distrib @@ Shl1 a

  let lshiftr1 a : injected = inj @@ E.distrib @@ Lshr1 a

  let land_ a b = inj @@ E.distrib @@ Land (a, b)

  let lor_ a b = inj @@ E.distrib @@ Lor (a, b)

  let mul a b = inj @@ E.distrib @@ Mul (a, b)

  let add a b = inj @@ E.distrib @@ Add (a, b)

  let sub a b = inj @@ E.distrib @@ Sub (a, b)

  let inj =
    let rec helper = function
      | Const n -> const (Bv.Repr.inj n)
      | Var s -> var !!s
      | Add (l, r) -> add (helper l) (helper r)
      | Sub (l, r) -> sub (helper l) (helper r)
      | Mul (l, r) -> mul (helper l) (helper r)
      | Land (l, r) -> land_ (helper l) (helper r)
      | Lor (l, r) -> lor_ (helper l) (helper r)
      | Shl1 l -> shiftl1 (helper l)
      | Lshr1 l -> lshiftr1 (helper l)
    in
    helper

  let pp : Format.formatter -> ground -> unit =
    let rec helper ppf = function
      | Const n -> Format.fprintf ppf "%s" (Bv.Repr.show_binary n)
      | Var s -> Format.pp_print_string ppf s
      | Add (l, r) -> Format.fprintf ppf "(bvadd %a %a)" helper l helper r
      | Sub (l, r) -> Format.fprintf ppf "(bvsub %a %a)" helper l helper r
      | Mul (l, r) -> Format.fprintf ppf "(bvmul %a %a)" helper l helper r
      | Land (l, r) -> Format.fprintf ppf "(bvand %a %a)" helper l helper r
      | Lor (l, r) -> Format.fprintf ppf "(bvor %a %a)" helper l helper r
      | Shl1 l -> Format.fprintf ppf "(bvshl %a 1)" helper l
      | Lshr1 l -> Format.fprintf ppf "(bvlshr %a 1)" helper l
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
    let rec helper = function
      | Const n -> N.to_smt ctx n
      | Var s -> T.var s
      | Add (l, r) -> T.add (helper l) (helper r)
      | Sub (l, r) -> T.sub (helper l) (helper r)
      | Mul (l, r) -> T.mul (helper l) (helper r)
      | Shl1 l -> T.shl1 (helper l)
      | Lshr1 l -> T.lshr1 (helper l)
      (* | Shl (l, r) -> T.shl (helper l) (helper r)
         | Lshr (l, r) -> T.lshr (helper l) (helper r) *)
      | Land (l, r) -> T.land_ (helper l) (helper r)
      | Lor (l, r) -> T.lor_ (helper l) (helper r)
    in
    helper

  let to_smt_logic_exn ctx : logic -> _ =
    let (module T), _ = Algebra.to_z3 ctx in
    let module T = Algebra.EnrichTerm (T) in
    let rec helper : logic -> _ = function
      | Value (Var (OCanren.Var _)) | Var _ -> failwith "logic inside"
      | Value (Const n) -> N.to_smt_logic_exn ctx n
      | Value (Var (OCanren.Value s)) -> T.var s
      | Value (Add (l, r)) -> T.add (helper l) (helper r)
      | Value (Sub (l, r)) -> T.sub (helper l) (helper r)
      | Value (Mul (l, r)) -> T.mul (helper l) (helper r)
      | Value (Shl1 l) -> T.shl1 (helper l)
      | Value (Lshr1 l) -> T.lshr1 (helper l)
      (* | Value (Shl (l, r)) -> T.shl (helper l) (helper r)
         | Value (Lshr (l, r)) -> T.lshr (helper l) (helper r) *)
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

module Ph = struct
  type ('self, 'term) t =
    | Conj of 'self * 'self
    | Disj of 'self * 'self
    | Not of 'self
    | Eq of 'term * 'term
    | Lt of 'term * 'term
    | Le of 'term * 'term
  [@@deriving gt ~options:{ show; fmt; gmap; foldl }]

  open OCanren

  module E = Fmap2 (struct
    type nonrec ('a, 'b) t = ('a, 'b) t

    let fmap eta = GT.gmap t eta
  end)

  type ground = (ground, T.ground) t
  [@@deriving gt ~options:{ show; fmt; gmap }]

  type logic = (logic, T.logic) t OCanren.logic
  [@@deriving gt ~options:{ show; fmt; gmap; foldl }]

  type nonrec injected = (ground, logic) injected

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
    let _, (module P) = Algebra.to_z3 ctx in

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
    let _, (module P) = Algebra.to_z3 ctx in

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

(* TODO: Here environment containts terms but in practice it's likely that we will need only constants *)
module Env = struct
  type ground = (string * T.ground) Std.List.ground

  type logic = (string OCanren.logic * T.logic) OCanren.logic Std.List.logic

  type injected = (ground, logic) OCanren.injected

  let reify env : injected -> logic =
    Std.List.reify (Std.Pair.reify OCanren.reify T.reify) env

  let empty : injected = Std.nil ()

  let cons name t tail = Std.List.cons (Std.Pair.pair name t) tail

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
(*
let z3_of_term (module BV : Bv.S) ctx :
    (module Algebra.TERM with type t = T.injected) =
  let module Ans = struct
    type t = T.injected

    let var s = T.var !!s

    let const n = T.const (BV.build_num n)

    let const_s s : t = T.const (BV.build_num @@ int_of_string s)

    let land_ = T.land_

    let lor_ = T.lor_

    let shl = T.shiftl1

    let lshr = T.lshiftr1

    let add = T.add

    let sub = T.sub

    let mul = T.mul
  end in
  (module Ans : Algebra.TERM with type t = T.injected)

let z3_of_formula ctx :
    (module FORMULA with type t = z3_expr and type term = z3_expr) =
  let module P = struct
    open Z3

    type t = z3_expr

    type term = z3_expr

    let iff a b = Boolean.mk_iff ctx a b

    let not = Boolean.mk_not ctx

    let conj a b = Boolean.mk_and ctx [ a; b ]

    let disj a b = Boolean.mk_or ctx [ a; b ]

    let eq = Boolean.mk_eq ctx

    let le = BitVector.mk_ule ctx

    let lt = BitVector.mk_ult ctx

    let forall name f =
      let x = BitVector.mk_const ctx (Symbol.mk_string ctx name) bv_size in
      Quantifier.expr_of_quantifier
        (Quantifier.mk_forall_const ctx [ x ] f None [] [] None None)

    let exists name f =
      let x = BitVector.mk_const ctx (Symbol.mk_string ctx name) bv_size in
      Quantifier.expr_of_quantifier
        (Quantifier.mk_exists_const ctx [ x ] f None [] [] None None)
  end in
  (module P : FORMULA with type t = z3_expr and type term = z3_expr)

let to_mk :
    Z3.context ->
    (module TERM with type t = z3_expr)
    * (module FORMULA with type t = z3_expr and type term = z3_expr) =
 fun ctx -> (z3_of_term ctx, z3_of_formula ctx)
*)
