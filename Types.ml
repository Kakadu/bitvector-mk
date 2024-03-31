module OCanren = struct
  include OCanren

  let logic =
    {
      logic with
      GT.plugins =
        object
          method show = GT.show OCanren.logic
          method fmt = GT.fmt OCanren.logic
          method gmap = GT.gmap OCanren.logic
          method foldl = GT.foldl OCanren.logic

          method compare f a b =
            match (a, b) with
            | Value ax, Value bx -> f ax bx
            | Value _, Var _ -> GT.LT
            | Var _, Value _ -> GT.GT
            | Var (l, _), Var (r, _) -> GT.compare GT.int l r
        end;
    }
end

open OCanren

exception HasFreeVars of string

let has_free_vars fmt = Format.kasprintf (fun s -> raise (HasFreeVars s)) fmt

let forget_var : 'a. ('a -> 'b) -> 'a OCanren.logic -> 'b =
 fun fa x ->
  GT.transform OCanren.logic
    (fun fself ->
      object
        inherit [_, _, _, _, _, _] OCanren.logic_t
        method c_Var () _ _ = has_free_vars ""
        method c_Value () _ v = fa v
      end)
    () x

let rec forget_list :
    ('a -> 'b) -> 'a OCanren.Std.List.logic -> 'b OCanren.Std.List.ground =
 fun fa xs ->
  forget_var
    (GT.transform OCanren.Std.List.t
       (fun fself ->
         object
           inherit [_, 'a, 'b, _, _, _, _, _, _] OCanren.Std.List.t_t
           method c_Nil () _ = []

           method c_Cons () _ h tl : _ OCanren.Std.List.ground =
             fa h :: forget_list fa tl
         end)
       ())
    xs

let flip f a b = f b a

let failwiths ?(here = Lexing.dummy_pos) ppf =
  let { Lexing.pos_fname; pos_lnum } = here in
  Format.kasprintf
    (fun s -> failwith @@ Format.asprintf "%s %d:  %s" pos_fname pos_lnum s)
    ppf

module N = struct
  type ground = Bv.Repr.g
  type nonrec logic = Bv.Repr.l
  type nonrec injected = Bv.Repr.injected

  let ground = Bv.Repr.g
  let logic = Bv.Repr.l
  let reify = Bv.Repr.reify
  let prj_exn = Bv.Repr.prj_exn
  let ground_of_logic : logic -> ground = forget_list (forget_var Fun.id)

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
          method compare = ground.GT.plugins#compare
          method foldl = ground.GT.plugins#foldl
          method fmt ppf n = Format.pp_print_int ppf (int_of_ground n)
        end;
    }

  let to_smt bv_size ctx xs : Z3.Expr.expr =
    let (module T), _ = Algebra.to_z3 bv_size ctx in

    (* let b = Buffer.create 20 in *)
    (* Buffer.add_string b "#x";
       let () =
         List.fold_right
           (fun n () -> Buffer.add_char b (if n then '1' else '0'))
           xs ()
       in
       T.const_s (Buffer.contents b) *)
    T.const_s @@ string_of_int @@ int_of_ground xs

  let to_smt_logic_exn bv_size ctx (xs : Bv.Repr.l) : Z3.Expr.expr =
    let (module T), _ = Algebra.to_z3 bv_size ctx in
    let acc = ref 0 in
    let module L = OCanren.Std.List in
    let rec iter base = function
      | OCanren.Value (L.Cons (OCanren.Var _, _))
      | Value (L.Cons (_, OCanren.Var _))
      | Var _ ->
          assert false
      | Value (L.Cons (Value n, tl)) ->
          acc := !acc + if n = 1 then base else 0;
          iter (base * 2) tl
      | Value L.Nil -> ()
    in
    iter 1 xs;
    T.const_s (string_of_int !acc)
end

module Op = struct
  [%%ocanren_inject
  type op = Shl | Lshr | Land | Lor | Mul | Add | Sub
  [@@deriving gt ~options:{ show; fmt; gmap; foldl; compare }]]
end

module T = struct
  [%%ocanren_inject
  type nonrec ('self, 'op, 'int, 'varname) t =
    | Const of 'int
    | SubjVar of 'varname
    (* | Shl1 of 'self
       | Lshr1 of 'self *)
    | Binop of 'op * 'self * 'self
  [@@deriving gt ~options:{ show; fmt; gmap; foldl; compare }]

  type ground = (ground, Op.ground, N.ground, GT.string) t]

  module PPNew = struct
    let hack fa ppf = function
      | OCanren.Value a -> fa ppf a
      | Var (n, []) -> Format.fprintf ppf "_.%d" n
      | Var (n, _) -> Format.fprintf ppf "_.%d {|constraints |}" n

    let pp_algebra pp_self pp_op pp_bv pp_name =
      GT.transform t (fun fself ->
          object
            inherit [_, _, _, _, _] fmt_t_t pp_self pp_op pp_bv pp_name fself
            method! c_Const ppf _ n = pp_bv ppf n
            method! c_SubjVar ppf _ v = pp_name ppf v

            method! c_Binop ppf _ op l r =
              Format.fprintf ppf "(%a %a %a)" pp_op op pp_self l pp_self r
          end)

    let my_pp_op ppf = function
      | Op.Add -> Format.fprintf ppf "bvadd"
      | Sub -> Format.fprintf ppf "bvsub"
      | Mul -> Format.fprintf ppf "bvmul"
      | Land -> Format.fprintf ppf "bvand"
      | Lor -> Format.fprintf ppf "bvor"
      | Shl -> Format.fprintf ppf "bvshl"
      | Lshr -> Format.fprintf ppf "bvlshr"

    let my_pp_name ppf = Format.fprintf ppf "%s"

    let rec my_ground_pp ppf : ground -> unit =
      pp_algebra my_ground_pp my_pp_op
        (fun ppf s -> Format.fprintf ppf "%s" (Bv.Repr.show s))
        my_pp_name ppf

    let rec my_logic_pp ppf : logic -> unit =
      hack
        (pp_algebra my_logic_pp (hack my_pp_op) Bv.Repr.pp_logic
           (hack my_pp_name))
        ppf
  end

  let pp : Format.formatter -> ground -> unit =
    let pp_op = PPNew.my_pp_op in
    let rec helper ppf = function
      | Const n -> Format.fprintf ppf "%a" Bv.Repr.pp n
      | SubjVar s -> Format.pp_print_string ppf s
      | Binop (op, l, r) ->
          Format.fprintf ppf "(%a %a %a)" pp_op op helper l helper r
      (* | Shl (l, r) -> Format.fprintf ppf "(bvshl %a %a)" helper l helper r
         | Lshr (l, r) -> Format.fprintf ppf "(bvlshr %a %a)" helper l helper r *)
    in
    helper

  let lt_logic : logic -> logic -> bool =
   fun a b -> GT.compare logic a b = GT.LT

  (* let rec helper : logic * logic -> bool = function
       | _, Var _ -> false (* var is smallest *)
       | Var _, Value (Const _) -> true
       | _, Value (Const _) -> false
       | Value (Const _), Value (Binop (_, _, _)) -> false
       | Value (Binop (o[]))
     in

     helper (a, b) *)
  (* let rec reify env x = E.reify reify OCanren.reify N.reify OCanren.reify env x *)
  let const (x : Bv.Repr.injected) : injected = inj @@ Const x
  let var s : injected = inj @@ SubjVar s

  (* let shiftl1 a : injected = inj @@ Shl1 a

     let lshiftr1 a : injected = inj @@ Lshr1 a
  *)
  let land_ a b = inj @@ Binop (!!Op.Land, a, b)
  let lor_ a b = inj @@ Binop (!!Op.Lor, a, b)
  let mul a b = inj @@ Binop (!!Op.Mul, a, b)
  let add a b = inj @@ Binop (!!Op.Add, a, b)
  let sub a b = inj @@ Binop (!!Op.Sub, a, b)
  let shl a b = inj @@ Binop (!!Op.Shl, a, b)
  let lshr a b = inj @@ Binop (!!Op.Lshr, a, b)
  let op o a b = inj @@ Binop (o, a, b)

  let inj : ground -> injected =
    let of_op = function
      | Op.Add -> add
      | Sub -> sub
      | Mul -> mul
      | Land -> land_
      | Lor -> lor_
      | Shl -> shl
      | Lshr -> lshr
    in
    let rec helper = function
      | Const n -> const (Bv.Repr.inj n)
      | SubjVar s -> var !!s
      | Binop (op, l, r) -> of_op op (helper l) (helper r)
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
          method compare = GT.compare ground
          method foldl = GT.foldl ground
        end;
    }

  let ground_of_logic_exn : logic -> ground =
    let helper =
      forget_var
        (GT.transform t
           (fun fself ->
             object
               inherit
                 [ unit,
                   logic,
                   ground,
                   _,
                   Op.t OCanren.logic,
                   Op.t,
                   _,
                   N.logic,
                   N.ground,
                   _,
                   GT.string OCanren.logic,
                   GT.string,
                   _,
                   (_, _, _, _) t,
                   ground ]
                 t_t

               method c_Const () _ (n : N.logic) = Const (N.ground_of_logic n)
               method c_SubjVar () _ v = SubjVar (forget_var Fun.id v)

               method c_Binop () _
                   : Op.t OCanren.logic -> logic -> logic -> ground =
                 fun op l r ->
                   Binop
                     ( (forget_var Fun.id op : Op.t),
                       forget_var (fself ()) l,
                       forget_var (fself ()) r )
             end)
           ())
    in

    helper

  let to_smt bv_size ctx : ground -> _ =
    let (module T), (module P) = Algebra.to_z3 bv_size ctx in
    (* TODO: maybe returned T should already be enriched *)
    let module T = Algebra.EnrichTerm (T) in
    let on_op = function
      | Op.Add -> T.add
      | Sub -> T.sub
      | Mul -> T.mul
      | Shl -> T.shl
      | Lshr -> T.lshr
      | Land -> T.land_
      | Lor -> T.lor_
    in

    let rec helper = function
      | Const n -> N.to_smt bv_size ctx n
      | SubjVar s -> T.var s
      | Binop (op, l, r) -> on_op op (helper l) (helper r)
    in
    helper

  type ctx = CtxConj | CtxDisj | CtxAny

  let to_smt_logic_exn bv_size ctx : logic -> _ =
   fun root ->
    let (module T), _ = Algebra.to_z3 bv_size ctx in
    let module T = Algebra.EnrichTerm (T) in
    let on_op = function
      | Op.Add -> T.add
      | Sub -> T.sub
      | Mul -> T.mul
      | Shl -> T.shl
      | Lshr -> T.lshr
      | Land -> T.land_
      | Lor -> T.lor_
    in
    let rec helper : logic -> _ = function
      | Value (Binop (Var _, _, _)) ->
          failwiths ~here:[%here] "logic inside %s %d (`%s`): " __FILE__
            __LINE__ (GT.show logic root)
      | Value (SubjVar (OCanren.Var _)) ->
          has_free_vars "logic inside %s %d" __FILE__ __LINE__
      | Var _ ->
          Format.printf "FIXME: inserting 'a' during SMT encoding...\n";
          T.var "a"
      | Value (Const n) -> N.to_smt_logic_exn bv_size ctx n
      | Value (SubjVar (OCanren.Value s)) -> T.var s
      | Value (Binop (Value op, l, r)) -> on_op op (helper l) (helper r)
    in

    helper root

  let ( <= ) a b =
    OCanren.structural (Std.Pair.pair a b) (Std.Pair.reify reify reify)
      (function
      | Var _ -> assert false
      | Value (a, b) -> (
          match GT.compare logic a b with
          | LT -> true
          | EQ -> false
          | GT -> false))

  let check_run_once goal =
    let stream = OCanren.(run q) goal (fun ss -> ss#reify OCanren.reify) in
    let len = List.length (Stream.take stream) in
    (* Format.printf "stream.length = %d\n%!" len; *)
    1 = len

  let%test _ =
    let (module BV) = Bv.create 4 in
    let a = shl (var !!"b") (const @@ BV.build_num 1) in
    let b = shl (var !!"b") (const @@ BV.build_num 2) in
    let c = shl (var !!"b") (const @@ BV.build_num 3) in

    check_run_once (fun v ->
        fresh () (v === !!"success") (a <= b) (b <= c) (a <= c))

  let%test _ =
    let (module BV) = Bv.create 4 in
    let vx = var !!"x" in
    let vy = var !!"y" in
    let c = const @@ BV.build_num 3 in
    let ab = add vx vy in

    check_run_once (fun v ->
        fresh () (v === !!"success") (vx <= vy)
          (* const is less then variable *)
          (c <= vx)
          (vx <= ab)
          (c <= shl vx c)
        (* (my_structural (Std.Pair.pair a c)) *))
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

module Binop = struct
  [%%ocanren_inject
  type nonrec t = Eq | Lt | Le
  [@@deriving gt ~options:{ show; fmt; gmap; foldl; compare }]

  type ground = t]
end

module Ph = struct
  [%%ocanren_inject
  type nonrec ('self, 'selflist, 'binop, 'term) t =
    | True
    | Conj of 'selflist
    | Disj of 'selflist
    | Not of 'self
    | Op of 'binop * 'term * 'term
  [@@deriving gt ~options:{ show; fmt; gmap; foldl; compare }]

  type ground =
    (ground, ground OCanren.Std.List.ground, Binop.ground, T.ground) t]

  let true_ : injected = inj True
  let eq a b = inj @@ Op (!!Binop.Eq, a, b)
  let lt a b = inj @@ Op (!!Binop.Lt, a, b)
  let le a b = inj @@ Op (!!Binop.Le, a, b)
  let op o a b = inj @@ Op (o, a, b)
  let conj2 a (b : injected) = inj @@ Conj Std.(a % (b % nil ()))
  let conj_list xs : injected = inj @@ Conj (Std.list Fun.id xs)
  let conj xs = inj @@ Conj xs
  let disj2 a (b : injected) = inj @@ Disj Std.(a % (b % nil ()))
  let disj xs = inj @@ Disj xs
  let disj_list xs : injected = inj @@ Disj (Std.list Fun.id xs)
  let not a = inj @@ Not a

  module PPNew = struct
    let pp_algebra pp_self pp_list pp_binop pp_term =
      GT.transform t (fun _ ->
          object
            inherit
              [_, _, _, _, _] fmt_t_t
                pp_self pp_list pp_binop pp_term
                (fun _ _ -> failwith "should not be called")

            method! c_Not ppf _ f = Format.fprintf ppf "(not %a)" pp_self f
            method! c_True ppf _ = Format.fprintf ppf "T"
            method! c_Conj ppf _ xs = Format.fprintf ppf "(and %a)" pp_list xs
            method! c_Disj ppf _ xs = Format.fprintf ppf "(or %a)" pp_list xs

            method! c_Op ppf _ op l r =
              Format.fprintf ppf "(%a %a %a)" pp_binop op pp_term l pp_term r
          end)

    let my_pp_list fa ppf lst =
      let is_ground_style =
        let rec onlogic () =
          GT.transform OCanren.logic
            (fun _ ->
              object
                inherit [_, _, _, _, _, _] OCanren.logic_t
                method c_Var _ _ _ _ = false
                method c_Value _ _ tl = on_slice () tl
              end)
            ()
        and on_slice () =
          GT.transform OCanren.Std.List.t
            (fun fself ->
              object
                inherit [_, _, _, _, _, _, _, _, _] OCanren.Std.List.t_t
                method c_Nil () _ = true
                method c_Cons () _ _h tl = onlogic () tl
                (* match tl with Var _ -> false | Value xs -> fself () xs *)
              end)
            ()
        in
        onlogic () lst
      in
      let rec pp_style_ground ppf xs =
        T.PPNew.hack
          (GT.transform OCanren.Std.List.t (fun fself ->
               object
                 inherit [_, _, _, _, _, _, _, _, _] OCanren.Std.List.t_t
                 method c_Nil ppf _ = Format.fprintf ppf "nil"

                 method c_Cons ppf _ h tl =
                   Format.fprintf ppf "%a %a" fa h pp_style_ground tl
               end))
          ppf xs
      in
      let rec pp_style_logic ppf xs =
        T.PPNew.hack
          (GT.transform OCanren.Std.List.t (fun fself ->
               object
                 inherit [_, _, _, _, _, _, _, _, _] OCanren.Std.List.t_t
                 method c_Nil _ _ = ()

                 method c_Cons ppf _ h tl =
                   Format.fprintf ppf "%a :: %a" fa h pp_style_logic tl
               end))
          ppf xs
      in
      (if is_ground_style then pp_style_ground else pp_style_logic) ppf lst

    let my_pp_binop ppf = function
      | Binop.Eq -> Format.fprintf ppf "="
      | Lt -> Format.fprintf ppf "<"
      | Le -> Format.fprintf ppf "<="

    let rec my_ground_pp ppf : ground -> unit =
      pp_algebra my_ground_pp
        (GT.fmt OCanren.Std.List.ground my_ground_pp)
        my_pp_binop T.PPNew.my_ground_pp ppf

    let rec my_logic_pp ppf : logic -> unit =
      T.PPNew.hack
        (pp_algebra my_logic_pp
           (my_pp_list @@ my_logic_pp)
           (T.PPNew.hack my_pp_binop) T.PPNew.my_logic_pp)
        ppf
  end

  let pp_ground : Format.formatter -> ground -> unit =
    let pp_binop = PPNew.my_pp_binop in
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

  let ground_of_logic_exn : logic -> ground =
    let helper =
      forget_var
        (GT.transform t
           (fun fself ->
             let (_ : logic Std.List.logic -> ground Std.List.ground) =
               forget_list (forget_var @@ fself ())
             in
             object
               inherit
                 [ unit,
                   logic,
                   ground,
                   _,
                   logic OCanren.Std.List.logic,
                   ground OCanren.Std.List.ground,
                   _,
                   Binop.logic,
                   Binop.ground,
                   _,
                   T.logic,
                   T.ground,
                   _,
                   (_, _, _, _) t,
                   ground ]
                 t_t

               method c_True () _ = True
               method c_Not _ _ f : ground = Not (forget_var (fself ()) f)

               method c_Op () _ op l r =
                 Op
                   ( forget_var Fun.id op,
                     T.ground_of_logic_exn l,
                     T.ground_of_logic_exn r )

               method c_Disj () _ xs =
                 Disj (forget_list (forget_var @@ fself ()) xs)

               method c_Conj () _ xs =
                 Conj (forget_list (forget_var @@ fself ()) xs)
             end)
           ())
    in

    helper

  let to_smt_logic_exn bv_size ctx : logic -> Z3.Expr.expr =
    let term = T.to_smt_logic_exn bv_size ctx in
    let _, (module P) = Algebra.to_z3 bv_size ctx in

    let rec helper : logic -> _ = function
      | Value (Op (Var _, _, _)) ->
          (* has_free_vars "Var instead of formula %d" __LINE__ *)
          P.true_
      | Value (Conj (Var _)) ->
          (* has_free_vars "Var instead of formula %d" __LINE__ *)
          P.true_
      | Value (Disj (Var _)) ->
          (* has_free_vars "Var instead of formula %d" __LINE__ *)
          P.true_
      | Var (vidx, _) ->
          (* has_free_vars "Var instead of formula %d" __LINE__ *)
          P.true_
      | Value True -> P.true_
      | Value (Not l) -> P.not (helper l)
      | Value (Op (Value Eq, l, r)) -> P.eq (term l) (term r)
      | Value (Op (Value Le, l, r)) -> P.le (term l) (term r)
      | Value (Op (Value Lt, l, r)) -> P.lt (term l) (term r)
      | Value (Conj (Value Std.List.Nil)) ->
          has_free_vars "We should not get empty conjunctions %d" __LINE__
      | Value (Conj (Value (Std.List.Cons (h, tl)))) ->
          helper_list P.conj ~acc:(helper h) tl
      | Value (Disj (Value Std.List.Nil)) ->
          has_free_vars "We should not get empty disjunctions %d" __LINE__
      | Value (Disj (Value (Std.List.Cons (h, tl)))) ->
          helper_list P.disj ~acc:(helper h) tl
    and helper_list ~acc op = function
      | Var _ -> has_free_vars "Var in a cons cell %d" __LINE__
      (* | Value (Std.List.Cons (Var _, tl)) ->

         helper_list ~acc op tl *)
      | Value (Std.List.Cons (e, tl)) ->
          helper_list ~acc:(op acc (helper e)) op tl
      | Value Std.List.Nil -> acc
    in
    helper

  let compare_le a b =
    match GT.compare logic a b with
    | GT.GT ->
        Format.printf "\t\tACHTUNG: `%s` > `%s`\n%!" (GT.show logic a)
          (GT.show logic b);
        false
    | _ -> true

  let compare_injected a b =
    OCanren.(run q)
      (fun _ ->
        OCanren.structural (Std.Pair.pair a b) (Std.Pair.reify reify reify)
          (function
          | Value ((a : logic), b) -> (
              match GT.compare logic a b with GT.LT -> true | _ -> false)
          | Var _ -> failwith "not impelemnted"))
      (fun rr -> rr#reify OCanren.reify)
    |> fun s -> if Stream.is_empty s then GT.GT else GT.LT

  (*
  let my_lessthan a b =
    let open GT in
    let rec helper : logic -> _ -> _ =
     fun h1 h2 ->
      match (h1, h2) with
      | _, Var _ | Var _, _ -> GT.LT
      | Value av, Value bv -> helper_nologic (av, bv)
    and helper_nologic = function
      | True, True -> GT.EQ
      | Conj xs, Conj ys -> helper_list xs ys
      | Disj xs, Disj ys -> helper_list xs ys
      | Not a, Not b -> helper a b
      | Op (op1, l1, r1), Op (op2, l2, r2) ->
          GT.chain_compare
            (helper_opl (op1, op2))
            (fun () ->
              GT.chain_compare (T.my_compare l1 l2) (fun () ->
                  T.my_compare r1 r2))
      | x, y -> (
          let tx, ty = Obj.(tag @@ repr x, tag @@ repr y) in
          assert (tx <> ty);
          match Stdlib.compare tx ty with 1 -> GT.GT | 0 -> GT.EQ | _ -> GT.LT)
    and helper_list xs ys =
      match (xs, ys) with
      | Var _, _ | _, Var _ -> LT
      | Value Std.List.Nil, Value Std.List.Nil -> GT.EQ
      | Value (Std.List.Cons (h1, t1)), Value (Std.List.Cons (h2, t2)) ->
          GT.chain_compare (helper h1 h2) (fun () -> helper_list t1 t2)
      | Value Std.List.Nil, Value (Std.List.Cons (_, _)) -> GT.LT
      | Value (Std.List.Cons (_, _)), Value Std.List.Nil -> GT.GT
    and helper_opl = function
      | Var _, _ | _, Var _ -> GT.LT
      | Value l, Value r ->
          GT.compare GT.int Obj.(tag @@ Obj.repr l) Obj.(tag @@ repr r)
    in

    helper *)
end

(* TODO: Here environment containts terms but in practice it's likely that we will need only constants *)
module Env = struct
  open OCanren

  type ground = (string * T.ground) Std.List.ground

  type logic = (GT.string OCanren.logic * T.logic) OCanren.logic Std.List.logic
  [@@deriving gt ~plugins:{ fmt; show }]

  type injected =
    (string OCanren.ilogic * T.injected) OCanren.ilogic Std.List.injected

  let reify env : injected -> logic =
    Std.List.reify (Std.Pair.reify OCanren.reify T.reify) env

  let embed : _ -> ground =
    OCanren.Std.List.of_list (fun (a, b) -> (a, T.Const b))

  let empty : injected = Std.nil ()
  let cons name t : injected -> injected = Std.List.cons (Std.Pair.pair name t)
  let conso name t (tail : injected) (env : injected) = env === cons name t tail

  (* let rec lookupo name (env : injected) rez =
     conde
       [
         fresh (k1 v1 e1) (conso k1 v1 e1 env)
           (conde
              [
                k1 === name &&& (rez === v1); k1 =/= name &&& lookupo name e1 rez;
              ]);
         env === empty &&& failure;
       ] *)
  let rec lookupo name (env : injected) rez =
    Fresh.three (fun k1 v1 e1 ->
        conso k1 v1 e1 env
        &&& (k1 === name &&& (rez === v1)
            ||| (k1 =/= name &&& lookupo name e1 rez)))

  let inject : ground -> injected =
    let rec helper = function
      | [] -> Std.nil ()
      | (s, t) :: tl -> cons !!s (T.inj t) (helper tl)
    in
    helper

  let pp ppf (xs : ground) =
    Format.fprintf ppf "@[(and ";
    (* let (_ : int) = GT.foldl Std.List.ground in *)
    GT.foldl Std.List.ground
      (fun () (name, t) -> Format.fprintf ppf "@[(= %s %a)@] " name T.pp t)
      () xs;
    Format.fprintf ppf ")@]"

  let show = Format.asprintf "%a" pp
  let pp_logic = GT.fmt logic
end

(* ********************************************************************* *)

let mk_of_term (module BV : Bv.S) =
  let module Ans = struct
    open OCanren

    type t = T.injected
    type rez = t

    let finish = Fun.id
    let var s : t = T.var !!s
    let const n = T.const (BV.build_num n)
    let const_s s : t = T.const (BV.build_num @@ int_of_string s)
    let const_int n = T.const (BV.build_num n)
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
    type rez = Ph.injected
    type t = Conjs of rez list | Disjs of rez list | Final of rez

    let finish = function
      | Final x -> x
      | Disjs xs -> Ph.disj_list xs
      | Conjs xs -> Ph.conj_list xs

    type term = T.injected

    let true_ = Final Ph.true_

    let iff a b =
      failwiths ~here:[%here] "not implemented %s %d" __FILE__ __LINE__

    let not f = Final (Ph.not (finish f))

    let conj x y =
      let sort xs ys =
        List.append xs ys
        |> List.sort (fun a b ->
               match Ph.compare_injected a b with
               | GT.LT -> -1
               | GT.EQ -> 0
               | GT.GT -> 1)
      in
      match (x, y) with
      | Conjs xs, Conjs ys -> Conjs (sort xs ys)
      | Final x, Conjs xs | Conjs xs, Final x -> Conjs (sort [ x ] xs)
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
      let _ = failwiths ~here:[%here] "exists is not supported" in
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
