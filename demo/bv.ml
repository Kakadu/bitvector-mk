open Printf
open Tester
open OCanren
open OCanren.Std

[%%define TRACE]
[%%undef TRACE]

type cmp_t = LT | EQ | GT [@@deriving gt ~options:{ show }]

let int_pow base width = int_of_float (float_of_int base ** float_of_int width)

module Repr = struct
  type e = int
  type g = e OCanren.Std.List.ground
  type l = e logic OCanren.Std.List.logic

  (* It seems we can't hide these types because
     unifucation with a variable requires l to be seen
     as _ logic in the second type parameter
  *)

  type injected = e OCanren.ilogic OCanren.Std.List.injected
  type n = injected

  let inj g = GT.foldl Std.List.ground (fun acc x -> !!x % acc) (Std.nil ()) g
  let reify = List.reify OCanren.reify
  let prj_exn = List.prj_exn OCanren.prj_exn

  (* let prjc_exn env : injected -> g =
     List.prjc
       (OCanren.prjc (fun _ _ -> failwith "should not happen"))
       (fun _ _ -> failwith "should not happen")
       env *)

  let ground_of_logic_exn : l -> g =
    let rec on_logic l =
      GT.transform OCanren.logic
        (fun _ ->
          object
            method c_Value () _ x = on_list x
            method c_Var () _ _ = failwith "free variables"
          end)
        () l
    and on_list lst =
      GT.transform OCanren.Std.List.t
        (fun _ ->
          object
            method c_Nil () _ = OCanren.Std.List.Nil
            method c_Cons () _ h tl = OCanren.Std.List.Cons (on_e h, on_logic tl)
          end)
        () lst
    and on_e e =
      GT.transform OCanren.logic
        (fun _ ->
          object
            method c_Value () _ x = x
            method c_Var () _ _ = failwith "free variables"
          end)
        () e
    in
    on_logic

  let show xs = GT.(show List.ground @@ show int) xs
  let pp_logic = GT.(fmt List.logic @@ fmt logic @@ fmt int)
  let show_logic = Format.asprintf "%a" pp_logic

  let pp_binary ppf (xs : g) =
    Format.fprintf ppf "0b";
    let add = Format.fprintf ppf "%c" in
    GT.foldr Std.List.ground
      (fun () -> function 0 -> add '0' | 1 -> add '1' | _ -> assert false)
      () xs

  let show_binary n = Format.asprintf "%a" pp_binary n

  let pp_logic_binary ppf n =
    try
      let g = ground_of_logic_exn n in
      pp_binary ppf g
    with Failure _ -> pp_logic ppf n

  let show_logic_binary n = Format.asprintf "%a" pp_logic_binary n

  let rec eq_exn xs ys =
    match (xs, ys) with
    | Std.List.Nil, Std.List.Nil -> true
    | Cons (h1, t1), Cons (h2, t2) -> h1 = h2 && eq_exn t1 t2
    | _ -> failwith "eq_exn: Different length of list"

  let g =
    {
      GT.gcata = ();
      GT.fix = ();
      GT.plugins =
        object
          method show = show
          method gmap = Fun.id
          method fmt ppf x = Format.fprintf ppf "%s" (show x)
          method foldl acc _ = acc

          method compare : g -> g -> GT.comparison =
            GT.compare Std.List.ground (GT.compare GT.int)
        end;
    }

  let hack_compare ~f a b =
    match (a, b) with
    | Value ax, Value bx -> f ax bx
    | Var _, _ | _, Var _ -> GT.EQ

  let l =
    {
      GT.gcata = ();
      GT.fix = ();
      GT.plugins =
        object
          method show = show_logic
          method gmap = Fun.id
          method fmt ppf x = Format.fprintf ppf "%s" (show_logic x)

          method foldl =
            GT.foldl Std.List.logic (GT.foldl OCanren.logic @@ GT.foldl GT.int)

          method compare =
            let rec helper a b =
              match (a, b) with
              | Var _, _ | _, Var _ -> GT.EQ
              | Value Std.List.Nil, Value (Std.List.Cons (_, _))
              | Value (Std.List.Cons (_, _)), Value Std.List.Nil ->
                  failwith "should not happen"
              | Value Std.List.Nil, Value Nil -> GT.EQ
              | Value (Std.List.Cons (h1, t1)), Value (Std.List.Cons (h2, t2))
                ->
                  GT.chain_compare (helper t1 t2) (fun () ->
                      hack_compare ~f:(GT.compare GT.int) h1 h2)
            in

            helper
        end;
    }

  let%test _ =
    let three : l =
      Std.List.of_list Fun.id [ 0; 1; 0; 0 ] |> Std.List.inj OCanren.to_logic
    in
    let one : l =
      Std.List.of_list Fun.id [ 1; 0; 0; 0 ] |> Std.List.inj OCanren.to_logic
    in
    GT.compare l one three = GT.LT
end

module type S = sig
  open Repr
  open OCanren

  val show_binary : g -> string
  val build_num : int -> n
  val of_int : int -> g
  val mod2 : n -> e ilogic -> goal
  val mul2 : n -> n -> goal
  val addo : n -> n -> n -> goal
  (*
  val gen_addero : int -> (int, int logic) OCanren.injected ->
      n -> n -> n -> goal

  val addero : int -> (int, int logic) OCanren.injected ->
      n -> n -> n -> goal
 *)

  val subo : n -> n -> n -> goal
  val multo : n -> n -> n -> goal
  val shiftl1 : n -> n -> goal
  val lshiftr1 : n -> n -> goal
  val ashiftr1 : n -> n -> goal
  val ashiftro : n -> n -> n -> goal
  val lshiftro : n -> n -> n -> goal
  val shiftlo : n -> n -> n -> goal
  val rotl : n -> n -> goal
  val rotr : n -> n -> goal
  val loro : n -> n -> n -> goal
  val lando : n -> n -> n -> goal
  val lto : n -> n -> goal
  val leo : n -> n -> goal
  val compare_helper : n -> n -> cmp_t ilogic -> goal
  val forallo : n -> (n -> goal) -> goal
  val width : int
end

let create width : (module S) =
  let module M = struct
    open OCanren
    include Repr

    let width = width
    let count = int_pow 2 width

    let of_int n : g =
      if n >= count then failwith "of_int: argument too big"
      else
        let rec helper i n =
          let b = n mod 2 in
          if i >= width then Std.List.Nil
          else Std.List.Cons (b, helper (1 + i) (n / 2))
        in
        helper 0 n

    let debug_n : n -> (int logic Std.List.logic list -> goal) -> goal =
     fun n -> debug_var n (fun a b -> OCanren.Std.List.reify OCanren.reify b a)

    let msg pp =
      debug_var !!1
        (fun a b -> OCanren.reify b a)
        (function
          | _ ->
              Format.printf "%a" pp ();
              success)

    let msg_here line = msg (fun ppf () -> Format.fprintf ppf "%d\n%!" line)

    let trace_n n fmt =
      debug_n n (function
        | [ n ] ->
            Format.printf "%s: %s\n%!" (Format.asprintf fmt) (show_logic n);
            success
        | _ -> assert false)

    let trace_peano n fmt =
      debug_var n
        (fun a b -> Std.Nat.reify b a)
        (function
          | [ n ] ->
              Format.printf "%s: %s\n%!" (Format.asprintf fmt)
                (GT.show Std.Nat.logic n);
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

    let trace_bool n fmt =
      debug_var n
        (fun a b -> OCanren.reify b a)
        (function
          | [ n ] ->
              Format.printf "%s: %s\n%!" (Format.asprintf fmt)
                (GT.show OCanren.logic (GT.show GT.bool) n);
              success
          | _ -> assert false)
    (* let peano_width : Std.Nat.groundi = Std.Nat.(nat (of_int width)) *)

    let rec appendo l s out =
      conde
        [
          List.nullo l &&& (s === out);
          fresh (a d res) (a % d === l) (a % res === out) (appendo d s res);
        ]

    module New = struct
      (* primitives for new representation *)

      let list_inito len x =
        let open OCanren.Std in
        let rec helper acc = function
          | 0 -> acc
          | n -> helper (x % acc) (n - 1)
        in
        helper (List.nil ()) len

      let zero = list_inito width !!0
      let one = Std.List.( % ) !!1 (list_inito (width - 1) !!0)

      (* Zero is empty list or a list of all zeros *)
      let is_zero n = n === zero

      let rec all_zeros xs =
        conde [ xs === Std.nil (); fresh tl (xs === !!0 % tl) (all_zeros tl) ]

      (* One is a list which head is 1 and tail is all zeros *)
      let is_one n = fresh tl (n === Std.List.cons !!1 tl) (all_zeros tl)

      let build_num n =
        let rec helper i n =
          let b = n mod 2 in
          if i >= width then Std.nil ()
          else Std.List.cons !!b (helper (1 + i) (n / 2))
        in
        helper 0 n

      module X = struct
        let build n =
          let rec helper i n =
            let b = n mod 2 in
            if i >= width then []
            else Stdlib.List.cons b (helper (1 + i) (n / 2))
          in
          helper 0 n
        (*
        let () = assert (build 1 = [ 1; 0 ])

        let () = assert (build 2 = [ 0; 1 ])

        let () = assert (build 3 = [ 1; 1 ]) *)
      end

      (* very costly implementation *)
      (* TODO: fixme *)
      (* let poso n = n = /= zero *)

      let rec has_a_one n =
        conde
          [
            n === Std.List.nil () &&& failure;
            fresh (h tl)
              (n === List.cons h tl)
              (conde [ h === !!1; h === !!0 &&& has_a_one tl ]);
          ]

      let gt1o n =
        conde
          [
            n === List.nil () &&& failure;
            fresh (b tl) (n === List.cons b tl) (has_a_one tl);
          ]
    end

    module Old = struct
      (* primitives for the old  representation *)

      (* zero is an empty list *)
      let zero : n = nil ()
      let is_zero n = n === zero

      (* one is a singleton list of 1 *)
      let one = !<(!!1)
      let is_one q = fresh tl (Std.List.cons !!1 tl === q) (is_zero tl)
      let poso q = fresh (h t) (q === h % t)
      let gt1o q = fresh (h t tt) (q === h % (t % tt))
    end

    include New

    let ( ! ) = ( !! )
    let mod2 n min = fresh tl (n === min % tl)

    let mul2 x _2x =
      let rec helper x ans =
        fresh (h tl)
          (conde
             [
               x === Std.nil () &&& failure;
               x === !<h &&& (ans === Std.nil ());
               fresh tl2 (x === h % tl) (ans === h % tl2) (helper tl tl2);
             ])
      in
      fresh tl (_2x === !!0 % tl) (helper x tl)

    let of_e e ans =
      assert (width > 1);
      let rec helper pos acc =
        if pos <= 0 then acc else helper (pos - 1) (!!0 % acc)
      in
      ans === e % helper (width - 1) (Std.nil ())

    (* Call [full_addero b x y r c] adds y to x with carry bit [b]
       and return result [r] and new carry bit [c]
    *)
    let full_addero b x y r c =
      (* msg_here __LINE__
         &&& *)
      conde
        [
          !0 === b &&& (!0 === x) &&& (!0 === y) &&& (!0 === r) &&& (!0 === c);
          !1 === b &&& (!0 === x) &&& (!0 === y) &&& (!1 === r) &&& (!0 === c);
          !0 === b &&& (!1 === x) &&& (!0 === y) &&& (!1 === r) &&& (!0 === c);
          !1 === b &&& (!1 === x) &&& (!0 === y) &&& (!0 === r) &&& (!1 === c);
          !0 === b &&& (!0 === x) &&& (!1 === y) &&& (!1 === r) &&& (!0 === c);
          !1 === b &&& (!0 === x) &&& (!1 === y) &&& (!0 === r) &&& (!1 === c);
          !0 === b &&& (!1 === x) &&& (!1 === y) &&& (!0 === r) &&& (!1 === c);
          !1 === b &&& (!1 === x) &&& (!1 === y) &&& (!1 === r) &&& (!1 === c);
        ]

    let make_short_one w =
      if w > 1 then Std.List.cons !!1 (list_inito (w - 1) !!0)
      else Std.(!<(!!1))

    let make_short_zero w =
      assert (w >= 0);
      list_inito w !!0

    let looks_like_zero ~pos n =
      (* TODO: optimize via memoization and single unification *)
      assert (pos >= 0);
      make_short_zero pos === n
    (*
      if pos = 0 then (n === Std.nil())
      else
        fresh (tl)
          (n === Std.List.cons !!0 tl )
          (looks_like_zero ~pos:(pos-1) tl)
      *)

    let looks_like_one ~pos n =
      if pos <= 0 then failure
      else
        fresh tl
          (n === Std.List.cons !!1 tl)
          (looks_like_zero ~pos:(pos - 1) tl)

    (* Very similar to concept of `positive` number *)
    let rec has_ones_inside ~pos n =
      (* TODO: force n to have right length *)
      (* n =/= (make_short_zero pos) *)
      if pos = 0 then failure
      else
        fresh tl
          (if pos = 1 then tl === Std.nil () else success)
          (conde
             [
               n === !!1 % tl;
               n === !!0 % tl &&& has_ones_inside ~pos:(pos - 1) tl;
             ])

    let looks_like_gt1o ~pos n =
      match pos with
      | 0 -> failure
      | x when x < 0 -> assert false
      | 1 -> failure
      | wide ->
          fresh (h tl)
            (List.cons h tl === n)
            (has_ones_inside ~pos:(wide - 1) tl)

    let rec looks_like_poso ~pos n =
      match pos with
      | 0 -> failure
      | x when x < 0 -> assert false
      | 1 -> n === !<(!!1)
      | wide ->
          fresh tl
            (conde
               [
                 List.cons !!1 tl === n;
                 List.cons !!0 tl === n &&& looks_like_poso ~pos:(pos - 1) tl;
               ])

    let poso = looks_like_poso ~pos:width

    module Sizes = struct
      let has_ones_inside = has_ones_inside
      let poso = looks_like_poso
      let gt1o = looks_like_gt1o
      let zero = looks_like_zero
      let is_one = looks_like_one

      let check_width =
        let rec helper pos x =
          if pos <= 0 then x === nil ()
          else fresh (h tl) (x === h % tl) (helper (pos - 1) tl)
        in
        helper width

      let width_is_lt =
        let rec helper pos x =
          if pos <= 0 then x === nil ()
          else
            conde
              [
                x === nil (); fresh (h tl) (x === h % tl) (helper (pos - 1) tl);
              ]
        in
        helper width
    end

    (* function that do not take to account size constraints *)
    module NoSize = struct
      let okay_size n =
        let rec helper sz x =
          if sz <= 0 then x === Std.nil ()
          else fresh (tmp tl) (x === tmp % tl) (helper (sz - 1) tl)
        in
        helper (2 * width) n

      let is_zero n =
        let rec helper sz x =
          if sz <= 0 then success
          else fresh tl (x === !!0 % tl) (helper (sz - 1) tl)
        in
        helper width n

      let is_one n = fresh tl (n === !!1 % tl) (is_zero (!!0 % tl))

      let has_ones_inside =
        let rec helper sz x =
          if sz <= 0 then failure
          else
            fresh (h tl)
              (x === h % tl)
              (conde [ h === !!1; h === !!0 &&& helper (sz - 1) tl ])
        in
        helper width

      let poso n =
        (* positive means it has ones inside *)
        has_ones_inside n

      let gt0 = poso
      let gt1 n = fresh (temp tl) (n === temp % tl) (gt0 tl)

      let normalize =
        let rec helper sz n out =
          if sz <= 0 then out === Std.nil ()
          else
            fresh (h1 tl1 tl2)
              (n === h1 % tl1)
              (out === h1 % tl2)
              (helper (sz - 1) tl1 tl2)
        in
        helper width
    end

    [%%if defined TRACE]

    let trace g = g

    [%%else]

    let trace _ = success

    [%%endif]

    (* carry + n + m = r
       extra_w is a (decreasing) number of positions left to investigate
    *)
    let rec addero pos car n m r =
      let () = assert (pos >= 0) in
      trace
        (trace_int !!pos "pos " &&& trace_int car "car " &&& trace_n n "  n"
       &&& trace_n m "  m" &&& trace_n r "  r")
      &&& conde
            [
              (* If we did all the work, then
                 result is already built in it's full length *)
              !!pos === !!0 &&& (r === Std.nil ());
              fresh () (!!pos =/= !!0)
                (conde
                   [
                     !0 === car &&& (make_short_zero pos === m) &&& (n === r);
                     !0 === car
                     &&& (make_short_zero pos === n)
                     &&& (m === r) &&& has_ones_inside ~pos m;
                     !1 === car
                     &&& (make_short_zero pos === m)
                     &&& (* (msg_here __LINE__) &&& *)
                     defer (addero pos !0 n (make_short_one pos) r);
                     !1 === car
                     &&& (make_short_zero pos === n)
                     &&& has_ones_inside ~pos m
                     &&& (* (msg_here __LINE__) &&& *)
                     defer (addero (pos - 1) !0 m (make_short_one pos) r);
                     fresh ()
                       (make_short_one pos === n)
                       (n === m)
                       (trace (msg_here __LINE__))
                       (conde
                          [
                            !!pos === !!1
                            &&& fresh (a temp) (!<a === r)
                                  (full_addero car !1 !1 a temp);
                            !!pos =/= !!1
                            &&& fresh (a c h)
                                  (a % c === r)
                                  (make_short_zero (pos - 1) === c)
                                  (Std.List.hdo c h)
                                  (full_addero car !1 !1 a h);
                          ]);
                     (* make_short_one pos === m
                        &&& trace (msg_here __LINE__)
                        &&& gen_addero pos car m n r; *)
                     make_short_one pos === n
                     &&& trace (msg_here __LINE__)
                     &&& gen_addero pos car n m r;
                     make_short_one pos === m &&& looks_like_gt1o ~pos n
                     &&& looks_like_gt1o ~pos r
                     &&& trace (msg_here __LINE__)
                     &&& defer (addero pos car m n r);
                     looks_like_gt1o ~pos n
                     &&& trace (msg_here __LINE__)
                     &&& gen_addero pos car n m r;
                   ]);
            ]

    and gen_addero pos car n m r =
      let () = assert (pos >= 0) in
      trace (trace_int !pos "gen_addero: pos")
      &&& trace (trace_n n "  n" &&& trace_n m "  m" &&& trace_n r "  r")
      &&& conde
            [
              !!pos === !!0 &&& (r === Std.nil ());
              fresh (a b c e x y z ppp) (!!pos =/= !!0)
                (a % x === n)
                (b % y === m)
                (* (looks_like_poso ~pos y) *)
                (c % z === r)
                (* (trace_n r "  next r") *)
                (has_ones_inside ~pos m)
                (full_addero car a b c e)
                (addero (pos - 1) e x y z);
            ]

    (* n + m = k *)
    let addo n m k = addero width !0 n m k

    (* n - m = k *)
    let subo n m k = addo m k n

    let rec bound_multo q p n m =
      conde
        [
          List.nullo q &&& poso p;
          fresh (x y z) (List.tlo q x) (List.tlo p y)
            (conde
               [
                 List.nullo n &&& List.cdro m z &&& bound_multo x y z @@ nil ();
                 List.cdro n z &&& bound_multo x y z m;
               ]);
        ]

    (* ****** Multiplication ************** *)

    (* The idea: n  =  (n1...nw)
       nm = sum{i\in 1..w}{ m lsl (i-1) }
    *)
    let multo n m nm =
      let rec helper pos ~shiftedm n nm =
        (* trace_n shiftedm "  shiftedm" &&& trace_n n "  n" &&& trace_n nm "  nm"
           &&& *)
        (* decreases on the length of N
           lengthes of M and NM are  constant *)
        if pos <= 0 then n === nil () &&& (nm === zero)
        else
          fresh (ntl shm2) (mul2 shiftedm shm2)
            (conde
               [
                 n === !!0 % ntl &&& helper (pos - 1) ntl ~shiftedm:shm2 nm;
                 fresh temp_nm
                   (n === !!1 % ntl)
                   (addo shiftedm temp_nm nm)
                   (helper (pos - 1) ntl ~shiftedm:shm2 temp_nm);
               ])
      in
      fresh () (Sizes.check_width m) (Sizes.check_width n)
        (Sizes.check_width nm)
        (helper width ~shiftedm:m n nm)

    let division n m q r = fresh t1 (multo m q t1) (addo t1 r n)
    let div n m q = division n m q zero
    let mod_ n m r = division n m one r

    (*
    (* n * m === p *)
    let rec multo_ n ~nw m ~mw p ~pw =
      success
      (* &&& (trace_n n "  n" &&& trace_n m "  m" &&& trace_n p "  p") *)
      &&& conde
            [
              (* 0 * m = 0 *)
              looks_like_zero ~pos:nw n &&& (make_short_zero pw === p);
              (* if n>0 then n * 0 = 0 *)
              Sizes.has_ones_inside ~pos:nw n &&& Sizes.zero ~pos:mw m &&& Sizes.zero ~pos:pw p;
              (* if n=1 and m>0 then n * m = m *)
              Sizes.is_one ~pos:nw n &&& NoSize.poso m &&& (m === p);
              (* if n>1 and m=1 then n * m = n *)
              (* N.B. 3rd conjunct (n === p) can be buggy because of sizes *)
              Sizes.gt1o ~pos:nw n &&& Sizes.is_one ~pos:mw m &&& (n === p);
              (* if m>1 and x>1 and z>1 then 2*x * m = 2*z *)
              fresh (n2 p2)
                (!0 % n2 === n)
                (* (looks_like_poso ~pos x) *)
                (!0 % p2 === p)
                (* (trace_n p "  splitting p:") (msg_here __LINE__) *)
                (* (looks_like_poso ~pos z) *)
                (* (looks_like_gt1o ~pos m) *)
                (multo_ ~nw:(nw - 1) n2 m ~mw p2 ~pw:(pw - 1));
              fresh (n2 m2)
                (!1 % n2 === n)
                (* (looks_like_poso ~pos x) *)
                (!0 % m2 === m)
                (* (msg_here __LINE__)  *)
                (* (poso y)  *)
                (multo_ ~nw:mw m ~mw:nw n ~pw p);
              fresh (n2 m2)
                (!1 % n2 === n)
                (* (looks_like_poso ~pos x) *)
                (!1 % m2 === m)
                (* (msg_here __LINE__) *)
                (* (looks_like_poso ~pos y)  *)
                (odd_multo ~nw:(nw - 1) n2 ~mw n2 m2 ~pw p);
            ]

    and odd_multo x ~nw n ~mw m ~pw p =
      fresh (q q2 m2) (bound_multo q p n m) (multo_ x m q)
        (!0 % q === q2)
        (NoSize.normalize n m2) (pluso q2 m2 p)

    and multo_helper n ~nw m ~mw nm =
      (* Underscored are not of normalized size *)
      (* TODO: normalization will hurt performance *)
      fresh ()
        (* (NoSize.normalize n_ n) *)
        (* (NoSize.normalize m_ m) *)
        (multo_ n ~nw m ~mw nm)
    (* (NoSize.normalize nm_ nm) *)

    let multo n m nm = multo_helper n ~nw:width m ~mw:width nm
*)

    (* Comparisons *)

    let compare_bits a b rez =
      conde
        [
          a === !!0 &&& (b === !!0) &&& (rez === !!EQ);
          a === !!0 &&& (b === !!1) &&& (rez === !!LT);
          a === !!1 &&& (b === !!1) &&& (rez === !!EQ);
          a === !!1 &&& (b === !!0) &&& (rez === !!GT);
        ]

    let rec compare_helper0 pos l r rez =
      conde
        [
          !!pos === !!0
          &&& conde [ l =/= Std.nil (); r =/= Std.nil () ]
          &&& failure;
          !!pos === !!0 &&& (l === Std.nil ()) &&& (r === l) &&& (rez === !!EQ);
          fresh (lh ltl rh rtl top_rez) (!!pos =/= !!0)
            (l === lh % ltl)
            (r === rh % rtl)
            (* (trace_n l " leo_helper.l")
               (trace_n r " leo_helper.r") *)
            (compare_helper0 (pos - 1) ltl rtl top_rez)
            (conde
               [
                 top_rez === !!GT &&& (rez === !!GT);
                 top_rez === !!LT &&& (rez === !!LT);
                 top_rez === !!EQ &&& compare_bits lh rh rez;
                 (* TODO: optimize intro two cases? *)
               ]);
        ]

    let compare_helper = compare_helper0 width
    let leo a b = fresh rez (rez =/= !!GT) (compare_helper a b rez)
    let lto a b = fresh rez (rez === !!LT) (compare_helper a b rez)
    let gto a b = lto b a
    let geo a b = leo b a

    let lando =
      let rec helper pos l r lr =
        conde
          [
            !!pos === !!0
            &&& conde [ l =/= Std.nil (); r =/= Std.nil (); lr =/= Std.nil () ]
            &&& failure;
            !!pos === !!0 &&& (l === Std.nil ()) &&& (r === l) &&& (lr === l);
            fresh (lh ltl rh rtl lrh lrtl) (!!pos =/= !!0)
              (l === lh % ltl)
              (r === rh % rtl)
              (lr === lrh % lrtl)
              (conde
                 [
                   lh === !!0 &&& (lrh === !!0);
                   lh === !!1 &&& (rh === !!1) &&& (lrh === !!1);
                   rh === !!0 &&& (lrh === !!0);
                 ])
              (helper (pos - 1) ltl rtl lrtl);
          ]
      in
      helper width

    let loro _ _ = assert false

    (* Shifts *)

    let rec go_left_helper pos prev ins outs last =
      if pos = 1 then fresh temp (outs === !<prev) (ins === !<last)
      else
        fresh (ih itl oh otl)
          (ins === ih % itl)
          (outs === oh % otl)
          (oh === prev)
          (go_left_helper (pos - 1) ih itl otl last)

    (* arithmetical and logical shift *)
    let shiftl1 n out =
      fresh (min tl)
        (conde
           [
             n === !<min &&& (out === !<(!!0));
             fresh (last otl)
               (n === min % tl)
               (out === !!0 % otl)
               (go_left_helper (width - 1) min tl otl last);
           ])

    let rotl n out =
      fresh (min tl)
        (conde
           [
             n === !<min &&& (out === n);
             fresh (last otl)
               (n === min % tl)
               (out === last % otl)
               (go_left_helper (width - 1) min tl otl last);
           ])

    let rotr m n = rotl n m

    let rec go_right_helper pos next ins outs last =
      if pos = 1 then fresh temp (outs === !<last) (ins === !<next)
      else
        (* prev is a previous digit in result
           we should unify it *)
        fresh (ih itl oh otl)
          (ins === ih % itl)
          (outs === oh % otl)
          (ih === next)
          (go_right_helper (pos - 1) oh itl otl last)

    (* logical shift right : put 0 to the end *)
    let lshiftr1 n out =
      fresh (min tl)
        (conde
           [
             n === !<min &&& (out === !<(!!0));
             fresh (min next otl)
               (n === min % tl)
               (out === next % otl)
               (go_right_helper (width - 1) next tl otl !!0);
           ])

    let rec go_right_helper2 pos next ins outs make_last =
      if pos = 1 then
        fresh last (outs === !<last) (ins === !<next) (make_last next last)
      else
        (* prev is a previous digit in result
           we should unify it *)
        fresh (ih itl oh otl)
          (ins === ih % itl)
          (outs === oh % otl)
          (ih === next)
          (go_right_helper2 (pos - 1) oh itl otl make_last)

    let lshiftr_attempt2 n out =
      let make_last _ last = last === !!0 in
      fresh (min tl)
        (conde
           [
             n === !<min &&& (out === !<(!!0));
             fresh (min next otl)
               (n === min % tl)
               (out === next % otl)
               (go_right_helper2 (width - 1) next tl otl make_last);
           ])

    let ashiftr1 n out =
      let make_last = ( === ) in
      fresh (min tl)
        (conde
           [
             n === !<min &&& (out === !<(!!0));
             fresh (min next otl)
               (n === min % tl)
               (out === next % otl)
               (go_right_helper2 (width - 1) next tl otl make_last);
           ])

    let ashiftro _ _ _ = assert false

    let rec while_ ~from init op ans =
      conde
        [
          fresh (next prev) (lto zero from) (op init next) (subo from one prev)
            (* (trace_n from "  from = ")
               (trace_n init "    init = ")
               (trace_n next "    next = ") *)
            (while_ ~from:prev next op ans);
          fresh () (zero === from) (ans === init);
        ]

    (*
    let spread_length w =
      let approx = log (float_of_int w) /. log 2.0 in
      (* ceil rounds up, but (ceil 1.0 = 1.0) *)
      1 + (int_of_float @@ ceil approx)

    let () = assert (spread_length 4 = 3)

    let modulo_max =
      let spread = spread_length width in

      let rec helper pos n rez =
        conde [ !!n ===!! 0 &&& n === Std.nil () &&& rez === n; !!n =/= !!0 ]
      in
      helper width
 *)
    (* Logical <-> MSB will be 0 *)
    let lshiftro op len rez =
      conde
        [
          leo len (build_num width) &&& while_ ~from:len op lshiftr1 rez;
          gto len (build_num width) &&& (rez === zero);
        ]

    let shiftlo op len rez =
      conde
        [
          lto len (build_num width) &&& while_ ~from:len op shiftl1 rez;
          geo len (build_num width) &&& (rez === zero);
        ]

    let forallo q relo =
      let helper n acc =
        if n >= count then acc else relo (build_num n) &&& acc
      in
      helper 0 success
  end in
  (module M : S)
