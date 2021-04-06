open Printf
open OCanren
open OCanren.Std
open Tester

[%%define TRACE]

[%%undef TRACE]

module Repr = struct
  type e = int

  type g = e Std.List.ground

  type l = e logic Std.List.logic

  (* It seems we can't hide these types because
     unifucation with a variable requires l to be seen
     as _ logic in the second type parameter
  *)

  type n = (g, l) injected

  type injected = n

  let reify = List.reify OCanren.reify

  let show xs = GT.(show List.ground @@ show int) xs

  let show_logic = GT.(show List.logic @@ show logic @@ show int)

  let g =
    {
      GT.gcata = ();
      (* (fun tr _ _ -> assert false); *)
      GT.fix = ();
      (* (fun _ _ -> assert false); *)
      GT.plugins =
        object
          method show = show

          method gmap = Fun.id

          method fmt ppf x = Format.fprintf ppf "%s" (show x)
        end;
    }

  let l =
    {
      GT.gcata = ();
      (* (fun tr _ _ -> assert false); *)
      GT.fix = ();
      (* (fun _ _ -> assert false); *)
      GT.plugins =
        object
          method show = show_logic

          method gmap = Fun.id

          method fmt ppf x = Format.fprintf ppf "%s" (show_logic x)
        end;
    }
end

module type S = sig
  open Repr
  open OCanren

  val show_binary : g -> string

  val build_num : int -> n

  val mod2 : n -> (e, e logic) injected -> goal

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

  val width : int
end

let create width : (module S) =
  let module M = struct
    open OCanren
    include Repr
    (* type e = int

       type g = e Std.List.ground

       type l = e logic Std.List.logic

       type n = (e, e logic) OCanren.Std.List.groundi

       type injected = n *)

    let show_binary (xs : g) =
      let b = Buffer.create (width + 4) in
      Buffer.add_string b "0b";
      let add = Buffer.add_char b in
      GT.foldr Std.List.ground
        (fun () -> function 0 -> add '0' | 1 -> add '1' | _ -> assert false)
        () xs;
      Buffer.contents b

    let width = width

    let count = int_of_float (2. ** float_of_int width)

    let debug_n : n -> (int logic Std.List.logic list -> goal) -> goal =
     fun n -> debug_var n (fun a b -> OCanren.Std.List.reify OCanren.reify b a)

    let msg pp =
      debug_var !!1
        (fun a b -> OCanren.reify b a)
        (function
          | _ ->
              Format.printf "%a" pp ();
              success)

    let msg_here line = msg (fun ppf () -> Format.fprintf ppf "%d\n" line)

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

    let rec looks_like_zero ~pos n =
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
      success
      (* &&& trace_int !!pos "pos " &&& trace_int car "car " &&& trace_n n "  n"
         &&& trace_n m "  m" &&& trace_n r "  r" *)
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
                       (conde
                          [
                            !!pos === !!0
                            &&& fresh (a temp) (!<a === r)
                                  (full_addero car !1 !1 a temp);
                            !!pos =/= !!0
                            &&& fresh (a c)
                                  (a %< c === r)
                                  (full_addero car !1 !1 a c);
                          ]);
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
                (looks_like_poso ~pos y)
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

    let lshiftro _ _ _ = assert false

    let shiftlo _ _ _ = assert false
    (* Comparisons *)

    let leo _ _ = assert false

    let lto _ _ = assert false

    let lando _ _ = assert false

    let loro _ _ = assert false
  end in
  (module M : S)

(*
let create_peano width : (module S) =
  let module M = struct
    open OCanren

    type g = Std.Nat.ground

    type l = Std.Nat.logic

    type n = OCanren.Std.Nat.groundi

    let show = GT.show Nat.ground

    let show_logic = GT.show Nat.logic

    let reify = Nat.reify

    let width = width

    let count = int_of_float (2. ** float_of_int width)

    let build_num n =
      if n >= count then
        failwith (Printf.sprintf "bad argument of build_num: %d" n)
      else
        let rec helper acc n =
          if n = 0 then acc else helper (Std.Nat.succ acc) (n - 1)
        in
        helper Std.Nat.zero n

    let overflow = Std.Nat.succ (build_num (count - 1))

    let max_int = build_num (count - 1)

    let () = Printf.printf "oveflow peano = %d\n" (count - 1)

    let trace_peano n fmt =
      debug_var n
        (fun a b -> Std.Nat.reify b a)
        (function
          | [ n ] ->
              Format.printf "%s: %s\n%!" (Format.asprintf fmt)
                (GT.show Std.Nat.logic n);
              success
          | _ -> assert false)

    let rec pluso m n r =
      trace_peano max_int "max_int"
      &&& trace_peano m "m" &&& trace_peano n "n" &&& trace_peano r "r"
      &&& conde
            [
              m === Std.Nat.zero &&& (n === r);
              fresh (prev nextr)
                (m === Std.Nat.s prev)
                (conde
                   [
                     r === max_int &&& (nextr === Std.Nat.zero);
                     r =/= max_int &&& (nextr === Std.Nat.s r);
                   ])
                (pluso prev n nextr);
            ]
  end in
  (module M : S) *)

(*
let rec eqlo n m =
  conde [
    (nil() === n) &&& (nil() === m);
    ((!< !1) === n) &&& ((!< !1) === m);
    fresh (a x b y)
      ((a % x) === n)
      (poso x)
      ((b % y) === m)
      (poso y)
      (eqlo x y)
  ]

let rec ltlo n m =
  conde [
    (nil() === n) &&& (poso m);
    ((!< !1) === n) &&& (gt1o m);
    fresh (a x b y)
      ((a % x) === n)
      (poso x)
      ((b % y) === m)
      (poso y)
      (ltlo x y)
  ]

let lelo n m =
  conde [
    (eqlo n m);
    (ltlo n m)
  ]

let rec lto n m =
  conde [
    (ltlo n m);
    ?& [
      (eqlo n m);
      fresh (x)
        (poso x)
        (pluso n x m)
    ]
  ]

let leo n m =
  conde [
    (n === m);
    (lto n m)
  ]

let rec splito n r l h =
  conde [
    (nil() === n) &&& (nil() === h) &&& (nil() === l);
    fresh (b n')
      ((!0 % (b % n')) === n)
      (nil() === r)
      ((b % n') === h)
      (nil() === l);
    fresh (n')
      ((!1 % n') === n)
      (nil() === r)
      (n' === h)
      ((!< !1) === l);
    fresh (b n' a r')
      ((!0 % (b % n')) === n)
      ((a % r') === r)
      (nil() === l)
      (splito (b % n') r' (nil()) h);
    fresh (n' a r')
      ((!1 % n') === n)
      ((a % r') === r)
      ((!< !1) === l)
      (splito n' r' (nil()) h);
    fresh (b n' a r' l')
      ((b % n') === n)
      ((a % r') === r)
      ((b % l') === l)
      (poso l')
      (splito n' r' l' h)
  ]

let rec divo n m q r =
  conde [
    (r === n) &&& (nil() === q) &&& (lto n m);
    ((!< !1) === q) &&& (eqlo n m) &&& (pluso r m n) &&& (lto r m);
    ?& [
      (ltlo m n);
      (lto r m);
      (poso q);
      fresh (nh nl qh ql qlm qlmr rr rh)
        (splito n r nl nh)
        (splito q r ql qh)
        (conde [
          (nil() === nh) &&& (nil() === qh) &&& (minuso nl r qlm) &&& (multo ql m qlm);
          ?& [
            (poso nh);
            (multo ql m qlm);
            (pluso qlm r qlmr);
            (minuso qlmr nl rr);
            (splito rr r (nil()) rh);
            (divo nh m qh rh)
          ]
        ])
    ]
  ]

let rec repeated_mul n q nq =
  conde [
    (poso n) &&& (nil() === q) &&& ((!< !1) === nq);
    ((!< !1) === q) &&& (n === nq);
    ?& [
      (gt1o q);
      fresh (q1 nq1)
        (pluso q1 (!< !1) q)
        (repeated_mul n q1 nq1)
        (multo nq1 n nq)
    ]
  ]

let rec exp2 n b q =
  conde [
    ((!< !1) === n) &&& (nil() === q);
    ?& [
      (gt1o n);
      ((!< !1) === q);
      fresh (s)
        (splito n b s (!< !1))
    ];
    fresh (q1 b2)
      ((!0 % q1) === q)
      (poso q1)
      (ltlo b n)
      (appendo b (!1 % b) b2)
      (exp2 n b2 q1);
    fresh (q1 nh b2 s)
      ((!1 % q1) === q)
      (poso q1)
      (poso nh)
      (splito n b s nh)
      (appendo b (!1 % b) b2)
      (exp2 nh b2 q1)
  ]

let rec logo n b q r =
  conde [
    ((!< !1) === n) &&& (poso b) &&& (nil() === q) &&& (nil() === r);
    (nil() === q) &&& (lto n b) &&& (pluso r (!< !1) n);
    ((!< !1) === q) &&& (gt1o b) &&& (eqlo n b) &&& (pluso r b n);
    ((!< !1) === b) &&& (poso q) &&& (pluso r (!< !1) n);
    (nil() === b) &&& (poso q) &&& (r === n);
    ?& [
      ((!0 %< !1) === b);
      fresh (a ad dd)
        (poso dd)
        ((a % (ad % dd)) === n)
        (exp2 n (nil()) q)
        (fresh (s)
          (splito n dd r s)
        )
    ];
    ?& [
      fresh (a ad add ddd)
        (conde [
          ((!1 %< !1) === b);
          ((a % (ad % (add % ddd))) === b)
        ]);
      (ltlo b n);
      fresh (bw1 bw nw nw1 ql1 ql s)
        (exp2 b (nil()) bw1)
        (pluso bw1 (!< !1) bw)
        (ltlo q n)
        (fresh (q1 bwq1)
          (pluso q (!< !1) q1)
          (multo bw q1 bwq1)
          (lto nw1 bwq1)
          (exp2 n (nil()) nw1)
          (pluso nw1 (!< !1) nw)
          (divo nw bw ql1 s)
          (pluso ql (!< !1) ql1)
          (lelo ql q)
          (fresh (bql qh s qdh qd)
            (repeated_mul b ql bql)
            (divo nw bw1 qh s)
            (pluso ql qdh qh)
            (pluso ql qd q)
            (leo qd qdh)
            (fresh (bqd bq1 bq)
              (repeated_mul b qd bqd)
              (multo bql bqd bq)
              (multo b bq bq1)
              (pluso bq r n)
              (lto n bq1)
            )
          )
        )
    ]
  ]

let expo b q n =
  (logo n b q @@  nil())

let test17 n m =
  (* n<=m && 2*n = m *)
  (lelo n m) &&& (multo n (build_num 2) m)

let test27 b q r =
  (logo (build_num 68) b q r) &&& (gt1o q)

let show_int_list   = GT.(show List.ground @@ show int)
let show_intl_List = GT.(show List.logic @@ show logic @@ show int)

let _ffoo _ =
  run_exn show_int_list (-1)  qr qrh (REPR (fun q r     -> multo q r (build_num 1)                          ));
  run_exn show_int_list (-1)   q  qh (REPR (fun q       -> multo (build_num 7) (build_num 63) q             ));
  run_exn show_int_list (-1)  qr qrh (REPR (fun q r     -> divo (build_num 3) (build_num 2) q r             ));
  run_exn show_int_list (-1)   q  qh (REPR (fun q       -> logo (build_num 14) (build_num 2) (build_num 3) q));
  run_exn show_int_list (-1)   q  qh (REPR (fun q       -> expo (build_num 3) (build_num 5) q               ))

let runL n = runR (List.reify OCanren.reify) show_int_list show_intl_List n

let _freeVars =
  runL   22  qrs  qrsh (REPR (fun q r s   -> pluso q r s                                      ));
  runL   34  qrs  qrsh (REPR (fun q r s   -> multo q r s                                      ));
  runL   10   qr   qrh (REPR (fun q r     -> test17 q r                                       ));
  runL   15   qr   qrh (REPR (fun q r     -> lelo q r                                         ));
  runL  (-1)   q    qh (REPR (fun q       -> lto (build_num 5) q                              ));
  runL  (-1)   q    qh (REPR (fun q       -> lto q (build_num 5)                              ));
  runL    6 (succ qrs) qrsth (REPR (fun q r s t -> divo q r s t                                     ));
  runL    5  qrs  qrsh (REPR (fun q r s   -> test27 q r s                                     ))

*)
