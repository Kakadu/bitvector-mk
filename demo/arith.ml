open Printf
open OCanren
open OCanren.Std
open Tester

let () = print_newline ()

module type S = sig
  open OCanren

  type g

  type l

  type n = (g, l) injected

  val reify : OCanren.Env.t -> n -> l

  val show : g -> string

  val show_logic : l -> string

  val build_num : int -> n

  val pluso : n -> n -> n -> goal

  (* val minuso : n -> n -> n -> goal *)

  (* val pluso : n -> n -> n -> goal *)

  (* val multo : n -> n -> n -> goal *)

  val width : int
end

let create width : (module S) =
  let module M = struct
    open OCanren

    type g = int Std.List.ground

    type l = int logic Std.List.logic

    type n = (int, int logic) OCanren.Std.List.groundi

    let reify = List.reify OCanren.reify

    let show = GT.(show List.ground @@ show int)

    let show_logic = GT.(show List.logic @@ show logic @@ show int)

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

    (* let rec build_num =
       let rec helper acc pos n =
         assert (pos <= width);
         if pos >= width then Std.list ( !! ) @@ Stdlib.List.rev acc
         else helper ((n mod 2) :: acc) (pos + 1) (n / 2)
       in
       helper [] 0 *)

    let peano_width : Std.Nat.groundi = Std.Nat.(nat (of_int width))

    (* function
       | 0                   -> nil()
       | n when n mod 2 == 0 -> (inj@@lift 0) % build_num (n / 2)
       | n                   -> (inj@@lift 1) % build_num (n / 2) *)

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
      let rec is_zero n = n === zero

      (* One is a list which head is 1 and tils is a Zero *)
      let rec is_one n = n === one

      let build_num n =
        let rec helper acc i n =
          let b = n mod 2 in
          if i >= width then acc
          else helper (Std.List.cons !!b acc) (1 + i) (n / 2)
        in
        helper (Std.List.nil ()) 0 n

      (* very costly implementation *)
      let rec poso n = n =/= zero

      let rec has_a_one n =
        conde
          [
            n === Std.List.nil () &&& failure;
            fresh (h tl)
              (n === List.cons h tl)
              (conde [ h === !!1; h === !!0 &&& has_a_one tl ]);
          ]

      let rec gt1o n =
        conde
          [
            n === List.nil () &&& failure;
            fresh (b tl)
              (n === List.cons b tl)
              (conde [ b === !!1; b === !!0 &&& gt1o tl ]);
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

    open New

    (* let is_zero q =
         let rec helper c q =
           if c >= width then failure
           else
             conde
               [
                 q === zero; fresh tl (q === List.cons !!0 tl) (helper (c + 1) tl);
               ]
         in
         helper 0 q
    *)

    let ( ! ) = ( !! )

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

    (* carry + n + m = r *)
    let rec addero extra_w d n m r =
      success
      (* &&& trace_peano extra_w "extra_w"
         &&& trace_n n "  n" &&& trace_n m "  m" &&& trace_n r "  r" *)
      &&& conde
            [
              extra_w === Std.Nat.zero &&& (r === zero);
              fresh prev_w
                (extra_w === Std.Nat.succ prev_w)
                (msg_here __LINE__)
                (conde
                   [
                     !0 === d &&& is_zero m &&& (n === r);
                     !0 === d &&& is_zero n &&& (m === r) &&& poso m;
                     !1 === d &&& is_zero m
                     &&& defer (addero extra_w !0 n one r);
                     !1 === d &&& is_zero n &&& poso m
                     &&& defer (addero extra_w !0 m one r);
                     ?&[
                         !<(!1) === n;
                         !<(!1) === m;
                         conde
                           [
                             prev_w === Nat.zero
                             &&& fresh (a c) (!<a === r)
                                   (full_addero d !1 !1 a c);
                             prev_w =/= Nat.zero
                             &&& fresh (a c)
                                   (a %< c === r)
                                   (full_addero d !1 !1 a c);
                           ];
                       ];
                     one === n &&& gen_addero extra_w d n m r;
                     one === m &&& gt1o n &&& gt1o r
                     &&& defer (addero extra_w d one n r);
                     gt1o n &&& gen_addero extra_w d n m r;
                   ]);
            ]

    and gen_addero prev_w d n m r =
      success
      &&& trace_peano prev_w "prev_w"
      &&& trace_n n "  n" &&& trace_n m "  m" &&& trace_n r "  r"
      &&& conde
            [
              prev_w === Std.Nat.zero &&& (r === zero);
              fresh (a b c e x y z ppp)
                (Nat.s ppp === prev_w)
                (a % x === n)
                (* (msg_here __LINE__) *)
                (b % y === m)
                (* (msg_here __LINE__)  *)
                (poso y)
                (c % z === r)
                (* (msg_here __LINE__)  *)
                (poso z)
                (* (msg_here __LINE__) *)
                (full_addero d a b c e)
                (* (msg_here __LINE__)  *)
                (addero ppp e x y z);
            ]

    (* n + m = k *)
    let pluso n m k = addero peano_width !0 n m k

    (* n - m = k *)
    let minuso n m k = pluso m k n

    (*
    let rec bound_multo q p n m =
      (* Что-то про длину произведения p = n*m
         Проверялка того, что в произведение не попали нули в
         старших разрядах? ???  WTFo
      *)
      conde
        [
          List.nullo q &&& poso p;
          fresh (x y z) (List.tlo q x) (List.tlo p y)
            (conde
               [
                 List.nullo n &&& List.tlo m z &&& bound_multo x y z n;
                 List.tlo n z &&& bound_multo x y z m;
               ]);
        ]

    let rec multo n m p =
      conde
        [
          (*  0 * m = 0 *)
          nil () === n &&& (nil () === p);
          poso n &&& (nil () === m) &&& (nil () === p);
          !<(!1) === n &&& poso m &&& (m === p);
          (* 1 * m = m, m > 1 *)
          gt1o n &&& (!<(!1) === m) &&& (n === p);
          (* 2*x * y = 2*z  iff  x*y=z *)
          fresh (x z)
            (!0 % x === n)
            (poso x)
            (!0 % z === p)
            (poso z) (gt1o m) (multo x m z);
          (* swap to reduce into previous case *)
          fresh (x y)
            (!1 % x === n)
            (poso x)
            (!0 % y === m)
            (poso y) (multo m n p);
          fresh (x y)
            (!1 % x === n)
            (poso x)
            (!1 % y === m)
            (poso y) (odd_multo x n m p);
        ]

    and odd_multo x n m p =
      (* n * m = (2*x+1) * m = (x*m)*2 + m = p *)
      fresh q (bound_multo q p n m)
        (* что-то про длину произведения...*)
        (multo x m q)
        (pluso (!0 % q) m p)
        *)
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

let _freeVars =
  let (module M) = create 2 in
  let open M in
  let runL n = runR M.reify show show_logic n in

  (* runL   22  qrs  qrsh (REPR (fun q r s   -> pluso q r s)); *)
  (* runL (-1) qr qrh (REPR (fun q r -> pluso q r (build_num 7))); *)
  (* runL (-1) q qh (REPR (fun q -> pluso (build_num 3) (build_num 0) q));
     runL (-1) q qh (REPR (fun q -> pluso (build_num 3) (build_num 1) q));
     runL (-1) q qh (REPR (fun q -> pluso (build_num 1) (build_num 2) q)); *)
  ()

let _freeVars =
  let (module M) = create 2 in
  let open M in
  let runL n = runR M.reify show show_logic n in

  (* runL (-1) q qh (REPR (fun q -> pluso q (build_num 3) (build_num 1))); *)
  runL (-1) q qh (REPR (fun q -> pluso (build_num 3) q (build_num 1)));
  (* runL (-1) q qh (REPR (fun q -> pluso (build_num 3) (build_num 2) q)); *)
  ()

(*
let __ _freeVars =
  let (module M) = create_peano 2 in
  let open M in
  let runL n = runR M.reify show show_logic n in

  (* runL   22  qrs  qrsh (REPR (fun q r s   -> pluso q r s)); *)
  (* runL (-1) qr qrh (REPR (fun q r -> pluso q r (build_num 7)));
     runL (-1) q qh (REPR (fun q -> pluso (build_num 15) (build_num 0) q)); *)
  runL (-1) q qh (REPR (fun q -> pluso (build_num 1) (build_num 1) q));
  (* runL (-1) q qh (REPR (fun q -> pluso (build_num 1) (build_num 2) q)); *)
  () *)

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
