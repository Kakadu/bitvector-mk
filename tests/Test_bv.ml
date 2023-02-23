open OCanren
module BV = (val Bv.create 4)

let checkBV :
    ?v:bool -> (Bv.Repr.injected -> goal) -> expected:Bv.Repr.g -> bool =
 fun ?(v = false) goal ~expected ->
  let stream = OCanren.run one goal Fun.id in
  match OCanren.Stream.take ~n:2 stream with
  | [] ->
      if v then Format.printf "Stream is empty\n%!";
      false
  | [ x ] ->
      let ans = x#reify Bv.Repr.prj_exn in
      let b = Bv.Repr.eq_exn ans expected in
      if (not b) && v then Format.printf "Wrong answer\n%!";
      b
  | _ :: _ :: _ ->
      if v then Format.printf "Too many answers\n%!";
      false

let test_addo a b ab =
  checkBV BV.(addo (build_num a) (build_num b)) ~expected:BV.(of_int ab)

let%test _ = test_addo 1 1 2
let%test _ = test_addo 1 0 1
let%test _ = test_addo 0 1 1

let test_multo a b ab =
  checkBV ~v:true
    BV.(multo (build_num a) (build_num b))
    ~expected:BV.(of_int ab)

let%test _ = test_multo 0 1 0
let%test _ = test_multo 1 0 0
let%test _ = test_multo 1 1 1
let%test _ = test_multo 4 4 (16 mod 16)

let test_shiftl a b ab =
  checkBV ~v:true
    BV.(shiftlo (build_num a) (build_num b))
    ~expected:BV.(of_int ab)

let%test _ = test_shiftl 0 1 0
let%test _ = test_shiftl 1 0 1
let%test _ = test_shiftl 1 1 2
let%test _ = test_shiftl 4 4 0
