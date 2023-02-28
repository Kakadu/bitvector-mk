  $ ./run_inhabit.exe
  fun ph ->
    let open Std in
      fresh (env rez) (env === (Std.List.list ["x" ** 1; "y" ** 1]))
        (rez === (!! true)) (evalo bv env ph rez), 20 answers {
  q=(<= x 0b[0001]);
  q=(<= x y);
  q=(<= x 0b[0010]);
  q=(<= 0b[0001] x);
  q=(<= x 0b[0011]);
  q=(<= 0b[0001] y);
  q=(<= y x);
  q=(<= y 0b[0001]);
  q=(<= y 0b[0010]);
  q=(<= y 0b[0011]);
  q=(and (<= x 0b[0001]) (<= x 0b[0010]) nil);
  q=(<= x (bvshl x x));
  q=(and (<= x 0b[0001]) (<= x y) nil);
  q=(<= x (bvshl x 0b[0001]));
  q=(not (and (not (<= x 0b[0001])) :: _.92 :: _.93));
  q=(<= 0b[0001] (bvshl x x));
  q=(not (<= 0b[0010] x));
  q=(and (<= x y) (<= y x) nil);
  q=(and (<= x 0b[0001]) (<= x 0b[0010]) (<= x 0b[0011]) nil);
  q=(<= x (bvshl x y));
  }
