  $ ./run_inhabit.exe
  fun ph ->
    fresh (env rez) (env === (Std.list Fun.id ["x" ** 1; "y" ** 1]))
      (rez === (!! true)) (evalo bv env ph rez), 20 answers {
  q=(<= 0b[0001] x);
  q=(<= x 0b[0001]);
  q=(<= x 0b[0001]);
  q=(<= 0b[0001] y);
  q=(<= 0b[0001] y);
  q=(<= 0b[0001] y);
  q=(<= 0b[0001] y);
  q=(<= x y);
  q=(<= x y);
  q=(<= x y);
  q=(<= x y);
  q=(<= x y);
  q=(<= x y);
  q=(<= x y);
  q=(<= x y);
  q=(<= x y);
  q=(<= x y);
  q=(<= x y);
  q=(<= x y);
  q=(<= x y);
  }
