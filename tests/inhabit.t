  $ ./run_inhabit.exe
  fun ph -> evalo bv env ph (!! true), 20 answers {
  q=(<= 0b[0001] x);
  q=(<= x 0b[0001]);
  q=(<= x 0b[0010]);
  q=(<= x 0b[0011]);
  q=(not (<= 0b[0010] x));
  q=(<= 0b[0001] (bvshl 0b[0001] x));
  q=(not (<= 0b[0011] x));
  q=(not (and (<= 0b[0001] x) ));
  q=(<= 0b[0001] (bvshl 0b[0010] x));
  q=(<= 0b[0010] (bvshl 0b[0001] x));
  q=(not (and (<= 0b[0010] x) :: _.65));
  q=(not (and (<= 0b[0001] x) :: (<= 0b[0010] x) :: _.1977));
  q=(<= 0b[0001] (bvshl 0b[0011] x));
  q=(<= 0b[0010] (bvshl 0b[0010] x));
  q=(<= 0b[0001] (bvshl x 0b[0001]));
  q=(not (and (<= 0b[0001] x) :: (<= 0b[0011] x) :: _.1977));
  q=(not (and (<= 0b[0011] x) :: _.65));
  q=(not (and (<= 0b[0001] x) (<= x 0b[0001]) ));
  q=(<= 0b[0010] (bvshl 0b[0011] x));
  q=(<= 0b[0001] (bvshl x 0b[0010]));
  }
