(* https://z3prover.github.io/api/html/ml/Z3.html
*)

module type TERM = sig
  type t

  val var : string -> t

  val const_s : string -> t

  val land_ : t -> t -> t

  val lor_ : t -> t -> t

  val add : t -> t -> t

  val sub : t -> t -> t

  val mul : t -> t -> t

  val shl : t -> t -> t

  val lshr : t -> t -> t
end

module type RICH_TERM = sig
  include TERM

  val ( + ) : t -> t -> t

  val ( * ) : t -> t -> t

  val shl1 : t -> t

  val lshr1 : t -> t

  (* TODO: power *)
  val i : int -> t
end

module EnrichTerm (T : TERM) : RICH_TERM with type t = T.t = struct
  include T

  let ( + ) = add

  let ( * ) = mul

  let i n = const_s (string_of_int n)

  let shl1 x = shl x (i 1)

  let lshr1 x = lshr x (i 1)
end

module type FORMULA = sig
  type t

  type term

  val eq : term -> term -> t

  val lt : term -> term -> t

  val le : term -> term -> t

  val conj : t -> t -> t

  val disj : t -> t -> t

  val not : t -> t

  val iff : t -> t -> t

  val forall : string -> t -> t

  val exists : string -> t -> t
end

module type RICH_FORMULA = sig
  include FORMULA

  val ( == ) : term -> term -> t

  val ( < ) : term -> term -> t

  val ( > ) : term -> term -> t

  val ( <= ) : term -> term -> t

  val ( && ) : t -> t -> t

  val ( || ) : t -> t -> t

  val ( <=> ) : t -> t -> t
end

module EnrichFormula (F : FORMULA) :
  RICH_FORMULA with type t = F.t and type term = F.term = struct
  include F

  let ( == ) = eq

  let ( < ) = lt

  let ( > ) a b = lt b a

  let ( <= ) = le

  let ( <=> ) = iff

  let ( || ) = disj

  let ( && ) = conj
end

type z3_expr = Z3.Expr.expr

module type FORMULA_Z3 = FORMULA with type t = z3_expr and type term = z3_expr

module type TERM_Z3 = TERM with type t = z3_expr

let bv_size = 4

let z3_of_term ctx : (module TERM_Z3) =
  let module T = struct
    open Z3

    type t = Z3.Expr.expr

    let var s = BitVector.mk_const ctx (Symbol.mk_string ctx s) bv_size

    let const n =
      Expr.mk_numeral_string ctx (Printf.sprintf "#x%X" n)
        (BitVector.mk_sort ctx bv_size)

    let const_s s = Expr.mk_numeral_string ctx s (BitVector.mk_sort ctx bv_size)

    let land_ = BitVector.mk_and ctx

    let lor_ = BitVector.mk_or ctx

    let shl = BitVector.mk_shl ctx

    let lshr = BitVector.mk_lshr ctx

    let add = BitVector.mk_add ctx

    let sub = BitVector.mk_sub ctx

    let mul = BitVector.mk_mul ctx
  end in
  (module T : TERM with type t = T.t)

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

let to_z3 :
    Z3.context ->
    (module TERM with type t = z3_expr)
    * (module FORMULA with type t = z3_expr and type term = z3_expr) =
 fun ctx -> (z3_of_term ctx, z3_of_formula ctx)

module type INPUT = functor (T : TERM) (P : FORMULA with type term = T.t) -> sig
  val info : string

  val ph : P.t

  (* hardcoded predefined answer *)
  val answer : P.t option
end

module SS = Set.Make (String)

let freevars m =
  let module T = struct
    type t = SS.t

    let add = SS.union

    let sub = add

    let mul = add

    let shl = add

    let lshr = add

    let land_ = add

    let lor_ = add

    let const_s _ = SS.empty

    let var = SS.singleton
  end in
  let module P = struct
    type t = SS.t

    type term = t

    let exists v t = SS.remove v t

    let forall = exists

    let iff = SS.union

    let eq = iff

    let not = Fun.id

    let conj = iff

    let disj = iff

    let le = iff

    let lt = iff
  end in
  let (module M : INPUT) = m in
  let module R = M (T) (P) in
  R.ph

let ex1 =
  let module M (T : TERM) (P : FORMULA with type term = T.t) = struct
    module P = EnrichFormula (P)
    module T = EnrichTerm (T)

    let info = "example1: (forall y. y=y) && (a = a&a)"

    let ph =
      P.(
        T.(
          conj
            (forall "y" (var "y" == var "y"))
            (var "a" == land_ (var "a") (var "a"))))

    let answer = None
  end in
  (module M : INPUT)

let ex2 =
  let module M (T : TERM) (P : FORMULA with type term = T.t) = struct
    module P = EnrichFormula (P)
    module T = EnrichTerm (T)

    let info = "example1"

    let ph = P.(T.(exists "q" (var "q" + var "q" == var "a")))

    let answer = None
  end in
  (module M : INPUT)

let ex3 =
  let module M (T : TERM) (P : FORMULA with type term = T.t) = struct
    module P = EnrichFormula (P)
    module T = EnrichTerm (T)

    let info = "example3: exists y. (0<=y) && (a = (1+1) << y)"

    let ph =
      P.(
        exists "y"
          T.(
            const_s "0" <= var "y"
            && var "a" == shl (const_s "1" + const_s "1") (var "y")))

    let answer = None
  end in
  (module M : INPUT)

let ex4 =
  let module M (T : TERM) (P : FORMULA with type term = T.t) = struct
    module P = EnrichFormula (P)
    module T = EnrichTerm (T)

    let info = "example4 about logarithm"

    let ph = P.(exists "x" T.(lt (var "a") (shl (var "b") (var "x"))))

    let answer =
      let open P in
      let a = T.var "a" in
      let ph0 = T.var "b" <= a in
      let ph1 = T.(shl (var "b") (T.const_s "1") <= a) in
      let ph2 = T.(shl (var "b") (T.const_s "2") <= a) in
      let ph3 = T.(shl (var "b") (T.const_s "3") <= a) in
      Some P.(not (ph0 && ph1 && ph2 && ph3))
    (*
    let answer =
      let open P in
      let a = T.var "a" in
      let ph1 = not T.(shl (var "b") (T.const_s "1") <= a) in
      let ph2 = not T.(shl (var "b") (T.const_s "2") <= a) in
      let ph3 = not T.(shl (var "b") (T.const_s "3") <= a) in
      Some P.(T.((not (T.var "b" <= a)) && ph1 && ph2 && ph3)) *)
  end in
  (module M : INPUT)

let ex5 =
  let module M (T : TERM) (P : FORMULA with type term = T.t) = struct
    module P = EnrichFormula (P)
    module T = EnrichTerm (T)

    let info = "example5"

    (* https://is.muni.cz/th/ovulj/teze.pdf *)
    (* 3<a ∧ ∀x (¬(a = 2*x)) *)
    let ph =
      P.(
        conj
          (T.const_s "3" < T.var "a")
          (forall "x" @@ not T.(var "a" == const_s "2" * var "x")))

    let answer = None
  end in
  (module M : INPUT)

let ex6 =
  let module M (T : TERM) (P : FORMULA with type term = T.t) = struct
    let info = "example6: (forall x . x=x) && (x+x+x+x+x > y+y)"

    module P = EnrichFormula (P)
    module T = EnrichTerm (T)

    let ph =
      let x = T.var "x" in
      let y = T.var "y" in
      let head = P.(forall "x" T.(x == x)) in
      let tail = P.(T.(x + x + x + x + x > y + y)) in
      P.(head && tail)

    let answer = None
  end in
  (module M : INPUT)

let ex7 =
  let module M (T : TERM) (P : FORMULA with type term = T.t) = struct
    let info = "example6: (forall x . x=x) && (x+x+x+x = y)"

    (*expected answer: x << 1 << 1 > y *)
    module P = EnrichFormula (P)
    module T = EnrichTerm (T)

    let ph =
      let x = T.var "x" in
      let y = T.var "y" in
      let head = P.(forall "x" T.(x == x)) in
      let tail = P.(T.(x + x + x + x == y)) in
      P.(head && tail)

    let answer = None
  end in
  (module M : INPUT)
