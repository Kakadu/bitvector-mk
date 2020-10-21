(* https://z3prover.github.io/api/html/ml/Z3.html
*)
module type TERM = sig
  type t

  val var : string -> t

  val const_s : string -> t

  val band : t -> t -> t

  val add : t -> t -> t

  val sub : t -> t -> t

  val mul : t -> t -> t

  val shl : t -> t -> t

  val lshr : t -> t -> t
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
      (* Format.printf "Creating const #x%X\n%!" n;
         print_int n;
         print_newline (); *)
      Expr.mk_numeral_string ctx (Printf.sprintf "#x%X" n)
        (BitVector.mk_sort ctx bv_size)

    let const_s s =
      (* Format.printf "mk_numeral_string `%s`\n%!" s; *)
      Expr.mk_numeral_string ctx s (BitVector.mk_sort ctx bv_size)

    let band = BitVector.mk_and ctx

    let shl = BitVector.mk_shl ctx

    let lshr = BitVector.mk_lshr ctx

    let add = BitVector.mk_add ctx

    let sub = BitVector.mk_sub ctx

    let mul = BitVector.mk_mul ctx
  end in
  (module T : TERM with type t = T.t)

let z3_of_formula ctx :
    (module FORMULA with type t = Z3.Expr.expr and type term = Z3.Expr.expr) =
  let module P = struct
    open Z3

    type t = Z3.Expr.expr

    type term = Z3.Expr.expr

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
  (module P : FORMULA with type t = Z3.Expr.expr and type term = Z3.Expr.expr)

let to_z3 :
    Z3.context ->
    (module TERM with type t = Z3.Expr.expr)
    * (module FORMULA with type t = Z3.Expr.expr and type term = Z3.Expr.expr) =
 fun ctx -> (z3_of_term ctx, z3_of_formula ctx)

module type INPUT = functor (T : TERM) (P : FORMULA with type term = T.t) -> sig
  val info : string

  val ph : P.t
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

    let band = add

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
    let info = "example1"

    let ph =
      P.(
        conj
          (forall "y" (eq (T.var "y") (T.var "y")))
          (eq (T.var "a") T.(band (T.var "a") (T.var "a"))))
  end in
  (module M : INPUT)

let ex2 =
  let module M (T : TERM) (P : FORMULA with type term = T.t) = struct
    let info = "example1"

    let ph = P.(exists "q" (eq T.(add (var "q") (var "q")) (T.var "a")))
  end in
  (module M : INPUT)

let ex3 =
  let module M (T : TERM) (P : FORMULA with type term = T.t) = struct
    let info = "example3"

    let ph =
      P.(
        exists "y"
          (conj
             (le T.(const_s "0") T.(var "y"))
             (eq (T.var "a")
                T.(shl (add (const_s "1") (const_s "1")) (var "y")))))
  end in
  (module M : INPUT)

let ex4 =
  let module M (T : TERM) (P : FORMULA with type term = T.t) = struct
    let info = "example4 about logarithm"

    let ph = P.(exists "x" T.(lt (var "a") (shl (var "b") (var "x"))))

    (* Идея: выкинуть младшие разряды из a и проверить, что b<>0 и a<>max_int
        unsigned long long remove_trailing_zeroes(unsigned long long v) {
          return v ? v / (-v & v) : v;
        }
    *)
  end in
  (module M : INPUT)

(* https://is.muni.cz/th/ovulj/teze.pdf *)
(* 3<a ∧ ∀x (¬(a = 2*x)) *)
