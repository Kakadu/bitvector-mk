(* https://z3prover.github.io/api/html/ml/Z3.html
*)
module type TERM = sig
  type t

  val var : string -> t

  val const_s : string -> t

  val band : t -> t -> t
end

module type FORMULA = sig
  type t

  type term

  val eq : term -> term -> t

  val conj : t -> t -> t

  val not : t -> t

  val iff : t -> t -> t

  val forall : string -> t -> t
end

let bv_size = 4

let to_z3 : Z3.context -> (module TERM) * (module FORMULA) =
 fun ctx ->
  let open Z3 in
  let module T = struct
    type t = Z3.Expr.expr

    let var s = BitVector.mk_const ctx (Symbol.mk_string ctx s) bv_size

    let const n =
      Expr.mk_numeral_string ctx (Printf.sprintf "#x%X" n)
        (BitVector.mk_sort ctx bv_size)

    let const_s s = Expr.mk_numeral_string ctx s (BitVector.mk_sort ctx bv_size)

    let band l r = BitVector.mk_and ctx l r
  end in
  let module P = struct
    type t = Z3.Expr.expr

    type term = T.t

    let iff = Boolean.mk_iff ctx

    let not = Boolean.mk_not ctx

    let conj a b = Boolean.mk_and ctx [ a; b ]

    let eq = Boolean.mk_eq ctx

    let forall name f =
      let x = BitVector.mk_const ctx (Symbol.mk_string ctx name) bv_size in
      Quantifier.expr_of_quantifier
        (Quantifier.mk_forall_const ctx [ x ] f None [] [] None None)
  end in
  ((module T : TERM), (module P : FORMULA))
