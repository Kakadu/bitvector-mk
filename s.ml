(* https://z3prover.github.io/api/html/ml/Z3.html
*)
module type TERM = sig
  type t

  val var : string -> t

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

    let var s = BitVector.mk_const ctx (Z3.Symbol.mk_string ctx s) bv_size

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
      (* NOT TESTED *)
      (* use quantifier module *)
      failwith "not implemented"
  end in
  ((module T : TERM), (module P : FORMULA))
