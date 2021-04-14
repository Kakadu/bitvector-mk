open Ctypes
open Foreign

module F = struct
  type btor = unit ptr

  let btor : btor typ = ptr void

  type bnode = unit ptr

  let bnode : bnode typ = ptr void

  type bsort = unit ptr

  let bsort : bnode typ = ptr void
end

open F

let create = foreign "boolector_new" (void @-> returning btor)

let delete = foreign "boolector_delete" (btor @-> returning void)

(* nodes *)

let implies =
  foreign "boolector_implies" (btor @-> bnode @-> bnode @-> returning bnode)

let eq = foreign "boolector_eq" (btor @-> bnode @-> bnode @-> returning bnode)

let neq = foreign "boolector_neq" (btor @-> bnode @-> bnode @-> returning bnode)

let not = foreign "boolector_not" (btor @-> bnode @-> returning bnode)

let neg = foreign "boolector_neg" (btor @-> bnode @-> returning bnode)

let redor = foreign "boolector_redor" (btor @-> bnode @-> returning bnode)

let redxor = foreign "boolector_redxor" (btor @-> bnode @-> returning bnode)

let redand = foreign "boolector_redand" (btor @-> bnode @-> returning bnode)

let xor = foreign "boolector_xor" (btor @-> bnode @-> bnode @-> returning bnode)

let xnor =
  foreign "boolector_xnor" (btor @-> bnode @-> bnode @-> returning bnode)

let and_ = foreign "boolector_and" (btor @-> bnode @-> bnode @-> returning bnode)

let or_ = foreign "boolector_or" (btor @-> bnode @-> bnode @-> returning bnode)

let add = foreign "boolector_add" (btor @-> bnode @-> bnode @-> returning bnode)

let sub = foreign "boolector_sub" (btor @-> bnode @-> bnode @-> returning bnode)

let udiv =
  foreign "boolector_udiv" (btor @-> bnode @-> bnode @-> returning bnode)

let sdiv =
  foreign "boolector_sdiv" (btor @-> bnode @-> bnode @-> returning bnode)

let urem =
  foreign "boolector_urem" (btor @-> bnode @-> bnode @-> returning bnode)

let boolector_concat =
  foreign "boolector_concat" (btor @-> bnode @-> bnode @-> returning bnode)

let cond =
  foreign "boolector_concat"
    (btor @-> bnode @-> bnode @-> bnode @-> returning bnode)

(* overflow detection *)
let uaddo =
  foreign "boolector_uaddo" (btor @-> bnode @-> bnode @-> returning bnode)

let mul = foreign "boolector_mul" (btor @-> bnode @-> bnode @-> returning bnode)

let ult = foreign "boolector_ult" (btor @-> bnode @-> bnode @-> returning bnode)

let ugt = foreign "boolector_ugt" (btor @-> bnode @-> bnode @-> returning bnode)

let ulte =
  foreign "boolector_ulte" (btor @-> bnode @-> bnode @-> returning bnode)

let ugte =
  foreign "boolector_ugte" (btor @-> bnode @-> bnode @-> returning bnode)

let slt = foreign "boolector_slt" (btor @-> bnode @-> bnode @-> returning bnode)

(* signed logical shift left *)
let sll = foreign "boolector_sll" (btor @-> bnode @-> bnode @-> returning bnode)

let srl = foreign "boolector_srl" (btor @-> bnode @-> bnode @-> returning bnode)

let sra = foreign "boolector_sra" (btor @-> bnode @-> bnode @-> returning bnode)

let slice =
  foreign "boolector_slice"
    (btor @-> bnode @-> uint32_t @-> uint32_t @-> returning bnode)

let is_bv_const_zero =
  foreign "boolector_is_bv_const_zero" (btor @-> bnode @-> returning bool)

let is_bv_const_one =
  foreign "boolector_is_bv_const_one" (btor @-> bnode @-> returning bool)

let is_bv_const_ones =
  foreign "boolector_is_bv_const_ones" (btor @-> bnode @-> returning bool)

let const = foreign "boolector_const" (btor @-> string @-> returning bnode)

let constd =
  foreign "boolector_constd" (btor @-> bsort @-> string @-> returning bnode)

let zero = foreign "boolector_zero" (btor @-> bsort @-> returning bnode)

let ones = foreign "boolector_ones" (btor @-> bsort @-> returning bnode)

let one = foreign "boolector_one" (btor @-> bsort @-> returning bnode)

let uint =
  foreign "boolector_unsigned_int"
    (btor @-> uint32_t @-> bsort @-> returning bnode)

let var = foreign "boolector_var" (btor @-> bsort @-> string @-> returning bnode)

module Sort = struct
  let bitvec =
    foreign "boolector_bitvec_sort" (btor @-> uint32_t @-> returning bsort)

  let bool_ = foreign "boolector_bool_sort" (btor @-> returning bsort)

  let delete =
    foreign "boolector_release_sort" (btor @-> bsort @-> returning void)
end
