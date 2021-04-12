module Repr : sig
  open OCanren

  type e = int

  type g = e OCanren.Std.List.ground

  type l = e OCanren.logic OCanren.Std.List.logic

  type n = (g, l) OCanren.injected

  type injected = n

  val inj : g -> injected

  val reify : OCanren.Env.t -> n -> l

  val prjc_exn : Env.t -> injected -> g

  val eq_exn : g -> g -> bool

  val g :
    ( unit,
      < show : g -> string
      ; gmap : g -> g
      ; fmt : Format.formatter -> g -> unit >,
      unit )
    GT.t

  val l :
    ( unit,
      < show : l -> string
      ; gmap : l -> l
      ; fmt : Format.formatter -> l -> unit
      ; foldl : 'a -> l -> 'a >,
      unit )
    GT.t

  val show : g -> string

  val show_binary : g -> string

  val show_logic : l -> string
end

module type S = sig
  open Repr
  open OCanren

  val show_binary : g -> string

  val build_num : int -> n

  val of_int : int -> g

  val mod2 : n -> (e, e logic) injected -> goal

  val mul2 : n -> n -> goal

  val addo : n -> n -> n -> goal
  (*
  val gen_addero : int -> (int, int logic) OCanren.injected ->
      n -> n -> n -> goal

  val addero : int -> (int, int logic) OCanren.injected ->
      n -> n -> n -> goal
 *)

  val subo : n -> n -> n -> goal

  val multo : n -> n -> n -> goal

  val shiftl1 : n -> n -> goal

  val lshiftr1 : n -> n -> goal

  val ashiftr1 : n -> n -> goal

  val ashiftro : n -> n -> n -> goal

  val lshiftro : n -> n -> n -> goal

  val shiftlo : n -> n -> n -> goal

  val rotl : n -> n -> goal

  val rotr : n -> n -> goal

  val loro : n -> n -> n -> goal

  val lando : n -> n -> n -> goal

  val lto : n -> n -> goal

  val leo : n -> n -> goal

  val width : int
end

val create : int -> (module S)
