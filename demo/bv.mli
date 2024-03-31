type cmp_t = LT | EQ | GT [@@deriving gt ~options:{ show; fmt }]

val int_pow : int -> int -> int

module Repr : sig
  type e = int
  type g = e OCanren.Std.List.ground
  type l = e OCanren.logic OCanren.Std.List.logic
  type injected = e OCanren.ilogic OCanren.Std.List.injected
  type n = injected

  val inj : g -> injected
  val reify : (injected, l) OCanren.Reifier.t
  val prj_exn : (injected, g) OCanren.Reifier.t
  val eq_exn : g -> g -> bool

  val g :
    ( unit,
      < show : g -> string
      ; gmap : g -> g
      ; fmt : Format.formatter -> g -> unit
      ; foldl : 'a -> g -> 'a
      ; compare : g -> g -> GT.comparison >,
      unit )
    GT.t

  val l :
    ( unit,
      < show : l -> string
      ; gmap : l -> l
      ; fmt : Format.formatter -> l -> unit
      ; compare : l -> l -> GT.comparison
      ; foldl : 'a -> l -> 'a >,
      unit )
    GT.t

  val show : g -> string
  val pp : Format.formatter -> g -> unit
  val show_logic : l -> string
  val pp_logic : Format.formatter -> l -> unit
end

module type S = sig
  open Repr
  open OCanren

  val show_binary : g -> string
  val build_num : int -> n
  val of_int : int -> g
  val inj_int : int -> injected
  val mod2 : n -> e ilogic -> goal
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
  val compare_helper : n -> n -> cmp_t OCanren.ilogic -> goal
  val forallo : n -> (n -> goal) -> goal
  val width : int
end

val create : int -> (module S)
