open OCanren

module type S = sig
  type e = int

  type g = e OCanren.Std.List.ground

  type l = e OCanren.logic OCanren.Std.List.logic

  type n = (g, l) OCanren.injected

  (* type injected = n *)

  val reify : OCanren.Env.t -> n -> l

  val show : g -> string

  val show_binary : g -> string

  val show_logic : l -> string

  val build_num : int -> n

  val mod2 : n -> (e, e logic) injected -> goal

  val mul2 : n -> n -> goal

  val pluso : n -> n -> n -> goal

  val minuso : n -> n -> n -> goal

  val multo : n -> n -> n -> goal

  val rotl : n -> n -> goal

  val rotr : n -> n -> goal

  val shiftl : n -> n -> goal

  val lshiftr : n -> n -> goal

  val width : int
end

val create : int -> (module S)
