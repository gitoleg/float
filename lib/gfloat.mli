open Bap_knowledge
open Bap_core_theory

module Make(B : Theory.Basic) : sig

  type 'a t = 'a knowledge

  val finite : ('e,'k) float sort -> bit value t ->
               'e bitv value t -> 'k bitv value t ->
               ('e,'k) float value t

  val pinf : ('e,'k) float sort -> ('e,'k) float value t
  val ninf : ('e,'k) float sort -> ('e,'k) float value t
  val snan : ('e,'k) float sort -> 'k bitv value t -> ('e,'k) float value t
  val qnan : ('e,'k) float sort -> 'k bitv value t -> ('e,'k) float value t

  val exponent    : ('e,'k) float value t -> 'e bitv value t
  val significand : ('e,'k) float value t -> 'k bitv value t
  val fsign       : ('e,'k) float value t -> bit value t

  val is_finite : ('e,'k) float value t -> bit value t
  val is_fzero  : ('e,'k) float value t -> bit value t
  val is_pinf   : ('e,'k) float value t -> bit value t
  val is_ninf   : ('e,'k) float value t -> bit value t
  val is_snan   : ('e,'k) float value t -> bit value t
  val is_qnan   : ('e,'k) float value t -> bit value t

  val fadd    : rmode value t -> ('e,'k) float value t -> ('e,'k) float value t -> ('e,'k) float value t

end

(*
  (** [sub ~rm x y] = x - y with rmode [rm] *)
  val sub : ?rm:rmode -> t -> t -> t

  (** [mul ~rm x y] = x * y with rmode [rm]  *)
  val mul : ?rm:rmode -> t -> t -> t

  (** [div ~rm x y] = x / y with rmode [rm]  *)
  val div : ?rm:rmode -> t -> t -> t

  (** [sqrt x] returns a square root of [x] with rmode [rm] *)
  val sqrt : ?rm:rmode -> t -> t

  (** [neg x] inverts sign of [x]  *)
  val neg : t -> t

  (** [round ~upto x] returns a rounded [x] to a [precision]. *)
  val round : ?rm:rmode -> precision:int -> t -> t

  (** [extend x n] extends precision of [x] with [n] bits *)
  val extend : t -> int -> t

  (** [equal x y] return true if [x = y] *)
  val equal : t -> t -> bool

  (** A set of infix operators with default rmode = NearestTiesToEven *)
  module Infix : sig
    val ( + ) : t -> t -> t
    val ( - ) : t -> t -> t
    val ( * ) : t -> t -> t
    val ( / ) : t -> t -> t
    val ( = ) : t -> t -> bool
  end
 *)
(* end *)
