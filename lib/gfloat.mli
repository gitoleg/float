open Core_float.Types

type rmode


module Make(B : Core_float.Core) : sig
  type 'a t = 'a knowledge

  type 'a number = 'a bitv value knowledge
  type nonrec bit = bit value knowledge

  type ('a, 'b) desc
  type ('a, 'b) float

  val rne : rmode (** round to nearest, ties to even *)
  val rna : rmode (** round to nearest, ties to away *)
  val rtp : rmode (** round toward positive infinity *)
  val rtn : rmode (** round toward negative infinity *)
  val rtz : rmode (** round toward zero              *)

  val finite : ('e,'k) desc -> bit -> 'e number -> 'k number -> ('e, 'k) float

  val pinf : ('e,'k) desc -> ('e,'k) float
  val ninf : ('e,'k) desc -> ('e,'k) float
  val snan : ('e,'k) desc -> 'k bitv value t -> ('e,'k) float
  val qnan : ('e,'k) desc -> 'k bitv value t -> ('e,'k) float

  val exponent    : ('e,'k) float -> 'e bitv value t
  val coefficient : ('e,'k) float -> 'k bitv value t
  val fsign       : ('e,'k) float -> bit

  val is_finite : ('e,'k) float -> bit
  val is_fzero  : ('e,'k) float -> bit
  val is_pinf   : ('e,'k) float -> bit
  val is_ninf   : ('e,'k) float -> bit
  val is_snan   : ('e,'k) float -> bit
  val is_qnan   : ('e,'k) float -> bit

  val fadd : rmode -> ('e,'k) float -> ('e,'k) float -> ('e,'k) float
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
