
type rounding =
  | Nearest_even  (** round to nearest, ties to even *)
  | Nearest_away  (** round to nearest, ties to away *)
  | Towards_zero  (** round toward zero              *)
  | Positive_inf  (** round toward positive infinity *)
  | Negative_inf  (** round toward negative infinity *)
[@@deriving sexp]

(** gfloat descriptor *)
type desc

(** [desc : ~expn_bits fraction_bits] *)
val desc : expn_bits:int -> int -> desc

module type Bignum = sig
  type t
  val of_int : width:int -> int -> t
  val to_int : t -> int
  val ones : int -> t
  val bitwidth : t -> int
  val extract : ?hi:int -> ?lo:int -> t -> t
  val zero_extend : t -> int -> t
  val ( + ) : t -> t -> t
  val ( - ) : t -> t -> t
  val ( * ) : t -> t -> t
  val ( / ) : t -> t -> t
  val ( = ) : t -> t -> bool
  val ( < ) : t -> t -> bool
  val ( lsl ) : t -> int -> t
  val ( lxor ) : t -> t -> t
  val lnot : t -> t
  val neg : t -> t
  val to_string : t -> string
  val tow : t -> Bap.Std.word
end

module Make(B : Bignum) : sig

  type t

  (** [create desc expn frac] creates gfloat from desc, signed expn
      and fraction.  *)
  val create : desc -> ?negative:bool -> expn:B.t -> B.t -> t

  (** [zero desc expn_bits prec] creates gfloat equaled to zero from
      radix, exponent bits and precision *)
  val zero : desc -> t

  (** [inf desc prec] creates positive or negative infinity from desc
      and precision *)
  val inf : ?negative:bool -> desc -> t

  (** [nan desc prec] creates nan from desc and precision. *)
  val nan : ?signaling:bool -> ?negative:bool -> ?payload:B.t -> desc -> t

  (** [is_fin x] returns true if [x] is finite number, i.e. neither nan
      nor inf *)
  val is_fin : t -> bool

  (** [is_nan x] returns true if [x] is nan *)
  val is_nan : t -> bool

  (** [is_signaling_nan x] returns true if [x] is nan and it's a
      signaling one *)
  val is_signaling_nan : t -> bool

  (** [is_quite_nan x] returns true if [x] is nan and it's a
      quite one *)
  val is_quite_nan : t -> bool

  (** [is_inf x] returns true if [x] is inf *)
  val is_inf : t -> bool

  (** [is_pos x] returns true if [x] is positive *)
  val is_pos : t -> bool

  (** [is_neg x] returns true if [x] is negative *)
  val is_neg : t -> bool

  (** [is_zero x] returns true if [x] is zero *)
  val is_zero : t -> bool

  (** [fin x] returns an exponent and fraction of [x], if
      [x] is finite number, i.e. neither infinity, nor nan *)
  val fin : t -> (B.t * B.t) option

  (** [frac x] returns a fraction of a finite number or
      a payload of a nan *)
  val frac : t -> B.t option

  (** [expn x] returns a exponent of a finite number *)
  val expn : t -> B.t option

  (** [add ~rm x y] = x + y with rounding [rm] *)
  val add : ?rm:rounding -> t -> t -> t

  (** [sub ~rm x y] = x - y with rounding [rm] *)
  val sub : ?rm:rounding -> t -> t -> t

  (** [mul ~rm x y] = x * y with rounding [rm]  *)
  val mul : ?rm:rounding -> t -> t -> t

  (** [div ~rm x y] = x / y with rounding [rm]  *)
  val div : ?rm:rounding -> t -> t -> t

  (** [sqrt x] returns a square root of [x] with rounding [rm] *)
  val sqrt : ?rm:rounding -> t -> t

  (** [neg x] inverts sign of [x]  *)
  val neg : t -> t

  (** [round ~upto x] returns a rounded [x] to a [precision]. *)
  val round : ?rm:rounding -> precision:int -> t -> t

  (** [extend x n] extends precision of [x] with [n] bits *)
  val extend : t -> int -> t

  (** [equal x y] return true if [x = y] *)
  val equal : t -> t -> bool

  (** A set of infix operators with default rounding = NearestTiesToEven *)
  module Infix : sig
    val ( + ) : t -> t -> t
    val ( - ) : t -> t -> t
    val ( * ) : t -> t -> t
    val ( / ) : t -> t -> t
    val ( = ) : t -> t -> bool
  end

end
