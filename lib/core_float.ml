open Bap.Std

module Types = struct
  module Knowledge = struct
    type 'a t = 'a
  end

  type 'a var
  type 'a sort
  type 'a err
  type 'a value
  type 'a bitv
  type bit
  type data
  type ctrl
  type ('a,'b) mem

  type ('b,'e,'k) float

  type 'a knowledge = 'a Knowledge.t

  module Sort = struct
    let size : 'a sort -> int = fun s ->
      Printf.eprintf "ready to fail!";
      42
  end
end

open Types

module type Basic = sig
  type 'a t = 'a Knowledge.t

  val sort : 'a value t -> 'a sort
  val int : 'a bitv sort -> word -> 'a bitv value t
  val b0 : bit value t
  val b1 : bit value t

  val inv : bit value t -> bit value t
  val and_ : bit value t -> bit value t -> bit value t
  val or_ : bit value t -> bit value t -> bit value t

  val msb : 'a bitv value t -> bit value t
  val lsb : 'a bitv value t -> bit value t

  (* arithmetics *)
  val neg  : 'a bitv value t -> 'a bitv value t
  val not    : 'a bitv value t -> 'a bitv value t
  val add  : 'a bitv value t -> 'a bitv value t -> 'a bitv value t
  val sub  : 'a bitv value t -> 'a bitv value t -> 'a bitv value t
  val mul  : 'a bitv value t -> 'a bitv value t -> 'a bitv value t
  val div  : 'a bitv value t -> 'a bitv value t -> 'a bitv value t
  val sdiv : 'a bitv value t -> 'a bitv value t -> 'a bitv value t

  val modulo : 'a bitv value t -> 'a bitv value t -> 'a bitv value t
  val smodulo : 'a bitv value t -> 'a bitv value t -> 'a bitv value t

  (* bitwise operations *)
  val logand : 'a bitv value t -> 'a bitv value t -> 'a bitv value t
  val logor  : 'a bitv value t -> 'a bitv value t -> 'a bitv value t
  val logxor  : 'a bitv value t -> 'a bitv value t -> 'a bitv value t

  val shiftr : bit value t -> 'a bitv value t -> 'b bitv value t -> 'a bitv value t
  val shiftl : bit value t -> 'a bitv value t -> 'b bitv value t -> 'a bitv value t

  val ite : bit value t -> 'a value t -> 'a value t -> 'a value t
  val sle : 'a bitv value t -> 'a bitv value t -> bit value t
  val ule : 'a bitv value t -> 'a bitv value t -> bit value t

  val cast : 'a bitv sort -> bit value t -> 'b bitv value t -> 'a bitv value t

  val concat : 'a bitv sort -> 'b bitv value t list -> 'a bitv value t


end

module type Core = sig
  include Basic

  val one  : 'a bitv sort -> 'a bitv value t
  val is_one : 'a bitv value t -> bit value t
  val zero : 'a bitv sort -> 'a bitv value t
  val is_zero  : 'a bitv value t -> bit value t
  val non_zero : 'a bitv value t -> bit value t

  val succ : 'a bitv value t -> 'a bitv value t
  val pred : 'a bitv value t -> 'a bitv value t

  val nsucc : 'a bitv value t -> int -> 'a bitv value t
  val npred : 'a bitv value t -> int -> 'a bitv value t


  val high : 'a bitv sort -> 'b bitv value t -> 'a bitv value t
  val low  : 'a bitv sort -> 'b bitv value t -> 'a bitv value t
  val signed : 'a bitv sort -> 'b bitv value t -> 'a bitv value t
  val unsigned  : 'a bitv sort -> 'b bitv value t -> 'a bitv value t
  val extract : 'a bitv sort -> 'b bitv value t -> 'b bitv value t -> _ bitv value t -> 'a bitv value t

  (** [loadw s dir mem key] loads consecutive words from locations
      [key], [succ key], [succ ... (succ key)] into the output
      bitvector of the given sort [s] until enough words is read
      to fill the whole word. The [dir] parameter specifies the order
      in which the read words are layed out in the output word, with
      [1] corresponding to the direct order (aka Big Endian) and [0]
      corresponds to the reversed order (aka Little Endian).
  *)
  val loadw : 'c bitv sort -> bit value t ->
    ('a, _) mem value t -> 'a bitv value t -> 'c bitv value t

  val storew : bit value t ->
    ('a, 'b) mem value t -> 'a bitv value t -> 'c bitv value t ->
    ('a, 'b) mem value t

  val arshift : 'a bitv value t -> 'b bitv value t -> 'a bitv value t
  val rshift : 'a bitv value t -> 'b bitv value t -> 'a bitv value t
  val lshift : 'a bitv value t -> 'b bitv value t -> 'a bitv value t

  val eq  : 'a bitv value t -> 'a bitv value t -> bit value t
  val neq : 'a bitv value t -> 'a bitv value t -> bit value t
  val slt : 'a bitv value t -> 'a bitv value t -> bit value t
  val ult : 'a bitv value t -> 'a bitv value t -> bit value t
  val sgt : 'a bitv value t -> 'a bitv value t -> bit value t
  val ugt : 'a bitv value t -> 'a bitv value t -> bit value t
  val sge : 'a bitv value t -> 'a bitv value t -> bit value t
  val uge : 'a bitv value t -> 'a bitv value t -> bit value t

end


module type Basic_FP = sig
  type 'a t = 'a knowledge
  type 'a value
  type 'a eff
  type rmode

  val floats : int -> 'e bitv sort -> 'k bitv sort -> ('b,'e,'k) float sort
  val fradix : ('b,'e,'k) float sort -> int
  val fesort : ('b,'e,'k) float sort -> 'e bitv sort
  val fksort : ('b,'e,'k) float sort -> 'k bitv sort

  val rne : rmode
  val rna : rmode
  val rtp : rmode
  val rtn : rmode
  val rtz : rmode

  val rmode : rmode -> rmode value t

  val finite : ('b,'e,'k) float sort -> bit t ->
    'e bitv value t -> 'k bitv value t ->
    ('b,'e,'k) float value t

  val pinf : ('b,'e,'k) float sort -> ('b,'e,'k) float value t
  val ninf : ('b,'e,'k) float sort -> ('b,'e,'k) float value t
  val snan : ('b,'e,'k) float sort -> 'x bitv value t -> ('b,'e,'k) float value t
  val qnan : ('b,'e,'k) float sort -> 'x bitv value t -> ('b,'e,'k) float value t

  val exponent    : ('b,'e,'k) float value t -> 'e bitv value t
  val coefficient : ('b,'e,'k) float value t -> 'k bitv value t
  val fsign       : ('b,'e,'k) float value t -> bit value t

  val is_finite : ('b,'e,'k) float value t -> bit value t
  val is_fzero  : ('b,'e,'k) float value t -> bit value t
  val is_pinf   : ('b,'e,'k) float value t -> bit value t
  val is_ninf   : ('b,'e,'k) float value t -> bit value t
  val is_snan   : ('b,'e,'k) float value t -> bit value t
  val is_qnan   : ('b,'e,'k) float value t -> bit value t

  val cast_float  : ('b,'e,'k) float sort  -> rmode value t -> 'a bitv value t -> ('b,'e,'k) float value t
  val cast_sfloat : ('b,'e,'k) float sort -> rmode value t -> 'a bitv value t -> ('b,'e,'k) float value t
  val cast_int    : 'a bitv sort -> rmode value t -> ('b,'e,'k) float value t -> 'a bitv value t

  val fneg    : ('b,'e,'k) float value t -> ('b,'e,'k) float value t
  val fabs    : ('b,'e,'k) float value t -> ('b,'e,'k) float value t

  val fadd    : rmode value t -> ('b,'e,'k) float value t -> ('b,'e,'k) float value t -> ('b,'e,'k) float value t
  val fsub    : rmode value t -> ('b,'e,'k) float value t -> ('b,'e,'k) float value t -> ('b,'e,'k) float value t
  val fmul    : rmode value t -> ('b,'e,'k) float value t -> ('b,'e,'k) float value t -> ('b,'e,'k) float value t
  val fdiv    : rmode value t -> ('b,'e,'k) float value t -> ('b,'e,'k) float value t -> ('b,'e,'k) float value t
  val sqrt       : rmode value t -> ('b,'e,'k) float value t -> ('b,'e,'k) float value t -> ('b,'e,'k) float value t
  val fmodulo : rmode value t -> ('b,'e,'k) float value t -> ('b,'e,'k) float value t -> ('b,'e,'k) float value t
  val fmad    : rmode value t -> ('b,'e,'k) float value t -> ('b,'e,'k) float value t -> ('b,'e,'k) float value t -> ('b,'e,'k) float value t

  val fround   : rmode value t -> ('b,'e,'k) float value t -> ('b,'e,'k) float value t
  val fconvert : rmode value t -> ('b,'e,'k) float sort -> (_,_,_) float value t -> ('b,'e,'k) float value t

  val fsucc  : ('b,'e,'k) float value t -> ('b,'e,'k) float value t
  val fpred  : ('b,'e,'k) float value t -> ('b,'e,'k) float value t
  val forder : ('b,'e,'k) float value t -> ('b,'e,'k) float value t -> bit value t
end

module type Core_FP = sig
  include Basic_FP
  val exp      : rmode value t -> ('b,'e,'k) float value t -> ('b,'e,'k) float value t
  val expm1    : rmode value t -> ('b,'e,'k) float value t -> ('b,'e,'k) float value t
  val exp2     : rmode value t -> ('b,'e,'k) float value t -> ('b,'e,'k) float value t
  val exp2m1   : rmode value t -> ('b,'e,'k) float value t -> ('b,'e,'k) float value t
  val exp10    : rmode value t -> ('b,'e,'k) float value t -> ('b,'e,'k) float value t
  val exp10m1  : rmode value t -> ('b,'e,'k) float value t -> ('b,'e,'k) float value t
  val log      : rmode value t -> ('b,'e,'k) float value t -> ('b,'e,'k) float value t
  val log2     : rmode value t -> ('b,'e,'k) float value t -> ('b,'e,'k) float value t
  val log10    : rmode value t -> ('b,'e,'k) float value t -> ('b,'e,'k) float value t
  val logp1    : rmode value t -> ('b,'e,'k) float value t -> ('b,'e,'k) float value t
  val log2p1   : rmode value t -> ('b,'e,'k) float value t -> ('b,'e,'k) float value t
  val log10p1  : rmode value t -> ('b,'e,'k) float value t -> ('b,'e,'k) float value t
  val rsqrt    : rmode value t -> ('b,'e,'k) float value t -> ('b,'e,'k) float value t
  val sin      : rmode value t -> ('b,'e,'k) float value t -> ('b,'e,'k) float value t
  val cos      : rmode value t -> ('b,'e,'k) float value t -> ('b,'e,'k) float value t
  val tan      : rmode value t -> ('b,'e,'k) float value t -> ('b,'e,'k) float value t
  val sinpi    : rmode value t -> ('b,'e,'k) float value t -> ('b,'e,'k) float value t
  val cospi    : rmode value t -> ('b,'e,'k) float value t -> ('b,'e,'k) float value t
  val atanpi   : rmode value t -> ('b,'e,'k) float value t -> ('b,'e,'k) float value t
  val atan2pi  : rmode value t -> ('b,'e,'k) float value t -> ('b,'e,'k) float value t
  val asin     : rmode value t -> ('b,'e,'k) float value t -> ('b,'e,'k) float value t
  val acos     : rmode value t -> ('b,'e,'k) float

  module type Basic_FP = sig
  type 'a t = 'a knowledge
  type 'a value
  type 'a eff
  type rmode

  val floats : int -> 'e bitv sort -> 'k bitv sort -> ('b,'e,'k) float sort
  val fradix : ('b,'e,'k) float sort -> int
  val fesort : ('b,'e,'k) float sort -> 'e bitv sort
  val fksort : ('b,'e,'k) float sort -> 'k bitv sort

  val rne : rmode
  val rna : rmode
  val rtp : rmode
  val rtn : rmode
  val rtz : rmode

  val rmode : rmode -> rmode value t

  val finite : ('b,'e,'k) float sort -> bit t ->
    'e bitv value t -> 'k bitv value t ->
    ('b,'e,'k) float value t

  val pinf : ('b,'e,'k) float sort -> ('b,'e,'k) float value t
  val ninf : ('b,'e,'k) float sort -> ('b,'e,'k) float value t
  val snan : ('b,'e,'k) float sort -> 'x bitv value t -> ('b,'e,'k) float value t
  val qnan : ('b,'e,'k) float sort -> 'x bitv value t -> ('b,'e,'k) float value t

  val exponent    : ('b,'e,'k) float value t -> 'e bitv value t
  val coefficient : ('b,'e,'k) float value t -> 'k bitv value t
  val fsign       : ('b,'e,'k) float value t -> bit value t

  val is_finite : ('b,'e,'k) float value t -> bit value t
  val is_fzero  : ('b,'e,'k) float value t -> bit value t
  val is_pinf   : ('b,'e,'k) float value t -> bit value t
  val is_ninf   : ('b,'e,'k) float value t -> bit value t
  val is_snan   : ('b,'e,'k) float value t -> bit value t
  val is_qnan   : ('b,'e,'k) float value t -> bit value t

  val cast_float  : ('b,'e,'k) float sort  -> rmode value t -> 'a bitv value t -> ('b,'e,'k) float value t
  val cast_sfloat : ('b,'e,'k) float sort -> rmode value t -> 'a bitv value t -> ('b,'e,'k) float value t
  val cast_int    : 'a bitv sort -> rmode value t -> ('b,'e,'k) float value t -> 'a bitv value t

  val fneg    : ('b,'e,'k) float value t -> ('b,'e,'k) float value t
  val fabs    : ('b,'e,'k) float value t -> ('b,'e,'k) float value t

  val fadd    : rmode value t -> ('b,'e,'k) float value t -> ('b,'e,'k) float value t -> ('b,'e,'k) float value t
  val fsub    : rmode value t -> ('b,'e,'k) float value t -> ('b,'e,'k) float value t -> ('b,'e,'k) float value t
  val fmul    : rmode value t -> ('b,'e,'k) float value t -> ('b,'e,'k) float value t -> ('b,'e,'k) float value t
  val fdiv    : rmode value t -> ('b,'e,'k) float value t -> ('b,'e,'k) float value t -> ('b,'e,'k) float value t
  val sqrt       : rmode value t -> ('b,'e,'k) float value t -> ('b,'e,'k) float value t -> ('b,'e,'k) float value t
  val fmodulo : rmode value t -> ('b,'e,'k) float value t -> ('b,'e,'k) float value t -> ('b,'e,'k) float value t
  val fmad    : rmode value t -> ('b,'e,'k) float value t -> ('b,'e,'k) float value t -> ('b,'e,'k) float value t -> ('b,'e,'k) float value t

  val fround   : rmode value t -> ('b,'e,'k) float value t -> ('b,'e,'k) float value t
  val fconvert : rmode value t -> ('b,'e,'k) float sort -> (_,_,_) float value t -> ('b,'e,'k) float value t

  val fsucc  : ('b,'e,'k) float value t -> ('b,'e,'k) float value t
  val fpred  : ('b,'e,'k) float value t -> ('b,'e,'k) float value t
  val forder : ('b,'e,'k) float value t -> ('b,'e,'k) float value t -> bit value t
  end
end

(* module type Core_FP = sig
 *   include Basic_FP
 *   val exp      : rmode value t -> ('b,'e,'k) float value t -> ('b,'e,'k) float value t
 *   val expm1    : rmode value t -> ('b,'e,'k) float value t -> ('b,'e,'k) float value t
 *   val exp2     : rmode value t -> ('b,'e,'k) float value t -> ('b,'e,'k) float value t
 *   val exp2m1   : rmode value t -> ('b,'e,'k) float value t -> ('b,'e,'k) float value t
 *   val exp10    : rmode value t -> ('b,'e,'k) float value t -> ('b,'e,'k) float value t
 *   val exp10m1  : rmode value t -> ('b,'e,'k) float value t -> ('b,'e,'k) float value t
 *   val log      : rmode value t -> ('b,'e,'k) float value t -> ('b,'e,'k) float value t
 *   val log2     : rmode value t -> ('b,'e,'k) float value t -> ('b,'e,'k) float value t
 *   val log10    : rmode value t -> ('b,'e,'k) float value t -> ('b,'e,'k) float value t
 *   val logp1    : rmode value t -> ('b,'e,'k) float value t -> ('b,'e,'k) float value t
 *   val log2p1   : rmode value t -> ('b,'e,'k) float value t -> ('b,'e,'k) float value t
 *   val log10p1  : rmode value t -> ('b,'e,'k) float value t -> ('b,'e,'k) float value t
 *   val rsqrt    : rmode value t -> ('b,'e,'k) float value t -> ('b,'e,'k) float value t
 *   val sin      : rmode value t -> ('b,'e,'k) float value t -> ('b,'e,'k) float value t
 *   val cos      : rmode value t -> ('b,'e,'k) float value t -> ('b,'e,'k) float value t
 *   val tan      : rmode value t -> ('b,'e,'k) float value t -> ('b,'e,'k) float value t
 *   val sinpi    : rmode value t -> ('b,'e,'k) float value t -> ('b,'e,'k) float value t
 *   val cospi    : rmode value t -> ('b,'e,'k) float value t -> ('b,'e,'k) float value t
 *   val atanpi   : rmode value t -> ('b,'e,'k) float value t -> ('b,'e,'k) float value t
 *   val atan2pi  : rmode value t -> ('b,'e,'k) float value t -> ('b,'e,'k) float value t
 *   val asin     : rmode value t -> ('b,'e,'k) float value t -> ('b,'e,'k) float value t
 *   val acos     : rmode value t -> ('b,'e,'k) float value t -> ('b,'e,'k) float value t
 *   val atan     : rmode value t -> ('b,'e,'k) float value t -> ('b,'e,'k) float value t
 *   val atan2    : rmode value t -> ('b,'e,'k) float value t -> ('b,'e,'k) float value t
 *   val sinh     : rmode value t -> ('b,'e,'k) float value t -> ('b,'e,'k) float value t
 *   val cosh     : rmode value t -> ('b,'e,'k) float value t -> ('b,'e,'k) float value t
 *   val tanh     : rmode value t -> ('b,'e,'k) float value t -> ('b,'e,'k) float value t
 *   val asinh    : rmode value t -> ('b,'e,'k) float value t -> ('b,'e,'k) float value t
 *   val acosh    : rmode value t -> ('b,'e,'k) float value t -> ('b,'e,'k) float value t
 *   val atanh    : rmode value t -> ('b,'e,'k) float value t -> ('b,'e,'k) float value t
 *   val hypot    : rmode value t -> ('b,'e,'k) float value t -> ('b,'e,'k) float value t -> ('b,'e,'k) float value t
 *   val pow      : rmode value t -> ('b,'e,'k) float value t -> ('b,'e,'k) float value t -> ('b,'e,'k) float value t
 *   val powr     : rmode value t -> ('b,'e,'k) float value t -> ('b,'e,'k) float value t -> ('b,'e,'k) float value t
 *   val compound : rmode value t -> ('b,'e,'k) float value t -> 'a bitv value t -> ('b,'e,'k) float value t
 *   val rootn    : rmode value t -> ('b,'e,'k) float value t -> 'a bitv value t -> ('b,'e,'k) float value t
 *   val pownn    : rmode value t -> ('b,'e,'k) float value t -> 'a bitv value t -> ('b,'e,'k) float value t
 * end *)
