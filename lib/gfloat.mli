open Bap_knowledge
open Bap_core_theory

module Make(B : Theory.Basic) : sig

  type 'a t = 'a knowledge

  val rne : rmode value t
  val rna : rmode value t
  val rtp : rmode value t
  val rtn : rmode value t
  val rtz : rmode value t

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

  val fsub    : rmode value t -> ('e,'k) float value t
                -> ('e,'k) float value t -> 'k bitv value t

  val fmul    : rmode value t -> ('e,'k) float value t
                -> ('e,'k) float value t -> ('e,'k) float value t

  val clz : 'k bitv value t ->  'k bitv value t
  val minimize_exponent: ('e,'k) float value t -> ('e,'k) float value t

  val to_ieee : 'a bitv sort -> rmode value t -> ('e,'k) float value t -> 'a bitv value t
  val of_ieee : 'a bitv value t -> rmode value t -> ('e,'k) float sort -> ('e,'k) float value t

end
