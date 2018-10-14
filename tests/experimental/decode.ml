open Core_kernel

let special_encoding_mask = 0x6000000000000000L
let large_coeff_mask      = 0x0007ffffffffffffL
let large_coeff_high_bit  = 0x0020000000000000L
let infinity_mask         = 0x7800000000000000L
let sinfinity_mask        = 0xf800000000000000L
let exponent_mask         = 0x00000000000003ffL
let exponent_shift_large  = 51
let exponent_shift_small  = 53
let nan_mask              = 0x7c00000000000000L
let small_coeff_mask      = 0x001fffffffffffffL

(** returns sign, expn, frac *)
let of_int64 x =
  let open Int64 in
  let bias = 398L in
  let sign = x land 0x8000000000000000L = 0x8000000000000000L in
  if x land special_encoding_mask = special_encoding_mask then
    (* special encodings *)
    let expn, pcoeff, _coeff =
      if x land infinity_mask = infinity_mask then
        let expn = 0L in
        let pcoeff = x land 0xfe03ffffffffffffL in
        let pcoeff =
          if x land 0x0003ffffffffffffL >= 1000000000000000L then
	    x land 0xfe00000000000000L
          else if x land nan_mask = infinity_mask then
            x land sinfinity_mask
          else pcoeff in
        expn - bias, pcoeff, 0L  (* nan or infinity *)
      else
        (* check for non-canonical values *)
        let coeff = (x land large_coeff_mask) lor large_coeff_high_bit in
        let coeff =
          if coeff >= 10000000000000000L then 0L else coeff in
        let pcoeff = coeff in
        let expn = (x lsr exponent_shift_large) land exponent_mask in
        expn, pcoeff, coeff in
    sign, expn - bias, pcoeff
  else
    let expn = (x lsr exponent_shift_small) land exponent_mask in
    let pcoeff = x land small_coeff_mask in
    sign, expn - bias, pcoeff
