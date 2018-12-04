open Core_kernel
open Bap.Std
open Gfloat

type bignum = word

module Bignum_of_word : Bignum with type t = bignum = struct

  include Word

  let zero_extend w width =
    Word.concat (Word.zero width) w

  let to_string x =
    sprintf "%s:%d"
      (Word.to_string x)
      (* (Word.string_of_value ~hex:false x) *)
      (Word.bitwidth x)

  let to_int = to_int_exn
  let extract ?hi ?lo w =
    extract_exn ?hi ?lo w

  let ( lsl ) x y =
    let width = bitwidth x in
    let y = Word.of_int ~width y in
    x lsl y

  let tow x = x

end

include Make(Bignum_of_word)
