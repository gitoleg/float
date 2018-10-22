open Core_kernel
open Gfloat

type bignum = int * Z.t

module Bignum_of_z : Bignum with type t = bignum = struct
  type t = bignum

  let of_int ~width x = width, Z.of_int x
  let to_int (_,t) = Z.to_int t
  let of_z ~width z = width, z
  let to_z (_,z) = z
  let bitwidth (w,_) = w

  let extract ?hi ?(lo = 0) (w,z) =
    let hi = Option.value ~default:(w-1) hi in
    let len = hi - lo + 1 in
    len, Z.extract z lo len

  let ones width = of_int ~width (-1)
  let is_zero w = w = of_int ~width:(bitwidth w) 0
  let is_one w = w = of_int ~width:(bitwidth w) 1
  let is_positive (_,x) = Z.sign x = 1
  let is_negative (_,x) = Z.sign x = -1

  let testbit (_,w) i = Z.testbit w i

  let zero_extend (w,x) w' = w + w', x

  let assert_length lenx leny =
    if lenx <> leny then
      failwith "attempting to operate over bignums with different length"

  let tos = Z.to_string

  let binop op (lenx,x) (leny,y) =
    assert_length lenx leny;
    let res' = op x y in
    let sign = Z.sign res' in
    let res'' = Z.extract (Z.abs res') 0 lenx in
    let res = if sign = -1 then Z.neg res'' else res'' in
    lenx, res

  let ( + ) x y = binop Z.( + ) x y
  let ( - ) x y = binop Z.( - ) x y
  let ( * ) x y = binop Z.( * ) x y
  let ( / ) x y = binop Z.( / ) x y
  let ( = ) (lenx,x) (leny,y) = Z.equal x y
  let ( < ) (lenx,x) (leny,y) = Z.lt x y

  let (lsl) (lenx,x) sh = lenx, Z.(x lsl sh)
  let (lxor) (lenx,x) (leny,y)  = assert_length lenx leny; lenx, Z.(x lxor y)

  let abs (len,w) = len, Z.abs w
  let max x y = if x < y then y else x

  let toz (_,z) = z
end

include Make(Bignum_of_z)
