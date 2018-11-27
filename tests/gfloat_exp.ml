open Bap.Std
open Gfloat
open Core_float

module MyExp : Core_float.Core = struct
  include Bil.Infix

  type t = exp

  let b0 = Bil.Int (Word.b0)
  let b1 = Bil.Int (Word.b1)
  let inv x = Bil.lnot x

  let and_ x y = Bil.(x land y)
  let or_ x y = Bil.(x lor y)
  let int w = Bil.int w
  let not = Bil.lnot
  let neg = Bil.neg
  let lsb x = Bil.extract ~hi:0 ~lo:0 x
  let add = (+)
  let sub = (-)
  let mul = ( * )
  let div = ( / )
  let modulo = ( mod )
  let smodulo = ( %$ )
  let sdiv = ( /$ )
  let logand = and_
  let logor = or_
  let logxor = (lxor)
  let shiftl = (lsl)
  let shiftr = (lsr)
  let cast = Bil.cast
  let concat = Bil.concat
  let ite = Bil.ite

  let sle = (<=$)
  let ule = (<=)

  let zero


  let msb x =
    match Type.infer_exn x with
    | Type.Imm i ->
       let i = Caml.(i - 1) in
       Bil.extract ~hi:i ~lo:i x
    | _ -> failwith "unexpected type"

end


module A = Gfloat.Make(MyExp)
