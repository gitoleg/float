open Core_kernel
open Format
open Bap.Std

module type What_I_am_going_to_do = sig

  type t
  type semantics

  val ieee_singe : semantics
  (* other semantics here *)

  val of_bits: semantics -> word -> t
  val of_float: float -> t
  val add : t -> t -> t
  val string_of_t : t -> string

end

let enum_bits w =
  let bits = Word.enum_bits w BigEndian in
  let b_len = Seq.length bits in
  let w_len = Word.bitwidth w in
  if b_len > w_len then
    Seq.drop bits (b_len - w_len)
  else bits

let string_of_bits w =
  let bits = enum_bits w in
  let (@@) = sprintf "%s%d" in
  Seq.fold bits ~init:"" ~f:(fun s x ->
      if x then s @@ 1
      else s @@ 0)

module Sema = struct

  type t = {
    max_exponent : int;
    precision : int;
    total : int;
  }

  let min_exponent t = 1 - t.max_exponent
  let max_exponent t = t.max_exponent
  let precision t = t.precision
  let total t = t.total
  let bias t = t.max_exponent

  let ieee_single = {
    max_exponent = 127;
    precision = 24;
    total = 32;
  }

  let ieee_double = {
    max_exponent = 1023;
    precision = 53;
    total = 64;
  }

end

type sema = Sema.t

module Try = struct

  open Sema

  type my_float = {
    sign : bool;
    exp  : int; (* biased exp  *)
    fra  : word;
    sema : sema;
  }

  let msb t =
    let bits = enum_bits t.fra in
    match Seq.findi bits ~f:(fun i x -> x) with
    | None -> None
    | Some (i,_) -> Some (Word.bitwidth t.fra - i)

  let lsb t =
    let bits = Seq.to_list_rev (enum_bits t.fra) in
    match List.findi bits ~f:(fun i x -> x) with
    | None -> None
    | Some (i,_) -> Some i

  let handle_overflow () = failwith "overflow handling is not implemented"

  let lsl_fra fra bits =
    let bits = Word.of_int ~width:(Word.bitwidth fra) bits in
    Word.(fra lsl bits)

  let lsr_fra fra bits =
    let bits = Word.of_int ~width:(Word.bitwidth fra) bits in
    Word.(fra lsr bits)

  let shift_fra_left t bits =
    {t with exp = t.exp - bits; fra = lsl_fra t.fra bits}

  let estimate_gone t bits =
    match lsb t with
    | None -> `Zero
    | Some lsb ->
      if bits <= lsb then `Zero
      else if bits = lsb + 1 then `Half
      else if bits <= Sema.precision t.sema
           && Word.is_one (Word.extract_exn
                             ~hi:(bits - 1) ~lo:(bits-1) t.fra) then
        `MoreThenHalf
      else `LessThenHalf

  let str_of_gone = function
    | `Zero -> "zero"
    | `Half -> "half"
    | `MoreThenHalf -> "more then half"
    | `LessThenHalf -> "less then half"


  let shift_fra_right t bits =
    let gone = Word.extract_exn ~hi:(bits - 1) t.fra  in
    {t with exp = t.exp + bits; fra = lsr_fra t.fra bits}, gone

  let exp_bits s = Sema.total s - Sema.precision s
  let unbiased_exp t = t.exp - Sema.bias t.sema

  let is_normal t =
    let e = unbiased_exp t in
    1 - Sema.bias t.sema <= e && e <= 2 * Sema.max_exponent t.sema

  let is_nan t =
    let e = unbiased_exp t in
    e = 2 * Sema.max_exponent t.sema + 1 && not (Word.is_zero t.fra)

  let is_inf t =
    let e = unbiased_exp t in
    e = 2 * Sema.max_exponent t.sema + 1 && Word.is_zero t.fra

  let is_subnormal t = t.exp = 0 && not (Word.is_zero t.fra)

  let is_zero t = t.exp = 0 && Word.is_zero t.fra

  (* TODO: a rounding propably should be used here  *)
  (* TODO: result should reflect what exactly we got: Norm, Inf, Nan *)
  let normalize t =
    if is_normal t then t
    else
      match msb t with
      | None -> failwith "will see"
      | Some msb ->
        let change = msb - Sema.precision t.sema in
        if (t.exp + change > Sema.max_exponent t.sema) then
          handle_overflow ()
        else
          let change =
            if t.exp + change < min_exponent t.sema then
              min_exponent t.sema - t.exp
            else change in
          if change < 0 then
            shift_fra_left t (abs change)
          else if change > 0 then
            fst @@ shift_fra_right t change
          else t

  let exp_hi sema = Sema.total sema - 2
  let exp_lo sema = Sema.precision sema - 1

  let of_bits sema bits =
    let bits =
      if Word.bitwidth bits < Sema.total sema then
        let x = Word.zero (Sema.total sema - Word.bitwidth bits) in
        Word.concat x bits
      else bits in
    let sign_bit = Sema.total sema - 1 in
    let sign = Word.extract_exn ~hi:sign_bit ~lo:sign_bit bits
               |> Word.is_one in
    let exp = Word.extract_exn ~hi:(exp_hi sema) ~lo:(exp_lo sema) bits
              |> Word.to_int_exn in
    let fra = Word.extract_exn ~hi:(exp_lo sema - 1) bits in
    normalize {sign; exp; fra; sema}

  let to_bitstring t =
    let exp = t.exp in
    let sign = if t.sign then "1" else "0" in
    let exp = Word.of_int ~width:(exp_hi t.sema - exp_lo t.sema + 1) exp in
    sprintf "%s%s%s" sign (string_of_bits exp) (string_of_bits t.fra)

  let bits t =
    let sign = if t.sign then Word.b1 else Word.b0 in
    let exp = Word.of_int ~width:(exp_bits t.sema) t.exp in
    Word.concat (Word.concat sign exp) t.fra

  let to_string_temp t =
    let exp = unbiased_exp t in
    let base = 2.0 ** float exp in
    let bits = enum_bits t.fra in
    let _,m = Seq.fold bits ~init:(1.0,0.0) ~f:(fun (d,r) b ->
        let r = if b then r +. 2.0 ** (~-. d)
          else r in
        d +. 1.0, r) in
    let sign = if t.sign then "-" else "" in
    sprintf "%s%f" sign ((1.0 +. m) *. base )


  let add x y =
    let x',y', gone =
      let dif = abs (x.exp - y.exp) in
      if x.exp > y.exp then
        let y', gone = shift_fra_right y dif in
        x, y', gone
      else
        let x', gone = shift_fra_right x dif in
        x', y, gone in
    let _gone' = Word.extract_exn ~hi:(Word.bitwidth x.fra - 1) gone in
    let _t = {x with fra=_gone'} in
    printf "gone is %s\n" (to_bitstring _t);
    printf "shift:\n %s\n %s\n" (to_bitstring x) (to_bitstring x');
    let fra = Word.(x'.fra + y'.fra) in
    normalize {x with exp = x'.exp ; fra}


end

let single_of_float f =
  let w = Word.of_int32 ~width:32 (Int32.bits_of_float f) in
  Try.of_bits Sema.ieee_single w

let double_of_float f =
  let w = Word.of_int64 ~width:64 (Int64.bits_of_float f) in
  Try.of_bits Sema.ieee_double w

module Test_space = struct

  let exp  w = Word.extract_exn ~hi:30 ~lo:23 w |> Word.to_int_exn
  let frac w = Word.extract_exn ~hi:22 w |> Word.to_int_exn

  let inspect x =
    let bits = Int32.bits_of_float x in
    let w = Word.of_int32 ~width:32 bits in
    let bits = Word.enum_bits w BigEndian in
    let (@@) = sprintf "%s%d" in
    let str = Seq.foldi bits ~init:"" ~f:(fun i s x ->
        let s = match i with
          | 1 | 9 -> sprintf "%s_" s
          | _ -> s in
        if x then s @@ 1
        else s @@ 0) in
    str, exp w, frac w

  let temp () =
    let w = Word.of_int ~width:23 420000 in
    let e = Word.of_int ~width:8 129 in
    let x = Word.concat Word.b0 e in
    let x = Word.concat x w in
    let x = Word.to_int32_exn x in
    let x = Int32.float_of_bits x in
    printf "temp: %g\n" x

  let a () =
    let test x =
      let bits,exp,frac = inspect x in
      printf "%-5g: %s (exp: %d, frac: %d)\n" x bits exp frac in
    let xs = [5.9; 4.2; 0.42] in
    List.iter ~f:test xs

  let word_of_float x =
    let x = Int32.bits_of_float x in
    Word.of_int32 ~width:32 x

  let test1 =
    let z = 4.2 in
    let q = 0.2 in
    let x = word_of_float (q +. z) in
    let str1 = string_of_bits x in
    let b1 = single_of_float q in
    let b2 = single_of_float z in
    let b = Try.add b1 b2 in
    let x = Int32.float_of_bits (Word.to_int32_exn (Try.bits b)) in
    printf "0.2: %s\n" (Try.to_bitstring b1);
    printf "we got %g\n" x;
    printf "test:\n should: %s\n got:    %s\n"
      str1 (Try.to_bitstring b)

end
