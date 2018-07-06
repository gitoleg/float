open Core_kernel
open Format
open Bap.Std

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

  (* precision is a total digits, with an explicit integer bit,
     as it is in ieee 754 *)
  type t = {
    max_exponent : int;
    precision : int;
    total : int;
    integer_bit : bool;
  }

  let min_exponent t = 1 - t.max_exponent
  let max_exponent t = t.max_exponent
  let precision t = t.precision
  let total t = t.total
  let bias t = t.max_exponent
  let integer_bit t = t.integer_bit

  let pow2 n = int_of_float (2.0 ** float_of_int n)

  let create ?(integer_bit=false) ~exp_bits total =
    let max_exponent = pow2 (exp_bits - 1) - 1 in
    let precision =
      if integer_bit then total - exp_bits - 1
      else  total - exp_bits in
    { max_exponent; precision; total; integer_bit; }

  let ieee_single = create ~exp_bits:8 32
  let ieee_double = create ~exp_bits:11 64
  let x87_double_ext = create ~integer_bit:true ~exp_bits:15 80

end

type sema = Sema.t

type cmp =
  | Unordered
  | LessThan
  | GreaterThan
  | Equal

type cat =
  | Normal
  | Subnormal
  | Nan
  | Inf
  | Zero

module Category = struct

  type t = cat

  let is_normal sema e =
    1 - Sema.bias sema <= e && e <= 2 * Sema.max_exponent sema

  let is_nan sema e fra =
    e = 2 * Sema.max_exponent sema + 1 && not (Word.is_zero fra)

  let is_inf sema e fra =
    e = 2 * Sema.max_exponent sema + 1 && Word.is_zero fra

  let is_subnormal e fra = e = 0 && not (Word.is_zero fra)
  let is_zero e fra = e = 0 && Word.is_zero fra

  (** [create sema biased_exp fraction]  *)
  let create sema exp fra =
    let exp = exp - Sema.bias sema in
    if is_normal sema exp then Normal
    else if is_nan sema exp fra then Nan
    else if is_inf sema exp fra then Inf
    else if is_subnormal exp fra  then Subnormal
    else Zero

end


module Try = struct

  open Sema

  type my_float = {
    sign : bool;
    exp  : int; (* biased exp, i.e. E = e + bias  *)
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

  let shift_fra_right t bits =
    let gone = Word.extract_exn ~hi:(bits - 1) t.fra  in
    {t with exp = t.exp + bits; fra = lsr_fra t.fra bits}, gone

  let exp_bits s = Sema.total s - Sema.precision s

  let fraction t = Word.extract ~hi:(Word.bitwidth t.fra - 2) t.fra

  (* Add a category? for subnormal *)
  let cat t = Category.create t.sema t.exp t.fra

  (* TODO: a rounding propably should be used here  *)
  (* TODO: result should reflect what exactly we got: Norm, Inf, Nan *)
  (* TODO: normalize should affect a leading significant bit *)
  let normalize t =
    match cat t with
    | Normal -> t
    | _ -> match msb t with
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

  let check_length sema bits =
    let bitwidth = Word.bitwidth bits in
    let total = Sema.total sema in
    if bitwidth < total then
      failwith
        (sprintf "Failed to create float: %d bits expected, %d got"
           total bitwidth)

  let sign_exn sema bits =
    let sign_bit = Sema.total sema - 1 in
    Word.extract_exn ~hi:sign_bit ~lo:sign_bit bits |> Word.is_one

  let exp_hi sema = Sema.total sema - 2
  let exp_lo sema = Sema.precision sema - 1

  let exp_exn sema bits =
    Word.extract_exn ~hi:(exp_hi sema) ~lo:(exp_lo sema) bits |>
    Word.to_int_exn

  let fra_exn sema bits =
    if Sema.integer_bit sema then
      Word.extract_exn ~hi:(Sema.precision sema - 1) bits
    else
      let exp = exp_exn sema bits in
      let fra = Word.extract_exn ~hi:(Sema.precision sema - 2) bits in
      let leading_bit = match Category.create sema exp fra with
        | Normal -> Word.b1
        | _ -> Word.b0 in
      Word.concat leading_bit fra

  (** [of_bits sema bits] - create only from normal bits *)
  let of_bits sema bits =
    check_length sema bits;
    let sign = sign_exn sema bits in
    let exp = exp_exn sema bits in
    let fra = fra_exn sema bits in
    normalize {sign; exp; fra; sema}

  let to_bitstring t =
    let exp = t.exp in
    let sign = if t.sign then "1" else "0" in
    let exp = Word.of_int ~width:(exp_hi t.sema - exp_lo t.sema + 1) exp in
    let fra = Word.extract_exn ~hi:(exp_lo t.sema - 1) t.fra in
    sprintf "%s%s%s" sign (string_of_bits exp) (string_of_bits fra)

  (* TODO: check an integer bit here and add it if needed  *)
  let bits t =
    let sign = if t.sign then Word.b1 else Word.b0 in
    let exp = Word.of_int ~width:(exp_bits t.sema) t.exp in
    let fra = Word.extract_exn ~hi:(exp_lo t.sema - 1) t.fra in
    Word.concat (Word.concat sign exp) fra

  let to_string_temp t =
    let exp = t.exp - Sema.bias t.sema in
    let base = 2.0 ** float exp in
    let bits = enum_bits t.fra in
    let _,m = Seq.fold bits ~init:(1.0,0.0) ~f:(fun (d,r) b ->
        let r = if b then r +. 2.0 ** (~-. d)
          else r in
        d +. 1.0, r) in
    let sign = if t.sign then "-" else "" in
    sprintf "%s%f" sign ((1.0 +. m) *. base )

  let cmp f x y =
    let r = f x y in
    if Int.(r > 0) then GreaterThan
    else if Int.(r < 0) then LessThan
    else Equal

  let cmp_abs x y =
    match cmp Int.compare x.exp y.exp with
    | Equal -> cmp Word.compare x.fra y.fra
    | x -> x

  let is_pos t = not t.sign

  let cmp_of_sign x y =
    if x.sign = y.sign then Equal
    else if is_pos x then GreaterThan
    else LessThan

  (* TODO: what to do with the subnormal numbers  *)
  let cmp x y =
    match cat x, cat y with
    | Nan, _ | _, Nan -> Unordered
    | Inf, Normal | Inf, Zero | Normal, Zero ->
      if is_pos x then GreaterThan else LessThan
    | Normal, Inf | Zero, Inf | Zero, Normal ->
      if is_pos y then LessThan else GreaterThan
    | Inf, Inf -> cmp_of_sign x y
    | Zero, Zero -> Equal
    | Normal, Normal ->
      if x.sign <> y.sign then cmp_of_sign x y
      else
        let r = cmp_abs x y in
        if is_pos x then r
        else match r with
          | GreaterThan -> LessThan
          | LessThan -> GreaterThan
          | x -> x

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
    let fra = Word.(x'.fra + y'.fra) in
    normalize {x with exp = x'.exp ; fra}

end

let single_of_float f =
  let w = Word.of_int32 ~width:32 (Int32.bits_of_float f) in
  Try.of_bits Sema.ieee_single w

let double_of_float f =
  let w = Word.of_int64 ~width:64 (Int64.bits_of_float f) in
  Try.of_bits Sema.ieee_double w

let float_of_single x =
  Int32.float_of_bits (Word.to_int32_exn (Try.bits x))

let float_of_double x =
  Int64.float_of_bits (Word.to_int64_exn (Try.bits x))

module Test_space = struct

  let word_of_float x =
    let x = Int32.bits_of_float x in
    Word.of_int32 ~width:32 x

  let test1 =
    let z = 4.2 in
    let q = 2.78 in
    let b1 = double_of_float q in
    let b2 = double_of_float z in
    let b = Try.add b1 b2 in
    let x = float_of_double b in
    printf "%g + %g = %g\n" z q x

end
