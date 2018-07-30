open Core_kernel
open Bap.Std

let ws = Word.to_string
let wi = Word.to_int_exn
let wdec = Word.string_of_value ~hex:false

let string_of_bits w =
  let bits = enum_bits w in
  let (@@) = sprintf "%s%d" in
  Seq.fold bits ~init:"" ~f:(fun s x ->
      if x then s @@ 1
      else s @@ 0)

let string_of_bits32 w =
  let bits = enum_bits w in
  let (@@) = sprintf "%s%d" in
  Seq.foldi bits ~init:"" ~f:(fun i acc x ->
      let a =
        if i = 1 || i = 9 then "_"
        else "" in
      let s = sprintf "%s%s" acc a in
      if x then s @@ 1
      else s @@ 0)

let string_of_bits64 w =
  let bits = enum_bits w in
  let (@@) = sprintf "%s%d" in
  Seq.foldi bits ~init:"" ~f:(fun i acc x ->
      let a =
        if i = 1 || i = 12 then "_"
        else "" in
      let s = sprintf "%s%s" acc a in
      if x then s @@ 1
      else s @@ 0)

let sb = string_of_bits
let sb32 = string_of_bits32
let sb64 = string_of_bits64

let deconstruct32 x =
  let w = Word.of_int32 (Int32.bits_of_float x) in
  let expn = Word.extract_exn ~hi:30 ~lo:23 w in
  let bias = Word.of_int ~width:8 127 in
  let expn = Word.(expn - bias) in
  let frac = Word.extract_exn ~hi:22 w in
  printf "ocaml %f: unbiased expn %d, frac %s %s, total %s\n"
    x (wi expn) (wdec frac) (string_of_bits frac) (string_of_bits32 w)

let deconstruct64 x =
  let w = Word.of_int64 (Int64.bits_of_float x) in
  let expn = Word.extract_exn ~hi:62 ~lo:52 w in
  let bias = Word.of_int ~width:11 1023 in
  let expn = Word.(signed (expn - bias)) in
  let frac = Word.extract_exn ~hi:51 w in
  printf "ocaml %f: unbiased expn %d, frac %s, total %s\n"
    x (wi expn) (string_of_bits frac) (string_of_bits64 w)




let bits_of_float x =
  string_of_bits32 (Word.of_int32 (Int32.bits_of_float x))

let compare_str x y =
  if String.equal x y then "ok" else "POSSIBLE FAIL"

let create x =
  let bin32 x =
    let y = single_of_float x in
    float_of_single y in
  let bin64 x =
    let y = double_of_float x in
    float_of_double y in
  let dec x =
    let x = str_of_float x in
    let v = decimal_of_string x in
    float_of_decimal v in
  let run x =
    let res = sprintf "%g" x in
    let bin32 = sprintf "%g" (bin32 x) in
    let bin64 = sprintf "%g" (bin64 x) in
    let dec = sprintf "%g" (dec x) in
    let cmp_bin32 = compare_str res bin32 in
    let cmp_bin64 = compare_str res bin64 in
    let cmp_dec = compare_str res dec in
    printf "make: from %s, bin32 %s, bin64 %s, dec %s\n"
      res cmp_bin32 cmp_bin64 cmp_dec in
  run x


module Run_manually(F : T) = struct

  let bitstring_of_float x =
    let x = Int64.bits_of_float x |> Word.of_int64 in
    sb64 x

  let unop2 opstr op op' x =
    let real = op x in
    let res = base2_unop op' x in
    let real_str = str_of_float real in
    let res_str = str_of_float res in
    if not (equal_base2 real res) then
      let bs = bitstring_of_float in
      let () = printf "cmp:\n %s <- expected (%f)\n %s <- what we got\n"
          (bs real) real (bs res) in
      printf "FAIL: base 2, %s %f <> %f, real %s <> %s\n"
        opstr x res real_str res_str
    else printf "OK!\n"

  let unop10 opstr op op' x =
    let x = truncate_float x in
    let real = op x in
    let res = base10_unop op' x in
    if not (equal_base10 real res) then
      printf "FAIL: base 10, %s %f <> %s (%f expected)\n"
        opstr x res real
    else printf "OK!\n"

  let binop2 opstr op op' x y =
    let real = op x y in
    let res = base2_binop op' x y in
    let bs = bitstring_of_float in
    if not (equal_base2 real res) then
      let () = printf "cmp:\n %s <- expected (%f)\n %s <- what we got\n"
          (bs real) real (bs res) in
      let real_str = str_of_float real in
      let res_str = str_of_float res in
      printf "FAIL: base 2, %f %s %f <> %f, real %s <> %s\n"
        x opstr y res real_str res_str
    else printf "OK!\n"

  let binop10 opstr op op' x y =
    let x = truncate_float x in
    let y = truncate_float y in
    let real = op x y in
    let res = base10_binop op' x y in
    if not (equal_base10 real res) then
      printf "FAIL: base 10, %f %s %f <> %s (%.16f expected)\n"
        x opstr y res real
    else printf "OK!\n"

  let run2 = false
  let run10 = true

  let unop opstr op op' x =
    if run2 then
      unop2 opstr op op' x;
    if run10 then
      unop10 opstr op op' x

  let binop opstr op op' x y =
    if run2 then
      binop2 opstr op op' x y;
    if run10 then
      binop10 opstr op op' x y

  let add x y = binop "+" (+.) add x y
  let sub x y = binop "-" (-.) sub x y
  let mul x y = binop "*" ( *. ) mul x y
  let div x y = binop "/" ( /. ) div x y
  let sqrt x = unop "sqrt" Float.sqrt sqrt x

  let neg x = ~-. x
  let (+) = add
  let (-) = sub
  let ( * ) = mul
  let ( / ) = div
  let ( sqrt ) = sqrt

  let () = 0.0 - 0.00000001

  let () = 4.2 + 2.3
  let () = (neg 2.2) - (neg 2.46)

  let () = 4.2 - 4.2
  let () = 2.0 * 0.5
  let () = 1.0 * (neg 0.5)
  let () = 2.4 / 3.123131

  let () = 324.32423 / 1.2
  let () = 1.0 / 0.0
  let () = 2.0 / 0.5
  let () = 1.0 / 3.0
  let () = 3.0 / 32.0
  let () = 42.3 / 0.0
  let () = 0.0 / 0.0
  let () = 324.32423 / 1.2
  let () = 2.4 / 3.123131
  let () = 0.1313134 / 0.578465631

  let () = sqrt 423245.0
  let () = sqrt 0.213
  let () = sqrt 1.2356
  let () = sqrt 0.0
  let () = sqrt 1.0
  let () = sqrt 2.0
  let () = sqrt 3.0
  let () = sqrt 20.0
  let () = sqrt (neg 1.0)

end
