open Core_kernel
open Bap.Std

let enum_bits w =
  let bits = Word.(enum_bits w BigEndian) in
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

let string_of_bits64 x =
  let w = Word.of_int64 (Int64.bits_of_float x) in
  let bits = enum_bits w in
  let (@@) = sprintf "%s%d" in
  Seq.foldi bits ~init:"" ~f:(fun i acc x ->
      let a =
        if i = 1 || i = 12 then "_"
        else "" in
      let s = sprintf "%s%s" acc a in
      if x then s @@ 1
      else s @@ 0)

let deconstruct x =
  let wi = Word.to_int_exn in
  let y = Int64.bits_of_float x in
  let w = Word.of_int64 y in
  let expn = Word.extract_exn ~hi:62 ~lo:52 w in
  let bias = Word.of_int ~width:11 1023 in
  let expn' = Word.(signed (expn - bias)) in
  let frac = Word.extract_exn ~hi:51 w in
  printf "ocaml %f: bits %s, 0x%LX\n" x (string_of_bits64 x) y;
  printf "ocaml %f: biased/unbiased expn %d/%d, coef 0x%x\n"
    x (wi expn) (wi expn') (wi frac)
