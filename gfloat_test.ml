open Core_kernel
open OUnit2
open Bap.Std

open Gfloat
open Gfloat.Debug

type ieee_bin = {
  expn_width : int;  (* bits in exponent *)
  frac_width : int;  (* bits in fraction *)
  int_bit    : bool;  (* integer bit, if exists *)
  bias       : int;
}

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
  let expn = Word.(expn - bias) in
  let frac = Word.extract_exn ~hi:51 w in
  printf "ocaml %f: unbiased expn %d, frac %s, total %s\n"
    x (wi expn) (string_of_bits frac) (string_of_bits64 w)

let single = { expn_width=8;  bias=127;  frac_width=23; int_bit=false }
let double = { expn_width=11; bias=1023; frac_width=52; int_bit=false }

let drop_hd w =
  let hi = Word.bitwidth w - 2 in
  Word.extract_exn ~hi w

let all_ones  x = Word.(x = ones (bitwidth x))
let all_zeros x = Word.(x = zero (bitwidth x))

let t_of_bits {expn_width;bias;frac_width;int_bit} bits =
  let total = Word.bitwidth bits in
  let sign = Word.extract_exn ~hi:(total - 1) ~lo:(total - 1) bits in
  let sign = if Word.is_zero sign then Pos else Neg in
  let hi_expn, lo_expn = total - 2, total - 2 - expn_width + 1 in
  let hi_frac = lo_expn - 1 in
  let precs = if int_bit then frac_width else frac_width + 1 in
  let expn_bits =
    Word.extract_exn ~hi:hi_expn ~lo:lo_expn bits in
  let frac = Word.extract_exn ~hi:hi_frac bits in
  let expn' = Word.to_int_exn expn_bits - bias in
  if all_ones expn_bits && Word.is_zero frac then
    mk_inf ~base:2 precs sign
  else if all_ones expn_bits then
    mk_nan ~base:2 precs
  else
    let dexp = Word.bitwidth frac in
    let ibit = if all_zeros expn_bits && all_zeros frac then Word.b0
      else Word.b1 in
    let expn = Word.of_int ~width:expn_width (expn' - dexp) in
    let frac = if int_bit then frac else Word.concat ibit frac in
    mk ~base:2 sign expn frac

let single_of_float f =
  let bits = Word.of_int32 (Int32.bits_of_float f) in
  t_of_bits single bits

let double_of_float f =
  let bits = Word.of_int64 (Int64.bits_of_float f) in
  t_of_bits double bits

let normalize_ieee bias biased_expn frac =
  let min_expn = 1 in
  let max_expn = bias * 2 in
  let rec norm_expn expn frac =
    if expn > max_expn then
      norm_expn (pred expn) Word.(frac lsl b1)
    else if expn < min_expn then
      norm_expn (succ expn) Word.(frac lsr b1)
    else expn, frac in
  let norm_frac expn frac =
    match msb frac with
    | None -> expn, frac
    | Some i ->
      let len = bits_in frac in
      let shift = len - i - 1 in
      let frac = lshift_frac 2 frac shift in
      let expn = expn - shift in
      expn, frac in
  let expn, frac = norm_expn biased_expn frac in
  norm_frac expn frac

let bits_of_t kind t =
  let total = kind.expn_width + kind.frac_width + 1 in
  let total = if kind.int_bit then total + 1 else total in
  let (^) = Word.concat in
  match t.value with
  | Fin x when is_zero t -> Word.zero total
  | Fin x  ->
    let {expn; frac;} = norm t.base x in
    let expn = Word.to_int_exn expn in
    let expn = kind.bias + expn in
    let n = Word.bitwidth x.frac - 1 in
    let expn = expn + n in
    let expn,frac = normalize_ieee kind.bias expn frac in
    let frac = if kind.int_bit then frac else drop_hd frac in
    let expn = Word.of_int ~width:kind.expn_width expn in
    word_of_sign t.sign ^ expn ^ frac
  | Nan (_,frac) ->
    let expn = Word.ones kind.expn_width in
    let frac = if kind.int_bit then frac else drop_hd frac in
    word_of_sign t.sign ^ expn ^ frac
  | Inf ->
    let expn = Word.ones kind.expn_width in
    let frac = Word.zero kind.frac_width in
    word_of_sign t.sign ^ expn ^ frac

let float_of_single t =
  let bits = bits_of_t single t in
  let bits = Word.signed bits |> Word.to_int32_exn in
  Int32.float_of_bits bits

let float_of_double t =
  let bits = bits_of_t double t in
  let bits = Word.signed bits |> Word.to_int64_exn in
  Int64.float_of_bits bits

let pow ~radix n =
  let rec run r m =
    if m < n then run (r * radix) (m + 1)
    else r in
  if n = 0 then 1
  else run radix 1

let max_of_precision p = pow ~radix:2 p

let truncate_zeros x =
  match String.index x '.' with
  | None -> x
  | Some p -> String.rstrip ~drop:(fun c -> Char.equal c '0') x

let rec truncate max_int expn x =
  let y = int_of_string x in
  if y <= max_int then expn, y
  else
    truncate max_int (expn + 1)
      (String.subo ~len:(String.length x - 1) x)

let decimal_precision = 20
let decimal_expn_bits = 10

let log2 x = Float.log10 x /. Float.log10 2.0

(* return max bits required for encodind [n] decimal digits  *)
let bits_of_digits n =
  int_of_float (Float.round_up (float n *. log2 10.0))

let decimal_of_string = function
  | "nan" -> mk_nan ~base:10 decimal_precision
  | "inf" -> mk_inf ~base:10 decimal_precision Pos
  | "-inf" -> mk_inf ~base:10 decimal_precision Neg
  | x ->
    let x = truncate_zeros x in
    let is_neg = List.hd_exn (String.to_list x) = '-' in
    let start, point =
      let p = String.index_exn x '.' in
      if is_neg then 1, p
      else 0, p in
    let base = String.subo ~pos:start ~len:(point - start) x in
    let remd = String.subo ~pos:(point + 1) x in
    let expn = - (String.length remd) in
    let frac = base ^ remd in
    let bits = bits_of_digits (String.length frac) in
    printf "bits: %d\n" bits;

    let len = sprintf ":%du" (bits_of_digits (String.length frac)) in
    let frac = Word.of_string (frac ^ len) in
    let sign = if is_neg then Neg else Pos in
    let expn = Word.of_int ~width:decimal_expn_bits expn in
    mk ~base:10 sign expn frac

let my_string_of_float x = sprintf "%.15f" x
let decimal_of_float x = decimal_of_string (my_string_of_float x)

let insert_point str before =
  List.foldi (String.to_list str) ~init:[]
    ~f:(fun i acc c ->
        if i = before then c :: '.' :: acc
        else c :: acc) |> List.rev |> String.of_char_list

let attach_sign x = function
  | Pos -> x
  | Neg -> ~-. x

let string_of_decimal t =
  let attach_sign x = match t.sign with
    | Pos -> x
    | Neg -> "-" ^ x in
  match t.value with
  | Fin {expn; frac} ->
    let expn = Word.to_int_exn (Word.signed expn) in
    let frac = wdec frac in
    let len = String.length frac in
    if expn = 0 then frac
    else if expn < 0 && abs expn > len then
      let zeros = String.init (abs expn - len + 1) ~f:(fun _ -> '0') in
      let frac = zeros ^ frac in
      insert_point frac (String.length frac - abs expn)
    else if expn < 0 then
      insert_point frac (len - abs expn)
    else if expn > 0 && expn > len then
      let zeros = String.init (expn - len) ~f:(fun _ -> '0') in
      let frac = zeros ^ frac in
      insert_point frac expn
    else
      let zeros = String.init expn ~f:(fun _ -> '0') in
      let frac = frac ^ zeros in
      insert_point frac (len + expn)
  | Inf   -> attach_sign "inf"
  | Nan _ -> attach_sign "nan"

let float_of_decimal x = float_of_string (string_of_decimal x)

let xs = "9.423424255353534543"
let ys = "1003.923627544745493"
let x = decimal_of_string xs
let y = decimal_of_string ys
let z = float_of_decimal (add x y)
let r = sprintf "%.21f" (float_of_string xs +. float_of_string ys)
let () = printf "%.21f\n%s\n" z r

let hexadecimal_of_string x =
  let x = truncate_zeros x in
  let is_neg = List.hd_exn (String.to_list x) = '-' in
  let start, point =
    let p = String.index_exn x '.' in
    if is_neg then 1, p
    else 0, p in
  let base = String.subo ~pos:start ~len:(point - start) x in
  let remd = String.subo ~pos:(point + 1) x in
  let precision = 26 in
  let max_int = max_of_precision precision in
  let expn = - (String.length remd) in
  let expn, int_part = truncate max_int expn ("0x" ^ base ^ remd) in
  let expn = Word.of_int ~width:10 expn in
  let frac = Word.of_int ~width:precision int_part in
  let sign = if is_neg then Neg else Pos in
  mk ~base:16 sign expn frac

let string_of_hexadecimal t = match t.value with
  | Fin {expn;frac} ->
    let expn = Word.to_int_exn expn in
    let expn = float_of_int expn in
    let frac = float_of_int @@ Word.to_int_exn frac in
    let r = frac *. (16.0 ** expn) in
    let int_part = Float.round_down r in
    let flt_part = frac -. int_part *. (16.0 ** (~-.expn)) in
    let sign = if t.sign = Neg then "-"
      else "" in
    sprintf "%s%x.%x\n" sign (int_of_float int_part) (int_of_float flt_part)
  | _ -> failwith "todo"

let test_hex () =
  let mk = hexadecimal_of_string in
  let fl = string_of_hexadecimal in
  let x = mk "abc.45a" in
  let y = mk "b.456a" in
  let z = mk "2a.c" in
  let r = mul z (add x y) in
  printf "%s\n" (fl r)

let word_of_float x =
  let x = Int32.bits_of_float x in
  Word.of_int32 ~width:32 x

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
    let x = my_string_of_float x in
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

let str_of_float f = sprintf "%.16h" f
let cmp x y = String.equal (str_of_float x) (str_of_float y)

let gen_binop of_float to_float op x y =
  op (of_float x) (of_float y) |> to_float

let gen_unop of_float to_float op x =
  op (of_float x) |> to_float

let base2_binop = gen_binop double_of_float float_of_double
let base10_binop = gen_binop decimal_of_float float_of_decimal
let base2_unop = gen_unop double_of_float float_of_double
let base10_unop = gen_unop decimal_of_float float_of_decimal
let nan = Float.nan
let inf = Float.infinity
let ninf = Float.neg_infinity

(* TODO: bit equality desired! *)
let equal_base2 x y =
  let x = Int64.bits_of_float x in
  let y = Int64.bits_of_float y in
  Int64.equal x y

module Run_test(F : T) = struct

  let run2 = true
  let run10 = false

  let binop op op' x y ctxt =
    let real = op x y in
    let () =
      if run2 then
        let r2 = base2_binop op' x y in
        assert_equal ~ctxt ~cmp real r2 in
    if run10 then
      let r10 = base10_binop op' x y in
      assert_equal ~ctxt ~cmp real r10

  let unop op op' x ctxt =
    let real = op x in
    let () = if run2 then
        let r2 = base2_unop op' x in
        assert_equal ~ctxt ~cmp real r2 in
    if run10 then
      let r10 = base10_unop op' x in
      assert_equal ~ctxt ~cmp real r10

  let add x y ctxt = binop (+.) add x y ctxt
  let sub x y ctxt = binop (-.) sub x y ctxt
  let mul x y ctxt = binop ( *. ) mul x y ctxt
  let div x y ctxt = binop ( /. ) div x y ctxt
  let sqrt x ctxt = unop Float.sqrt sqrt x ctxt

  let (+) = add
  let (-) = sub
  let ( * ) = mul
  let ( / ) = div
  let ( sqrt ) = sqrt

  let suite () =
    let neg x = ~-.x in
    "Gfloat test" >::: [

      (* special cases  *)
      "nan  + nan"  >:: nan  + nan;
      "inf  + inf"  >:: inf  + inf;
      "-inf + -inf" >:: ninf + ninf;
      "nan  + -inf" >:: nan  + ninf;
      "-inf + nan"  >:: ninf + nan;
      "nan  + inf"  >:: nan  + inf;
      "inf  + nan"  >:: inf  + nan;
      "-inf + inf"  >:: ninf + inf;
      "inf  + -inf" >:: inf  + ninf;

      "nan  - nan"  >:: nan  - nan;
      "inf  - inf"  >:: inf  - inf;
      "-inf - -inf" >:: ninf - ninf;
      "nan  - -inf" >:: nan  - ninf;
      "-inf - nan"  >:: ninf - nan;
      "nan  - inf"  >:: nan  - inf;
      "inf  - nan"  >:: inf  - nan;
      "-inf - inf"  >:: ninf - inf;
      "inf  - -inf" >:: inf  - ninf;

      "nan  * nan"  >:: nan  * nan;
      "inf  * inf"  >:: inf  * inf;
      "-inf * -inf" >:: ninf * ninf;
      "nan  * -inf" >:: nan  * ninf;
      "-inf * nan"  >:: ninf * nan;
      "nan  * inf"  >:: nan  * inf;
      "inf  * nan"  >:: inf  * nan;
      "-inf * inf"  >:: ninf * inf;
      "inf  * -inf" >:: inf  * ninf;

      "nan  / nan"  >:: nan  / nan;
      "inf  / inf"  >:: inf  / inf;
      "-inf / -inf" >:: ninf / ninf;
      "nan  / -inf" >:: nan  / ninf;
      "-inf / nan"  >:: ninf / nan;
      "nan  / inf"  >:: nan  / inf;
      "inf  / nan"  >:: inf  / nan;
      "-inf / inf"  >:: ninf / inf;
      "inf  / -inf" >:: inf  / ninf;

      "sqrt nan"    >:: sqrt nan;
      "sqrt inf"    >:: sqrt inf;
      "sqrt -inf"   >:: sqrt ninf;

      (* add *)
      "4.2 + 2.3"   >:: 4.2 + 2.3;
      "4.2 + 2.98"  >:: 4.2 + 2.98;
      "2.2 + 4.28"  >:: 2.2 + 4.28;
      "2.2 + -4.28" >:: 2.2 + (neg 4.28);
      "-2.2 + 4.28" >:: (neg 2.2) + 4.28;
      "2.2 + 2.46"  >:: 2.2 + 2.46;
      "4.2 + 2.98"  >:: 4.2 + 2.98;
      "0.0000001 + 0.00000002" >:: 0.0000001 + 0.00000002;

      (* sub *)
      "4.2 - 2.28"    >:: 4.2 - 2.28;
      "4.28 - 2.2"    >:: 4.28 - 2.2;
      "2.2 - 4.28"    >:: 2.2 - 4.28;
      "2.2 - -4.28"   >:: 2.2 - (neg 4.28);
      "2.2 - 2.6"     >:: 2.2 - 2.6;
      "-2.2 - 2.46"   >:: (neg 2.2) - 2.46;
      "-2.2 - -2.46)" >:: (neg 2.2) - (neg 2.46);
      "0.0000001 - 0.00000002" >:: 0.0000001 - 0.00000002;

      (* mul *)
      "1.0 * 2.5"    >:: 1.0 * 2.5;
      "2.5 * 0.5"    >:: 2.5 * 0.5;
      "4.2 * 3.4"    >:: 4.2 * 3.4;
      "0.01 * 0.02"  >:: 0.01 * 0.02;
      "1.0 * 0.5"    >:: 1.0 * 0.5;
      "1.0 * -0.5"   >:: 1.0 * (neg 0.5);
      "- 1.0 * -0.5" >:: (neg 1.0) * (neg 0.5);

      (* div *)
      "1.0 / 0.0"  >:: 1.0 / 0.0;
      "2.0 / 0.5"  >:: 2.0 / 0.5;
      "1.0 / 3.0"  >:: 1.0 / 3.0;
      "3.0 / 32.0" >:: 3.0 / 32.0;
      "42.3 / 0.0" >:: 42.3 / 0.0;
      "0.0 / 0.0"  >:: 0.0 / 0.0;
      "324.32423 / 1.2" >:: 324.32423 / 1.2;
      "2.4 / 3.123131"  >:: 2.4 / 3.123131;
      "0.1313134 / 0.578465631" >:: 0.1313134 / 0.578465631;

      (* sqrt  *)
      "sqrt 423245.0" >:: sqrt 423245.0;
      "sqrt 0.213"    >:: sqrt 0.213;
      "sqrt 1.2356"   >:: sqrt 1.2356;
      "sqrt 0.0"      >:: sqrt 0.0;
      "sqrt 1.0"      >:: sqrt 1.0;
      "sqrt 2.0"      >:: sqrt 2.0;
      "sqrt 3.0"      >:: sqrt 3.0;
      "sqrt 20.0"     >:: sqrt 20.0;
      "sqrt (-1)"     >:: sqrt (neg 1.0);
    ]

  let () = run_test_tt_main (suite ())

end

module Run_manually(F : T) = struct

  let str_of_float x = sprintf "%.15f" x
  let str_of_float f = sprintf "%.16h" f

  let unop2 opstr op op' x =
    let real = op x in
    let res = base2_unop op' x in
    let real_str = str_of_float real in
    let res_str = str_of_float res in
    if not (String.equal real_str res_str) then
      printf "FAIL: base 2, %s %f <> %f, real %s <> %s\n"
        opstr x res real_str res_str
    else printf "OK!\n"

  let unop10 opstr op op' x =
    let real = op x in
    let res = base10_unop op' x in
    let real_str = str_of_float real in
    let res_str = str_of_float res in
    if not (String.equal real_str res_str) then
      printf "FAIL: base 10, %s %f <> %f, real %s <> %s\n"
        opstr x res real_str res_str
    else printf "OK!\n"

  let fraction_of_float x =
    let bits = Word.of_int64 (Int64.bits_of_float x) in
    let frac = Word.extract_exn ~hi:51 bits in
    string_of_bits frac

  let bitstring_of_float x =
    let x = Int64.bits_of_float x |> Word.of_int64 in
    sb64 x

  let binop2 opstr op op' x y =
    let real = op x y in
    let res = base2_binop op' x y in
    let bs = bitstring_of_float in
    printf "cmp:\n %s <- expected (%f)\n %s <- what we got\n"
      (bs real) real (bs res);

    let real_str = str_of_float real in
    let res_str = str_of_float res in
    if not (String.equal real_str res_str) then
      printf "FAIL: base 2, %f %s %f <> %f, real %s <> %s\n"
        x opstr y res real_str res_str
    else printf "OK!\n"

  let binop10 opstr op op' x y =
    let real = op x y in
    let res = base10_binop op' x y in
    let real_str = str_of_float real in
    let res_str = str_of_float res in
    if not (String.equal real_str res_str) then
      printf "FAIL: base 10, %f %s %f <> %f, real %s <> %s\n"
        x opstr y res real_str res_str
    else printf "OK!\n"

  let run2 = true
  let run10 = false

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

  (* let () = 4.2 - 2.28 *)
  (* let () = (neg 2.2) + 4.8 *)
  let () = 0.01 - 0.0002
  (* let () = 0.0000001 - 0.00000002 *)
end

(* module Run1 = Run_test(struct type t = unit end) *)
(* module Run2 = Run_manually(struct type t = unit end) *)

(* let () = *)
(*   let x = 0.0002 in *)
(*   let bits = Word.of_int64 (Int64.bits_of_float x) in *)
(*   printf "test %f %s\n" x (sb64 bits) *)
