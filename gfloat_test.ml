open Core_kernel
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

let max_of_precision p = int_of_float (2.0 ** float_of_int p)

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

let decimal_precision = 26
let decimal_expn_bits = 10

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
    let precision = decimal_precision in
    let max_int = max_of_precision precision in
    let expn = - (String.length remd) in
    let expn, int_part = truncate max_int expn (base ^ remd) in
    let frac = Word.of_int ~width:precision int_part in
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

let float_of_decimal t = match t.value with
  | Fin {expn;frac} ->
    let expn = Word.to_int_exn (Word.signed expn) in
    let frac = wdec frac in
    let len = String.length frac in
    let frac =
      if expn = 0 then frac
      else if expn < 0 && expn < -len then
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
        insert_point frac (len + expn) in
    let frac = float_of_string frac in
    if t.sign = Neg then ~-. frac
    else frac
  | Inf ->
    begin
      match t.sign with
      | Pos -> Float.infinity
      | Neg -> Float.neg_infinity
    end
  | Nan _ ->
    let x = Float.nan in
    match t.sign with
    | Pos -> x
    | Neg -> ~-. x



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

type binop =
  | Add
  | Sub
  | Mul
  | Div

type unop =
  | Sqrt

let str_of_binop = function
  | Add -> "+"
  | Sub -> "-"
  | Mul -> "*"
  | Div -> "/"

let str_of_unop = function
  | Sqrt -> "sqrt"

let true_result x y op = match op with
  | Add -> x +. y
  | Sub -> x -. y
  | Mul -> x *. y
  | Div -> x /. y

let binop = function
  | Add -> add ~rm:Nearest_even
  | Sub -> sub ~rm:Nearest_even
  | Mul -> mul ~rm:Nearest_even
  | Div -> div ~rm:Nearest_even

let unop = function
  | Sqrt -> sqrt ~rm:Nearest_even

let compare_str x y =
  if String.equal x y then "ok" else "POSSIBLE FAIL"

let my_string_of_float x = sprintf "%.15f" x

let decimal op x y =
  let f1 = decimal_of_string (my_string_of_float x) in
  let f2 = decimal_of_string (my_string_of_float y) in
  let fr = (binop op) f1 f2 in
  float_of_decimal fr

let ieee_single op x y =
  let f1 = single_of_float x in
  let f2 = single_of_float y in
  let fr = (binop op) f1 f2 in
  float_of_single fr

let ieee_double op x y =
  let f1 = double_of_float x in
  let f2 = double_of_float y in
  let fr = (binop op) f1 f2 in
  float_of_double fr

let double_nan = double_of_float Float.nan
let double_inf = double_of_float Float.infinity
let decimal_nan = decimal_of_float Float.nan
let decimal_inf = decimal_of_float Float.infinity

let run op x y =
  let res = true_result x y op in
  let bin = ieee_double op x y in
  let dec = decimal op x y in
  let res_str = sprintf "%.6f" res in
  let bin_str = sprintf "%.6f" bin in
  let dec_str = sprintf "%.6f" dec in
  printf "bin: %g %s %g = %s(%s) %s\n" x (str_of_binop op) y bin_str res_str
    (compare_str res_str bin_str);
  printf "dec: %g %s %g = %s(%s) %s\n" x (str_of_binop op) y dec_str res_str
    (compare_str res_str dec_str)

let true_result_unop op x =
  match op with
  | Sqrt -> Float.sqrt x

let run_unop op x =
  let res = true_result_unop op x in
  let bin = unop op @@ (double_of_float x) in
  let bin = float_of_double bin in
  let dec = unop op @@ decimal_of_string (my_string_of_float x) in
  let dec = float_of_decimal dec in
  let res_str = sprintf "%.6f" res in
  let bin_str = sprintf "%.6f" bin in
  let dec_str = sprintf "%.6f" dec in
  printf "bin: %g %s = %s(%s) %s\n" x (str_of_unop op) bin_str res_str
    (compare_str res_str bin_str);
  printf "dec: %g %s = %s(%s) %s\n" x (str_of_unop op) dec_str res_str
    (compare_str res_str dec_str)

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

let neg x = ~-. x
let (+) = run Add
let (-) = run Sub
let ( * ) = run Mul
let ( / ) = run Div
let ( sqrt ) = run_unop Sqrt
let space () = printf "\n\n"
let nan = Float.nan
let inf = Float.infinity
let ninf = Float.neg_infinity

module Main_test(F : T) = struct

  let () =
    create 4.2;
    create 4.28;
    create 2.2;
    create 7.18;
    create (~-.2.00008);
    space ();

    4.2 + 2.3;
    4.2 + 2.98;
    2.2 + 4.28;
    2.2 + (neg 4.28);
    (neg 2.2) + 4.28;
    2.2 + 2.46;
    0.0000001 + 0.00000002;
    4.2 + 2.98;
    space ();

    4.2 - 2.28;
    4.28 - 2.2;
    2.2 - 4.28;
    2.2 - (neg 4.28);
    2.2 - 2.6;
    (neg 2.2) - 2.46;
    (neg 2.2) - (neg 2.46);
    0.0000001 - 0.00000002;
    space ();

    1.0 * 2.5;
    2.5 * 0.5;
    4.2 * 3.4;
    0.01 * 0.02;
    1.0 * 0.5;
    1.0 * (neg 0.5);
    (neg 1.0) * (neg 0.5);
    space ();

    1.0 / 0.0;
    2.0 / 0.5;
    1.0 / 3.0;
    2.4 / 3.123131;
    0.1313134 / 0.578465631;
    3.0 / 32.0;
    324.32423 / 1.2;
    42.3 / 0.0;
    0.0 / 0.0;
    space ();

    sqrt 423245.0;
    sqrt 0.213;
    sqrt 1.2356;
    sqrt 0.0;
    sqrt 1.0;
    sqrt 2.0;
    sqrt 3.0;
    sqrt 20.0;
    sqrt (~-.1.0);
    space ();

    nan  + nan;
    inf  + inf;
    ninf + ninf;
    nan  + ninf;
    ninf + nan;
    nan  + inf;
    inf  + nan;
    ninf + inf;
    inf  + ninf;
    space();

    nan  - nan;
    inf  - inf;
    ninf - ninf;
    nan  - ninf;
    ninf - nan;
    nan  - inf;
    inf  - nan;
    ninf - inf;
    inf  - ninf;
    space();

    nan  * nan;
    inf  * inf;
    ninf * ninf;
    nan  * ninf;
    ninf * nan;
    nan  * inf;
    inf  * nan;
    ninf * inf;
    inf  * ninf;
    space();

    nan  / nan;
    inf  / inf;
    ninf / ninf;
    nan  / ninf;
    ninf / nan;
    nan  / inf;
    inf  / nan;
    ninf / inf;
    inf  / ninf;
    space();

    sqrt nan;
    sqrt inf;
    sqrt ninf;
    sqrt ninf;
    sqrt nan;
    sqrt inf;
    sqrt nan;
    sqrt inf;
    sqrt ninf;
    space();

(*     // See Note 1. *)
(*     { PInf, SNaN, "nan", APFloat::opInvalidOp, APFloat::fcNaN }, *)
(* #endif *)
(*     { PInf, PNormalValue, "inf", APFloat::opOK, APFloat::fcInfinity }, *)
(*     { PInf, MNormalValue, "inf", APFloat::opOK, APFloat::fcInfinity }, *)
(*     { PInf, PLargestValue, "inf", APFloat::opOK, APFloat::fcInfinity }, *)
(*     { PInf, MLargestValue, "inf", APFloat::opOK, APFloat::fcInfinity }, *)
(*     { PInf, PSmallestValue, "inf", APFloat::opOK, APFloat::fcInfinity }, *)
(*     { PInf, MSmallestValue, "inf", APFloat::opOK, APFloat::fcInfinity }, *)
(*     { PInf, PSmallestNormalized, "inf", APFloat::opOK, APFloat::fcInfinity }, *)
(*     { PInf, MSmallestNormalized, "inf", APFloat::opOK, APFloat::fcInfinity }, *)
(*     { MInf, PInf, "nan", APFloat::opInvalidOp, APFloat::fcNaN }, *)
(*     { MInf, MInf, "-inf", APFloat::opOK, APFloat::fcInfinity }, *)
(*     { MInf, PZero, "-inf", APFloat::opOK, APFloat::fcInfinity }, *)
(*     { MInf, MZero, "-inf", APFloat::opOK, APFloat::fcInfinity }, *)
(*     { MInf, QNaN, "nan", APFloat::opOK, APFloat::fcNaN }, *)

end

module Run = Main_test(struct type t = unit end)

(* let () = deconstruct64 Float.epsilon_float *)
(* let () = printf "min is %.56f\n" Float.epsilon_float *)
(* let () = printf "max is %f\n" Float.max_finite_value *)
(* let x = largest ~base:2 11 53 *)
(* let y = float_of_double x *)
(* let () = printf "my max y is %f\n" y *)
(* let x = least ~base:2 11 53 *)
(* let y = float_of_double x *)
(* let () = printf "my min y is %f\n" y *)
