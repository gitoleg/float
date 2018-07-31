open Core_kernel
open OUnit2
open Bap.Std

open Gfloat

type ieee_bin = {
  expn_width : int;  (* bits in exponent *)
  frac_width : int;  (* bits in fraction *)
  int_bit    : bool;  (* integer bit, if exists *)
  bias       : int;
}

let single = { expn_width=8;  bias=127;  frac_width=23; int_bit=false }
let double = { expn_width=11; bias=1023; frac_width=52; int_bit=false }

let drop_hd w =
  let hi = Word.bitwidth w - 2 in
  Word.extract_exn ~hi w

let all_ones  x = Word.(x = ones (bitwidth x))
let all_zeros x = Word.(x = zero (bitwidth x))

let enum_bits w =
  let bits = Word.enum_bits w BigEndian in
  let b_len = Seq.length bits in
  let w_len = Word.bitwidth w in
  if b_len > w_len then
    Seq.drop bits (b_len - w_len)
  else bits

let msb w =
  let bits = enum_bits w in
  match Seq.findi bits ~f:(fun i x -> x) with
  | None -> None
  | Some (i,_) -> Some (Word.bitwidth w - i - 1)

let t_of_bits {expn_width;bias;frac_width;int_bit} bits =
  let total = Word.bitwidth bits in
  let sign = Word.extract_exn ~hi:(total - 1) ~lo:(total - 1) bits in
  let negative = Word.is_one sign in
  let hi_expn, lo_expn = total - 2, total - 2 - expn_width + 1 in
  let hi_frac = lo_expn - 1 in
  let precs = if int_bit then frac_width else frac_width + 1 in
  let expn_bits =
    Word.extract_exn ~hi:hi_expn ~lo:lo_expn bits in
  let frac = Word.extract_exn ~hi:hi_frac bits in
  let expn' = Word.to_int_exn expn_bits - bias in
  if all_ones expn_bits && Word.is_zero frac then
    mk_inf ~base:2 precs ~negative
  else if all_ones expn_bits then
    mk_nan ~base:2 precs
  else if all_zeros expn_bits && all_zeros frac then
    let expn = Word.of_int ~width:expn_width expn' in
    mk ~base:2 ~negative expn (Word.concat Word.b0 frac)
  else
    let dexp = Word.bitwidth frac in
    let ibit = if all_zeros expn_bits && all_zeros frac then Word.b0
      else Word.b1 in
    let expn = Word.of_int ~width:expn_width (expn' - dexp) in
    let frac = if int_bit then frac else Word.concat ibit frac in
    mk ~base:2 ~negative expn frac

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
      let len = Word.bitwidth frac in
      let shift = len - i - 1 in
      let shift' = Word.of_int ~width:len shift in
      let frac = Word.(frac lsl shift') in
      let expn = expn - shift in
      expn, frac in
  let expn, frac = norm_expn biased_expn frac in
  norm_frac expn frac

let sign_bit t = if is_neg t then Word.b1 else Word.b0

let bits_of_t kind t =
  let total = kind.expn_width + kind.frac_width + 1 in
  let total = if kind.int_bit then total + 1 else total in
  let (^) = Word.concat in
  if is_zero t then Word.zero total
  else if is_fin t then
    let expn, frac = Option.value_exn (fin t) in
    let expn = Word.to_int_exn expn in
    let expn = kind.bias + expn in
    let n = Word.bitwidth frac - 1 in
    let expn = expn + n in
    let expn,frac = normalize_ieee kind.bias expn frac in
    let frac = if kind.int_bit then frac else drop_hd frac in
    let expn = Word.of_int ~width:kind.expn_width expn in
    sign_bit t ^ expn ^ frac
  else if is_nan t then
    let frac = Option.value_exn (frac t) in
    let expn = Word.ones kind.expn_width in
    let frac = if kind.int_bit then frac else drop_hd frac in
    sign_bit t ^ expn ^ frac
  else
    let expn = Word.ones kind.expn_width in
    let frac = Word.zero kind.frac_width in
    sign_bit t ^ expn ^ frac

let float_of_single t =
  let bits = bits_of_t single t in
  let bits = Word.signed bits |> Word.to_int32_exn in
  Int32.float_of_bits bits

let float_of_double t =
  let bits = bits_of_t double t in
  let bits = Word.signed bits |> Word.to_int64_exn in
  Int64.float_of_bits bits

let truncate_zeros x =
  match String.index x '.' with
  | None -> x
  | Some p -> String.rstrip ~drop:(fun c -> Char.equal c '0') x

let decimal_precision = 50
let decimal_expn_bits = 10

let log2 x = Float.log10 x /. Float.log10 2.0
let pow2 x = int_of_float (2.0 ** float_of_int x)

(* return max bits required for encodind [n] decimal digits  *)
let bits_of_digits n =
  int_of_float (Float.round_up (float n *. log2 10.0))

(* return max decimal digits, that could be encoding using [n] bits *)
let digits_of_bits n =
  String.length (sprintf "%d" (pow2 n - 1))

let enum_bits w =
  let bits = Word.enum_bits w BigEndian in
  let b_len = Seq.length bits in
  let w_len = Word.bitwidth w in
  if b_len > w_len then
    Seq.drop bits (b_len - w_len)
  else bits

let msb w =
  let bits = enum_bits w in
  match Seq.findi bits ~f:(fun i x -> x) with
  | None -> None
  | Some (i,_) -> Some (Word.bitwidth w - i - 1)

let min_bits w = match msb w with
  | None -> 0
  | Some i -> i + 1

let is_zero_float x =
  String.for_all x ~f:(fun c ->
      Char.equal c '0' || Char.equal c '.')

let actual_bits x =
  if String.is_empty x then 0
  else
    let len = bits_of_digits (String.length x) in
    let w = Word.of_string (sprintf "%s:%du" x len) in
    min_bits w

exception Not_created of string

let check_int_part str =
  let max_digits = digits_of_bits decimal_precision in
  if (String.length str > max_digits) then
    let err = sprintf "cat'n represent %s in %d bits" str
        decimal_precision in
    raise (Not_created err)

let rec adjust_base10 x expn bits =
  if min_bits x <= bits then x,expn
  else
    let ten = Word.of_int ~width:(Word.bitwidth x) 10 in
    adjust_base10 Word.(x / ten) (expn + 1) bits

let str_of_float x = sprintf "%.16f" x

let insert_point str expn =
  let insert str before =
    List.foldi (String.to_list str) ~init:[]
      ~f:(fun i acc c ->
          if i = before then c :: '.' :: acc
          else c :: acc) |> List.rev |> String.of_char_list in
  let len = String.length str in
  if expn = 0 then str
  else if is_zero_float str then "0.0"
  else if expn < 0 && abs expn > len then
    let zeros = String.init (abs expn - len + 1) ~f:(fun _ -> '0') in
    let str = zeros ^ str in
    insert str (String.length str - abs expn)
  else if expn < 0 && abs expn = len then
    let str = "0" ^ str in
    insert str (len - abs expn + 1)
  else if expn < 0 then
    insert str (len - abs expn)
  else if expn > 0 && expn > len then
    let zeros = String.init (expn - len) ~f:(fun _ -> '0') in
    let str = zeros ^ str in
    insert str expn
  else
    let zeros = String.init expn ~f:(fun _ -> '0') in
    let str = str ^ zeros in
    insert str (len + expn)

let truncate str =
  let x = truncate_zeros str in
  let is_neg = List.hd_exn (String.to_list x) = '-' in
  let start, point =
    let p = String.index_exn x '.' in
    if is_neg then 1, p
    else 0, p in
  let base = String.subo ~pos:start ~len:(point - start) x in
  let remd = String.subo ~pos:(point + 1) x in
  let expn = - (String.length remd) in
  check_int_part base;
  let bits = actual_bits (base ^ remd) in
  if bits = 0 then is_neg, str, expn
  else
    let frac = Word.of_string (sprintf "%s%s:%du" base remd bits) in
    let frac,expn = adjust_base10 frac expn decimal_precision in
    let frac = Word.extract_exn ~hi:(decimal_precision - 1) frac in
    is_neg, Word.string_of_value ~hex:false frac, expn

let decimal_of_string = function
  | "nan" -> mk_nan ~base:10 decimal_precision
  | "inf" -> mk_inf ~base:10 decimal_precision
  | "-inf" -> mk_inf ~base:10 decimal_precision ~negative:true
  | str ->
    let negative, frac,expn = truncate str in
    if is_zero_float frac then
      mk ~base:10 ~negative
        (Word.zero decimal_expn_bits)
        (Word.zero decimal_precision)
    else
      let frac = Word.of_string (sprintf "%s:%du" frac decimal_precision) in
      let expn = Word.of_int ~width:decimal_expn_bits expn in
      mk ~base:10 ~negative expn frac

let truncate_float f =
  let is_neg, x,e = truncate (str_of_float f) in
  let x = float_of_string (insert_point x e) in
  if is_neg then ~-. x
  else x

let decimal_of_float x = decimal_of_string (str_of_float x)
let attach_sign x t = if is_neg t then ~-. x else x

let string_of_decimal t =
  let attach_sign x = if is_neg t then "-" ^ x else x in
  if is_fin t then
    let expn, frac = Option.value_exn (fin t) in
    let expn = Word.to_int_exn (Word.signed expn) in
    let frac = Word.string_of_value ~hex:false frac in
    insert_point frac expn |> attach_sign
  else if is_nan t then attach_sign "nan"
  else attach_sign "inf"

let float_of_decimal x = float_of_string (string_of_decimal x)

let factorial x =
  let rec loop r n =
    if n <> 0 then
      loop (r * n) (n - 1)
    else r in
  loop x (x - 1)

let max_n = 50

let gfloat_pow of_float x n =
  let rec loop r k =
    if k < n then loop (mul r x) (k + 1)
    else r in
  if n = 0 then of_float 1.0
  else loop x 1

let gen_sin of_float to_float arg =
  let pow = gfloat_pow of_float in
  let of_int_opt x =
    try Some (of_float (float_of_int x))
    with _ -> None in
  let arg = of_float arg in
  let mone = of_float (~-. 1.0) in
  let rec run res n =
    if n < max_n then
      let s = pow mone n in
      match of_int_opt (factorial (2 * n + 1)) with
      | None -> res
      | Some f ->
        let res' = add res (mul (pow arg (2 * n + 1)) (div s f)) in
        if is_fin res' then
          run res' (n + 1)
        else res
    else res in
  run (of_float 0.0) 0 |> to_float

(* we will compute a real sin x like bellow, i.e.
   like we do it for gfloat above, because
   we can't assume that implementation behind
   Pervasives.sin is the same as ours *)
let ocaml_sin arg =
  let rec run res n =
    if n < max_n then
      let s = (~-. 1.0) ** float_of_int n in
      let f = float_of_int (factorial (2 * n + 1)) in
      let x = arg ** float_of_int (2 * n + 1) in
      let res' = res +. (x *. s /. f) in
      if Float.is_nan res' || Float.is_inf res' then res
      else run res' (n + 1)
    else res in
  run 0.0 0

let gen_binop of_float to_float op x y =
  op (of_float x) (of_float y) |> to_float

let gen_unop of_float to_float op x =
  op (of_float x) |> to_float

let base2_binop = gen_binop double_of_float float_of_double
let base10_binop = gen_binop decimal_of_float string_of_decimal
let base2_unop = gen_unop double_of_float float_of_double
let base10_unop = gen_unop decimal_of_float string_of_decimal
let nan = Float.nan
let inf = Float.infinity
let ninf = Float.neg_infinity

let equal_base2 x y =
  let x = Int64.bits_of_float x in
  let y = Int64.bits_of_float y in
  Int64.equal x y

let string_equal real ours =
  let ours = truncate_zeros ours in
  let len = String.length ours in
  let f x =
    match String.index x '.' with
    | None -> x
    | Some i when i < len - 2 ->
      String.subo ~len:(len - 1) x
    | _ ->
      String.subo ~len:len  x in
  String.equal (f real) (f ours)

let string_equal' real ours =
  let real_plus = real +. Float.epsilon_float |> str_of_float in
  let real_mins = real -. Float.epsilon_float |> str_of_float in
  string_equal real_plus ours ||
  string_equal real_mins ours

let equal_base10 real ours =
  string_equal (str_of_float real) ours ||
  string_equal' real ours

let equal_base2 x y =
  let x = Int64.bits_of_float x in
  let y = Int64.bits_of_float y in
  Int64.equal x y

let binop op op' x y ctxt =
  let real2 = op x y in
  let r2 = base2_binop op' x y in
  assert_equal ~ctxt ~cmp:equal_base2 real2 r2;
  let x = truncate_float x in
  let y = truncate_float y in
  let real10 = op x y in
  let r10 = base10_binop op' x y in
  let equal = equal_base10 real10 r10 in
  assert_bool "binop base 10 failed" equal

let binop_special op op' x y ctxt =
  let real = str_of_float (op x y) in
  let r2 = str_of_float (base2_binop op' x y) in
  assert_equal ~ctxt ~cmp:String.equal real r2;
  let r10 = base10_binop op' x y in
  assert_equal ~ctxt ~cmp:String.equal real r10

let unop op op' x ctxt =
  let real2 = op x in
  let r2 = base2_unop op' x in
  assert_equal ~ctxt ~cmp:equal_base2 real2 r2;
  let x = truncate_float x in
  let real10 = op x in
  let r10 = base10_unop op' x in
  let equal = equal_base10 real10 r10 in
  assert_bool "unop base 10 failed" equal

let sin x ctxt =
  let real = ocaml_sin x in
  let r2 = gen_sin double_of_float float_of_double x in
  assert_equal ~ctxt ~cmp:equal_base2 real r2;
  let r10 = gen_sin decimal_of_float string_of_decimal x in
  let equal = equal_base10 real r10 in
  assert_bool "sin base 10 failed" equal

let unop_special op op' x ctxt =
  let real = str_of_float (op x) in
  let r2 = str_of_float @@ base2_unop op' x in
  assert_equal ~ctxt ~cmp:String.equal real r2;
  let r10 = base10_unop op' x in
  assert_equal ~ctxt ~cmp:String.equal real r10

let add_special x y ctxt = binop_special (+.) add x y ctxt
let sub_special x y ctxt = binop_special (-.) sub x y ctxt
let mul_special x y ctxt = binop_special ( *. ) mul x y ctxt
let div_special x y ctxt = binop_special ( /. ) div x y ctxt
let sqrt_special x ctxt = unop_special Float.sqrt sqrt x ctxt

let add x y ctxt = binop (+.) add x y ctxt
let sub x y ctxt = binop (-.) sub x y ctxt
let mul x y ctxt = binop ( *. ) mul x y ctxt
let div x y ctxt = binop ( /. ) div x y ctxt
let sqrt x ctxt = unop Float.sqrt sqrt x ctxt

let ( + ) = add
let ( - ) = sub
let ( * ) = mul
let ( / ) = div
let ( sqrt ) = sqrt

let ( +$ ) = add_special
let ( -$ ) = sub_special
let ( *$ ) = mul_special
let ( /$ ) = div_special

let neg x = ~-.x

let suite () =

  "Gfloat test" >::: [

    (* add *)
    "0.0 + 0.5"     >:: 0.0 + 0.5;
    "4.2 + 2.3"     >:: 4.2 + 2.3;
    "4.2 + 2.98"    >:: 4.2 + 2.98;
    "2.2 + 4.28"    >:: 2.2 + 4.28;
    "2.2 + -4.28"   >:: 2.2 + (neg 4.28);
    "-2.2 + 4.28"   >:: (neg 2.2) + 4.28;
    "2.2 + 2.46"    >:: 2.2 + 2.46;
    "0.0000001 + 0.00000002" >:: 0.0000001 + 0.00000002;
    "123213123.23434 + 56757.05656549151" >:: 123213123.23434 + 56757.05656549151;
    "nan  + nan"    >:: nan  +$ nan;
    "inf  + inf"    >:: inf  +$ inf;
    "-inf + -inf"   >:: ninf +$ ninf;
    "nan  + -inf"   >:: nan  +$ ninf;
    "-inf + nan"    >:: ninf +$ nan;
    "nan  + inf"    >:: nan  +$ inf;
    "inf  + nan"    >:: inf  +$ nan;
    "-inf + inf"    >:: ninf +$ inf;
    "inf  + -inf"   >:: inf  +$ ninf;

    (* sub *)
    "4.2 - 2.28"    >:: 4.2 - 2.28;
    "4.28 - 2.2"    >:: 4.28 - 2.2;
    "2.2 - 4.28"    >:: 2.2 - 4.28;
    "2.2 - -4.28"   >:: 2.2 - (neg 4.28);
    "2.2 - 2.6"     >:: 2.2 - 2.6;
    "-2.2 - 2.46"   >:: (neg 2.2) - 2.46;
    "-2.2 - -2.46)" >:: (neg 2.2) - (neg 2.46);
    "0.0000001 - 0.00000002" >:: 0.0000001 - 0.00000002;
    "0.0 - 0.00000001" >:: 0.0 - 0.0000001;
    "0.0 - 0.0"     >:: 0.0 - 0.0;
    "4.2 - 4.2"     >:: 4.2 - 4.2;
    "123213123.23434 - 56757.05656549151" >:: 123213123.23434 - 56757.05656549151;
    "nan  - nan"    >:: nan  -$ nan;
    "inf  - inf"    >:: inf  -$ inf;
    "-inf - -inf"   >:: ninf -$ ninf;
    "nan  - -inf"   >:: nan  -$ ninf;
    "-inf - nan"    >:: ninf -$ nan;
    "nan  - inf"    >:: nan  -$ inf;
    "inf  - nan"    >:: inf  -$ nan;
    "-inf - inf"    >:: ninf -$ inf;
    "inf  - -inf"   >:: inf  -$ ninf;

    (* mul *)
    "1.0 * 2.5"    >:: 1.0 * 2.5;
    "2.5 * 0.5"    >:: 2.5 * 0.5;
    "4.2 * 3.4"    >:: 4.2 * 3.4;
    "0.01 * 0.02"  >:: 0.01 * 0.02;
    "1.0 * 0.5"    >:: 1.0 * 0.5;
    "1.0 * -0.5"   >:: 1.0 * (neg 0.5);
    "- 1.0 * -0.5" >:: (neg 1.0) * (neg 0.5);
    "9991132.2131363434 * 2435.05656549151" >:: 9991132.2131363434 * 2435.05656549151;
    "nan  * nan"   >:: nan  *$ nan;
    "inf  * inf"   >:: inf  *$ inf;
    "-inf * -inf"  >:: ninf *$ ninf;
    "nan  * -inf"  >:: nan  *$ ninf;
    "-inf * nan"   >:: ninf *$ nan;
    "nan  * inf"   >:: nan  *$ inf;
    "inf  * nan"   >:: inf  *$ nan;
    "-inf * inf"   >:: ninf *$ inf;
    "inf  * -inf"  >:: inf  *$ ninf;

    (* div *)
    "1.0 / 0.0"   >:: 1.0 / 0.0;
    "2.0 / 0.5"   >:: 2.0 / 0.5;
    "1.0 / 3.0"   >:: 1.0 / 3.0;
    "3.0 / 32.0"  >:: 3.0 / 32.0;
    "42.3 / 0.0"  >:: 42.3 / 0.0;
    "0.0 / 0.0"   >:: 0.0 /$ 0.0;
    "324.32423 / 1.2" >:: 324.32423 / 1.2;
    "2.4 / 3.123131"  >:: 2.4 / 3.123131;
    "0.1313134 / 0.578465631" >:: 0.1313134 / 0.578465631;
    "9991132.2131363434 / 2435.05656549151" >:: 9991132.2131363434 / 2435.05656549151;
    "nan  / nan"  >:: nan  /$ nan;
    "inf  / inf"  >:: inf  /$ inf;
    "-inf / -inf" >:: ninf /$ ninf;
    "nan  / -inf" >:: nan  /$ ninf;
    "-inf / nan"  >:: ninf /$ nan;
    "nan  / inf"  >:: nan  /$ inf;
    "inf  / nan"  >:: inf  /$ nan;
    "-inf / inf"  >:: ninf /$ inf;
    "inf  / -inf" >:: inf  /$ ninf;

    (* sqrt  *)
    "sqrt 423245.0" >:: sqrt 423245.0;
    "sqrt 0.213"    >:: sqrt 0.213;
    "sqrt 1.2356"   >:: sqrt 1.2356;
    "sqrt 0.0"      >:: sqrt 0.0;
    "sqrt 1.0"      >:: sqrt 1.0;
    "sqrt 2.0"      >:: sqrt 2.0;
    "sqrt 3.0"      >:: sqrt 3.0;
    "sqrt 20.0"     >:: sqrt 20.0;
    "sqrt 9991132.2131363434 " >:: sqrt 9991132.2131363434;
    "sqrt (-1)"     >:: sqrt_special (neg 1.0);
    "sqrt nan"      >:: sqrt_special nan;
    "sqrt inf"      >:: sqrt_special inf;
    "sqrt -inf"     >:: sqrt_special ninf;

    (* sin  *)
    "sin 0.0"       >:: sin 0.0;
    "sin 0.5"       >:: sin 0.5;
    "sin 1.0"       >:: sin 1.0;
    "sin 0.5216..." >:: sin 0.52167823455675756576;
  ]

let () = run_test_tt_main (suite ())
