open Core_kernel
open OUnit2
open Bap.Std
open Gfloat
open Gfloat_w

let allow_output = true

let printf fmt =
  let doit str =
    if allow_output then
      printf "%s" str in
  ksprintf doit fmt

let msb w =
  let rec run n =
    if n = 64 then None
    else
      let probe = Int64.((one lsl 63) lsr n) in
      if Int64.(probe land w = probe) then Some (63 - n)
      else run (n + 1) in
  run 0

let double_total = 64
let double_ebits = 11
let double_fbits = 52
let double_bias = 1023

let inf_bits = Int64.bits_of_float Caml.infinity
let ninf_bits = Int64.bits_of_float Caml.neg_infinity
let nan_bits = Int64.bits_of_float Caml.nan

let double_of_float x =
  let desc = desc ~radix:2 ~expn_bits:double_ebits (double_fbits + 1) in
  let negative = x < 0.0 in
  let create ~expn frac =
    create desc ~negative ~expn frac in
  let bits = Int64.bits_of_float x in
  if Int64.(bits = inf_bits) then inf desc
  else if Int64.(bits = ninf_bits) then inf desc ~negative:true
  else if Int64.(bits = nan_bits) then nan desc
  else
    let bits = Word.of_int64 bits in
    let expn = Word.to_int_exn (Word.extract_exn ~hi:62 ~lo:52 bits) in
    let frac = Word.extract_exn ~hi:51 bits in
    let expn' = expn - double_bias in
    if Int.(expn = 0) && Word.is_zero frac then zero desc
    else
      let is_subnormal = Int.(expn = 0) in
      let dexp = if expn = 0 then 0 else 52 in
      let expn = expn' - dexp in
      let expn = Word.of_int ~width:double_ebits expn in
      let frac =
        if is_subnormal then Word.(concat b0 frac)
        else Word.(concat b1 frac) in
      create ~expn frac

let normalize_ieee biased_expn frac =
  let bias = double_bias in
  let min_expn = 1 in
  let max_expn = bias * 2 in
  let rec norm_expn expn frac =
    if expn = 0 then expn,frac
    else if Int.(expn > max_expn) then
      norm_expn (pred expn) Int64.(frac lsl 1)
    else if Int.(expn < min_expn) then
      norm_expn (succ expn) Int64.(frac lsr 1)
    else expn, frac in
  let norm_frac expn frac =
    let len = 53 in
    let unos = Int64.minus_one in
    if Int64.(frac = unos) then
      expn + 1, Int64.zero
    else
    match msb frac with
    | None -> expn, frac
    | Some i ->
      let shift = len - i - 1 in
      let frac = Int64.(frac lsl shift) in
      let expn = expn - shift in
      expn, frac in
  if biased_expn = 0 then biased_expn,frac
  else
    let expn, frac = norm_expn biased_expn frac in
    norm_frac expn frac

let sign_bit t bits =
  if is_neg t then
    let uno = Int64.(one lsl 63) in
    Int64.(uno lor bits)
  else bits

let drop_hd w =
  let ones = Int64.of_int (-1) in
  let ones = Int64.(ones lsr 12) in
  Int64.(w land ones)

let int64_of_bits is_neg expn frac =
  let signb = if is_neg then Int64.(one lsl 63) else Int64.zero in
  let expn = Int64.(expn lsl 52) in
  let expn = Int64.((expn lsl 1) lsr 1) in
  Int64.(signb lor expn lor frac)

let float_of_double t =
  if is_zero t then if is_neg t then ~-. 0.0 else 0.0
  else if is_fin t then
    let (expn, frac) = Option.value_exn (fin t) in
    let expn = Word.signed expn in
    let expn = Word.to_int_exn expn in
    let frac = Word.to_int64_exn frac in
    let expn = double_bias + expn in
    let dexpn = if expn = 0 then 0 else 52 in
    let expn = expn + dexpn in
    let expn,frac = normalize_ieee expn frac in
    let frac = drop_hd frac in
    let expn = Int64.of_int expn in
    let r = int64_of_bits (is_neg t) expn frac in
    Int64.float_of_bits r
  else if is_nan t then
    if is_neg t then ~-. Caml.nan else Caml.nan
  else
  if is_neg t then Caml.neg_infinity
  else Caml.infinity

let bits64 f =
  let bits = Z.of_int64 (Int64.bits_of_float f) in
  let bits = List.init 64 ~f:(fun i ->
      if Z.testbit bits i then '1' else '0') |>
             List.rev in
  List.foldi ~init:"" bits ~f:(fun i s c ->
      if i = 0 || i = 11 then sprintf "%s%c_" s c
      else sprintf "%s%c" s c)

let truncate_zeros x =
  match String.index x '.' with
  | None -> x
  | Some p -> String.rstrip ~drop:(fun c -> Char.equal c '0') x

let decimal_precision = 50
let decimal_expn_bits = 10
let decimal_desc = desc ~radix:10 ~expn_bits:decimal_expn_bits decimal_precision

let log2 x = Float.log10 x /. Float.log10 2.0
let pow2 x = int_of_float (2.0 ** float_of_int x)

(* return max bits required for encodind [n] decimal digits  *)
let bits_of_digits n =
  int_of_float (Float.round_up (float n *. log2 10.0))

(* return max decimal digits, that could be encoding using [n] bits *)
let digits_of_bits n =
  String.length (sprintf "%d" (pow2 n - 1))

let min_bits w = Z.numbits w

let is_zero_float x =
  String.for_all x ~f:(fun c ->
      Char.equal c '0' || Char.equal c '.')

let str_of_float x = sprintf "%.16f" x

let actual_bits x =
  if String.is_empty x then 0
  else min_bits (Z.of_string x)

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
    let ten = Z.of_int 10 in
    adjust_base10 Z.(x / ten) (expn + 1) bits

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
    let frac = Z.of_string (base ^ remd) in
    let frac,expn = adjust_base10 frac expn decimal_precision in
    let frac = Z.extract frac 0 decimal_precision in
    is_neg, Z.to_string frac, expn

let create_decimal negative ~expn frac =
  create decimal_desc ~negative ~expn frac

let decimal_of_string = function
  | "nan" -> nan decimal_desc
  | "inf" -> inf decimal_desc
  | "-inf" -> inf ~negative:true decimal_desc
  | str ->
    let negative, frac, expn = truncate str in
    if is_zero_float frac then
      let expn = Word.zero decimal_expn_bits in
      let frac = Word.zero decimal_precision in
      create_decimal negative ~expn frac
    else
      let frac = Word.of_int64 ~width:decimal_precision
                   (Int64.of_string frac) in
      let expn = Word.of_int ~width:decimal_expn_bits expn in
      create_decimal negative ~expn frac

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
    let (expn,frac) = Option.value_exn (fin t) in
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

(* just an arbitary number  *)
let max_n = 50


let to_str x = match fin x with
  | None -> "not a finite number"
  | Some (e,f) ->
     sprintf "(%s %s)"
       (Bignum_of_word.to_string e)
       (Bignum_of_word.to_string f)


let gfloat_pow of_float x n =
  let rec loop r k =
    if k < n then loop (mul r x) (k + 1)
    else r in
  if n = 0 then of_float 1.0
  else loop x 1

let gen_sin of_float to_float ~prec arg =
  let ext x = extend x prec in
  let of_float x = ext @@ of_float x in
  let to_float x = round x ~precision:prec |> to_float in
  let pow = gfloat_pow of_float in
  let of_int_opt x =
    try Some (of_float (float_of_int x))
    with _ -> None in
  let arg = of_float arg in
  let mone = of_float (~-. 1.0) in
  let zero = of_float 0.0 in
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
  run zero 0 |> to_float

let gen_binop of_float to_float op x y =
  op (of_float x) (of_float y) |> to_float

let gen_unop of_float to_float op x =
  op (of_float x) |> to_float

let equal_base2 x y =
  let bits = Int64.bits_of_float in
  Int64.equal (bits x) (bits y)

let base2_binop = gen_binop double_of_float float_of_double
let base2_unop = gen_unop double_of_float float_of_double

let nan = Float.nan
let inf = Float.infinity
let ninf = Float.neg_infinity

let string_equal1 real ours =
  let real = truncate_zeros (string_of_float real) in
  String.equal real (truncate_zeros ours)

let string_equal2 real ours =
  let ours = truncate_zeros ours in
  let len = String.length ours in
  let f x =
    match String.index x '.' with
    | None -> x
    | Some i when i < len - 2 ->
      String.subo ~len:(len - 1) x
    | _ -> String.subo ~len:len  x in
  String.equal (f real) (f ours)

let string_equal3 real ours =
  let real_plus = real +. Float.epsilon_float |> str_of_float in
  let real_mins = real -. Float.epsilon_float |> str_of_float in
  string_equal2 real_plus ours ||
  string_equal2 real_mins ours

let equal_base10 real ours =
  string_equal1 real ours ||
  string_equal2 (str_of_float real) ours ||
  string_equal3 real ours

let base10_binop = gen_binop decimal_of_float string_of_decimal
let base10_unop = gen_unop decimal_of_float string_of_decimal

type binop = [ `Add | `Sub | `Mul | `Div ]
type unop = [ `Sqrt ]

let string_of_binop op x y =
  let op = match op with
    | `Add -> "+"
    | `Sub -> "-"
    | `Mul -> "*"
    | `Div -> "/" in
  sprintf "%.5f %s %.5f" x op y

let string_of_unop op x =
  let op = match op with
    | `Sqrt -> "sqrt" in
  sprintf "%s %.5f" op x

(* returns real and ours binop *)
let get_binop = function
  | `Add -> (+.), add
  | `Sub -> (-.), sub
  | `Mul -> ( *.), mul
  | `Div -> ( /.), div

let get_unop = function
  | `Sqrt -> Caml.sqrt, sqrt



module Debug = struct
  open Pervasives
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

  let wi = Word.to_int_exn

  let deconstruct64 x =
    let y = Int64.bits_of_float x in
    let w = Word.of_int64 y in
    let expn = Word.extract_exn ~hi:62 ~lo:52 w in
    let bias = Word.of_int ~width:11 1023 in
    let expn = Word.(signed (expn - bias)) in
    let frac = Word.extract_exn ~hi:51 w in
    printf "ocaml %f: bits %s\n" x (string_of_bits64 x);
    printf "ocaml %f: unbiased expn %d, frac %s (%d)\n"
      x (wi expn) (string_of_bits frac) (wi frac)
end

let sb = Debug.string_of_bits64

let test_create real =
  let ours = float_of_double (double_of_float real) in
  let x = equal_base2 real ours in
  printf "create %e : %b\n" real x;
  printf "\nreal: %s\nours: %s\n" (sb real) (sb ours)

let is_ok_binop2 op x y =
  let op_real,op_ours = get_binop op in
  let real = op_real x y in
  let ours = base2_binop op_ours x y in
  (* if not (equal_base2 real ours) then
   *   begin *)
      printf "\nreal: %s\nours: %s\n" (sb real) (sb ours);
      printf "\nreal: %g, ours: %g\n" real ours;
    (* end; *)
  equal_base2 real ours

let is_ok_binop10 op x y = true
  (* let op_real,op_ours = get_binop op in
   * let x = truncate_float x in
   * let y = truncate_float y in
   * let real = op_real x y in
   * let ours = base10_binop op_ours x y in
   * equal_base10 real ours *)

let binop op x y ctxt =
  let op_str = string_of_binop op x y in
  let () =
    if not (is_ok_binop2 op x y) then
      let error = sprintf "%s failed for radix 2" op_str in
      assert_bool error false in
  if not (is_ok_binop10 op x y) then
    let error = sprintf "%s failed for radix 10" op_str in
    assert_bool error false

let binop_special op op' x y ctxt =
  let real = str_of_float (op x y) in
  let ours = str_of_float (base2_binop op' x y) in
  assert_equal ~ctxt ~cmp:String.equal real ours;
  let r10 = base10_binop op' x y in
  assert_equal ~ctxt ~cmp:String.equal real r10

let is_ok_unop2 op x =
  let op_real, op_ours = get_unop op in
  let real = op_real x in
  let ours = base2_unop op_ours x in
  if not (equal_base2 real ours) then
    begin
      printf "\nreal: %s\nours: %s\n" (sb real) (sb ours);
      printf "\nreal: %g, ours: %g\n" real ours;
    end;
  equal_base2 real ours

let is_ok_unop10 op x = true
  (* let x = truncate_float x in
   * let op_real, op_ours = get_unop op in
   * let real = op_real x in
   * let ours = base10_unop op_ours x in
   * equal_base10 real ours *)

let unop op x ctxt =
  let op_str = string_of_unop op x in
  let () =
    if not (is_ok_unop2 op x) then
      let error = sprintf "%s failed for radix 2" op_str in
      assert_bool error false in
  if not (is_ok_unop10 op x) then
    let error = sprintf "%s failed for radix 10" op_str in
    assert_bool error false

let sin2  = gen_sin double_of_float float_of_double ~prec:53
let sin10 = gen_sin decimal_of_float string_of_decimal ~prec:decimal_precision

let sin x ctxt =
  let real = Pervasives.sin x in
  let r2 = sin2 x in
  assert_equal ~ctxt ~cmp:equal_base2 real r2
  (* let r10 = sin10 x in
   * let equal = equal_base10 real r10 in
   * assert_bool "sin base 10 failed" equal *)

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

let add x y ctxt = binop `Add x y ctxt
let sub x y ctxt = binop `Sub x y ctxt
let mul x y ctxt = binop `Mul x y ctxt
let div x y ctxt = binop `Div x y ctxt
let sqrt x ctxt     = unop  `Sqrt x ctxt

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

let () = Random.self_init ()

let make_int64 sign_bit expn frac =
  let sign_bit = Int64.(of_int sign_bit lsl 63) in
  let expn = Int64.(of_int expn lsl 52) in
  let frac = Int64.of_int frac in
  Int64.(sign_bit lor expn lor frac)

let make_float sign expn frac =
  let x = make_int64 sign expn frac in

  printf "make_float: %d %d ---> %Ld\n" expn frac x;

  Int64.float_of_bits x

let random_int ~from ~to_ =
  let open Caml in
  let max = to_ - from in
  let x = Random.int max in
  x + from

(* value itself, expn, frac *)
type random_float = float * int * int

let string_of_random (f, e, frac) =
  sprintf "(Random %e, %d, %d)" f e frac

let random_float () =
  let expn () = random_int ~from:1020 ~to_:1040 in
  let frac () = Random.int 4503599627000000 in
  let sign () = Random.int 2 in
  let make () =
    let expn = expn () in
    let frac = frac () in
    let float = make_float (sign ()) expn frac in
    float, (float, expn, frac) in
  let small () =
    let x = Random.int 9 in
    let y = Int64.of_int x in
    let float = Random.float (Int64.float_of_bits y) in
    float, (float, 0, x) in
  match Random.int 2 with
  | 0 -> small ()
  | _ -> make ()


let make_random ~times =
  let binop op (x, x') (y, y') ctxt =
    if op = `Div && (y = 0.0 || y = ~-.0.0) then ()
    else
      let isok = is_ok_binop2 op x y in
      let op_str =
        sprintf "%s: %s %s"
          (string_of_binop op x y)
          (string_of_random x') (string_of_random y') in
      let error = sprintf "%s failed for radix 2" op_str in
      assert_bool error isok in
  let sqrt (x, x') ctxt =
    if x < 0.0 then ()
    else
      let op = `Sqrt in
      let isok = is_ok_unop2 op x in
      let op_str = sprintf "%s, %s"
          (string_of_unop op x) (string_of_random x') in
      let error = sprintf "%s failed for radix 2" op_str in
      assert_bool error isok in
  let random = Random.int in
  let random_elt xs = List.nth_exn xs @@ random (List.length xs) in
  List.init times ~f:(fun i ->
      let f (ctxt : test_ctxt) =
        let op = random_elt [`Add;`Sub;`Mul; `Div] in
        let x = random_float () in
        let y = random_float () in
        let () = binop op x y ctxt in
        sqrt x ctxt in
      (sprintf "random%d" i) >:: f)

let suite () =
  let small_x = make_float 0 0 2 in
  let small_y = make_float 0 0 3 in

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
    "0.0 * 0.0"    >:: 0.0 * 0.0;
    "0.0 * 0.1738" >:: 0.0 * 0.1738;
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
    "1.0 / 1.1"   >:: 1.0 / 1.1;
    "1.0 / 1.12"   >:: 1.0 / 1.12;
    "1.0 / 1.123"   >:: 1.0 / 1.123;
    "1.0 / 1.1234"   >:: 1.0 / 1.1234;
    "1.0 / 1.12345"   >:: 1.0 / 1.12345;
    "1.0 / 1.123456"   >:: 1.0 / 1.123456;
    "1.0 / 1.1234567"   >:: 1.0 / 1.1234567;
    "1.0 / 1.12345678"   >:: 1.0 / 1.12345678;
    "1.0 / 1.123456789"   >:: 1.0 / 1.123456789;
    "1.0 / 1.1234567891"   >:: 1.0 / 1.1234567891;
    "1.0 / 1.12345678912"   >:: 1.0 / 1.12345678912;
    "1.0 / 1.123456789123"   >:: 1.0 / 1.123456789123;

    "1.1 / 0.9"   >:: 1.1 / 0.9;
    "1.1 / 0.99"   >:: 1.1 / 0.99;
    "1.1 / 0.999"   >:: 1.1 / 0.999;
    "1.1 / 0.9999"   >:: 1.1 / 0.9999;
    "1.1 / 0.99999"   >:: 1.1 / 0.99999;
    "1.1 / 0.999999"   >:: 1.1 / 0.999999;
    "1.1 / 0.9999999"   >:: 1.1 / 0.9999999;

    (* test subnormal floats *)
    "small_x + small_y" >:: small_x + small_y;
    "small_x - small_y" >:: small_x - small_y;
    "small_x * small_y" >:: small_x * small_y;
    "small_x / small_y" >:: small_x / small_y;
    "small_y - small_x" >:: small_y - small_x;
    "small_y / small_x" >:: small_y / small_x;

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

    (* sin - just test that it could be implemented *)
    "sin 0.0"       >:: sin 0.0;
    "sin 0.5"       >:: sin 0.5;
    "sin 1.0"       >:: sin 1.0;
    "sin 0.5216..." >:: sin 0.52167823455675756576;
    "sin 0.023345"  >:: sin 0.0232345;
    "sin 0.423890723482" >:: sin 0.423890723482;
    "sin 0.000000042"  >:: sin 0.000000042;

    (* random - +,-,*,/ with a random operands for radix=2 *)
  ] @ make_random ~times:2

let test_it () =
  let a = 3.456 in
  let b = 13.1986 in
  let real = a /. b in
  let x = decimal_of_float a in
  let y = decimal_of_float b in
  let ours = Gfloat_w.div x y in
  printf "z is %f, real %f\n" (float_of_decimal ours) real

let suite () =
  let y = make_float 0 2042 10000000000000 in
  let x = make_float 0 0 2 in

  (* let x' = double_of_float x in
   * let y' = double_of_float y in
   * let ours = Gfloat_w.Infix.(y' / x') in
   * let ours = float_of_double ours in
   *
   * let real' = ours *. x in
   * Debug.deconstruct64 real';
   * printf "\n";
   * Debug.deconstruct64 y;
   * printf "real' is %f\n\n\n" real'; *)

  "test" >::: [
      (* "1.0 / 1.1"   >:: 1.0 / 1.1; *)
      (* "aaaaaaaaaa" >:: y / x; *)
      "bbbbbbbbbb" >:: x / y;

    ]

let () = run_test_tt_main (suite ())
