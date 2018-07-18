open Core_kernel
open Format
open Bap.Std

let ws = Word.to_string
let wi = Word.to_int_exn
let wdec = Word.string_of_value ~hex:false

type sign = Pos | Neg [@@deriving sexp]

type finite = {
  sign : sign;
  expn : int;
  frac : word;
} [@@deriving sexp]

type value =
  | Inf of sign
  | Nan of bool * word
  | Fin of finite
[@@deriving sexp]

type gfloat = {
  radix : int;
  precs : int;
  value : value;
}

type roundmode_type =
  | RNE (** round to nearest ties to even  *)
  | RTZ (** round toward zero              *)
  | RTP (** round toward positive infinity *)
  | RTN (** round toward negative infinity *)
  | RNA (** round to nearest ties to away  *)

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

let lsb w =
  let bits = enum_bits w in
  match List.findi (Seq.to_list_rev bits) ~f:(fun i x -> x) with
  | None -> None
  | Some (i,_) -> Some i

module Debug = struct
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
end

open Debug

(* we assume here that shift will not be bigger then capacity of
   int63  *)
let pow radix n =
  let rec run r m =
    if m < n then run (r * radix) (m + 1)
    else r in
  if n = 0 then 1
  else run radix 1

let lshift_frac radix frac n =
  if n = 0 then frac
  else
    let k = Word.of_int ~width:(Word.bitwidth frac) (pow radix n) in
    Word.(frac * k)

let rshift_frac radix frac n =
  if n = 0 then frac
  else
    let k = Word.of_int ~width:(Word.bitwidth frac) (pow radix n) in
    if Word.is_zero k then k
    else Word.(frac / k)

(* this a variant  *)
let rshift_frac' radix frac n =
  if n = 0 then frac, `Nothing
  else
    let k = Word.of_int ~width:(Word.bitwidth frac) (pow radix n) in
    if Word.is_zero k then k, `Nothing
    else
      let result = Word.(frac / k) in
      let restored = Word.(result * k) in
      let lost = if Word.equal frac restored then `Nothing
        else `Lost Word.(frac - restored) in
      result, lost

let lshift radix x n =
  { x with expn = x.expn - n; frac = lshift_frac radix x.frac n }

let rshift radix x n =
  { x with expn = x.expn + n; frac = rshift_frac radix x.frac n }

let word_of_sign = function
  | Pos -> Word.b0
  | Neg -> Word.b1

let hd_exn w = Seq.hd_exn (enum_bits w)

(* [unsafe_align_right radix precision expn frac]
   shifts frac right with possible loss of bits in order to keep
   most significant bits. It assumes [bitwidth frac > precision]. *)
let unsafe_align_right radix precision expn frac =
  let rec run expn frac =
    match msb frac with
    | None -> expn,frac
    | Some i when i < precision -> expn,frac
    | _ -> run (expn + 1) (rshift_frac radix frac 1) in
  run expn frac

(* the same as unsafe version above, but stops in case of bits loss *)
let safe_align_right radix expn frac =
  let width = Word.bitwidth frac in
  let rec run expn x =
    let y = rshift_frac radix x 1 in
    let z = Word.extract_exn ~hi:(width - 1) y in
    if Word.is_zero z then run (expn + 1) y
    else expn, x in
  if Word.is_zero frac then expn,frac
  else
    let frac = Word.concat frac (Word.zero width) in
    let expn,frac = run expn frac in
    let frac = Word.extract_exn ~lo:width frac in
    expn, frac

let safe_align_left radix expn frac =
  let width = Word.bitwidth frac in
  let rec run e x =
    let y = lshift_frac radix x 1 in
    let z = Word.extract_exn ~lo:width y in
    if Word.is_zero z then run (e - 1) y
    else e,x in
  if Word.is_zero frac then expn, frac
  else
    let frac = Word.concat (Word.zero width) frac in
    let e,frac = run expn frac in
    let frac = Word.extract_exn ~hi:(width - 1) frac in
    e,frac

(* min exponent without bit loss, fraction shifted
   as left as possible, i.e. it occupies more
   significant bits *)
let minimize_exponent radix x =
  let expn, frac = safe_align_left radix x.expn x.frac in
  {x with expn; frac}

let norm = minimize_exponent

(* max exponent without bit loss, fraction shifted
   as right as possible, i.e. it occupies less
   significant bits *)
let maximize_exponent radix x =
  let expn, frac = safe_align_right radix x.expn x.frac in
  {x with expn; frac}

let min_exp_of_precision radix precision =
  let x = {sign=Pos; frac = Word.one precision; expn = 0} in
  let y = minimize_exponent radix x in
  y.expn

let mk ~radix sign expn frac =
  let value = norm radix {sign; expn; frac} in
  let precs = Word.bitwidth frac in
  {radix; value = Fin value; precs }

let mk_inf ~radix precs sign = {radix; precs; value = Inf sign}

(* mk nan with payload 1 *)
let mk_nan ?(signaling=false) ~radix precs =
  let value = Nan (signaling, Word.one precs) in
  {radix; precs; value}

let is_zero x = match x.value with
  | Fin x -> Word.is_zero x.frac
  | _ -> false

let is_inf x = match x.value with
  | Inf _ -> true
  | _ -> false

let is_nan x = match x.value with
  | Nan _ -> true
  | _ -> false

let is_finite x = match x.value with
  | Fin _ -> true
  | _ -> false

let is_pos x = match x.value with
  | Fin {sign}
  | Inf sign -> sign = Pos
  | _ -> false

let is_neg x = match x.value with
  | Fin {sign}
  | Inf sign -> sign = Neg
  | _ -> false

let common_ground radix x y =
  let expn = max x.expn y.expn in
  if x.expn > y.expn then
    x, rshift radix y (expn - y.expn)
  else if x.expn < y.expn then
    rshift radix x (expn - x.expn), y
  else x,y

let rec add radix x y =
  let x,y = common_ground radix x y in
  let frac = Word.(x.frac + y.frac) in
  if frac < x.frac then
    let x = rshift radix x 1 in
    let y = rshift radix y 1 in
    add radix x y
  else
    let r = {sign = x.sign; expn=x.expn; frac} in
    Fin (norm radix r)

let revert_sign = function
  | Pos -> Neg
  | Neg -> Pos

let xor_sign s s' =
  let r = Word.(word_of_sign s lxor word_of_sign s') in
  if Word.is_one r then Neg else Pos

let sub radix x y =
  let x,y = common_ground radix x y in
  let sign, frac =
    if x.frac < y.frac then revert_sign x.sign, Word.(y.frac - x.frac)
    else x.sign, Word.(x.frac - y.frac) in
  let r = { sign; expn=x.expn; frac } in
  Fin (norm radix r)

let add_or_sub subtract a b = match a.value,b.value with
  | Fin x, Fin y ->
    let s1 = Word.of_bool subtract in
    let s2 = word_of_sign x.sign in
    let s3 = word_of_sign y.sign in
    let subtract = Word.(s1 lxor (s2 lxor s3)) in
    let value =
      if Word.is_one subtract then sub a.radix x y
      else add a.radix x y in
    {a with value}
  | Nan _, _ | Inf _, _ -> a
  | _, Nan _ | _, Inf _ -> b

let add = add_or_sub false
let sub = add_or_sub true

let mul a b = match a.value,b.value with
  | Fin x, Fin y ->
    let x = maximize_exponent a.radix x in
    let y = maximize_exponent a.radix y in
    let precision = Word.bitwidth x.frac in
    let expn = x.expn + y.expn in
    let zeros = Word.zero (precision + 1) in
    let xfrac = Word.concat zeros x.frac in
    let yfrac = Word.concat zeros y.frac in
    let frac = Word.(xfrac * yfrac) in
    let expn, frac = unsafe_align_right a.radix precision expn frac in
    let frac = Word.extract_exn ~hi:(precision - 1) frac in
    let sign = xor_sign x.sign y.sign in
    let value = norm a.radix {sign; expn; frac} in
    {a with value = Fin value }
  | Nan _, _ -> a
  | _, Nan _ -> b
  | Inf _, _ when is_zero b -> mk_nan a.radix a.precs
  | _, Inf _ when is_zero a -> mk_nan a.radix a.precs
  | Inf _, _ -> a
  | _, Inf _ -> b

(** [divide radix min_degree start_dividend divisor] - divides
    two integers and returns list of [q_i, -i] from the following
    sum:
          n
      q = Σ  q_i * B ^ -i
         i=0

    where B is a radix, and q_i ⋲ {0 .. B - 1}
    The length of the list depends on number of representable digits,
    i.e. from [min_degree]: e.g. assume min_degree = -4 for decimal
    floating point arithmetic, therefore a number:
    1.234567 will be represented as a list:
    [1,0; 2,-1; 3,-2; 4,-3; 5,-4] and everything else will be
    truncated.
    Also returns the next available digit for rounding purposes,
    [6] from example above *)
let divide radix min_degree start_dividend divisor =
  let min_degree' = min_degree - 1 in
  let rec loop acc dividend degree =
    let dividend, acc =
      if Word.(dividend >= divisor) then
        let res = Word.(dividend / divisor) in
        let dividend = Word.(dividend - res * divisor) in
        dividend, (res,degree) :: acc
      else
        let zero = Word.zero (Word.bitwidth dividend) in
        let acc = (zero, degree) :: acc in
        dividend, acc in
    if degree > min_degree' then
      let dividend = if dividend < divisor then
          lshift_frac radix dividend 1
        else dividend in
      loop acc dividend (degree - 1)
    else acc in
  let res = loop [] start_dividend 0 in
  let last,_ = List.hd_exn res in
  let res = List.rev (List.tl_exn res) in
  res, last

let naive_round x last =
  if Word.is_zero last then x
  else Word.succ x

let div a b = match a.value,b.value with
  | Fin x, Fin y when not (is_zero b) ->
    let x = minimize_exponent a.radix x in
    let y = minimize_exponent a.radix y in
    let expn = x.expn - y.expn in
    let extend = Word.zero a.precs in
    let xfrac = Word.concat extend x.frac in
    let yfrac = Word.concat extend y.frac in
    let expn, xfrac = if Word.(xfrac < yfrac) then
        expn - 1, lshift_frac a.radix xfrac 1
      else expn, xfrac in
    let min_degree = min_exp_of_precision a.radix a.precs in
    let res,next = divide a.radix min_degree xfrac yfrac in
    let frac = List.fold ~init:(Word.zero (2 * a.precs)) res
        ~f:(fun r (q,d) ->
            let d' = d - min_degree in
            Word.(r + lshift_frac a.radix q d')) in
    let frac = naive_round frac next in
    let expn = expn + min_degree in
    let expn,frac = safe_align_right a.radix expn frac in
    (* and here we need to check for overflow of course *)
    let frac = Word.extract_exn ~hi:(a.precs - 1) frac in
    let sign = xor_sign x.sign y.sign in
    let value = norm a.radix {sign; frac; expn = expn} in
    {a with value = Fin value}
  | Fin x, Fin y -> {a with value = Inf x.sign}
  | Nan _, _ -> a
  | _, Nan _ -> b
  | Inf _, _ -> a
  | _, Inf _ -> b

let string_of_t t =
  let str_of_sign = function
    | Pos -> ""
    | Neg -> "-" in
  match t.value with
  | Nan _ -> "nan"
  | Fin {sign; expn; frac} ->
    sprintf "%s * %d * %d ^ %d" (str_of_sign sign) (wi frac) t.radix expn
  | Inf s -> sprintf "%sinf" (str_of_sign s)

module Front = struct

  let drop_hd w =
    let hi = Word.bitwidth w - 2 in
    Word.extract_exn ~hi w

  let all_ones x = Word.(x = ones (bitwidth x))
  let all_zeros x = Word.(x = zero (bitwidth x))

  let single_of_float f =
    let w = Word.of_int32 (Int32.bits_of_float f) in
    let sign = Word.extract_exn ~hi:31 ~lo:31 w in
    let sign = if Word.is_zero sign then Pos else Neg in
    let expn' = Word.extract_exn ~hi:30 ~lo:23 w in
    let bias = 127 in
    let expn = Word.to_int_exn expn' - bias in
    let frac = Word.extract_exn ~hi:22 w in
    if all_ones expn' && Word.is_zero frac then
      mk_inf ~radix:2 24 sign
    else if all_ones expn' then
      mk_nan ~radix:2 24
    else
      let dexp = Word.bitwidth frac in
      let expn = expn - dexp in
      let int_bit = if all_zeros expn' && all_zeros frac then Word.b0
        else Word.b1 in
      let frac = Word.concat int_bit frac in
      mk ~radix:2 sign expn frac

  let normalize_ieee bias biased_expn frac =
    let min_expn = 1 in
    let max_expn = bias * 2 - 1 in
    let rec run expn frac =
      if expn > max_expn then
        run (pred expn) Word.(frac lsl b1)
      else if expn < min_expn then
        run (succ expn) Word.(frac lsr b1)
      else expn, frac in
    run biased_expn frac

  let to_ieee_float_bits t =
    let (^) = Word.concat in
    match t.value with
    | Fin x when t.radix = 2 ->
      let {sign; expn; frac} = norm t.radix x in
      let bias = 127 in
      let expn = bias + expn in
      let n = Word.bitwidth frac - 1 in
      let expn = expn + n in
      let frac = drop_hd frac in (* in assumption that it's normal value *)
      let expn,frac = normalize_ieee bias expn frac in
      let expn = Word.of_int ~width:8 expn in
      word_of_sign sign ^ expn ^ frac
    | Fin x -> failwith "can't convert from radix other than 2"
    | Nan (_,frac) ->
      let expn = Word.ones 8 in
      let frac = drop_hd frac in
      word_of_sign Neg ^ expn ^ frac
    | Inf sign ->
      let expn = Word.ones 8 in
      let frac = Word.zero 23 in
      word_of_sign sign^ expn ^ frac

  let float_of_bin t =
    let bits = to_ieee_float_bits t in
    let bits = Word.signed bits |> Word.to_int32_exn in
    Int32.float_of_bits bits

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

  let decimal_of_string x =
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
    let expn, int_part = truncate max_int expn (base ^ remd) in
    let frac = Word.of_int ~width:precision int_part in
    let sign = if is_neg then Neg else Pos in
    mk ~radix:10 sign expn frac

  let float_of_decimal t = match t.value with
    | Fin {sign;expn;frac} ->
      let expn = float_of_int expn in
      let frac = float_of_int @@ Word.to_int_exn frac in
      let r = frac *. (10.0 ** expn) in
      let r = Int32.bits_of_float r |> Int32.float_of_bits in
      if sign = Neg then ~-. r
      else r
    | Inf sign ->
      begin
        match sign with
        | Pos -> Float.infinity
        | Neg -> Float.neg_infinity
      end
    | _ -> failwith "TODO"

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
    let frac = Word.of_int ~width:precision int_part in
    let sign = if is_neg then Neg else Pos in
    mk ~radix:16 sign expn frac

  let string_of_hexadecimal t = match t.value with
    | Fin {sign;expn;frac} ->
      let expn = float_of_int expn in
      let frac = float_of_int @@ Word.to_int_exn frac in
      let r = frac *. (16.0 ** expn) in
      let int_part = Float.round_down r in
      let flt_part = frac -. int_part *. (16.0 ** (~-.expn)) in
      let sign = if sign = Neg then "-"
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

end

module Test_space = struct

  let deconstruct x =
    let w = Word.of_int32 (Int32.bits_of_float x) in
    let expn = Word.extract_exn ~hi:30 ~lo:23 w in
    let bias = Word.of_int ~width:8 127 in
    let expn = Word.(expn - bias) in
    let frac = Word.extract_exn ~hi:22 w in
    printf "ocaml %f: unbiased expn %d, frac %s, total %s\n"
      x (wi expn) (string_of_bits frac) (string_of_bits32 w)


  let word_of_float x =
    let x = Int32.bits_of_float x in
    Word.of_int32 ~width:32 x

  let bits_of_float x =
    string_of_bits32 (Word.of_int32 (Int32.bits_of_float x))

  type op =
    | Add
    | Sub
    | Mul
    | Div

  let str_of_op = function
    | Add -> "+"
    | Sub -> "-"
    | Mul -> "*"
    | Div -> "/"

  let true'_result x y op =
    let nop' a = Int32.bits_of_float a |> Int32.float_of_bits in
    let x = nop' x in
    let y = nop' y in
    let r = match op with
      | Add -> x +. y
      | Sub -> x -. y
      | Mul -> x *. y
      | Div -> x /. y in
    nop' r

  let f_of_op = function
    | Add -> add
    | Sub -> sub
    | Mul -> mul
    | Div -> div

  let compare_str x y =
    if String.equal x y then "ok" else "POSSIBLE FAIL"

  let my_string_of_float x = sprintf "%.15f" x

  let decimal op x y =
    let f1 = Front.decimal_of_string (my_string_of_float x) in
    let f2 = Front.decimal_of_string (my_string_of_float y) in
    let fr = (f_of_op op) f1 f2 in
    Front.float_of_decimal fr

  let ieee_single32 op x y =
    let f1 = Front.single_of_float x in
    let f2 = Front.single_of_float y in
    let fr = (f_of_op op) f1 f2 in
    let fb = Front.to_ieee_float_bits fr in
    let fb = Word.signed fb in
    Int32.float_of_bits (Word.to_int32_exn fb)

  let bits32_of_float x =
    Word.of_int32 (Int32.bits_of_float x)

  let bits64_of_float x =
    Word.of_int64 (Int64.bits_of_float x)

  let run op x y =
    let res = true'_result x y op in
    let bin = ieee_single32 op x y in
    let dec = decimal op x y in
    let res_str = sprintf "%f" res in
    let bin_str = sprintf "%f" bin in
    let dec_str = sprintf "%f" dec in
    let long_res = sprintf "%.8f" res in

    (* printf "cmp true %s and my %s\n" res_str dec_str; *)
    (* printf "cmp:\n %s\n %s\n" *)
    (*   (string_of_bits (bits32_of_float res)) *)
    (*   (string_of_bits (bits32_of_float bin)); *)

    printf "bin: %g %s %g = %g(%g, %s) %s\n" x (str_of_op op) y bin res
      long_res (compare_str res_str bin_str);
    printf "dec: %g %s %g = %g(%g, %s) %s\n" x (str_of_op op) y dec res
      long_res (compare_str res_str dec_str)

  let create x =
    let bin x =
      let y = Front.single_of_float x in
      let z = Front.to_ieee_float_bits y in
      let z = Word.signed z in
      Int32.float_of_bits (Word.to_int32_exn z) in
    let dec x =
      let x = my_string_of_float x in
      let v = Front.decimal_of_string x in
      Front.float_of_decimal v in
    let run x =
      let res = sprintf "%g" x in
      let bin = sprintf "%g" (bin x) in
      let dec = sprintf "%g" (dec x) in
      let cmp_bin = compare_str res bin in
      let cmp_dec = compare_str res dec in
      printf "make: from %s, bin %s, dec %s\n"
        res cmp_bin cmp_dec in
    run x

  let neg x = ~-. x
  let (+) = run Add
  let (-) = run Sub
  let ( * ) = run Mul
  let ( / ) = run Div
  let space () = printf "\n\n"

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
      324.32423 / 1.2


  end

  let () =
    3.0 / 32.0;
    2.4 / 3.123131;
    1.0 / 0.0;
    2.0 / 0.5;
    1.0 / 3.0;
    0.1313134 / 0.578465631;
    324.32423 / 1.2

  (* module Run = Main_test(struct type t = unit end) *)

  let single_inf_bits s =
    let expn = Word.ones 8 in
    let frac = Word.zero 23 in
    let (^) = Word.concat in
    let sign = if s = 0 then Word.b0 else Word.b1 in
    let bits = sign ^ expn ^ frac in
    Word.signed bits

  let inf = single_inf_bits 0

  let a () =
    let x = Front.single_of_float 1.0 in
    let y = Front.single_of_float 0.0 in
    let z = div x y in
    let r = mul z y in
    let r1 = Front.float_of_bin r in
    printf "res %s, %f\n" (string_of_t r) r1

  let neg_inf = single_inf_bits 1

  let x s =
    let inf = Int32.float_of_bits (Word.to_int32_exn inf) in
    let r = Float.(0.0 * inf) in
    let bits = Word.of_int32 (Int32.bits_of_float r) in
    printf "%f\n%s\n" r (string_of_bits32 bits);
    let bits = Word.of_int32 (Int32.bits_of_float Float.nan) in
    printf "nan %s\n" (string_of_bits32 bits)

end
