open Core_kernel
open Bap.Std
open Gfloat

open Gfloat.Debug

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
      let expn = Word.of_int ~width:8 expn in
      mk ~radix:2 sign expn frac

  let double_of_float f =
    let w = Word.of_int64 (Int64.bits_of_float f) in
    let sign = Word.extract_exn ~hi:63 ~lo:63 w in
    let sign = if Word.is_zero sign then Pos else Neg in
    let expn' = Word.extract_exn ~hi:62 ~lo:52 w in
    let bias = 1023 in
    let expn = Word.to_int_exn expn' - bias in
    let frac = Word.extract_exn ~hi:51 w in
    if all_ones expn' && Word.is_zero frac then
      mk_inf ~radix:2 53 sign
    else if all_ones expn' then
      mk_nan ~radix:2 53
    else
      let dexp = Word.bitwidth frac in
      let expn = expn - dexp in
      let int_bit = if all_zeros expn' && all_zeros frac then Word.b0
        else Word.b1 in
      let frac = Word.concat int_bit frac in
      let expn = Word.of_int ~width:11 expn in
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

  let to_single_float_bits t =
    let (^) = Word.concat in
    match t.value with
    | Fin x when t.radix = 2 ->
      let {sign; expn; frac} = norm t.radix x in
      let bias = 127 in
      let expn = Word.to_int_exn expn in
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

  let to_double_float_bits t =
    let (^) = Word.concat in
    match t.value with
    | Fin x when t.radix = 2 ->
      let {sign; expn; frac} = norm t.radix x in
      let bias = 1023 in
      let expn = Word.to_int_exn expn in
      let expn = bias + expn in
      let n = Word.bitwidth frac - 1 in
      let expn = expn + n in
      let frac = drop_hd frac in (* in assumption that it's normal value *)
      let expn,frac = normalize_ieee bias expn frac in
      let expn = Word.of_int ~width:11 expn in
      word_of_sign sign ^ expn ^ frac
    | Fin x -> failwith "can't convert from radix other than 2"
    | Nan (_,frac) ->
      let expn = Word.ones 11 in
      let frac = drop_hd frac in
      word_of_sign Neg ^ expn ^ frac
    | Inf sign ->
      let expn = Word.ones 11 in
      let frac = Word.zero 52 in
      word_of_sign sign^ expn ^ frac

  let float_of_single t =
    let bits = to_single_float_bits t in
    let bits = Word.signed bits |> Word.to_int32_exn in
    Int32.float_of_bits bits

  let float_of_double t =
    let bits = to_double_float_bits t in
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
    let expn = Word.of_int ~width:10 expn in
    mk ~radix:10 sign expn frac

  let my_string_of_float x = sprintf "%.15f" x
  let decimal_of_float x = decimal_of_string (my_string_of_float x)

  let insert_point str before =
    List.foldi (String.to_list str) ~init:[]
      ~f:(fun i acc c ->
          if i = before then c :: '.' :: acc
          else c :: acc) |> List.rev |> String.of_char_list

  let float_of_decimal t = match t.value with
    | Fin {sign;expn;frac} ->
      let expn = Word.to_int_exn expn in
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
          insert_point frac expn in
      let frac = float_of_string frac in
      if sign = Neg then ~-. frac
      else frac
    | Inf sign ->
      begin
        match sign with
        | Pos -> Float.infinity
        | Neg -> Float.neg_infinity
      end
    | Nan _ -> Float.(neg nan)

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
    mk ~radix:16 sign expn frac

  let string_of_hexadecimal t = match t.value with
    | Fin {sign;expn;frac} ->
      let expn = Word.to_int_exn expn in
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

  let true_result x y op = match op with
      | Add -> x +. y
      | Sub -> x -. y
      | Mul -> x *. y
      | Div -> x /. y

  let f_of_op = function
    | Add -> add ~rm:Nearest_even
    | Sub -> sub ~rm:Nearest_even
    | Mul -> mul ~rm:Nearest_even
    | Div -> div ~rm:Nearest_even

  let compare_str x y =
    if String.equal x y then "ok" else "POSSIBLE FAIL"

  let my_string_of_float x = sprintf "%.15f" x

  let decimal op x y =
    let f1 = Front.decimal_of_string (my_string_of_float x) in
    let f2 = Front.decimal_of_string (my_string_of_float y) in
    let fr = (f_of_op op) f1 f2 in
    Front.float_of_decimal fr

  let ieee_single op x y =
    let f1 = Front.single_of_float x in
    let f2 = Front.single_of_float y in
    let fr = (f_of_op op) f1 f2 in
    let fb = Front.to_single_float_bits fr in
    let fb = Word.signed fb in
    Int32.float_of_bits (Word.to_int32_exn fb)

  let ieee_double op x y =
    let f1 = Front.double_of_float x in
    let f2 = Front.double_of_float y in
    let fr = (f_of_op op) f1 f2 in
    let fb = Front.to_double_float_bits fr in
    let fb = Word.signed fb in
    Int64.float_of_bits (Word.to_int64_exn fb)

  let bits32_of_float x = Word.of_int32 (Int32.bits_of_float x)
  let bits64_of_float x = Word.of_int64 (Int64.bits_of_float x)

  let run op x y =
    let res = true_result x y op in
    let bin = ieee_double op x y in
    let dec = decimal op x y in
    let res_str = sprintf "%.6f" res in
    let bin_str = sprintf "%.6f" bin in
    let dec_str = sprintf "%.6f" dec in
    printf "bin: %g %s %g = %s(%s) %s\n" x (str_of_op op) y bin_str res_str
      (compare_str res_str bin_str);
    printf "dec: %g %s %g = %s(%s) %s\n" x (str_of_op op) y dec_str res_str
      (compare_str res_str dec_str)

  let create x =
    let bin32 x =
      let y = Front.single_of_float x in
      let z = Front.to_single_float_bits y in
      let z = Word.signed z in
      Int32.float_of_bits (Word.to_int32_exn z) in
    let bin64 x =
      let y = Front.double_of_float x in
      let z = Front.to_double_float_bits y in
      let z = Word.signed z in
      Int64.float_of_bits (Word.to_int64_exn z) in
    let dec x =
      let x = my_string_of_float x in
      let v = Front.decimal_of_string x in
      Front.float_of_decimal v in
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
      324.32423 / 1.2;
      42.3 / 0.0;
      0.0 / 0.0


  end

  (* module Run = Main_test(struct type t = unit end) *)

  let test_sqrt () =
    let open Caml in
    let value = 42324500.0 in
    let init = 6000.0 in
    let max = 8 in
    let rec run x i =
      if i < max then
        let x' = (x +. value /. x) /. 2.0 in
        let () = printf "%f ---> %f\n" x x' in
        run x' (i + 1)
      else x in
    let a = run init 0 in
    printf "a is %f\n" a

  let test_sqrt =
    let x = 423245.0 in
    (* let xb = Front.double_of_float x in *)
    (* let yb = sqrt xb in *)
    (* let zb = Front.float_of_double yb in *)
    (* printf "binary sqrt: %f\n" zb; *)
    let xd = Front.decimal_of_float x in
    let yd = sqrt xd in
    let zd = Front.float_of_decimal yd in
    printf "decimal sqrt: %f\n" zd



  let test_nan = Word.of_int64 (Int64.bits_of_float Float.nan)

  let a () =
    let sign = "0" in
    let expn = "00000000001" in
    let data = String.init 51 (fun _ -> '0') in
    let data = data ^ "1" in
    let head = "0b" in
    let tail = ":64u" in
    let str = sign ^ expn ^ data  in
    let w = Word.of_string (head ^ str ^ tail) |> Word.signed in
    let f = Int64.float_of_bits (Word.to_int64_exn w) in
    let f1 = f /. 2.0 in
    let f1' = Word.of_int64 (Int64.bits_of_float f1) in
    printf "%f\n%f\n%s\n%s\n" f f1 (sb f1') (sb test_nan)


  let a () =
    let a = 21452525.043223423111 in
    let b = 9.53534534111115 in
    let x = Front.double_of_float a in
    let y = Front.double_of_float b in
    let z = div x y in
    let true_res = a /. b in
    let r1 = Front.to_double_float_bits z in
    let r2 = Word.of_int64 (Int64.bits_of_float true_res) in
    printf "results:\n  ours: %s\n  caml: %s\n" (sb r1) (sb r2)

  let a () =
    let str a = match a.value with
      | Fin x -> sprintf "%s %s [%d %d]"
                   (sb x.expn) (sb x.frac) (wi x.expn) (wi x.frac)
      | Inf s ->
        let s = if s = Pos then "" else "-" in
        s ^ "inf"
      | _ -> "not a value" in
    let mk exp frac =
      let exp = Word.signed Word.(of_int ~width:3 exp) in
      mk ~radix:10 Pos exp (Word.of_int ~width:4 frac) in
    printf "max pos exp %d\n" (max_exponent 3);

    let x = mk (-2) 14 in
    let y = mk 3 15 in
    let z = div x y in
    printf " %s\n+%s\n=%s\n" (str x) (str y) (str z);

end
