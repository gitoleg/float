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
  value : value;
}

let enum_bits w =
  let bits = Word.enum_bits w BigEndian in
  let b_len = Seq.length bits in
  let w_len = Word.bitwidth w in
  if b_len > w_len then
    Seq.drop bits (b_len - w_len)
  else bits

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
end

let msb w =
  let bits = enum_bits w in
  match Seq.findi bits ~f:(fun i x -> x) with
  | None -> None
  | Some (i,_) -> Some (Word.bitwidth w - i - 1)

module Shift = struct

  let pow radix n =
    let rec run r m =
      if m < n then run (r * radix) (m + 1)
      else r in
    if n = 0 then 1
    else run radix 1

  let left radix x n =
    if n = 0 then x
    else
      let k = Word.of_int ~width:(Word.bitwidth x.frac) (pow radix n) in
      let frac = Word.(x.frac * k) in
      { x with expn = x.expn - n; frac }

  let right radix x n =
    if n = 0 then x
    else
      let k = Word.of_int ~width:(Word.bitwidth x.frac) (pow radix n) in
      let frac = Word.(x.frac / k ) in
      { x with expn = x.expn + n; frac }

end

open Debug

let word_of_sign = function
  | Pos -> Word.b0
  | Neg -> Word.b1

let drop_hd w =
  let hi = Word.bitwidth w - 2 in
  Word.extract_exn ~hi w

let hd_exn w = Seq.hd_exn (enum_bits w)

(* min exponent without bit loss  *)
let norm radix x =
  let width = Word.bitwidth x.frac in
  let rec run x =
    let y = Shift.left radix x 1 in
    let z = Word.extract_exn ~lo:width y.frac in
    if Word.is_zero z then run y
    else x in
  let frac = Word.concat (Word.zero width) x.frac in
  let x = run {x with frac} in
  let frac = Word.extract_exn ~hi:(width - 1) x.frac in
  {x with frac}

(* no implicit bits! *)
let mk ~radix sign expn frac =
  let fin = {sign; expn; frac} in
  let value = norm radix fin in
  {radix; value = Fin value }

let common_ground radix x y =
  let expn = max x.expn y.expn in
  if x.expn > y.expn then
    let y = Shift.right radix y (expn - y.expn) in
    x,y
  else if x.expn < y.expn then
    let x = Shift.right radix x (expn - x.expn) in
    x,y
  else x,y

let rec add radix x y =
  let x,y = common_ground radix x y in
  let frac = Word.(x.frac + y.frac) in
  if frac < x.frac then
    let x = Shift.right radix x 1 in
    let y = Shift.right radix y 1 in
    add radix x y
  else
    let r = {sign = x.sign; expn=x.expn; frac} in
    Fin (norm radix r)

let revert_sign = function
  | Pos -> Neg
  | Neg -> Pos

let sub radix x y =
  let x,y = common_ground radix x y in
  let sign, frac =
    if x.frac < y.frac then
      revert_sign x.sign, Word.(y.frac - x.frac)
    else
      x.sign, Word.(x.frac - y.frac) in
  let r = {sign; expn=x.expn; frac} in
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
  | _ -> failwith "TODO"

let add = add_or_sub false
let sub = add_or_sub true

let mul a b = match a.value,b.value with
  | Fin x, Fin y ->
    let expn = x.expn + y.expn in
    let width = Word.bitwidth x.frac in
    let zeros = Word.zero (width + 1) in
    let xfrac = Word.concat zeros x.frac in
    let yfrac = Word.concat zeros y.frac in
    let frac = Word.(xfrac * yfrac) in
    let msb = Option.value_exn (msb frac) in
    let frac = Word.extract_exn ~hi:msb ~lo:(msb - width + 1) frac in
    let value = norm a.radix {x with expn; frac } in
    {a with value = Fin value  }
  | _ -> failwith "TODO"

module Front = struct

  let single_of_float f =
    let w = Word.of_int32 ~width:32 (Int32.bits_of_float f) in
    let sign = Word.extract_exn ~hi:31 ~lo:31 w in
    let sign = if Word.is_zero sign then Pos else Neg in
    let expn' = Word.extract_exn ~hi:30 ~lo:23 w in
    let bias = 127 in
    let expn = Word.to_int_exn expn' - bias in
    let frac = Word.extract_exn ~hi:22 w in
    let frac = Word.concat Word.b1 frac in
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

  let to_ieee_float_bits t = match t.value with
    | Fin {sign; expn; frac} when t.radix = 2 ->
      let bias = 127 in
      let expn = bias + expn in
      let frac = drop_hd frac in
      let expn,frac = normalize_ieee bias expn frac in
      let expn = Word.of_int ~width:8 expn in
      let (^) = Word.concat in
      word_of_sign sign ^ expn ^ frac
    | _ -> failwith "todo"

  let decimal_of_string x =
    let is_neg = List.hd_exn (String.to_list x) = '-' in
    let start, point =
      let p = String.index_exn x '.' in
      if is_neg then 1, p
      else 0, p in
    let base = String.subo ~pos:start ~len:(point - start) x in
    let remd = String.subo ~pos:(point + 1) x in
    let int_part = int_of_string (base ^ remd) in
    let expn = - (String.length remd) in
    let frac = Word.of_int ~width:25 int_part in
    let sign = if is_neg then Neg else Pos in
    mk ~radix:10 sign expn frac

  let float_of_decimal t = match t.value with
    | Fin {sign;expn;frac} ->
      let expn = float_of_int expn in
      let frac = float_of_int @@ Word.to_int_exn frac in
      let r = frac *. (10.0 ** expn) in
      if sign = Neg then ~-. r
      else r
    | _ -> failwith "TODO"

end

module Test_space = struct

  let test_dec  =
    let create = Front.decimal_of_string in
    let undo = Front.float_of_decimal in
    let test x =
      let v = create x in
      let y = undo v in
      printf "constructing %s -> %.6f\n" x y in
    test "-4.2";
    test "0.42";
    test "1323.66";
    test "0.0001";
    test "-42.3";
    let x = sub (create "0.0001") (create "4.2") in
    printf "ss %g\n" (undo x)

  let test_construct () =
    let create x =
      let y = Front.single_of_float x in
      let z = Front.to_ieee_float_bits y in
      let z = Int32.float_of_bits (Word.to_int32_exn z) in
      printf "test construct %g ~ %g\n" x z in
    create 4.2;
    create 4.28;
    create 2.2;
    create 7.18

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

  let true_result x y = function
    | Add -> x +. y
    | Sub -> x -. y
    | Mul -> x *. y
    | Div -> x /. y

  let f_of_op = function
    | Add -> add
    | Sub -> sub
    | Mul -> mul
    | Div -> failwith "unimplemented"

  let compare_str x y =
    if String.equal x y then "" else "POSSIBLE FAIL"

  let run op x y =
    let z = true_result x y op in
    let f1 = Front.single_of_float x in
    let f2 = Front.single_of_float y in
    let fr = (f_of_op op) f1 f2 in
    let fb = Front.to_ieee_float_bits fr in
    let fb = Word.signed fb in
    let r = Int32.float_of_bits (Word.to_int32_exn fb) in
    let str1 = sprintf "%g\n" z in
    let str2 = sprintf "%g\n" r in
    (* printf "should: %s\n" (bits_of_float z); *)
    (* printf "got   : %s\n" (string_of_bits32 fb); *)
    printf "bin: %g %s %g = %g(%g)%s\n" x (str_of_op op) y r z
      (compare_str str1 str2)

  let run' op x y =
    let z = true_result (float_of_string x) (float_of_string y) op in
    let f1 = Front.decimal_of_string x in
    let f2 = Front.decimal_of_string y in
    let fr = (f_of_op op) f1 f2 in
    let r = Front.float_of_decimal fr in
    let str1 = sprintf "%g\n" z in
    let str2 = sprintf "%g\n" r in
    printf "dec: %s %s %s = %g(%g)%s\n" x (str_of_op op) y r z
      (compare_str str1 str2)

  let neg x = ~-. x
  let (+) = run Add
  let (-) = run Sub
  let ( * ) = run Mul
  let ( / ) = run Div
  let (+.) = run' Add
  let (-.) = run' Sub
  let ( *. ) = run' Mul
  let ( /. ) = run' Div

  let () = 4.2 + 2.3
  let () = 4.2 + 2.98
  let () = 2.2 + 4.28
  let () = 2.2 + (neg 4.28)
  let () = (neg 2.2) + 4.28
  let () = 2.2 + 2.46
  let () = 0.0000001 + 0.00000002

  let () = "4.2" +. "2.3"
  let () = "4.2" +. "2.98"
  let () = "2.2" +. "4.28"
  let () = "2.2" +. "-4.28"
  let () = "-2.2" +. "4.28"
  let () = "2.2" +. "2.46"
  let () = "0.0000001" +. "0.00000002"


  let () = 4.2 - 2.28
  let () = 4.28 - 2.2
  let () = 2.2 - 4.28
  let () = 2.2 - (neg 4.28)
  let () = 2.2 - 2.6
  let () = (neg 2.2) - 2.46
  let () = (neg 2.2) - (neg 2.46)
  let () = 0.0000001 - 0.00000002

  let () = "4.2" -. "2.28"
  let () = "4.28" -. "2.2"
  let () = "2.2" -. "4.28"
  let () = "2.2" -. "-4.28"
  let () = "2.2" -. "2.6"
  let () = "-2.2" -. "2.46"
  let () = "-2.2" -. "-2.46"
  let () = "0.0000001" -. "0.00000002"


  let () = 1.0 * 2.5
  let () = 2.5 * 0.5
  let () = 4.2 * 3.4
  let () = 0.01 * 0.02
  let () = 1.0 * 0.5
  let () = 4.2 + 2.98



end
