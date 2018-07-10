open Core_kernel
open Format
open Bap.Std

let ws = Word.to_string
let wi = Word.to_int_exn

type sign = Pos | Neg [@@deriving sexp]

type finite = {
  sign : sign;
  expn : word;
  frac : word;
} [@@deriving sexp]

type gfloat =
  | Inf  of sign
  | Nan of bool * word
  | Normal of finite
[@@deriving sexp]

(* no implicit bits! *)
let mk sign expn frac = Normal {sign; expn; frac}

let word_of_sign = function
  | Pos -> Word.b0
  | Neg -> Word.b1

let drop_hd w =
  let hi = Word.bitwidth w - 2 in
  Word.extract_exn ~hi w

let single_of_float f =
  let w = Word.of_int32 ~width:32 (Int32.bits_of_float f) in
  let sign = Word.extract_exn ~hi:31 ~lo:31 w in
  let sign = if Word.is_zero sign then Pos else Neg in
  let expn = Word.extract_exn ~hi:30 ~lo:23 w in
  let bias = Word.of_int ~width:8 127 in
  let expn = Word.(expn - bias) in
  let frac = Word.extract_exn ~hi:22 w in
  let frac = Word.concat Word.b1 frac in
  let n = Word.bitwidth frac - 1 in
  let expn = Word.(expn - (of_int ~width:(bitwidth expn) n)) in
  mk sign expn frac

let to_ieee_float_bits t = match t with
  | Normal {sign; expn; frac} ->
    let bias = Word.of_int ~width:8 127 in
    let expn = Word.(bias + expn) in
    let n = Word.bitwidth frac - 1 in
    let expn = Word.(expn + (of_int ~width:(bitwidth expn) n)) in
    let frac = drop_hd frac in
    let frac =
      let w = Word.bitwidth frac in
      let hi = w - 1 in
      let lo = hi - 23 + 1 in
      Word.extract_exn ~hi ~lo frac in
    let (^) = Word.concat in
    word_of_sign sign ^ expn ^ frac
  | _ -> failwith "todo"

let test_construct =
  let x = 0.42 in
  let y = single_of_float x in
  let z = to_ieee_float_bits y in
  let z = Int32.float_of_bits (Word.to_int32_exn z) in
  printf "test construct %g ~= %g\n" x z

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

let lshift x n =
  let expn = Word.(x.expn - n) in
  let frac = Word.(x.frac lsl n) in
  {x with expn; frac}

let rshift x n =
  let expn = Word.(x.expn + n) in
  let frac = Word.(x.frac lsr n) in

  printf "%s >> %s = %s\n" (ws x.frac) (ws n) (ws frac);

  {x with expn; frac}


(* TODO: what if overflow/underflow here?? *)
let add x y = match x,y with
  | Normal x, Normal y ->
    begin
      let expn = Word.max x.expn y.expn in
      let x = rshift x Word.(expn - x.expn) in
      let y = rshift y Word.(expn - y.expn) in
      let frac = Word.(x.frac + y.frac) in
      Normal {sign = x.sign; expn; frac}
    end
  | _ -> failwith "TODO"


(* TODO: what if overflow/underflow here?? *)
let sub x y = match x,y with
  | Normal x, Normal y ->
    begin
      let diff = Word.(x.expn - y.expn) in

      let x = lshift x Word.b1 in
      let y = rshift y Word.(diff - b1) in
      let frac = Word.(x.frac - y.frac) in

      printf "subtract: x: %d * %s; y: %d * %s\n"
        (wi x.expn) (ws x.frac)
        (wi y.expn) (ws y.frac);


      (* let x = rshift x Word.(diff - x.expn) in *)
      let y = rshift y diff in

      printf "common: x: %d * %s; y: %d * %s\n"
        (wi x.expn) (ws x.frac)
        (wi y.expn) (ws y.frac);

      let frac = Word.(x.frac - y.frac) in

      printf "x < y %b\n" Word.(x.frac < y.frac);


      let expn,frac = if Word.(x.frac < y.frac) then
          Word.pred x.expn,
          Word.(frac lsl Word.b1)
          else x.expn, frac in


      (* let expn = Word.pred x.expn in *)
      (* let frac = Word.(frac lsl Word.b1) in *)


      Normal {sign = x.sign; expn; frac}
    end
  | _ -> failwith "TODO"


module Test_space = struct

  let word_of_float x =
    let x = Int32.bits_of_float x in
    Word.of_int32 ~width:32 x

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

  let bits_of_float x =
    string_of_bits32 (Word.of_int32 (Int32.bits_of_float x))

  let test1 =
    let x = 4.2 in
    let y = 2.98 in
    let z = x +. y in
    let f1 = single_of_float x in
    let f2 = single_of_float y in
    let fr = add f1 f2 in
    let fb = to_ieee_float_bits fr in
    let r = Int32.float_of_bits (Word.to_int32_exn fb) in
    printf "should: %s\n" (bits_of_float z);
    printf "got   : %s\n" (string_of_bits32 fb);
    printf "%g + %g = %g(%g)\n\n" x y r z

  let test2 =
    let x = 4.2 in
    let y = 2.28 in
    let z = x -. y in
    let f1 = single_of_float x in
    let f2 = single_of_float y in
    let fr = sub f1 f2 in
    let fb = to_ieee_float_bits fr in
    let r = Int32.float_of_bits (Word.to_int32_exn fb) in
    printf "should: %s\n" (bits_of_float z);
    printf "got   : %s\n" (string_of_bits32 fb);
    printf "%g - %g = %g(%g)\n\n" x y r z



  let test3 =
    let x = 4.28 in
    let y = 2.2 in
    let z = x -. y in
    let f1 = single_of_float x in
    let f2 = single_of_float y in
    let fr = sub f1 f2 in
    let fb = to_ieee_float_bits fr in
    let r = Int32.float_of_bits (Word.to_int32_exn fb) in
    printf "should: %s\n" (bits_of_float z);
    printf "got   : %s\n" (string_of_bits32 fb);
    printf "%g - %g = %g(%g)\n\n" x y r z



end
