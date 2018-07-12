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

(* no implicit bits! *)
let mk sign expn frac = Normal {sign; expn; frac}

let word_of_sign = function
  | Pos -> Word.b0
  | Neg -> Word.b1

let drop_hd w =
  let hi = Word.bitwidth w - 2 in
  Word.extract_exn ~hi w

let hd w =
  Seq.hd_exn (enum_bits w)

let single_of_float f =
  let w = Word.of_int32 ~width:32 (Int32.bits_of_float f) in
  let sign = Word.extract_exn ~hi:31 ~lo:31 w in
  let sign = if Word.is_zero sign then Pos else Neg in
  let expn' = Word.extract_exn ~hi:30 ~lo:23 w in
  let bias = Word.of_int ~width:8 127 in
  let expn = Word.(expn' - bias) in
  let frac = Word.extract_exn ~hi:22 w in
  let frac = Word.concat Word.b1 frac in
  mk sign expn frac

let normalize bias biased_expn frac =
  let min_expn = Word.one (Word.bitwidth bias) in
  let max_expn = Word.(bias * of_int ~width:(bitwidth bias) 2 - b1) in
  let rec run expn frac =
    if Word.(expn > max_expn) then
      run (Word.pred expn) Word.(frac lsl b1)
    else if Word.(expn < min_expn) then
      run (Word.succ expn) Word.(frac lsr b1)
    else expn, frac in
  run biased_expn frac

let to_ieee_float_bits t = match t with
  | Normal {sign; expn; frac} ->
    let bias = Word.of_int ~width:8 127 in
    let expn = Word.(bias + expn) in
    let frac = drop_hd frac in
    let expn,frac = normalize bias expn frac in
    let (^) = Word.concat in
    word_of_sign sign ^ expn ^ frac
  | _ -> failwith "todo"

let lshift x n =
  let expn = Word.(x.expn - n) in
  let frac = Word.(x.frac lsl n) in
  {x with expn; frac}

let rshift x n =
  let expn = Word.(x.expn + n) in
  let frac = Word.(x.frac lsr n) in
  {x with expn; frac}

module Draft = struct

  let rshift x n =
    if Word.is_zero n then x, Word.b0
    else
      let expn = Word.(x.expn + n) in
      let frac = Word.(x.frac lsr n) in
      let n = Word.to_int_exn n in
      let gone = Word.extract_exn ~hi:(n - 1) x.frac in
      {x with expn; frac}, gone

  (* only scratch! o o .. oooonly scraaatch! *)
  let round_away_from_zero x gone =
    if Word.is_zero x then x
    else Word.succ x

end

let rec norm_hd expn frac =
  if Word.is_zero frac then expn,frac
  else
  if not (hd frac) then
    norm_hd (Word.pred expn) Word.(frac lsl b1)
  else expn, frac

let common_ground x y =
  let expn = Word.max x.expn y.expn in
  if x.expn > y.expn then
    let y,gone = Draft.rshift y Word.(expn - y.expn) in
    x,y,gone
  else if x.expn < y.expn then
    let x,gone = Draft.rshift x Word.(expn - x.expn) in
    x,y,gone
  else x,y,Word.b0

let rec add x y =
  let x,y,gone = common_ground x y in
  let frac = Word.(x.frac + y.frac) in
  if frac < x.frac then
    let x = rshift x Word.b1 in
    let y = rshift y Word.b1 in
    add x y
  else
    let expn, frac = norm_hd x.expn frac in
    let frac = Draft.round_away_from_zero frac gone in
    Normal {sign = x.sign; expn; frac}

let revert_sign = function
  | Pos -> Neg
  | Neg -> Pos

let sub x y =
  let x,y,gone = common_ground x y in
  let sign, frac =
    if x.frac < y.frac then
      revert_sign x.sign, Word.(y.frac - x.frac)
    else
      x.sign, Word.(x.frac - y.frac) in
  let expn, frac = norm_hd x.expn frac in
  Normal {sign; expn; frac}

let add_or_sub subtract x y = match x,y with
  | Normal x, Normal y ->
    let s1 = Word.of_bool subtract in
    let s2 = word_of_sign x.sign in
    let s3 = word_of_sign y.sign in
    let subtract = Word.(s1 lxor (s2 lxor s3)) in
    if Word.is_one subtract then sub x y
    else add x y
  | _ -> failwith "TODO"

let add = add_or_sub false
let sub = add_or_sub true

let msb w =
  let bits = enum_bits w in
  match Seq.findi bits ~f:(fun i x -> x) with
  | None -> None
  | Some (i,_) -> Some (Word.bitwidth w - i - 1)

let mul x y = match x,y with
  | Normal x, Normal y ->
    let expn = Word.(x.expn + y.expn) in
    let width = Word.bitwidth x.frac in
    let zeros = Word.zero (width + 1) in
    let xfrac = Word.concat zeros x.frac in
    let yfrac = Word.concat zeros y.frac in
    let frac = Word.(xfrac * yfrac) in
    let msb = Option.value_exn (msb frac) in
    let frac = Word.extract_exn ~hi:msb ~lo:(msb - width + 1) frac in
    Normal {x with expn; frac }
  | _ -> failwith "TODO"

module Test_space = struct

  let test_construct () =
    let create x =
      let y = single_of_float x in
      let z = to_ieee_float_bits y in
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
    | Div -> div

  let run op x y =
    let z = true_result x y op in
    let f1 = single_of_float x in
    let f2 = single_of_float y in
    let fr = (f_of_op op) f1 f2 in
    let fb = to_ieee_float_bits fr in
    let fb = Word.signed fb in
    let r = Int32.float_of_bits (Word.to_int32_exn fb) in
    (* printf "should: %s\n" (bits_of_float z); *)
    (* printf "got   : %s\n" (string_of_bits32 fb); *)
    printf "%g %s %g = %g(%g)\n" x (str_of_op op) y r z

  let neg x = ~-. x
  let (+) = run Add
  let (-) = run Sub
  let ( * ) = run Mul
  let ( / ) = run Div

  let () = 1.0 * 2.5
  let () = 2.5 * 0.5
  let () = 4.2 * 3.4
  let () = 0.01 * 0.02

  let () = 0.05 / 0.5
  let () = 1.0 * 0.5

  let () = 4.2 + 2.98

  (* let () = 4.2 + 2.3 *)
  (* let () = 4.2 + 2.98 *)
  (* let () = 2.2 + 4.28 *)
  (* let () = 2.2 + (neg 4.28) *)
  (* let () = (neg 2.2) + 4.28 *)
  (* let () = 2.2 + 2.46 *)
  (* let () = 4.2 - 2.28 *)
  (* let () = 4.28 - 2.2 *)
  (* let () = 2.2 - 4.28 *)
  (* let () = 2.2 - (neg 4.28) *)
  (* let () = 2.2 - 2.6 *)
  (* let () = (neg 2.2) - 2.46 *)
  (* let () = (neg 2.2) - (neg 2.46) *)
end
