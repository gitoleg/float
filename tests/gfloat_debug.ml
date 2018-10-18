open Core_kernel
open Bap.Std
open Gfloat

let ws = Word.to_string
let wi = Word.to_int_exn
let wdec = Word.string_of_value ~hex:false

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
  let expn = Word.(signed (expn - bias)) in
  let frac = Word.extract_exn ~hi:51 w in
  printf "ocaml %f: unbiased expn %d, frac %s, total %s\n"
    x (wi expn) (string_of_bits frac) (string_of_bits64 w)

let bits_of_float x =
  string_of_bits32 (Word.of_int32 (Int32.bits_of_float x))

let compare_str x y =
  if String.equal x y then "ok" else "POSSIBLE FAIL"

(* module Run_manually(F : T) = struct *)
(*   open Gfloat *)

(*   let bitstring_of_float x = *)
(*     let x = Int64.bits_of_float x |> Word.of_int64 in *)
(*     sb64 x *)

(*   let unop2 opstr op op' x = *)
(*     let real = op x in *)
(*     let res = base2_unop op' x in *)
(*     let real_str = str_of_float real in *)
(*     let res_str = str_of_float res in *)
(*     if not (equal_base2 real res) then *)
(*       let bs = bitstring_of_float in *)
(*       let () = printf "cmp:\n %s <- expected (%f)\n %s <- what we got\n" *)
(*           (bs real) real (bs res) in *)
(*       printf "FAIL: base 2, %s %f <> %f, real %s <> %s\n" *)
(*         opstr x res real_str res_str *)
(*     else printf "OK!\n" *)

(*   let unop10 opstr op op' x = *)
(*     let x = truncate_float x in *)
(*     let real = op x in *)
(*     let res = base10_unop op' x in *)
(*     if not (equal_base10 real res) then *)
(*       printf "FAIL: base 10, %s %f <> %s (%f expected)\n" *)
(*         opstr x res real *)
(*     else printf "OK!\n" *)

(*   let binop2 opstr op op' x y = *)
(*     let real = op x y in *)
(*     let res = base2_binop op' x y in *)
(*     let bs = bitstring_of_float in *)
(*     if not (equal_base2 real res) then *)
(*       let () = printf "cmp:\n %s <- expected (%f)\n %s <- what we got\n" *)
(*           (bs real) real (bs res) in *)
(*       let real_str = str_of_float real in *)
(*       let res_str = str_of_float res in *)
(*       printf "FAIL: base 2, %f %s %f <> %f, real %s <> %s\n" *)
(*         x opstr y res real_str res_str *)
(*     else printf "OK!\n" *)

(*   let binop10 opstr op op' x y = *)
(*     let x = truncate_float x in *)
(*     let y = truncate_float y in *)
(*     let real = op x y in *)
(*     let res = base10_binop op' x y in *)
(*     if not (equal_base10 real res) then *)
(*       printf "FAIL: base 10, %f %s %f <> %s (%.16f expected)\n" *)
(*         x opstr y res real *)
(*     else printf "OK!\n" *)

(*   let run2 = true *)
(*   let run10 = false *)

(*   let unop opstr op op' x = *)
(*     if run2 then *)
(*       unop2 opstr op op' x; *)
(*     if run10 then *)
(*       unop10 opstr op op' x *)

(*   let binop opstr op op' x y = *)
(*     if run2 then *)
(*       binop2 opstr op op' x y; *)
(*     if run10 then *)
(*       binop10 opstr op op' x y *)

(*   let add x y = binop "+" (+.) add x y *)
(*   let sub x y = binop "-" (-.) sub x y *)
(*   let mul x y = binop "*" ( *. ) mul x y *)
(*   let div x y = binop "/" ( /. ) div x y *)
(*   let sqrt x = unop "sqrt" Float.sqrt sqrt x *)

(*   let neg x = ~-. x *)
(*   let (+) = add *)
(*   let (-) = sub *)
(*   let ( * ) = mul *)
(*   let ( / ) = div *)
(*   let ( sqrt ) = sqrt *)

(* end *)

(* module Run = Run_manually(struct type t = () end) *)


module Debug = struct

  let ws = Word.to_string
  let wi = Word.to_int_exn
  let wdec = Word.string_of_value ~hex:false

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

  let string_of_t t =
    let str_of_sign = function
      | Pos -> ""
      | Neg -> "-" in
    match t.value with
    | Nan _ -> "nan"
    | Fin {expn; frac} ->
      sprintf "%s * %d * %d ^ %d" (str_of_sign t.sign) (wi frac) t.base
        (wi expn)
    | Inf -> sprintf "%sinf" (str_of_sign t.sign)

  let string_of_loss a = Sexp.to_string (sexp_of_loss a)

  let msb_exn x = Option.value_exn (msb x)

  let lsb w =
    let bits = enum_bits w in
    match List.findi (Seq.to_list_rev bits) ~f:(fun i x -> x) with
    | None -> None
    | Some (i,_) -> Some i

  let frac_exn a = match a.value with
    | Fin {frac} -> frac
    | _ -> failwith "frac unavailable"

  let expn_exn a = match a.value with
    | Fin {expn} -> expn
    | _ -> failwith "frac unavailable"

  let data_exn a = match a.value with
    | Fin {expn; frac} -> expn, frac
    | _ -> failwith "data unavailable"

  let str_exn a =
    let e, f = data_exn a in
    sprintf "expn %d, frac %d" (wi e) (wi f)

  let pr_xy pref base x y = match base with
    | 2 ->
      printf "%s:\n  x: %d, %s\n  y: %d, %s\n" pref
        (wi x.expn) (sb x.frac) (wi y.expn) (sb y.frac)
    | _ ->
      printf "%s:\n  x: %d, %s\n  y: %d, %s\n" pref
        (wi x.expn) (wdec x.frac) (wi y.expn) (wdec y.frac)

end

open Debug
