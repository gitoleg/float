open Core_kernel
open OUnit2
open Bap.Std

type test = float -> float -> test_ctxt -> unit

open Bap_knowledge
open Bap_core_theory

open Gfloat
module GE = Gfloat_exp

module G = Gfloat.Make(GE.BIL)

open Knowledge.Syntax

[@@@warning "-3"]

let eval x =
  let x = x >>| Value.semantics in
  match Knowledge.run x Knowledge.empty with
  | Error _ -> assert false
  | Ok (s,_) ->
     match Semantics.get GE.exp s with
     | None -> printf "Semantics.get: none!\n"; None
     | Some e ->
        (* printf "%s\n" (Exp.to_string e); *)
        match Exp.eval e with
        | Bil.Imm w -> Some w
        | _ -> assert false

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

let print_result ~pref x =
  let e = eval (G.exponent x) in
  let s = eval (G.significand x) in
  match e,s with
  | Some e, Some s ->
     printf "%s: %s %s\n" pref (Word.to_string e) (Word.to_string s)
  | _ -> printf "fail!\n"


type bits11
type bits53
type bits64

let exps : bits11 bitv sort = Bits.define 11
let sigs : bits53 bitv sort = Bits.define 53
let bitv : bits64 bitv sort = Bits.define 64

let fsort = Floats.define exps sigs

let knowledge_of_word sort w =
  let v = Value.create sort Semantics.empty in
  !! (Value.put GE.exp v (Some (Bil.int w)))

let of_float x =
  let bits = Word.of_int64 (Int64.bits_of_float x) in
  let bitv = knowledge_of_word bitv bits in
  G.of_ieee bitv G.rne fsort

let to_float x =
  let bitv = G.to_ieee bitv G.rne x in
  match eval bitv with
  | None -> None
  | Some w ->
     Word.signed w |>
     Word.to_int64_exn  |>
     Int64.float_of_bits |>
     Option.some

let rounding = G.rne

type binop = [
  | `Add
  | `Sub
  | `Mul
  | `Div
] [@@deriving sexp]

let caml_result x y = function
  | `Add -> x +. y
  | `Sub -> x -. y
  | `Mul -> x *. y
  | `Div -> x /. y

let string_of_op op x y =
  sprintf "%s %g %g" (Sexp.to_string (sexp_of_binop op)) x y

let fail info op x y =
  let op = string_of_op op x y in
  assert_bool (sprintf "failed %s(%s)" op info) false


let bit_equal op x y =
  let r = Int64.(bits_of_float x = bits_of_float y) in
  if not r then
    printf "Fail %s:\nreal: %s\nours: %s\n" op
      (string_of_bits64 x) (string_of_bits64 y);
  r

let binop op x y ctxt =
  let real = caml_result x y op in
  let f = match op with
       | `Add -> G.fadd
       | `Sub -> G.fsub
       | `Mul -> G.fmul
       | `Div -> G.fdiv in
  let x' = of_float x in
  let y' = of_float y in
  let z = f G.rne x' y' in
  match to_float z with
  | None -> fail "result is none" op x y
  | Some ours ->
     let op = string_of_op op x y in
     assert_bool op (bit_equal op real ours)

let ( - ) : test = binop `Sub
let ( + ) : test = binop `Add
let ( * ) : test = binop `Mul
let ( / ) : test = binop `Div


let suite () =
  let neg x = ~-. x in

  "Gfloat" >::: [

      (* add *)
      "0.0 + 0.5"     >:: 0.0 + 0.5;
      "4.2 + 2.3"     >:: 4.2 + 2.3;
      "4.2 + 2.98"    >:: 4.2 + 2.98;
      "2.2 + 4.28"    >:: 2.2 + 4.28;
      "2.2 + 2.46"    >:: 2.2 + 2.46;
      "0.0000001 + 0.00000002" >:: 0.0000001 + 0.00000002;
      "123213123.23434 + 56757.05656549151" >:: 123213123.23434 + 56757.05656549151;

      (* sub *)
      "4.2 - 2.28"    >:: 4.2 - 2.28;
      "4.28 - 2.2"    >:: 4.28 - 2.2;
      "2.2 - 4.28"    >:: 2.2 - 4.28;
      "2.2 - 2.6"     >:: 2.2 - 2.6;
      "0.0000001 - 0.00000002" >:: 0.0000001 - 0.00000002;
      "0.0 - 0.00000001" >:: 0.0 - 0.0000001;
      "0.0 - 0.0"     >:: 0.0 - 0.0;
      "4.2 - 4.2"     >:: 4.2 - 4.2;
      "123213123.23434 - 56757.05656549151" >:: 123213123.23434 - 56757.05656549151;

      (* mul *)
      "1.0 * 2.5"    >:: 1.0 * 2.5;
      "2.5 * 0.5"    >:: 2.5 * 0.5;
      "4.2 * 3.4"    >:: 4.2 * 3.4;
      "0.01 * 0.02"  >:: 0.01 * 0.02;
      "1.0 * 0.5"    >:: 1.0 * 0.5;
      "1.0 * -0.5"   >:: 1.0 * (neg 0.5);
      "- 1.0 * -0.5" >:: (neg 1.0) * (neg 0.5);

      (* div *)
      "2.0 / 0.5"   >:: 2.0 / 0.5;
      "1.0 / 3.0"   >:: 1.0 / 3.0;
      "3.0 / 32.0"  >:: 3.0 / 32.0;
      "42.3 / 0.0"  >:: 42.3 / 0.0;
      "324.32423 / 1.2" >:: 324.32423 / 1.2;
      "2.4 / 3.123131"  >:: 2.4 / 3.123131;
      "0.1313134 / 0.578465631" >:: 0.1313134 / 0.578465631;
      "9991132.2131363434 / 2435.05656549151" >:: 9991132.2131363434 / 2435.05656549151;

    ]

let float_result = print_result ~pref:"result"

let result x =
  match eval x with
  | Some e -> printf "result %s\n" (Word.to_string e)
  | _ -> printf "fail!\n"

let deconstruct x =
  let wi = Word.to_int_exn in
  let y = Int64.bits_of_float x in
  let w = Word.of_int64 y in
  let expn = Word.extract_exn ~hi:62 ~lo:52 w in
  let bias = Word.of_int ~width:11 1023 in
  let expn' = Word.(signed (expn - bias)) in
  let frac = Word.extract_exn ~hi:51 w in
  printf "ocaml %f: bits %s, 0x%LX\n" x (string_of_bits64 x) y;
  printf "ocaml %f: biased/unbiased expn %d/%d, coef 0x%x\n"
    x (wi expn) (wi expn') (wi frac)

let test_conv () =
  let x = ~-. 4.2 in
  deconstruct x;
  let bits = Word.of_int64 (Int64.bits_of_float x) in
  let bs = knowledge_of_word bitv bits in
  let x = G.of_ieee bs G.rne fsort in
  let y = G.to_ieee bitv G.rne x in
  result y

let test_min () =
  let create expn coef =
    let sign = GE.Basic.b0 in
    let expn = knowledge_of_word exps (Word.of_string expn) in
    let coef = knowledge_of_word sigs (Word.of_string coef) in
    G.finite fsort sign expn coef in
  let x = create "0x01:11u" "0x01:53u" in
  let z = G.minimize_exponent x in
  let z = G.exponent z in
  result z

let test () =
  let x = of_float 5.0 in
  float_result x

let a () = test ()
let () = run_test_tt_main (suite ())

module Clz = struct
  type bits122
  let sigs : bits122 bitv sort = Bits.define 122

  let test_clz () =
    let x = Word.of_int64 ~width:122 0x4L in
    let x = knowledge_of_word sigs x in
    let y = G.clz x in
    result y

  let res () = test_clz ()
end
