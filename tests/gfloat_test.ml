open Core_kernel
open Bap.Std
open Bap_knowledge
open Bap_core_theory

open Gfloat
module GE = Gfloat_exp

module G = Gfloat.Make(GE.BIL)

open Knowledge.Syntax

[@@warning "-3"]

let to_exp x =
  match Knowledge.run x Knowledge.empty with
  | Error _ -> assert false
  | Ok (s,_) ->
     match Semantics.get GE.exp s with
     | None -> printf "none!\n"
     | Some e ->
        printf "%s\n" (Exp.to_string e);
        printf "eval ... \n%!";
        match Exp.eval e with
        | Bil.Imm x ->
           printf "evaluated!\n%!";
           printf "result: %s!\n" (Word.to_string x)
        | _ -> assert false

type bits11
type bits53
type bits64

let exps : bits11 bitv sort = Bits.define 11
let sigs : bits53 bitv sort = Bits.define 53
let bitv : bits64 bitv sort = Bits.define 64

let fsort = Floats.define exps sigs

let create sort w =
  let v = Value.create sort Semantics.empty in
  !! (Value.put GE.exp v (Some (Bil.int w)))

let test () =
  let create expn coef =
    let sign = GE.Basic.b0 in
    let expn = create exps (Word.of_string expn) in
    let coef = create sigs (Word.of_string coef) in
    G.finite fsort sign expn coef in
  let x = create "0x7CD:11u" "0x1B333333333333:53u" in
  let y = create "0x7CE:11u" "0x10CCCCCCCCCCCD:53u" in
  let rm = G.rne in
  let z = G.fsub rm x y in
  (* let _ze = G.exponent z in
   * let z = G.significand z in *)
  z >>| fun v -> Value.semantics v


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

let deconstruct64 x =
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
  deconstruct64 x;
  let bits = Word.of_int64 (Int64.bits_of_float x) in
  let bs = create bitv bits in
  let x = G.of_ieee bs G.rne fsort in
  let y = G.to_ieee bitv G.rne x in
  y >>| fun v -> Value.semantics v

let test_min () =
  let create expn coef =
    let sign = GE.Basic.b0 in
    let expn = create exps (Word.of_string expn) in
    let coef = create sigs (Word.of_string coef) in
    G.finite fsort sign expn coef in
  let x = create "0x01:11u" "0x01:53u" in
  let z = G.minimize_exponent x in
  let z = G.significand z in
  z >>| fun v -> Value.semantics v

let res = to_exp @@ test_conv ()

module Clz = struct
  type bits122
  let sigs : bits122 bitv sort = Bits.define 122

  let test_clz () =
    let x = Word.of_int64 ~width:122 0x4L in
    let x = create sigs x in
    let y = G.clz x in
    y >>| fun y -> Value.semantics y

  let res () = to_exp @@ test_clz ()
end
