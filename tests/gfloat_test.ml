open Core_kernel
open OUnit2
open Bap.Std
open Bap_knowledge
open Bap_core_theory

open Gfloat

[@@@warning "-3"]

module Expi = struct
  open Bil
  open Monads.Std
  open Monad.State.Syntax
  module State = Monad.State

  class ['a] t = object(self)
    inherit ['a] Expi.t

    method! eval_let var u body=
      self#eval_exp u >>= fun u ->
      self#lookup var >>= fun w ->
      self#update var u >>= fun () ->
      self#eval_exp body >>= fun r ->
      self#update var w >>= fun () ->
      State.return r

    method! eval_exp exp = match exp with
      | Load (m,a,e,s) -> self#eval_load ~mem:m ~addr:a e s
      | Store (m,a,u,e,s) -> self#eval_store ~mem:m ~addr:a u e s
      | Var v -> self#eval_var v
      | BinOp (op,u,v) -> self#eval_binop op u v
      | UnOp (op,u) -> self#eval_unop op u
      | Int u -> self#eval_int u
      | Cast (ct,sz,e) -> self#eval_cast ct sz e
      | Let (v,u,b) -> self#eval_let v u b
      | Unknown (m,t) -> self#eval_unknown m t
      | Ite (cond,yes,no) -> self#eval_ite ~cond ~yes ~no
      | Extract (hi,lo,w) -> self#eval_extract hi lo w
      | Concat (u,w) -> self#eval_concat u w
  end

  let eval x =
    let expi = new t and ctxt = new Expi.context in
    Bil.Result.value @@ Monad.State.eval (expi#eval_exp x) ctxt
end

open Gfloat
module GE = Gfloat_exp

module G = Gfloat.Make(GE.BIL)

open Knowledge.Syntax

let eval x =
  let x = x >>| Value.semantics in
  match Knowledge.run x Knowledge.empty with
  | Error _ -> assert false
  | Ok (s,_) ->
     match Semantics.get GE.exp s with
     | None -> printf "Semantics.get: none!\n"; None
     | Some e ->
        (* printf "%s\n" (Exp.to_string e); *)
        match Expi.eval e with
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

type bits11
type bits53
type bits64

let exps : bits11 bitv sort = Bits.define 11
let sigs : bits53 bitv sort = Bits.define 53
let bitv : bits64 bitv sort = Bits.define 64

let knowledge_of_word sort w =
  let v = Value.create sort Semantics.empty in
  !! (Value.put GE.exp v (Some (Bil.int w)))

let fsort : ((int,bits11,bits53) IEEE754.ieee754,'s) format float sort  = IEEE754.(Sort.define binary64)

let of_float x =
  let bits = Word.of_int64 (Int64.bits_of_float x) in
  let bitv = knowledge_of_word bitv bits in
  bitv

let to_float bitv =
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
  let z = f fsort G.rne x' y' in
  match to_float z with
  | None -> fail "result is none" op x y
  | Some ours ->
     let op = string_of_op op x y in
     assert_bool op (bit_equal op real ours)

let ( + ) = binop `Add
let ( - ) = binop `Sub
let ( * ) = binop `Mul
let ( / ) = binop `Div

let make_float s e c =
  let s = Word.of_int ~width:1 s in
  let e = Word.of_int ~width:11 e in
  let c = Word.of_int ~width:52 c in
  let w = Word.(concat (concat s e) c) in
  Word.signed w |> Word.to_int64_exn |> Int64.float_of_bits

(* let bits64 : bits64 bitv sort = Bits.define 64
 *
 * let a = Var.create bits64 "A"
 * let b = Var.create bits64 "B"
 *
 * let z = G.fadd fsort G.rne (GE.BIL.var a) (GE.BIL.var b)
 * let _ = eval z *)

let neg x = ~-. x
let nan = Float.nan
let inf = Float.infinity
let ninf = Float.neg_infinity
let smallest_nonzero = make_float 0 0 1
let some_small = make_float 0 0 2
let biggest_subnormal = make_float 0 0 0xFFFF_FFFF_FFFF_F
let smallest_normal = Float.(biggest_subnormal + smallest_nonzero)
let biggest_normal = make_float 0 2046 0xFFFF_FFFF_FFFF_F


let small_test () =
  let (+) = G.fadd fsort G.rne in
  let (/) = G.fdiv fsort G.rne in
  let pi = of_float 3.14 in
  let phi = of_float 1.61 in
  let e = of_float 2.71 in
  let n = of_float 3.0 in
  let avg = to_float ((pi + phi + e) / n) in
  match  avg with
  | None -> printf "FAIL!!!\n"
  | Some avg -> printf "%g\n" avg

let () = small_test ()


let suite () =

  "Gfloat" >::: [

      (* add *)
      "0.0 + 0.5"     >:: 0.0 + 0.5;
      "4.2 + 2.3"     >:: 4.2 + 2.3;
      "4.2 + 2.98"    >:: 4.2 + 2.98;
      "2.2 + 4.28"    >:: 2.2 + 4.28;
      "2.2 + 2.46"    >:: 2.2 + 2.46;
      "2.2 + -4.28"   >:: 2.2 + (neg 4.28);
      "-2.2 + 4.28"   >:: (neg 2.2) + 4.28;
      "0.0000001 + 0.00000002" >:: 0.0000001 + 0.00000002;
      "123213123.23434 + 56757.05656549151" >:: 123213123.23434 + 56757.05656549151;
      "nan  + nan"    >:: nan  + nan;
      "inf  + inf"    >:: inf  + inf;
      "-inf + -inf"   >:: ninf + ninf;
      "nan  + -inf"   >:: nan  + ninf;
      "-inf + nan"    >:: ninf + nan;
      "nan  + inf"    >:: nan  + inf;
      "inf  + nan"    >:: inf  + nan;
      "-inf + inf"    >:: ninf + inf;
      "inf  + -inf"   >:: inf  + ninf;
      "0.0 + small"   >:: 0.0 + smallest_nonzero;
      "small + small" >:: smallest_nonzero + some_small;
      "biggest_sub + small"  >:: biggest_subnormal + smallest_nonzero;
      "biggest_sub + small"   >:: biggest_subnormal + smallest_nonzero;
      "biggest_normal + small"  >:: biggest_normal + smallest_nonzero;

      (* sub *)
      "4.2 - 2.28"    >:: 4.2 - 2.28;
      "4.28 - 2.2"    >:: 4.28 - 2.2;
      "2.2 - 4.28"    >:: 2.2 - 4.28;
      "2.2 - 2.6"     >:: 2.2 - 2.6;
      "0.0 - 0.0"     >:: 0.0 - 0.0;
      "4.2 - 4.2"     >:: 4.2 - 4.2;
      "2.2 - -4.28"   >:: 2.2 - (neg 4.28);
      "-2.2 - 2.46"   >:: (neg 2.2) - 2.46;
      "-2.2 - -2.46"  >:: (neg 2.2) - (neg 2.46);
      "0.0000001 - 0.00000002" >:: 0.0000001 - 0.00000002;
      "0.0 - 0.00000001"       >:: 0.0 - 0.0000001;
      "123213123.23434 - 56757.05656549151" >:: 123213123.23434 - 56757.05656549151;
      "nan  - nan"    >:: nan  - nan;
      "inf  - inf"    >:: inf  - inf;
      "-inf - -inf"   >:: ninf - ninf;
      "nan  - -inf"   >:: nan  - ninf;
      "-inf - nan"    >:: ninf - nan;
      "nan  - inf"    >:: nan  - inf;
      "inf  - nan"    >:: inf  - nan;
      "-inf - inf"    >:: ninf - inf;
      "inf  - -inf"   >:: inf  - ninf;
      "0.0 0 small"   >:: 0.0 - smallest_nonzero;
      "small - small"  >:: smallest_nonzero - smallest_nonzero;
      "small - small'" >:: smallest_nonzero - some_small;
      "small' - small" >:: some_small - smallest_nonzero;
      "smalles_norm - small" >:: smallest_normal - smallest_nonzero;
      "biggest_sub - small"   >:: biggest_subnormal - smallest_nonzero;
      "biggest_normal - small"  >:: biggest_normal - smallest_nonzero;

      (* mul *)
      "1.0 * 2.5"    >:: 1.0 * 2.5;
      "2.5 * 0.5"    >:: 2.5 * 0.5;
      "4.2 * 3.4"    >:: 4.2 * 3.4;
      "0.01 * 0.02"  >:: 0.01 * 0.02;
      "1.0 * 0.5"    >:: 1.0 * 0.5;
      "1.0 * -0.5"   >:: 1.0 * (neg 0.5);
      "- 1.0 * -0.5" >:: (neg 1.0) * (neg 0.5);
      "nan  * nan"    >:: nan  * nan;
      "inf  * inf"    >:: inf  * inf;
      "-inf * -inf"   >:: ninf * ninf;
      "nan  * -inf"   >:: nan  * ninf;
      "-inf * nan"    >:: ninf * nan;
      "nan  * inf"    >:: nan  * inf;
      "inf  * nan"    >:: inf  * nan;
      "-inf * inf"    >:: ninf * inf;
      "inf  * -inf"   >:: inf  * ninf;
      "0.0 * small"  >:: 0.0 * smallest_nonzero;
      "small * small" >:: smallest_nonzero * some_small;
      "smalles_norm * small" >:: smallest_normal * smallest_nonzero;
      "biggest_sub * small"   >:: biggest_subnormal * smallest_nonzero;
      "biggest_normal * small"  >:: biggest_normal * smallest_nonzero;
      "biggest_normal * 2.0"  >:: biggest_normal * 2.0;

      (* div *)
      "2.0 / 0.5"   >:: 2.0 / 0.5;
      "1.0 / 3.0"   >:: 1.0 / 3.0;
      "3.0 / 32.0"  >:: 3.0 / 32.0;
      "324.32423 / 1.2" >:: 324.32423 / 1.2;
      "2.4 / 3.123131"  >:: 2.4 / 3.123131;
      "0.1313134 / 0.578465631" >:: 0.1313134 / 0.578465631;
      "9991132.2131363434 / 2435.05656549151" >:: 9991132.2131363434 / 2435.05656549151;
      "nan  / nan"    >:: nan  / nan;
      "inf  / inf"    >:: inf  / inf;
      "-inf / -inf"   >:: ninf / ninf;
      "nan  / -inf"   >:: nan  / ninf;
      "-inf / nan"    >:: ninf / nan;
      "nan  / inf"    >:: nan  / inf;
      "inf  / nan"    >:: inf  / nan;
      "-inf / inf"    >:: ninf / inf;
      "inf  / -inf"   >:: inf  / ninf;
      "0.0  / small"  >:: 0.0 / smallest_nonzero;
      "small  / small'" >:: smallest_nonzero / some_small;
      "small' / small" >:: some_small / smallest_nonzero;
      "small  / small" >:: smallest_nonzero / smallest_nonzero;
      "smallest_norm / small" >:: smallest_normal / smallest_nonzero;
      "biggest_sub / small"   >:: biggest_subnormal / smallest_nonzero;
      "biggest_normal / small"  >:: biggest_normal / smallest_nonzero;
    ]

let asuite () =
  "test" >::: [
      "biggest_normal * small"  >:: biggest_normal * biggest_subnormal;
      (* "aa" >:: 3.0 / 32.0; *)
      (* "biggest_norm / small"  >:: biggest_normal / smallest_nonzero; *)
      (* "smalles_norm / small" >:: smallest_normal / smallest_nonzero; *)
    ]

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

(* let () = deconstruct (make_float 0 0 0xFFFF_FFFF_FFFF_F) *)
(* let nan = Int64.float_of_bits (0b0_11111111111_0000000000000000000000000000111000000000000000000001L) *)

(* let () = deconstruct nan
 * let () = deconstruct (Float.neg_infinity *. Float.neg_infinity) *)

let  () = run_test_tt_main (suite ())
