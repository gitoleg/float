open Core_kernel
open OUnit2
open Bap_plugins.Std
open Bap.Std
open Bap_knowledge
open Bap_core_theory

open Gfloat_debug

[@@@warning "-3"]

let () = Plugins.run ~provides:["bil"] ()

module Manager = Theory.Manager

module G = Gfloat.Make(Theory.Manager)

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

let eval x =
  let open Knowledge.Syntax in
  let x = x >>| Value.semantics in
  match Knowledge.run x Knowledge.empty with
  | Error _ -> assert false
  | Ok (s,_) ->
     match Semantics.get Bil.Domain.exp s with
     | None -> printf "Semantics.get: none!\n"; None
     | Some e ->
        (* printf "%s\n" (Exp.to_string e); *)
        let _a = Type.infer_exn e in
        match Expi.eval e with
        | Bil.Imm w -> Some w
        | Bil.Bot -> printf "got BOT!\n"; exit 1
        | Bil.Mem _ -> printf "got MEM!!\n"; exit 1

let exp x =
  let open Knowledge.Syntax in
  let x = x >>| Value.semantics in
  match Knowledge.run x Knowledge.empty with
  | Error _ -> assert false
  | Ok (s,_) -> Semantics.get Bil.Domain.exp s

type bits11
type bits53
type bits64

let exps : bits11 bitv sort = Bits.define 11
let sigs : bits53 bitv sort = Bits.define 53
let bitv : bits64 bitv sort = Bits.define 64
let fsort : ((int,bits11,bits53) IEEE754.ieee754,'s) format float sort  = IEEE754.(Sort.define binary64)


let word_of_float x = Word.of_int64 (Int64.bits_of_float x)

let float_of_word w =
  let a = Word.signed w in
  let b = Word.to_int64_exn a in
  Int64.float_of_bits b

let eval_binop op x y =
  let x = word_of_float x in
  let y = word_of_float y in
  let var = Theory.Manager.var in
  let op1 = Var.create bitv "op1" in
  let op2 = Var.create bitv "op2" in
  let r = op fsort G.rne (var op1) (var op2) in
  match exp r with
  | None -> assert false
  | Some exp ->
    let m = (object
      inherit Exp.mapper
      method! map_var v =
        if Bap.Std.Var.name v = "op1" then Bil.int x
        else if Bap.Std.Var.name v = "op2" then Bil.int y
        else Bil.var v
    end)#map_exp exp in
    match Expi.eval m with
    | Bil.Imm w -> float_of_word w
    | Bil.Bot -> printf "got BOT!\n"; exit 1
    | Bil.Mem _ -> printf "got MEM!!\n"; exit 1


let eval_unop op x =
  let x = word_of_float x in
  let var = Theory.Manager.var in
  let op1 = Var.create bitv "op1" in
  let r = op fsort G.rne (var op1)in
  match exp r with
  | None -> assert false
  | Some exp ->
    let m = (object
      inherit Exp.mapper
      method! map_var v =
        if Bap.Std.Var.name v = "op1" then Bil.int x
        else Bil.var v
    end)#map_exp exp in
    match Expi.eval m with
    | Bil.Imm w -> float_of_word w
    | Bil.Bot -> printf "got BOT!\n"; exit 1
    | Bil.Mem _ -> printf "got MEM!!\n"; exit 1


let of_word sort w =
  let v = Value.create sort Semantics.empty in
  Knowledge.return (Value.put Bil.Domain.exp v (Some (Bil.int w)))

let of_float x = of_word bitv (word_of_float x)

let to_float bitv =
  match eval bitv with
  | None -> None
  | Some w -> Some (float_of_word w)

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
  let x' = Int64.bits_of_float x in
  let y' = Int64.bits_of_float y in
  sprintf "%s %g %g(%Ld %Ld)"
    (Sexp.to_string (sexp_of_binop op)) x y x' y'

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
  let ours = eval_binop f x y in
  let op = string_of_op op x y in
  assert_bool op (bit_equal op real ours)

let sqrt x ctxt =
  let _fail info =
    assert_bool (sprintf "failed sqrt %g: %s" x info) false in
  let real = Float.sqrt x in
  let ours = eval_unop G.fsqrt x in
  assert_bool "sqrt" (bit_equal "sqrt" real ours)

let make_float s e c =
  let s = Word.of_int ~width:1 s in
  let e = Word.of_int ~width:11 e in
  let c = Word.of_int ~width:52 c in
  let w = Word.(concat (concat s e) c) in
  Word.signed w |> Word.to_int64_exn |> Int64.float_of_bits

let small_test () =
  let x = of_float (make_float 0 2011 0xFFFFFFFFF) in
  let y = of_float (make_float 0 0111 0xccccccccc) in
  let z = of_float (make_float 0 0555 0xaaaaaaaaa) in
  let (+) = G.fadd fsort G.rne in
  let r = x + y + z + y in
  eval r |> ignore

let ( + ) = binop `Add
let ( - ) = binop `Sub
let ( * ) = binop `Mul
let ( / ) = binop `Div

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

let a () = small_test ()

let gfloat_of_int x =
  let bits = Word.of_int ~width:64 x in
  let bitv = of_word bitv bits in
  G.cast_float fsort G.rne bitv

let of_uint x ctxt =
  let ops = sprintf "cast to float %d\n" x in
  let real = float x in
  let bitv = gfloat_of_int x in
  let ours = to_float bitv in
  match ours with
  | None -> assert_bool (sprintf "result is none %s" ops) false
  | Some ours ->
     assert_bool ops (bit_equal ops real ours)

let of_sint x ctxt =
  let ops = sprintf "cast to float signed %d\n" x in
  let real = float x in
  let bits = Word.of_int ~width:53 x in
  let bitv = of_word sigs bits in
  let ours = G.cast_float_signed fsort G.rne bitv |> to_float in
  match ours with
  | None -> assert_bool (sprintf "result is none %s" ops) false
  | Some ours ->
     assert_bool ops (bit_equal ops real ours)

let to_int x ctxt =
  let ops = sprintf "cast to int %f\n" x in
  let real = Int64.of_int (int_of_float x) in
  let check res =
    match res with
    | None -> assert_bool (sprintf "result is none %s" ops) false
    | Some res when Int64.(real = res) -> ()
    | Some res ->
      assert_bool (sprintf "%s failed: got %Ld" ops res) false in
  let ours = of_float x |> G.cast_int fsort bitv in
  match eval ours with
  | None -> check None
  | Some w ->
     let w = Word.to_int64_exn (Word.signed w) in
     check (Some w)

let small_test () =
  let x = gfloat_of_int 3 in
  let y = gfloat_of_int 4 in
  let z = G.fadd fsort G.rne x y in
  let w = G.cast_int fsort bitv z in
  match eval w with
  | None -> printf "fail!!\n"
  | Some r -> printf "myres %d\n" (Word.to_int_exn r)

let a () = small_test ()

let random_int ~from ~to_ =
  let open Caml in
  let max = to_ - from in
  let x = Random.int max in
  x + from

let random_float () =
  let expn () = random_int ~from:0 ~to_:2046 in
  let frac () = Random.int 4503599627370495 in
  let sign () = Random.int 2 in
  let make () =
    let expn = expn () in
    let frac = frac () in
    make_float (sign ()) expn frac in
  let small () =
    let x = Random.int 9 in
    let y = Int64.of_int x in
    Random.float (Int64.float_of_bits y) in
  match Random.int 10 with
  | 3 | 6 -> small ()
  | _ -> make ()

let make_random ~times =
  let random = Random.int in
  let random_elt xs = List.nth_exn xs @@ random (List.length xs) in
  List.init times ~f:(fun i ->
      let f (ctxt : test_ctxt) =
        let op = random_elt [`Add;`Sub; `Mul; `Div] in
        let x = random_float () in
        let y = random_float () in
        binop op x y ctxt in
       (sprintf "random%d" i) >:: f)

let of_int64 = Int64.float_of_bits

let suite () =

  "Gfloat" >::: [

      (* (\* of uint *\)
       * "of uint 42" >:: of_uint 42;
       * "of uint 0"  >:: of_uint 0;
       * "of uint 1"  >:: of_uint 1;
       * "of uint 2"  >:: of_uint 2;
       * "of uint 10" >:: of_uint 10;
       * "of uint 13213" >:: of_uint 13213;
       * "of uint 45676" >:: of_uint 45667;
       * "of uint 98236723" >:: of_uint 98236723;
       * "of uint 0xFFFF_FFFF_FFFF_FFF" >:: of_uint 0xFFFF_FFFF_FFFF_FFF;
       *
       * (\* of sint *\)
       * "of sint -42" >:: of_sint (-42);
       * "of sint 0"  >:: of_sint 0;
       * "of sint -1"  >:: of_sint 1;
       * "of sint -2"  >:: of_sint (-2);
       * "of sint -10" >:: of_sint (-10);
       * "of sint -13213" >:: of_sint (-13213);
       * "of sint -45676" >:: of_sint (-45667);
       * "of sint -98236723" >:: of_sint (-98236723);
       *
       * (\* to int *\)
       * "to int 42.42" >:: to_int 42.42;
       * "to int 0.42" >:: to_int 0.42;
       * "to int 0.99999999999" >:: to_int 0.99999999999;
       * "to int 13123120.98882344542" >:: to_int 13123120.98882344542;
       * "to int -42.42" >:: to_int (-42.42);
       * "to int -13123120.98882344542" >:: to_int (-13123120.98882344542); *)

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
      "biggest_normal + small"  >:: biggest_normal + smallest_nonzero;
      "biggest_normal + biggest_subnorm"  >:: biggest_normal + biggest_subnormal;
      "near inf case" >:: make_float 0 2046 0xFFFF_FFFF_FFFF_FFF + make_float 0 2046 1;

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
      "0.0 - small"   >:: 0.0 - smallest_nonzero;
      "small - 0.0"   >:: smallest_nonzero - 0.0;
      "small - small"  >:: smallest_nonzero - smallest_nonzero;
      "small - small'" >:: smallest_nonzero - some_small;
      "small' - small" >:: some_small - smallest_nonzero;
      "smalles_norm - small" >:: smallest_normal - smallest_nonzero;
      "biggest_sub - small"   >:: biggest_subnormal - smallest_nonzero;
      "biggest_normal - small"  >:: biggest_normal - smallest_nonzero;
      "biggest_normal - biggest_subnorm"  >:: biggest_normal - biggest_subnormal;
      "biggest_subnorm - biggest_normal"  >:: biggest_subnormal - biggest_normal;
      "near inf case" >:: make_float 1 2046 0xFFFF_FFFF_FFFF_FFF - make_float 0 2046 1;

      (* mul *)
      "1.0 * 2.5"    >:: 1.0 * 2.5;
      "2.5 * 0.5"    >:: 2.5 * 0.5;
      "4.2 * 3.4"    >:: 4.2 * 3.4;
      "0.01 * 0.02"  >:: 0.01 * 0.02;
      "1.0 * 0.5"    >:: 1.0 * 0.5;
      "1.0 * -0.5"   >:: 1.0 * (neg 0.5);
      "- 1.0 * -0.5" >:: (neg 1.0) * (neg 0.5);
      "123734.86124324198 * 23967986786.4834517" >:: 123734.86124324198 * 23967986786.4834517;
      "nan  * nan"    >:: nan  * nan;
      "inf  * inf"    >:: inf  * inf;
      "-inf * -inf"   >:: ninf * ninf;
      "nan  * -inf"   >:: nan  * ninf;
      "-inf * nan"    >:: ninf * nan;
      "nan  * inf"    >:: nan  * inf;
      "inf  * nan"    >:: inf  * nan;
      "-inf * inf"    >:: ninf * inf;
      "inf  * -inf"   >:: inf  * ninf;
      "0.0 * big"     >:: 0.0 * biggest_normal;
      "0.0 * small"   >:: 0.0 * biggest_subnormal;
      "0.0 * small'"  >:: 0.0 * smallest_nonzero;
      "2.0 * small"  >:: 2.0 * smallest_nonzero;
      "1123131.45355 * small"  >:: 1123131.45355 * smallest_nonzero;
      "small * small" >:: smallest_nonzero * some_small;
      "smallest normal * small"    >:: smallest_normal * smallest_nonzero;
      "biggest subnormal * small"     >:: biggest_subnormal * smallest_nonzero;
      "biggest normal * small"  >:: biggest_normal * smallest_nonzero;
      "biggest normal * 2.0"    >:: biggest_normal * 2.0;
      "biggest normal * biggest subnormal"  >:: biggest_normal * biggest_subnormal;
      "biggest subnormal * small" >:: biggest_subnormal * smallest_nonzero;
      "biggest subnormal * biggest subnormal" >:: biggest_subnormal *  biggest_subnormal;
      "biggest normal * biggest normal" >:: biggest_normal *  biggest_normal;
      "test with underflow" >:: of_int64 974381688320862858L * of_int64 (-5590604654947855237L);

      (* div *)
      "2.0 / 0.5"   >:: 2.0 / 0.5;
      "1.0 / 3.0"   >:: 1.0 / 3.0;
      "3.0 / 32.0"  >:: 3.0 / 32.0;
      "324.32423 / 1.2" >:: 324.32423 / 1.2;
      "2.4 / 3.123131"  >:: 2.4 / 3.123131;
      "0.1313134 / 0.578465631" >:: 0.1313134 / 0.578465631;
      "9991132.2131363434 / 2435.05656549153" >:: 9991132.2131363434 / 2435.05656549153;
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
      "biggest_normal / biggest_subnorm"  >:: biggest_normal / biggest_subnormal;
      "biggest_normal / smallest_normal"  >:: biggest_normal / smallest_normal;
  ] @ make_random ~times:50000

let suite () =
  "test" >::: [
      "1"  >:: sqrt 1.0;
      "2"  >:: sqrt 2.0;
      "3"  >:: sqrt 3.0;
      "4"  >:: sqrt 4.0;
      "small" >:: sqrt some_small

    ]

let () = run_test_tt_main (suite ())

let test a =
  let ( * ) = G.fmul fsort G.rne in
  let x = of_float 1.0 in
  let x' = of_float 2.0 in
  let y = x * x' * x in
  match to_float y with
  | None -> printf "result is none!!\n"
  | Some x ->
     let s = string_of_bits64 x in
     printf "result is %g %s\n" x s

let l2 (x,y,z) (x',y',z') =
  let of_op f = f fsort G.rne in
  let ( + ) = of_op G.fadd in
  let ( - ) = of_op G.fsub in
  let ( * ) = of_op G.fmul in
  let sqrt = of_op G.fsqrt in
  let pow2 x = x * x in
  let x = of_float x in
  let y = of_float y in
  let z = of_float z in
  let x' = of_float x' in
  let y' = of_float y' in
  let z' = of_float z' in
  sqrt (((pow2 (x - x')) + (pow2 (y - y')) + (pow2 (z - z'))))

let a () =
  let x = l2 (1.0,0.0,0.0) (0.0,0.0,0.0) in
  match to_float x with
  | None -> printf "result is none!!\n"
  | Some x ->
     let s = string_of_bits64 x in
     printf "result is %g %s\n" x s
