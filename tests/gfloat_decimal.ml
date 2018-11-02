open Core_kernel
open OUnit2
open Gfloat
open Gfloat_z

let ebits = 10
let fbits = 54
let desc = desc ~radix:10 ~expn_bits:ebits fbits

(* For the record only. we will not use it until will be sure about it  *)
let maxe = 767
let bias = 398

type sign = Pos | Neg [@@deriving sexp]

type num =
  | Def of (sign * int64 * int64)
  | Inf of sign
  | Qnan

let rnd_of_int = function
  | 0 -> Nearest_even
  | 1 -> Negative_inf
  | 2 -> Positive_inf
  | 3 -> Towards_zero
  | 4 -> Nearest_away
  | _ -> failwith "unexpected rounding!"

let gfloat_is_inf x =
  Gfloat_z.is_inf x ||
  (match Gfloat_z.fin x with
   | None -> false
   | Some ((_,expn), (_, frac)) ->
     Z.(frac = zero) &&
     Z.(expn = of_int (-1)))

let make_gfloat = function
  | Qnan -> Gfloat_z.nan ~signaling:true desc
  | Inf s -> Gfloat_z.inf ~negative:(s = Neg) desc
  | Def (sign,expn,frac) ->
    let expn = Z.of_int64 expn in
    let frac = Z.of_int64 frac in
    let negative = sign = Neg in
    create desc ~negative ~expn:(ebits,expn) (fbits, frac)


let triple_to_string (sign,expn,frac) =
  let sign = if sign = Pos then "" else "-" in
  sprintf "(%s 0x%Lx 0x%Lx)" sign expn frac

let check (f,x,y) expected (_ : test_ctxt ) =
  let x = make_gfloat x in
  let y = make_gfloat y in
  let result = f x y in
  let expected = make_gfloat expected in
  match Gfloat_z.fin result, Gfloat_z.fin expected with
  | Some ((_,expn_r), (_,frac_r)), Some ((_,expn_e), (_,frac_e)) ->

    let r = Z.equal expn_r expn_e && Z.equal frac_r frac_e in
    if not r then
      begin
        printf "my result is %s %s \n"
          (Z.to_string expn_r) (Z.to_string frac_r);
        printf "right result is %s %s \n\n"
          (Z.to_string expn_e) (Z.to_string frac_e);
      end;
    assert_bool "" r
  | _ ->
    let r =
      Gfloat_z.is_inf result && Gfloat_z.is_inf expected  ||
      Gfloat_z.is_nan result && Gfloat_z.is_nan expected in
    assert_bool "" r

let (=) = check

let suite () =
  "Some test" >::: [

    (* "(Qnan + Qnan = Qnan" >:: *)
    (* ((add ~rm:Nearest_away, Qnan, Qnan) = Qnan); *)

    (* "(Qnan + inf = Qnan)" >:: *)
    (* ((add ~rm:Nearest_away,Qnan,(Inf Pos)) = Qnan); *)

    (* "((-inf) + (Pos,0x18e,0x0) = (-inf))" >:: *)
    (* ((add ~rm:Nearest_away,(Inf Neg),(Def (Pos,0x18eL,0x0L))) = (Inf Neg)); *)

    (* "(inf + (Pos,0x18e,0x0) = inf)" >:: *)
    (* ((add ~rm:Nearest_away,(Inf Pos),(Def (Pos,0x18eL,0x0L))) = (Inf Pos)); *)

    (* "((Neg,0x193,0x8) + (Pos,0x190,0xab1) = (Neg,0x190,0x148f))" >:: *)
    (* ((add ~rm:Nearest_away,(Def (Neg,0x193L,0x8L)),(Def (Pos,0x190L,0xab1L))) = (Def (Neg,0x190L,0x148fL))); *)

    (* "((Pos,0x191,0x2b) + (Pos,0x18a,0x0) = (Pos,0x18a,0x19a14780))" >:: *)
    (* ((add ~rm:Nearest_away,(Def (Pos,0x191L,0x2bL)),(Def (Pos,0x18aL,0x0L))) = (Def (Pos,0x18aL,0x19a14780L))); *)

    (* "((Pos,0x295,0x2710) + (Neg,0xc9,0x0) = (Pos,0x28a,0x38d7ea4c68000))" >:: *)
    (* ((add ~rm:Nearest_away,(Def (Pos,0x295L,0x2710L)),(Def (Neg,0xc9L,0x0L))) = (Def (Pos,0x28aL,0x38d7ea4c68000L))); *)

    (* "(Qnan + Qnan = Qnan)" >:: *)
    (* ((add ~rm:Towards_zero,Qnan,Qnan) = Qnan); *)

    (* "(Qnan + inf = Qnan)" >:: *)
    (* ((add ~rm:Towards_zero,Qnan,(Inf Pos)) = Qnan); *)

    (* "((-inf) + (Pos,0x18e,0x0) = (-inf))" >:: *)
    (* ((add ~rm:Towards_zero,(Inf Neg),(Def (Pos,0x18eL,0x0L))) = (Inf Neg)); *)

    (* "(inf + (Pos,0x18e,0x0) = inf)" >:: *)
    (* ((add ~rm:Towards_zero,(Inf Pos),(Def (Pos,0x18eL,0x0L))) = (Inf Pos)); *)

    (* "((Neg,0x193,0x8) + (Pos,0x190,0xab1) = (Neg,0x190,0x148f))" >:: *)
    (* ((add ~rm:Towards_zero,(Def (Neg,0x193L,0x8L)),(Def (Pos,0x190L,0xab1L))) = (Def (Neg,0x190L,0x148fL))); *)

    (* "((Pos,0x191,0x2b) + (Pos,0x18a,0x0) = (Pos,0x18a,0x19a14780))" >:: *)
    (* ((add ~rm:Towards_zero,(Def (Pos,0x191L,0x2bL)),(Def (Pos,0x18aL,0x0L))) = (Def (Pos,0x18aL,0x19a14780L))); *)

    (* "((Pos,0x295,0x2710) + (Neg,0xc9,0x0) = (Pos,0x28a,0x38d7ea4c68000))" >:: *)
    (* ((add ~rm:Towards_zero,(Def (Pos,0x295L,0x2710L)),(Def (Neg,0xc9L,0x0L))) = (Def (Pos,0x28aL,0x38d7ea4c68000L))); *)

    (* "(Qnan + Qnan = Qnan)" >:: *)
    (* ((add ~rm:Positive_inf,Qnan,Qnan) = Qnan); *)

    (* "(Qnan + inf = Qnan)" >:: *)
    (* ((add ~rm:Positive_inf,Qnan,(Inf Pos)) = Qnan); *)

    (* "((-inf) + (Pos,0x18e,0x0) = (-inf))" >:: *)
    (* ((add ~rm:Positive_inf,(Inf Neg),(Def (Pos,0x18eL,0x0L))) = (Inf Neg)); *)

    (* "(inf + (Pos,0x18e,0x0) = inf)" >:: *)
    (* ((add ~rm:Positive_inf,(Inf Pos),(Def (Pos,0x18eL,0x0L))) = (Inf Pos)); *)

    (* "((Neg,0x193,0x8) + (Pos,0x190,0xab1) = (Neg,0x190,0x148f))" >:: *)
    (* ((add ~rm:Positive_inf,(Def (Neg,0x193L,0x8L)),(Def (Pos,0x190L,0xab1L))) = (Def (Neg,0x190L,0x148fL))); *)

    (* "((Pos,0x191,0x2b) + (Pos,0x18a,0x0) = (Pos,0x18a,0x19a14780))" >:: *)
    (* ((add ~rm:Positive_inf,(Def (Pos,0x191L,0x2bL)),(Def (Pos,0x18aL,0x0L))) = (Def (Pos,0x18aL,0x19a14780L))); *)

    (* "((Pos,0x295,0x2710) + (Neg,0xc9,0x0) = (Pos,0x28a,0x38d7ea4c68000))" >:: *)
    (* ((add ~rm:Positive_inf,(Def (Pos,0x295L,0x2710L)),(Def (Neg,0xc9L,0x0L))) = (Def (Pos,0x28aL,0x38d7ea4c68000L))); *)

    (* "(Qnan + Qnan = Qnan)" >:: *)
    (* ((add ~rm:Negative_inf,Qnan,Qnan) = Qnan); *)

    (* "(Qnan + inf = Qnan)" >:: *)
    (* ((add ~rm:Negative_inf,Qnan,(Inf Pos)) = Qnan); *)

    (* "((-inf) + (Pos,0x18e,0x0) = (-inf))" >:: *)
    (* ((add ~rm:Negative_inf,(Inf Neg),(Def (Pos,0x18eL,0x0L))) = (Inf Neg)); *)

    (* "(inf + (Pos,0x18e,0x0) = inf)" >:: *)
    (* ((add ~rm:Negative_inf,(Inf Pos),(Def (Pos,0x18eL,0x0L))) = (Inf Pos)); *)

    (* "((Neg,0x193,0x8) + (Pos,0x190,0xab1) = (Neg,0x190,0x148f))" >:: *)
    (* ((add ~rm:Negative_inf,(Def (Neg,0x193L,0x8L)),(Def (Pos,0x190L,0xab1L))) = (Def (Neg,0x190L,0x148fL))); *)

    (* "((Pos,0x1f,0x0) + (Neg,0xfe,0x0) = (Neg,0x1f,0x0))" >:: *)
    (* ((add ~rm:Negative_inf,(Def (Pos,0x1fL,0x0L)),(Def (Neg,0xfeL,0x0L))) = (Def (Neg,0x1fL,0x0L))); *)

    (* "((Pos,0x191,0x2b) + (Pos,0x18a,0x0) = (Pos,0x18a,0x19a14780))" >:: *)
    (* ((add ~rm:Negative_inf,(Def (Pos,0x191L,0x2bL)),(Def (Pos,0x18aL,0x0L))) = (Def (Pos,0x18aL,0x19a14780L))); *)

    (* "((Pos,0xed,0x0) + (Neg,0x2e9,0x0) = (Neg,0xed,0x0))" >:: *)
    (* ((add ~rm:Negative_inf,(Def (Pos,0xedL,0x0L)),(Def (Neg,0x2e9L,0x0L))) = (Def (Neg,0xedL,0x0L))); *)

    (* "((Pos,0x295,0x2710) + (Neg,0xc9,0x0) = (Pos,0x28a,0x38d7ea4c68000))" >:: *)
    (* ((add ~rm:Negative_inf,(Def (Pos,0x295L,0x2710L)),(Def (Neg,0xc9L,0x0L))) = (Def (Pos,0x28aL,0x38d7ea4c68000L))); *)

    (* "(Qnan + Qnan = Qnan)" >:: *)
    (* ((add ~rm:Nearest_even,Qnan,Qnan) = Qnan); *)

    (* "(Qnan + inf = Qnan)" >:: *)
    (* ((add ~rm:Nearest_even,Qnan,(Inf Pos)) = Qnan); *)

    (* "((-inf) + (Pos,0x18e,0x0) = (-inf))" >:: *)
    (* ((add ~rm:Nearest_even,(Inf Neg),(Def (Pos,0x18eL,0x0L))) = (Inf Neg)); *)

    (* "(inf + (Pos,0x18e,0x0) = inf)" >:: *)
    (* ((add ~rm:Nearest_even,(Inf Pos),(Def (Pos,0x18eL,0x0L))) = (Inf Pos)); *)

    (* "((-inf) + (-inf) = (-inf))" >:: *)
    (* ((add ~rm:Nearest_even,(Inf Neg),(Inf Neg)) = (Inf Neg)); *)

    (* "((Neg,0x193,0x8) + (Pos,0x190,0xab1) = (Neg,0x190,0x148f))" >:: *)
    (* ((add ~rm:Nearest_even,(Def (Neg,0x193L,0x8L)),(Def (Pos,0x190L,0xab1L))) = (Def (Neg,0x190L,0x148fL))); *)

    (* "((Neg,0x0,0x465810d808004) + (Pos,0x8,0x202000) = (Neg,0x0,0x3a60631608004))" >:: *)
    (* ((add ~rm:Nearest_even,(Def (Neg,0x0L,0x465810d808004L)),(Def (Pos,0x8L,0x202000L))) = (Def (Neg,0x0L,0x3a60631608004L))); *)

    (* "((Pos,0x191,0x2b) + (Pos,0x18a,0x0) = (Pos,0x18a,0x19a14780))" >:: *)
    (* ((add ~rm:Nearest_even,(Def (Pos,0x191L,0x2bL)),(Def (Pos,0x18aL,0x0L))) = (Def (Pos,0x18aL,0x19a14780L))); *)

    (* "((Pos,0x295,0x2710) + (Neg,0xc9,0x0) = (Pos,0x28a,0x38d7ea4c68000))" >:: *)
    (* ((add ~rm:Nearest_even,(Def (Pos,0x295L,0x2710L)),(Def (Neg,0xc9L,0x0L))) = (Def (Pos,0x28aL,0x38d7ea4c68000L))); *)

    (* "((Pos,0x2fe,0x0) + (Neg,0x0,0xfc00000000000000) = (Neg,0x0,0xfc00000000000000))" >:: *)
    (* ((add ~rm:Nearest_even,(Def (Pos,0x2feL,0x0L)),(Def (Neg,0x0L,0xfc00000000000000L))) = (Def (Neg,0x0L,0xfc00000000000000L))); *)

    (* "((-inf) + (Pos,0x24e,0x154d8203c5a840) = (-inf))" >:: *)
    (* ((add ~rm:Nearest_even,(Inf Neg),(Def (Pos,0x24eL,0x154d8203c5a840L))) = (Inf Neg)); *)


    (* "(inf - (Neg,0x18e,0x0) = inf)" >:: *)
    (* ((sub ~rm:Nearest_away,(Inf Pos),(Def (Neg,0x18eL,0x0L))) = (Inf Pos)); *)

    (* "(inf - (Neg,0x18e,0x0) = inf)" >:: *)
    (* ((sub ~rm:Towards_zero,(Inf Pos),(Def (Neg,0x18eL,0x0L))) = (Inf Pos)); *)

    (* "(inf - (Neg,0x18e,0x0) = inf)" >:: *)
    (* ((sub ~rm:Positive_inf,(Inf Pos),(Def (Neg,0x18eL,0x0L))) = (Inf Pos)); *)

    (* "(inf - (Neg,0x18e,0x0) = inf)" >:: *)
    (* ((sub ~rm:Negative_inf,(Inf Pos),(Def (Neg,0x18eL,0x0L))) = (Inf Pos)); *)

    (* "((Pos,0x18e,0x0) - (Pos,0x18e,0x0) = (Neg,0x18e,0x0))" >:: *)
    (* ((sub ~rm:Negative_inf,(Def (Pos,0x18eL,0x0L)),(Def (Pos,0x18eL,0x0L))) = (Def (Neg,0x18eL,0x0L))); *)

    (* "((Pos,0x0,0x400) - (Pos,0x0,0x400) = (Neg,0x0,0x0))" >:: *)
    (* ((sub ~rm:Negative_inf,(Def (Pos,0x0L,0x400L)),(Def (Pos,0x0L,0x400L))) = (Def (Neg,0x0L,0x0L))); *)

    (* "(inf - (Neg,0x18e,0x0) = inf)" >:: *)
    (* ((sub ~rm:Nearest_even,(Inf Pos),(Def (Neg,0x18eL,0x0L))) = (Inf Pos)); *)

    (* "(Qnan * (-inf) = Qnan)" >:: *)
    (* ((mul ~rm:Nearest_away,Qnan,(Inf Neg)) = Qnan); *)

    (* "(inf * inf = inf)" >:: *)
    (* ((mul ~rm:Nearest_away,(Inf Pos),(Inf Pos)) = (Inf Pos)); *)

    (* "((-inf) * (-inf) = inf)" >:: *)
    (* ((mul ~rm:Nearest_away,(Inf Neg),(Inf Neg)) = (Inf Pos)); *)

    (* "(Qnan * (-inf) = Qnan)" >:: *)
    (* ((mul ~rm:Towards_zero,Qnan,(Inf Neg)) = Qnan); *)

    (* "(inf * inf = inf)" >:: *)
    (* ((mul ~rm:Towards_zero,(Inf Pos),(Inf Pos)) = (Inf Pos)); *)

    (* "((-inf) * (-inf) = inf)" >:: *)
    (* ((mul ~rm:Towards_zero,(Inf Neg),(Inf Neg)) = (Inf Pos)); *)

    (* "(Qnan * (-inf) = Qnan)" >:: *)
    (* ((mul ~rm:Positive_inf,Qnan,(Inf Neg)) = Qnan); *)

    (* "(inf * inf = inf)" >:: *)
    (* ((mul ~rm:Positive_inf,(Inf Pos),(Inf Pos)) = (Inf Pos)); *)

    (* "((-inf) * (-inf) = inf)" >:: *)
    (* ((mul ~rm:Positive_inf,(Inf Neg),(Inf Neg)) = (Inf Pos)); *)

      "((Pos,0x2e9,0x130a9955f87cf6) * (Pos,0x0,0x2) = (Pos,0x15c,0x3ceeb779818fe))" >::
    ((mul ~rm:Positive_inf,(Def (Pos,0x2e9L,0x130a9955f87cf6L)),(Def (Pos,0x0L,0x2L))) = (Def (Pos,0x15cL,0x3ceeb779818feL)));

    (* "((Pos,0xd,0x1) * (Neg,0x180,0x3328b944c4000) = (Neg,0x0,0x51dac207a000))" >:: *)
    (* ((mul ~rm:Positive_inf,(Def (Pos,0xdL,0x1L)),(Def (Neg,0x180L,0x3328b944c4000L))) = (Def (Neg,0x0L,0x51dac207a000L))); *)

    (* "((Pos,0xd,0x1) * (Pos,0x180,0x5af3107a4000) = (Pos,0x0,0x9184e72a000))" >:: *)
    (* ((mul ~rm:Positive_inf,(Def (Pos,0xdL,0x1L)),(Def (Pos,0x180L,0x5af3107a4000L))) = (Def (Pos,0x0L,0x9184e72a000L))); *)

    (* "(Qnan * (-inf) = Qnan)" >:: *)
    (* ((mul ~rm:Negative_inf,Qnan,(Inf Neg)) = Qnan); *)

    (* "(inf * inf = inf)" >:: *)
    (* ((mul ~rm:Negative_inf,(Inf Pos),(Inf Pos)) = (Inf Pos)); *)

    (* "((-inf) * (-inf) = inf)" >:: *)
    (* ((mul ~rm:Negative_inf,(Inf Neg),(Inf Neg)) = (Inf Pos)); *)

    (* "((Pos,0x2e9,0x130a9955f87cf6) * (Pos,0x0,0x2) = (Pos,0x15c,0x3ceeb779818fe))" >:: *)
    (* ((mul ~rm:Negative_inf,(Def (Pos,0x2e9L,0x130a9955f87cf6L)),(Def (Pos,0x0L,0x2L))) = (Def (Pos,0x15cL,0x3ceeb779818feL))); *)

    (* "((Pos,0xd,0x1) * (Pos,0x180,0x5af3107a4000) = (Pos,0x0,0x9184e72a000))" >:: *)
    (* ((mul ~rm:Negative_inf,(Def (Pos,0xdL,0x1L)),(Def (Pos,0x180L,0x5af3107a4000L))) = (Def (Pos,0x0L,0x9184e72a000L))); *)

    (* "(Qnan * (-inf) = Qnan)" >:: *)
    (* ((mul ~rm:Nearest_even,Qnan,(Inf Neg)) = Qnan); *)

    (* "(inf * inf = inf)" >:: *)
    (* ((mul ~rm:Nearest_even,(Inf Pos),(Inf Pos)) = (Inf Pos)); *)

    (* "((-inf) * (-inf) = inf)" >:: *)
    (* ((mul ~rm:Nearest_even,(Inf Neg),(Inf Neg)) = (Inf Pos)); *)

    (* "((-inf) * (Neg,0x105,0x1608081a304820) = inf)" >:: *)
    (* ((mul ~rm:Nearest_even,(Inf Neg),(Def (Neg,0x105L,0x1608081a304820L))) = (Inf Pos)); *)

    (* "((Neg,0x1ef,0x1fffffffffffbd) * (-inf) = inf)" >:: *)
    (* ((mul ~rm:Nearest_even,(Def (Neg,0x1efL,0x1fffffffffffbdL)),(Inf Neg)) = (Inf Pos)); *)

    (* "((Pos,0x2e9,0x130a9955f87cf6) * (Pos,0x0,0x2) = (Pos,0x15c,0x3ceeb779818fe))" >:: *)
    (* ((mul ~rm:Nearest_even,(Def (Pos,0x2e9L,0x130a9955f87cf6L)),(Def (Pos,0x0L,0x2L))) = (Def (Pos,0x15cL,0x3ceeb779818feL))); *)

    (* "((Pos,0x22c,0x86aa80268140) * (Pos,0x0,0x8) = (Pos,0x9e,0x4355401340a00))" >:: *)
    (* ((mul ~rm:Nearest_even,(Def (Pos,0x22cL,0x86aa80268140L)),(Def (Pos,0x0L,0x8L))) = (Def (Pos,0x9eL,0x4355401340a00L))); *)

    (* "((Pos,0x200,0x202010) * (Pos,0x0,0x100000200) = (Pos,0x72,0x20201040402000))" >:: *)
    (* ((mul ~rm:Nearest_even,(Def (Pos,0x200L,0x202010L)),(Def (Pos,0x0L,0x100000200L))) = (Def (Pos,0x72L,0x20201040402000L))); *)

    (* "((Pos,0xd,0x1) * (Pos,0x180,0x5af3107a4000) = (Pos,0x0,0x9184e72a000))" >:: *)
    (* ((mul ~rm:Nearest_even,(Def (Pos,0xdL,0x1L)),(Def (Pos,0x180L,0x5af3107a4000L))) = (Def (Pos,0x0L,0x9184e72a000L))); *)

    (* "((Pos,0x0,0x1) * (Neg,0x1a3,0x1ef9e1dfcdf74f) = (Neg,0x15,0x1ef9e1dfcdf74f))" >:: *)
    (* ((mul ~rm:Nearest_even,(Def (Pos,0x0L,0x1L)),(Def (Neg,0x1a3L,0x1ef9e1dfcdf74fL))) = (Def (Neg,0x15L,0x1ef9e1dfcdf74fL))); *)

    (* "(Qnan / Qnan = Qnan)" >:: *)
    (* ((div ~rm:Nearest_away,Qnan,Qnan) = Qnan); *)

    (* "(inf / Qnan = Qnan)" >:: *)
    (* ((div ~rm:Nearest_away,(Inf Pos),Qnan) = Qnan); *)

    (* "(inf / (Neg,0x18e,0x0) = (-inf))" >:: *)
    (* ((div ~rm:Nearest_away,(Inf Pos),(Def (Neg,0x18eL,0x0L))) = (Inf Neg)); *)

    (* "(inf / (Pos,0x18e,0x0) = inf)" >:: *)
    (* ((div ~rm:Nearest_away,(Inf Pos),(Def (Pos,0x18eL,0x0L))) = (Inf Pos)); *)

    (* "((Neg,0x18e,0x0) / Qnan = Qnan)" >:: *)
    (* ((div ~rm:Nearest_away,(Def (Neg,0x18eL,0x0L)),Qnan) = Qnan); *)

    (* "((Neg,0x18e,0x0) / inf = (Neg,0x0,0x0))" >:: *)
    (* ((div ~rm:Nearest_away,(Def (Neg,0x18eL,0x0L)),(Inf Pos)) = (Def (Neg,0x0L,0x0L))); *)

    (* "(Qnan / Qnan = Qnan)" >:: *)
    (* ((div ~rm:Towards_zero,Qnan,Qnan) = Qnan); *)

    (* "(inf / Qnan = Qnan)" >:: *)
    (* ((div ~rm:Towards_zero,(Inf Pos),Qnan) = Qnan); *)

    (* "(inf / (Neg,0x18e,0x0) = (-inf))" >:: *)
    (* ((div ~rm:Towards_zero,(Inf Pos),(Def (Neg,0x18eL,0x0L))) = (Inf Neg)); *)

    (* "(inf / (Pos,0x18e,0x0) = inf)" >:: *)
    (* ((div ~rm:Towards_zero,(Inf Pos),(Def (Pos,0x18eL,0x0L))) = (Inf Pos)); *)

    (* "((Neg,0x18e,0x0) / Qnan = Qnan)" >:: *)
    (* ((div ~rm:Towards_zero,(Def (Neg,0x18eL,0x0L)),Qnan) = Qnan); *)

    (* "((Neg,0x18e,0x0) / inf = (Neg,0x0,0x0))" >:: *)
    (* ((div ~rm:Towards_zero,(Def (Neg,0x18eL,0x0L)),(Inf Pos)) = (Def (Neg,0x0L,0x0L))); *)

    (* "(Qnan / Qnan = Qnan)" >:: *)
    (* ((div ~rm:Positive_inf,Qnan,Qnan) = Qnan); *)

    (* "(inf / Qnan = Qnan)" >:: *)
    (* ((div ~rm:Positive_inf,(Inf Pos),Qnan) = Qnan); *)

    (* "(inf / (Neg,0x18e,0x0) = (-inf))" >:: *)
    (* ((div ~rm:Positive_inf,(Inf Pos),(Def (Neg,0x18eL,0x0L))) = (Inf Neg)); *)

    (* "(inf / (Pos,0x18e,0x0) = inf)" >:: *)
    (* ((div ~rm:Positive_inf,(Inf Pos),(Def (Pos,0x18eL,0x0L))) = (Inf Pos)); *)

    (* "((Neg,0x18e,0x0) / Qnan = Qnan)" >:: *)
    (* ((div ~rm:Positive_inf,(Def (Neg,0x18eL,0x0L)),Qnan) = Qnan); *)

    (* "((Neg,0x18e,0x0) / inf = (Neg,0x0,0x0))" >:: *)
    (* ((div ~rm:Positive_inf,(Def (Neg,0x18eL,0x0L)),(Inf Pos)) = (Def (Neg,0x0L,0x0L))); *)

    (* "(Qnan / Qnan = Qnan)" >:: *)
    (* ((div ~rm:Negative_inf,Qnan,Qnan) = Qnan); *)

    (* "(inf / Qnan = Qnan)" >:: *)
    (* ((div ~rm:Negative_inf,(Inf Pos),Qnan) = Qnan); *)

    (* "(inf / (Neg,0x18e,0x0) = (-inf))" >:: *)
    (* ((div ~rm:Negative_inf,(Inf Pos),(Def (Neg,0x18eL,0x0L))) = (Inf Neg)); *)

    (* "(inf / (Pos,0x18e,0x0) = inf)" >:: *)
    (* ((div ~rm:Negative_inf,(Inf Pos),(Def (Pos,0x18eL,0x0L))) = (Inf Pos)); *)

    (* "((Neg,0x18e,0x0) / Qnan = Qnan)" >:: *)
    (* ((div ~rm:Negative_inf,(Def (Neg,0x18eL,0x0L)),Qnan) = Qnan); *)

    (* "((Neg,0x18e,0x0) / inf = (Neg,0x0,0x0))" >:: *)
    (* ((div ~rm:Negative_inf,(Def (Neg,0x18eL,0x0L)),(Inf Pos)) = (Def (Neg,0x0L,0x0L))); *)

    (* "(Qnan / Qnan = Qnan)" >:: *)
    (* ((div ~rm:Nearest_even,Qnan,Qnan) = Qnan); *)

    (* "(inf / Qnan = Qnan)" >:: *)
    (* ((div ~rm:Nearest_even,(Inf Pos),Qnan) = Qnan); *)

    (* "(inf / (Neg,0x18e,0x0) = (-inf))" >:: *)
    (* ((div ~rm:Nearest_even,(Inf Pos),(Def (Neg,0x18eL,0x0L))) = (Inf Neg)); *)

    (* "(inf / (Pos,0x18e,0x0) = inf)" >:: *)
    (* ((div ~rm:Nearest_even,(Inf Pos),(Def (Pos,0x18eL,0x0L))) = (Inf Pos)); *)

    (* "((Neg,0x0,0xfc01ddfd386feeff) / (Neg,0x0,0xfc01747ddffbbaeb) = (Neg,0x0,0xfc01ddfd386feeff))" >:: *)
    (* ((div ~rm:Nearest_even,(Def (Neg,0x0L,0xfc01ddfd386feeffL)),(Def (Neg,0x0L,0xfc01747ddffbbaebL))) = (Def (Neg,0x0L,0xfc01ddfd386feeffL))); *)

    (* "((-inf) / (Pos,0x1,0xc04142292d400) = (-inf))" >:: *)
    (* ((div ~rm:Nearest_even,(Inf Neg),(Def (Pos,0x1L,0xc04142292d400L))) = (Inf Neg)); *)

    (* "((Pos,0x59,0x236ee11abc0476) / (Pos,0x0,0x1) = (Pos,0x1e7,0x236ee11abc0476))" >:: *)
    (* ((div ~rm:Nearest_even,(Def (Pos,0x59L,0x236ee11abc0476L)),(Def (Pos,0x0L,0x1L))) = (Def (Pos,0x1e7L,0x236ee11abc0476L))); *)

    (* "((Pos,0x2fe,0x0) / (-inf) = (Neg,0x0,0x0))" >:: *)
    (* ((div ~rm:Nearest_even,(Def (Pos,0x2feL,0x0L)),(Inf Neg)) = (Def (Neg,0x0L,0x0L))); *)

    (* "((Pos,0x2fe,0x0) / inf = (Pos,0x0,0x0))" >:: *)
    (* ((div ~rm:Nearest_even,(Def (Pos,0x2feL,0x0L)),(Inf Pos)) = (Def (Pos,0x0L,0x0L))); *)

    (* "((Pos,0x17c,0x1cf28d6eaaebcc) / (-inf) = (Neg,0x0,0x0))" >:: *)
    (* ((div ~rm:Nearest_even,(Def (Pos,0x17cL,0x1cf28d6eaaebccL)),(Inf Neg)) = (Def (Neg,0x0L,0x0L))); *)

    (* "((Pos,0x120,0x8100) / (Pos,0x0,0x20) = (Pos,0x2ae,0x408))" >:: *)
    (* ((div ~rm:Nearest_even,(Def (Pos,0x120L,0x8100L)),(Def (Pos,0x0L,0x20L))) = (Def (Pos,0x2aeL,0x408L))); *)

    (* "((Pos,0x100,0x18024302120800) / (Pos,0x0,0x8000) = (Pos,0x28a,0x753b0b301c0b1))" >:: *)
    (* ((div ~rm:Nearest_even,(Def (Pos,0x100L,0x18024302120800L)),(Def (Pos,0x0L,0x8000L))) = (Def (Pos,0x28aL,0x753b0b301c0b1L))); *)

    (* "((Neg,0x18e,0x0) / Qnan = Qnan)" >:: *)
    (* ((div ~rm:Nearest_even,(Def (Neg,0x18eL,0x0L)),Qnan) = Qnan); *)

    (* "((Neg,0x18e,0x0) / inf = (Neg,0x0,0x0))" >:: *)
    (* ((div ~rm:Nearest_even,(Def (Neg,0x18eL,0x0L)),(Inf Pos)) = (Def (Neg,0x0L,0x0L))); *)

    (* "((Pos,0x10,0x6060800800) / (Pos,0x0,0x4000) = (Pos,0x19b,0x5e1e3d07d))" >:: *)
    (* ((div ~rm:Nearest_even,(Def (Pos,0x10L,0x6060800800L)),(Def (Pos,0x0L,0x4000L))) = (Def (Pos,0x19bL,0x5e1e3d07dL))); *)

    (* "((Pos,0xc,0x400000000000) / (Pos,0x0,0x1000000000000) = (Pos,0x198,0x19))" >:: *)
    (* ((div ~rm:Nearest_even,(Def (Pos,0xcL,0x400000000000L)),(Def (Pos,0x0L,0x1000000000000L))) = (Def (Pos,0x198L,0x19L))); *)

    (* "((Pos,0x0,0x282) / (Pos,0x40,0xa) = (Pos,0x14d,0x282))" >:: *)
    (* ((div ~rm:Nearest_even,(Def (Pos,0x0L,0x282L)),(Def (Pos,0x40L,0xaL))) = (Def (Pos,0x14dL,0x282L))); *)

    (* "((Pos,0x0,0x4) / (Pos,0x2,0x400) = (Pos,0x184,0x5f5e1))" >:: *)
    (* ((div ~rm:Nearest_even,(Def (Pos,0x0L,0x4L)),(Def (Pos,0x2L,0x400L))) = (Def (Pos,0x184L,0x5f5e1L))); *)

  ]

let () = run_test_tt_main (suite ())
