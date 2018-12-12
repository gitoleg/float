open Core_kernel
open Bap.Std

open Bap_knowledge
open Bap_core_theory

type rounding =
  | Nearest_even  (** round to nearest, ties to even *)
  | Nearest_away  (** round to nearest, ties to away *)
  | Towards_zero  (** round toward zero              *)
  | Positive_inf  (** round toward positive infinity *)
  | Negative_inf  (** round toward negative infinity *)
[@@deriving sexp]

type 'a t = 'a knowledge

type ('b, 'e, 't, 's) binop =
  ((('b,'e,'t) IEEE754.t,'s) format float sort ->
   rmode value t -> 's bitv value t -> 's bitv value t -> 's bitv value t)


module Rounding = struct
  open Knowledge.Syntax

  module Rounding_domain = struct
    open Domain.Order

    type t = rounding option

    let empty = None

    let partial x y : Domain.Order.partial = match x,y with
      | None,None -> EQ
      | None,_ -> LE
      | _,None -> GE
      | _ -> NC

    let inspect t = failwith "unimplemented"
  end

  let rounding = Semantics.declare ~name:"rounding" (module Rounding_domain)

  module T = struct
    let make t =
      !! (Value.put rounding (Value.empty Rmode.t) (Some t))

    let rne = make Nearest_even
    let rna = make Nearest_away
    let rtp = make Towards_zero
    let rtn = make Positive_inf
    let rtz = make Negative_inf
  end

  let get rm =
    rm >>= fun r ->
    match Value.get rounding r with
    | None -> !! None
    | Some r -> !! (Some r)
end

module Make(B : Theory.Basic) = struct

  include Rounding.T

  open Knowledge.Syntax

  module B = struct
    include B

    let one s = succ (zero s)
    let ones s = B.(not (zero s))

    let is_one x =
      x >>= fun v ->
      let y = one (Value.sort v) in
      eq x y

    let is_all_ones x =
      x >>= fun v ->
      let y = ones (Value.sort v) in
      eq x y

    let of_int sort v =
      int sort
        (Word.of_int ~width:(Bits.size sort) v)

    let is_negative = B.msb
    let is_positive x = B.inv (B.msb x)
    let is_non_negative x = B.or_ (is_positive x) (B.is_zero x)

    let zero_extend x upto = B.unsigned upto x
    let sign_extend x upto = B.signed upto x

    let abs x = ite (is_negative x) (neg x) x

    let of_bool = function
      | true -> b1
      | false -> b0

    let if_ cond ~then_ ~else_ = ite cond then_ else_

    module Infix = struct
      let ( + ) = add
      let ( - ) = sub
      let ( * ) = mul
      let ( / ) = div
      let ( /$ ) = sdiv
      let ( = ) = eq
      let ( <> ) = neq
      let ( < ) = ult
      let ( > ) = ugt
      let ( <= ) = ule
      let ( >= ) = uge
      let ( <$ ) = slt
      let ( >$ ) = sgt
      let ( <=$ ) = sle
      let ( >=$ ) = sge
      let ( lsr ) = rshift
      let ( lsl ) = lshift
      let ( land ) = logand
      let ( lor ) = logor
      let ( lxor ) = logxor
    end

    include Infix

    let max x y = ite (x >$ y) x y
    let min x y = ite (x <$ y) x y
    let umin x y = ite (x < y) x y
  end

  module Lost = struct
    let alot s = B.of_int s 0b11
    let half s = B.of_int s 0b10
    let zero s = B.of_int s 0b00
    let afew s = B.of_int s 0b01
    let bits s = B.of_int s 2
  end

  type 'a t = 'a knowledge

  let sort x = x >>= fun x -> !! (Value.sort x)
  let size x = sort x >>= fun s -> !! (Bits.size s)
  let sema x = x >>= fun x -> !! (Value.semantics x)
  let empty dom sort x = !! (Value.put dom (Value.empty sort) x)

  let bind a body =
    a >>= fun a ->
    sort !!a >>= fun s ->
    Var.Generator.fresh s >>= fun v ->
    B.let_ v !!a (body (B.var v))

  let (>=>) = bind

  let bind2 a b body =
    bind a @@ fun a ->
    bind b @@ fun b ->
    body a b

  let bind3 a b c body =
    bind a @@ fun a ->
    bind b @@ fun b ->
    bind c @@ fun c ->
    body a b c

  let bind4 a b c d body =
    bind a @@ fun a ->
    bind b @@ fun b ->
    bind c @@ fun c ->
    bind d @@ fun d ->
    body a b c d

  let floats fsort =
    let open IEEE754 in
    let exps = Sort.exps fsort in
    let spec = Sort.spec fsort in
    let sigs = Bits.define spec.p in
    exps, sigs

  let fsign = B.msb

  let exponent fsort bitv =
    let open IEEE754 in
    let bits = Sort.bits fsort in
    let exps = Sort.exps fsort in
    let spec = Sort.spec fsort in
    let shift = B.of_int bits spec.t in
    B.low exps B.(bitv lsr shift)

  let significand fsort expn bitv =
    let open IEEE754 in
    let spec = Sort.spec fsort in
    let coef = B.low (Sort.sigs fsort) bitv in
    if spec.t = spec.p then coef
    else
      let sigs' = Bits.define spec.p in
      let bit = Bits.define 1 in
      let leading_bit = B.(ite (is_zero expn) (zero bit) (one bit)) in
      B.append sigs' leading_bit coef

  let pack fsort sign expn coef =
    let open B in
    let open IEEE754 in
    let bits = Sort.bits fsort in
    let bit = Bits.define 1 in
    let spec = Sort.spec fsort in
    let coef =
      if Caml.(spec.p = spec.t) then coef
      else B.low (Sort.sigs fsort) coef in
    let bits_1 = Bits.define Caml.(Bits.size bits - 1) in
    let sign = ite sign (B.one bit) (B.zero bit) in
    B.append bits sign (B.append bits_1 expn coef)

  let unpack fsort x f =
    exponent fsort x >=> fun expn ->
    significand fsort expn x >=> fun coef ->
    f (fsign x) expn coef

  let is_inf fsort x =
    unpack fsort x @@ fun _ expn coef ->
    B.(and_ (is_zero coef) (is_all_ones expn))

  let is_nan fsort x =
    unpack fsort x @@ fun _ expn coef ->
    B.(and_ (non_zero coef) (is_all_ones expn))

  let is_special fsort x = B.or_ (is_nan fsort x) (is_inf fsort x)
  let is_finite fsort x = B.inv (is_special fsort x)

  let match_ cases ~default =
    let cases = List.rev cases in
    List.fold cases ~init:default
      ~f:(fun fin (cond, ok) -> B.ite cond ok fin)

  let (-->) x y = x,y

  let extract_last x n =
    let open B in
    sort x >>= fun sort ->
    x >>= fun v ->
    let mask = not (ones sort lsl n)  in
    x land mask

  let rshift_coef coef n =
    B.(coef lsr n), extract_last coef n

  let half_of_loss loss lost_bits =
    let open B in
    loss >>= fun vloss ->
    let vsort = Value.sort vloss in
    let x = one vsort in
    let n = pred lost_bits in
    x lsl n

  (* TODO: consider to add expn here and if all ones - adjust it  *)
  let round rm sign coef loss lost_bits =
    let open Rmode in
    let open B in
    Rounding.get rm >>= fun rm ->
    sort coef >>= fun sigs ->
    let loss = extract_last loss lost_bits in
    let half = half_of_loss loss lost_bits in
    let is_needed = match rm with
      | Some Positive_inf -> B.inv sign
      | Some Negative_inf -> sign
      | Some Nearest_away -> loss >= half
      | Some Nearest_even ->
        if_ (loss > half) ~then_:b1
          ~else_:(
            if_ (loss = half) ~then_:(lsb coef)
              ~else_:b0)
      | _ -> b0 in
    let is_needed = and_ (non_zero lost_bits) is_needed in
    let all_ones = not (zero sigs) in
    if_ (and_ (coef <> all_ones) is_needed)
      ~then_:(succ coef)
      ~else_:coef

  (* [align_right base precision expn frac] shifts fraction right to fit
     into [precision] with a possible loss of bits in order to keep
     most significant bits. Returns [Some (expn, frac, loss)], if
     no exponent overflow occured, [None] otherwise. *)
  let align_right expn coef =
    coef >>| fun vcoef ->
    let vsort = Value.sort vcoef in
    let prec = Bits.size (Value.sort vcoef) in
    let zero = B.(zero vsort) in
    let unos = B.(one vsort) in
    let rec loop i num coef =
      if i < prec then
        let lsb = B.lsb coef in
        let num'  = B.ite lsb num (B.succ num) in
        let frac' = B.ite lsb coef B.(coef lsr unos) in
        loop (i + 1) num' frac'
      else coef, num in
    let frac', num = loop 0 zero coef in
    let loss = extract_last coef num in
    B.(expn + num), frac', loss

  (* maximum possible exponent that fits in [n - 1] bits. (one for sign) *)
  let max_exponent' n = int_of_float (2.0 ** (float_of_int n )) - 2
  let min_exponent' n = 0
  let max_exponent  n = B.of_int n (Bits.size n |> max_exponent')
  let min_exponent  n = B.of_int n (Bits.size n |> min_exponent')

  (* returns pow of 2 nearest to n and 2 in that power *)
  let nearest_pow2 num =
    let rec find pow n =
      let n' = 2 * n in
      if n' >= num then pow + 1, n'
      else find (pow + 1) n' in
    find 0 1

  let clz x =
    sort x >>= fun sort ->
    size x >>= fun size ->
    let pow, num = nearest_pow2 size in
    let sort' = Bits.define num in
    let shifts = List.init pow ~f:(fun p -> num / (2 lsl p)) in
    let shifts,_ =
      List.fold shifts ~init:([],0)
        ~f:(fun (acc,prev) curr ->
            let total = curr + prev in
            (total, curr) :: acc, total) in
    let shifts = List.rev shifts in
    let x' = B.unsigned sort' x in
    let rec loop lets x = function
      | [] -> List.fold lets ~f:B.(+) ~init:(B.zero sort)
      | (total, shift) :: shifts ->
        let shift = B.of_int sort shift in
        let total = B.of_int sort total in
        let mask = B.(ones sort' lsl total) in
        let nextx = B.(ite (is_zero (x land mask)) (x lsl shift) x) in
        let nextn = B.(ite (is_zero (x land mask)) shift (B.zero sort)) in
        bind nextx @@ fun nextx ->
        bind nextn @@ fun nextn ->
        loop (nextn :: lets) nextx shifts in
    let n = loop [] x' shifts in
    let dif = B.of_int sort (num - size) in
    B.ite (B.is_zero x) (B.of_int sort size) B.(n - dif)

  let possible_lshift expn coef =
    let open B in
    sort expn >>= fun exps ->
    sort coef >>= fun sigs ->
    let min_expn = min_exponent exps in
    clz coef >=> fun clz ->
    umin clz (unsigned sigs (abs (expn - min_expn)))

  (* TODO: consider test coef for zero to prevent expn change *)
  let safe_align_left expn coef =
    let open B in
    sort expn >>= fun exps ->
    sort coef >>= fun sigs ->
    let shift = possible_lshift expn coef in
    let dexpn = unsigned exps shift in
    let coef = coef lsl shift in
    let expn = expn - dexpn in
    !! (expn,coef)

  let msbn x =
    let open B in
    sort x >>= fun sort ->
    size x >>= fun prec ->
    bind (clz x) (fun clz ->
        of_int sort prec - clz - one sort)

  (* min exponent without bit loss or exponent overflow,
     fraction shifted as left as possible, i.e. it occupies
     more significant bits *)
  let minimize_exponent = safe_align_left
  let norm = safe_align_left

  let prec x = Bits.size (Value.sort x)

  (* returns result sign *)
  let xor_sign s s' = B.(and_ (or_ s s') (inv (and_ s s')))

  (* TODO: consider other version *)
  let combine_loss more less =
    more >>= fun vmore ->
    less >>= fun vless ->
    let smore = Value.sort vmore in
    let sless = Value.sort vless in
    let size = Bits.size smore + Bits.size sless in
    let sort' = Bits.define size in
    B.concat sort' [more; less]

  let fadd fsort rm x y =
    let open B in
    let exps,sigs = floats fsort in
    unpack fsort x @@ fun sign xexpn xcoef ->
    unpack fsort y @@ fun _ yexpn ycoef ->
    let lost_bits = abs (xexpn - yexpn) in
    ite (xexpn > yexpn) xcoef (xcoef lsr lost_bits) >=> fun xcoef ->
    ite (yexpn > xexpn) ycoef (ycoef lsr lost_bits) >=> fun ycoef ->
    xcoef + ycoef >=> fun coef ->
    max xexpn yexpn >=> fun expn ->
    ite (coef >= xcoef) expn (succ expn) >=> fun expn ->
    match_ [
          (xexpn = yexpn) --> zero sigs;
          (xexpn > yexpn) --> extract_last ycoef lost_bits;
      ] ~default:(extract_last xcoef lost_bits) >=> fun loss ->
    ite (coef >= xcoef) (round rm sign coef loss lost_bits)
        (combine_loss (extract_last coef (one sigs)) loss >=> fun loss ->
         coef lsr one sigs >=> fun coef ->
         one sigs lsl (of_int sigs Caml.(Bits.size sigs - 1)) >=> fun lead_one ->
         coef lor lead_one >=> fun coef ->
         round rm sign coef loss (succ lost_bits)) >=> fun coef ->
    norm expn coef >>= fun (expn,coef) ->
    pack fsort sign expn coef

  let extend bitv ~addend  =
    sort bitv >>= fun sort ->
    let sort' = Bits.define (Bits.size sort + addend) in
    B.unsigned sort' bitv

  let invert_loss loss lost_bits =
    let open B in
    sort loss >>= fun sort ->
    let half = half_of_loss loss lost_bits in
    let inverted =
      let mask = not (ones sort lsl lost_bits) in
      mask land (not loss) in
    match_ [
        is_zero lost_bits --> zero sort;
        is_zero loss --> loss;
        (loss = half) --> loss;
      ] ~default:inverted

  (** [combine_loss more_significant less_significant length_of_less ] *)
  let combine_loss more less length_of_less =
    let more = B.(more lsl length_of_less) in
    B.(more lor less)

  let match_cmp x y ~on_eql ~on_gt ~on_lt =
    let open B in
    match_ [
      (x =  y) --> on_eql;
      (x >$ y) --> on_gt;
    ] ~default:on_lt

  let fsub fsort rm x y =
    let open B in
    let exps,sigs = floats fsort in
    let min_expn = min_exponent exps in
    unpack fsort x @@ fun xsign xexpn xcoef ->
    unpack fsort y @@ fun _     yexpn ycoef ->
    extend xcoef ~addend:1 >=> fun xcoef ->
    extend ycoef ~addend:1 >=> fun ycoef ->
    sort xcoef >>= fun sigs' ->
    abs (xexpn - yexpn) >=> fun diff ->
    ite (is_zero diff) diff (diff - one exps) >=> fun lost_bits ->
    match_ [
        (xexpn > yexpn) --> extract_last ycoef lost_bits;
        (xexpn < yexpn) --> extract_last xcoef lost_bits;
      ] ~default:(zero sigs') >=> fun loss ->
    invert_loss loss lost_bits >=> fun loss ->
    or_ (xexpn < yexpn) (and_ (xexpn = yexpn) (xcoef < ycoef)) >=> fun swap ->
    ite swap (inv xsign) xsign >=> fun sign ->
    match_ [
        (xexpn > yexpn) --> xcoef lsl one sigs';
        (xexpn < yexpn) --> xcoef lsr lost_bits;
      ] ~default:xcoef >=> fun xcoef ->
    match_ [
        (yexpn > xexpn) --> ycoef lsl one sigs';
        (yexpn < xexpn) --> ycoef lsr lost_bits;
      ] ~default:ycoef >=> fun ycoef ->
    ite (is_zero loss) (zero sigs') (one sigs') >=> fun borrow ->
    ite swap (ycoef - xcoef - borrow) (xcoef - ycoef - borrow) >=> fun coef ->
    msb coef >=> fun msbc ->
    max xexpn yexpn >=> fun expn ->
    ite (xexpn = yexpn) expn (expn - one exps) >=> fun expn ->
    ite (is_zero coef) min_expn (ite msbc (succ expn) expn) >=> fun expn ->
    ite msbc (extract_last coef (one sigs')) (zero sigs') >=> fun loss' ->
    ite msbc (combine_loss loss' loss lost_bits) loss >=> fun loss ->
    ite msbc (succ lost_bits) lost_bits >=> fun lost_bits ->
    ite msbc (coef lsr one sigs') coef >=> fun coef ->
    unsigned sigs coef >=> fun coef ->
    round rm sign coef loss lost_bits >=> fun coef ->
    norm expn coef >>= fun (expn,coef) ->
    pack fsort sign expn coef

    (* let lost_bits = bind (abs (xexpn - yexpn)) @@ fun diff ->
     *   ite (is_zero diff) diff (diff - one exps) in
     * let loss =
     *   bind3 xcoef ycoef lost_bits @@ fun xcoef ycoef lost_bits ->
     *   match_expn ~on_eql:(zero sigs')
     *     ~on_xgt:(extract_last ycoef lost_bits)
     *     ~on_ygt:(extract_last xcoef lost_bits) >=> fun loss ->
     *   invert_loss loss lost_bits in
     * let swap = match_expn ~on_eql:(xcoef < ycoef) ~on_xgt:b0 ~on_ygt:b1 in
     * let sign = ite swap (inv xsign) xsign in
     * let coef =
     *   bind4 xcoef ycoef loss lost_bits @@ fun xcoef ycoef loss lost_bits ->
     *   match_expn ~on_eql:xcoef
     *     ~on_xgt:(xcoef lsl one sigs') ~on_ygt:(xcoef lsr lost_bits) >=> fun xcoef ->
     *   match_expn ~on_eql:ycoef
     *     ~on_xgt:(ycoef lsr lost_bits) ~on_ygt:(ycoef lsl one sigs') >=> fun ycoef ->
     *   ite (is_zero loss) (zero sigs') (one sigs') >=> fun borrow ->
     *   ite swap (ycoef - xcoef - borrow) (xcoef - ycoef - borrow) in
     * let expn =
     *   bind3 (msb coef) xexpn yexpn @@ fun msb xexpn yexpn ->
     *   max xexpn yexpn >=> fun max ->
     *   min_exponent exps >=> fun min ->
     *   ite (xexpn = yexpn) xexpn (max - one exps) >=> fun expn ->
     *   ite (is_zero coef) min (ite msb (succ expn) expn) in
     * let coef = bind3 coef loss lost_bits @@ fun coef loss lost_bits ->
     *   msb coef >=> fun msb ->
     *   ite msb (extract_last coef (one sigs')) (zero sigs') >=> fun loss' ->
     *   ite msb (combine_loss loss' loss lost_bits) loss >=> fun loss ->
     *   ite msb (succ lost_bits) lost_bits >=> fun lost_bits ->
     *   ite msb (coef lsr one sigs') coef >=> fun coef ->
     *   unsigned sigs coef >=> fun coef ->
     *   round rm sign coef loss lost_bits in
     * with' x ~expn ~coef ~sign >>= fun x ->
     * minimize_exponent !!x *)

  (* let add_or_sub ~is_sub rm x y =
   *   let ( lxor ) = xor_sign in
   *   let s1 = if is_sub then B.b1 else B.b0 in
   *   let s2 = fsign x in
   *   let s3 = fsign y in
   *   let is_sub = s1 lxor (s2 lxor s3) in
   *   B.ite is_sub (fsub rm x y) (fadd rm x y) *)

  (* let fsub = add_or_sub ~is_sub:true
   * let fadd = add_or_sub ~is_sub:false *)

  (* let double s = Bits.define ((Bits.size s) * 2)
   *
   * let fmul rm x y =
   *   let open B in
   *   sort x >>= fun fsort ->
   *   precision x >>= fun coef_bits ->
   *   x >>> fun exps' sigs' ->
   *   let exps = double exps' in
   *   let sigs = double sigs' in
   *   let min_expn = signed exps (min_exponent exps') in
   *   let max_expn = signed exps (max_exponent sigs') in
   *   let xsign, xexpn, xcoef = data x in
   *   let ysign, yexpn, ycoef = data y in
   *   let expn = signed exps xexpn + signed exps yexpn in
   *   let coef = unsigned sigs xcoef * unsigned sigs ycoef in
   *   let sign = xor_sign xsign ysign in
   *   let clz  = clz coef in
   *   let prec  = of_int sigs coef_bits in
   *   let shift = ite (clz >= prec) (zero sigs) (prec - clz) in
   *   let dexpn = ite (expn <$ min_expn) (abs expn - abs min_expn) (zero exps) in
   *   let shift = shift + unsigned sigs dexpn in
   *   let dexpn' = unsigned exps shift + dexpn in
   *   let expn = expn + dexpn' in
   *   let coef =
   *     extract_last coef shift >=> fun loss ->
   *     coef lsr shift >=> fun coef ->
   *     round rm sign coef loss shift >=> fun coef ->
   *     ite (expn <$ min_expn) (zero sigs) coef >=> fun coef ->
   *     unsigned sigs' coef in
   *   let is_inf = expn >$ max_expn in
   *   let expn =
   *     expn >=> fun expn ->
   *     ite (expn <$ min_expn) (zero exps) expn >=> fun expn ->
   *     unsigned exps' expn >=> fun expn ->
   *     min_exponent exps' >=> fun min ->
   *     ite (is_zero coef) min expn in
   *   with' x ~expn ~coef ~sign ~is_inf
   *
   * let mask_bit sort i =
   *   let uno = B.one sort in
   *   let shf = B.of_int sort i in
   *   B.(uno lsl shf)
   *
   * let fdiv rm x y =
   *   let open B in
   *   let extend z =
   *     z >>= fun z ->
   *     minimize_exponent !!z >>= fun z ->
   *     extend !!z ~addend:1 >>= fun z ->
   *     !! z in
   *   x >>> fun exps sigs ->
   *   let sign = xor_sign (fsign x) (fsign y) in
   *   let x' = extend x in
   *   let y' = extend y in
   *   sort (significand x') >>= fun sigs ->
   *   let rec loop i bits nomin denom =
   *     if Caml.(i < 0) then
   *       List.fold bits ~f:(lor) ~init:(zero sigs) >=> fun coef ->
   *       let loss = match_ [
   *           (nomin > denom) --> Lost.alot sigs;
   *           (nomin = denom) --> Lost.half sigs;
   *           (nomin = zero sigs) --> Lost.zero sigs;
   *        ] ~default:(Lost.afew sigs) in
   *       round rm sign coef loss (Lost.bits sigs)
   *     else
   *       let next_nomin = ite (nomin > denom) (nomin - denom) nomin in
   *       let bit = ite (nomin > denom) (mask_bit sigs i) (zero sigs) in
   *       let bits = bit :: bits in
   *       bind next_nomin (fun next_nomin ->
   *        loop Caml.(i - 1) bits (next_nomin lsl one sigs) denom) in
   *   let coef =
   *     precision x    >>= fun prec ->
   *     significand x' >=> fun nomin ->
   *     significand y' >=> fun denom ->
   *     ite (nomin < denom) (nomin lsl one sigs) nomin >=> fun nomin ->
   *     loop Caml.(prec - 1) [] nomin denom >=> fun coef ->
   *     unsigned sigs coef in
   *   let expn =
   *     precision   x >>= fun prec ->
   *     significand x' >=> fun nomin ->
   *     significand y' >=> fun denom ->
   *     ite (nomin < denom) (one exps) (zero exps) >=> fun dexpn' ->
   *     of_int sigs prec >=> fun prec ->
   *     prec - one sigs >=> fun dexpn ->
   *     exponent x' - exponent y' - dexpn' - low exps dexpn in
   *   with' x ~expn ~coef ~sign >>= fun x ->
   *   minimize_exponent !!x *)


end
