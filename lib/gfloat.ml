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

type ('b, 'e, 't, 's) unop =
  ((('b,'e,'t) IEEE754.t,'s) format float sort ->
   rmode value t -> 's bitv value t -> 's bitv value t)


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
    let make t = !! (Value.put rounding (Value.empty Rmode.t) (Some t))

    let rne = make Nearest_even
    let rna = make Nearest_away
    let rtp = make Towards_zero
    let rtn = make Positive_inf
    let rtz = make Negative_inf
  end

  let get rm =
    rm >>= fun r ->
    match Value.get rounding r with
    | None -> !! Nearest_even
    | Some r -> !! r
end

module Make(B : Theory.Basic) = struct

  include Rounding.T

  open Knowledge.Syntax

  module B = struct
    include B

    let one s = succ (zero s)
    let ones s = B.(not (zero s))

    let is_one x =
      x >>= fun v -> eq x (one (Value.sort v))

    let is_all_ones x =
      x >>= fun v -> eq x (ones (Value.sort v))

    let of_int sort v =
      int sort (Word.of_int ~width:(Bits.size sort) v)

    let is_negative = B.msb
    let is_positive x = B.inv (B.msb x)
    let is_non_negative x = B.or_ (is_positive x) (B.is_zero x)
    let abs x = ite (is_negative x) (neg x) x

    let of_bool = function
      | true -> b1
      | false -> b0

    module Infix = struct
      let ( + ) = add
      let ( - ) = sub
      let ( * ) = mul
      let ( / ) = div
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

    let max x y = ite (x > y) x y
    let min x y = ite (x < y) x y
    let smax x y = ite (x >$ y) x y
    let smin x y = ite (x <$ y) x y
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

  (* pre: input coef is already of t-bits length  *)
  let pack_raw fsort sign expn coef =
    let open B in
    let open IEEE754 in
    let bits = Sort.bits fsort in
    let bit  = Bits.define 1 in
    let bits_1 = Bits.define Caml.(Bits.size bits - 1) in
    let sign = ite sign (B.one bit) (B.zero bit) in
    B.append bits sign (B.append bits_1 expn coef)

  let pack fsort sign expn coef =
    let {IEEE754.p; t} = IEEE754.Sort.spec fsort in
    if p = t then pack_raw fsort sign expn coef
    else
      B.low (Bits.define t) coef >=> fun coef ->
      pack_raw fsort sign expn coef

  let raw_significand fsort bitv =
    let open IEEE754 in
    let spec = Sort.spec fsort in
    let sigs = Bits.define spec.t in
    B.low sigs bitv

  let finite_significand fsort expn bitv =
    let open IEEE754 in
    let spec = Sort.spec fsort in
    raw_significand fsort bitv >=> fun coef ->
    if spec.t = spec.p then coef
    else
      let sigs = Bits.define spec.p in
      let bit = Bits.define 1 in
      let leading_bit = B.(ite (is_zero expn) (zero bit) (one bit)) in
      B.append sigs leading_bit coef

  let unpack fsort x f =
    exponent fsort x >=> fun expn ->
    finite_significand fsort expn x >=> fun coef ->
    f (fsign x) expn coef

  let unpack_raw fsort x f =
    exponent fsort x >=> fun expn ->
    raw_significand fsort x >=> fun coef ->
    f (fsign x) expn coef

  let with_sign sign bitv =
    let open B in
    sort bitv >>= fun s ->
    let s' = Bits.define Caml.(Bits.size s - 1) in
    let bit = Bits.define 1 in
    ite sign ((append s (one bit) (zero s')) lor bitv)
      ((append s (zero bit) (ones s')) land bitv)

  let fzero fsort = B.zero (IEEE754.Sort.bits fsort)
  let fone fsort =
    let open IEEE754 in
    let {bias; t} = Sort.spec fsort in
    let expn = B.of_int (Sort.exps fsort) bias in
    let sigs = Bits.define t in
    pack_raw fsort B.b0 expn (B.zero sigs)

  let inf fsort sign =
    let open B in
    let open IEEE754 in
    let exps = Sort.exps fsort in
    let {p} = Sort.spec fsort in
    let sigs = Bits.define p in
    pack fsort sign (B.ones exps) (B.zero sigs)

  let is_inf fsort x =
    unpack fsort x @@ fun _ expn coef ->
    B.(and_ (is_zero coef) (is_all_ones expn))

  let is_pinf fsort x =
    is_inf fsort x >=> fun is_inf ->
    B.(and_ is_inf (inv (msb x)))

  let is_ninf fsort x =
    is_inf fsort x >=> fun is_inf ->
    B.(and_ is_inf (msb x))

  let is_qnan fsort x =
    let open B in
    let (&&) = and_ in
    unpack_raw fsort x @@ fun sign expn coef ->
    is_all_ones expn && non_zero coef && msb coef

  let is_snan fsort x =
    let open B in
    let (&&) = and_ in
    unpack_raw fsort x @@ fun sign expn coef ->
    is_all_ones expn && non_zero coef && inv (msb coef)

  let is_nan fsort x =
    let open B in
    let (&&) = and_ in
    unpack_raw fsort x @@ fun sign expn coef ->
    is_all_ones expn && non_zero coef

  let qnan fsort =
    let open B in
    let open IEEE754 in
    let exps = Sort.exps fsort in
    let spec = Sort.spec fsort in
    let sigs = Bits.define spec.t in
    not (ones sigs lsr one sigs) >=> fun coef ->
    pack_raw fsort B.b1 (ones exps) coef

  let snan fsort =
    let open B in
    let open IEEE754 in
    let exps = Sort.exps fsort in
    let spec = Sort.spec fsort in
    let sigs = Bits.define spec.t in
    pack_raw fsort B.b0 (ones exps) (B.one sigs)

  (* unset a leading bit in coef, no-checks for nan are performed *)
  let transform_to_signal fsort x =
    let open IEEE754 in
    let spec = Sort.spec fsort in
    let bits = Sort.bits fsort in
    let shift = B.of_int bits (spec.t - 1) in
    let mask = B.(not (one bits lsl shift)) in
    B.(x land mask)

  (* set a leading bit in coef, no-checks for nan are performed *)
  let transform_to_quite fsort x =
    let open IEEE754 in
    let spec = Sort.spec fsort in
    let bits = Sort.bits fsort in
    let shift = B.of_int bits (spec.t - 1) in
    let mask = B.(one bits lsl shift) in
    B.(x lor mask)

  let with_special fsort x f =
    let open B in
    let (&&) = and_ in
    unpack_raw fsort x @@ fun sign expn coef ->
    is_all_ones expn >=> fun is_special ->
    (is_special && is_zero coef) >=> fun is_inf ->
    (is_special && non_zero coef && inv (msb coef)) >=> fun is_snan ->
    (is_special && msb coef) >=> fun is_qnan ->
    f ~is_inf ~is_snan ~is_qnan

  let is_special fsort x = unpack fsort x @@ fun _ expn _ -> B.is_all_ones expn
  let is_finite fsort x = B.inv (is_special fsort x)

  let is_normal_expn e = B.(and_ (non_zero e) (inv (is_all_ones e)))
  let is_subnorm_expn e = B.is_zero e

  let is_norml fsort x = unpack fsort x @@ fun _ e _ -> is_normal_expn e
  let is_subnormal fsort x =
    unpack fsort x @@ fun _ e _ -> is_subnorm_expn e

  let is_zero x =
    let open B in
    sort x >>= fun s ->
    is_zero ((x lsl one s) lsr one s)

  let precision fsort = let {IEEE754.p} = IEEE754.Sort.spec fsort in p
  let bias fsort = let {IEEE754.bias} = IEEE754.Sort.spec fsort in bias

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

  let half_of_loss loss lost_bits =
    let open B in
    sort loss >>= fun vsort ->
    let x = one vsort in
    let n = ite (is_zero lost_bits) (zero vsort) (pred lost_bits) in
    x lsl n

  (* the result of rounding must be checked because in the corner case
     when input is 111...1 it could return 000..0, that means that
     exponent must be incremented and msb set to 1 *)
  let round rm sign coef loss lost_bits f =
    let open Rmode in
    let open B in
    Rounding.get rm >>= fun rm ->
    sort coef >>= fun sigs ->
    let loss = extract_last loss lost_bits in
    let half = half_of_loss loss lost_bits in
    let is_needed = match rm with
      | Positive_inf -> B.inv sign
      | Negative_inf -> sign
      | Nearest_away -> loss >= half
      | Nearest_even ->
         or_ (loss > half) (and_ (loss = half) (lsb coef))
      | Towards_zero -> b0 in
    let is_needed = and_ (non_zero lost_bits) is_needed in
    ite is_needed (succ coef) coef >=> fun coef' ->
    and_ (non_zero coef) (is_zero coef') >=> fun is_overflow ->
    f coef' is_overflow


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
    min clz (unsigned sigs (abs (expn - min_expn)))

  let norm expn coef =
    let open B in
    sort expn >>= fun exps ->
    sort coef >>= fun sigs ->
    let shift = possible_lshift expn coef in
    let dexpn = unsigned exps shift in
    let coef = coef lsl shift in
    let min_expn = min_exponent exps in
    let expn = ite (is_zero coef) min_expn (expn - dexpn) in
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
  let minimize_exponent = norm

  let xor s s' = B.(and_ (or_ s s') (inv (and_ s s')))

  (** [combine_loss more_significant less_significant length_of_less ] *)
  let combine_loss more less length_of_less =
    let more = B.(more lsl length_of_less) in
    B.(more lor less)

  (* TODO: handle rounding overflow *)
  let fadd_finite fsort rm x y =
    let open B in
    let exps,sigs = floats fsort in
    unpack fsort x @@ fun sign xexpn xcoef ->
    unpack fsort y @@ fun _ yexpn ycoef ->
    sort xexpn >>= fun xes ->
    sort xcoef >>= fun xec ->
    abs (xexpn - yexpn) >=> fun lost_bits ->
    ite (xexpn > yexpn) xcoef (xcoef lsr lost_bits) >=> fun xcoef ->
    ite (yexpn > xexpn) ycoef (ycoef lsr lost_bits) >=> fun ycoef ->
    xcoef + ycoef >=> fun coef ->
    max xexpn yexpn >=> fun expn ->
    ite (coef >= xcoef) expn (succ expn) >=> fun expn ->
    and_ (is_subnorm_expn xexpn) (is_subnorm_expn yexpn) >=> fun is_subn ->
    msb coef >=> fun msbc ->
    ite (and_ msbc is_subn) (succ expn) expn >=> fun expn ->
    match_ [
          (xexpn = yexpn) --> zero sigs;
          (xexpn > yexpn) --> extract_last ycoef lost_bits;
      ] ~default:(extract_last xcoef lost_bits) >=> fun loss ->
    extract_last coef (one sigs) >=> fun loss' ->
    coef < xcoef >=> fun coef_overflow ->
    ite coef_overflow (succ lost_bits) lost_bits >=> fun lost_bits ->
    ite coef_overflow (combine_loss loss' loss lost_bits) loss >=> fun loss ->
    ite coef_overflow (coef lsr one sigs) coef >=> fun coef ->
    one sigs lsl (of_int sigs Caml.(Bits.size sigs - 1)) >=> fun leading_one ->
    ite coef_overflow (coef lor leading_one) coef >=> fun coef ->
    round rm sign coef loss lost_bits @@ fun coef is_overflow ->
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

  let match_cmp x y ~on_eql ~on_gt ~on_lt =
    let open B in
    match_ [
      (x =  y) --> on_eql;
      (x >$ y) --> on_gt;
    ] ~default:on_lt

  (* TODO: handle rounding overflow *)
  let fsub_finite fsort rm x y =
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
    round rm sign coef loss lost_bits @@ fun coef is_overflow ->
    norm expn coef >>= fun (expn,coef) ->
    pack fsort sign expn coef

  let fsum_special fsort is_sub x y =
    let open B in
    let (&&) = and_ in
    let (||) = or_  in
    let not = inv in
    with_special fsort x @@ fun ~is_inf:xinf ~is_snan:xsnan ~is_qnan:xqnan ->
    with_special fsort y @@ fun ~is_inf:yinf ~is_snan:ysnan ~is_qnan:yqnan ->
    (xsnan || xqnan) >=> fun xnan ->
    (ysnan || yqnan) >=> fun ynan ->
    fsign x  >=> fun xsign ->
    fsign y  >=> fun ysign ->
    (xinf && yinf) >=> fun is_inf ->
       match_ [
       (is_sub && is_inf) --> qnan fsort;
       (xinf && yinf) --> x;
       (xnan && (not ynan)) --> transform_to_quite fsort x;
       (ynan && (not xnan)) --> transform_to_quite fsort y;
    ] ~default:(transform_to_quite fsort x)

  let add_or_sub ~is_sub fsort rm x y =
    let open B in
    let (&&) = and_ in
    let ( lxor ) = xor in
    let s1 = is_sub in
    let s2 = fsign x in
    let s3 = fsign y in
    let is_sub = s1 lxor (s2 lxor s3) in
    ite (is_finite fsort x && is_finite fsort y)
      (B.ite is_sub (fsub_finite fsort rm x y) (fadd_finite fsort rm x y))
      (fsum_special fsort is_sub x y)

  let fsub fsort rm x y = add_or_sub ~is_sub:B.b1 fsort rm x y
  let fadd fsort rm x y = add_or_sub ~is_sub:B.b0 fsort rm x y

  let double bitv =
    sort bitv >>= fun sort ->
    extend bitv ~addend:(Bits.size sort)

  let normalize_coef exps coef f =
    let open B in
    clz coef >=> fun clz ->
    coef lsl clz >=> fun coef ->
    unsigned exps clz >=> fun dexpn ->
    f coef dexpn

  (* TODO: handle rounding overflow *)
  let fmul_finite fsort rm x y =
    let open B in
    let double e c f =
      double e >=> fun e -> double c >=> fun c -> f e c in
    let exps,sigs = floats fsort in
    let maxe = max_exponent' (Bits.size exps) in
    unpack fsort x @@ fun xsign xexpn xcoef ->
    unpack fsort y @@ fun ysign yexpn ycoef ->
    (* normalize_coef exps xcoef @@ fun xcoef dexpnx ->
     * normalize_coef exps ycoef @@ fun ycoef dexpny ->
     * abs (dexpnx - dexpny) >=> fun de -> *)
    double xexpn xcoef @@ fun xexpn xcoef ->
    double yexpn ycoef @@ fun yexpn ycoef ->
    sort xexpn >>= fun exps' ->
    sort xcoef >>= fun sigs' ->
    xor xsign ysign >=> fun sign ->
    xcoef * ycoef >=> fun coef ->
    clz coef >=> fun clz ->
    of_int sigs' (precision fsort) >=> fun prec ->
    ite (clz >= prec) (zero sigs') (prec - clz) >=> fun shift ->
    xexpn + yexpn >=> fun expn ->
    of_int exps' (bias fsort) >=> fun bias ->
    ite (bias > expn) (bias - expn) (zero exps') >=> fun dexpn ->
    dexpn > unsigned exps' prec >=> fun is_underflow ->
    expn - bias + dexpn >=> fun expn ->
    shift + unsigned sigs' dexpn >=> fun shift ->
    expn > of_int exps' maxe >=> fun is_overflow ->
    match_ [
       is_underflow --> fzero fsort;
       is_overflow  --> inf fsort sign;
      ] ~default:
       begin
         extract_last coef shift >=> fun loss ->
         coef lsr shift >=> fun coef ->
         round rm sign coef loss shift @@ fun coef is_overflow ->
         low sigs coef >=> fun coef ->
         low exps expn >=> fun expn ->
         min_exponent exps >=> fun min ->
         norm expn coef >>= fun (expn,coef) ->
         pack fsort sign expn coef
       end

  let fmul_special fsort x y =
    let open B in
    let (&&) = and_ in
    let (||) = or_  in
    with_special fsort x @@ fun ~is_inf:xinf ~is_snan:xsnan ~is_qnan:xqnan ->
    with_special fsort y @@ fun ~is_inf:yinf ~is_snan:ysnan ~is_qnan:yqnan ->
    fsign x >=> fun xsign ->
    fsign y >=> fun ysign ->
    (xinf && yinf) >=> fun is_inf ->
    match_ [
      (is_zero x && yinf) --> qnan fsort;
      (is_zero y && xinf) --> qnan fsort;
      is_inf --> with_sign (xor xsign ysign) x;
      (xsnan || xqnan) --> transform_to_quite fsort x
    ] ~default:(transform_to_quite fsort y)

  let fmul fsort rm x y =
    let (&&) = B.and_ in
    B.ite (is_finite fsort x && is_finite fsort y)
      (fmul_finite fsort rm x y)
      (fmul_special fsort x y)

  let mask_bit sort i =
    let uno = B.one sort in
    let shf = B.of_int sort i in
    B.(uno lsl shf)

  (* pre: nominator > denominator
     the msb of result can be 1 only (and only) in rare
     case of applying rounding to 01111..11. And we need to
     to check msb manually, since rounding itself
     will no help us.  *)
  let long_division prec rm sign nomin denom =
    let open B in
    sort nomin >>= fun sort ->
    let rec loop i bits nomin =
      if Caml.(i < 0) then
        List.fold bits ~f:(lor) ~init:(zero sort) >=> fun coef ->
        match_ [
            (nomin > denom) --> Lost.alot sort;
            (nomin = denom) --> Lost.half sort;
            (nomin = zero sort) --> Lost.zero sort;
         ] ~default:(Lost.afew sort) >=> fun loss ->
        round rm sign coef loss (Lost.bits sort) @@ fun coef _ ->
        coef
      else
        ite (nomin > denom) (mask_bit sort i) (zero sort) >=> fun bit ->
        ite (nomin > denom) (nomin - denom) nomin >=> fun next_nomin ->
        next_nomin lsl one sort >=> fun next_nomin ->
        bind next_nomin (fun next_nomin ->
          loop Caml.(i - 1) (bit :: bits) next_nomin) in
    loop Caml.(prec - 1) [] nomin

  let fdiv_finite fsort rm x y =
    let open B in
    let norm_nominator exps nomin denom f =
      sort nomin >>= fun sigs ->
      ite (nomin < denom) (nomin lsl one sigs) nomin >=> fun nomin' ->
      ite (nomin < denom) (one exps) (zero exps) >=> fun dexpn ->
      f nomin' dexpn in
    let prec = precision fsort in
    let exps,sigs = floats fsort in
    unpack fsort x @@ fun xsign xexpn xcoef ->
    unpack fsort y @@ fun ysign yexpn ycoef ->
    xor xsign ysign >=> fun sign ->
    normalize_coef exps xcoef @@ fun nomin dexpnx ->
    normalize_coef exps ycoef @@ fun denom dexpny ->
    extend nomin ~addend:1 >=> fun nomin ->
    extend denom ~addend:1 >=> fun denom ->
    norm_nominator exps nomin denom @@ fun nomin dexpn' ->
    long_division prec rm sign nomin denom >=> fun coef ->
    msb coef >=> fun coef_overflow ->
    ite coef_overflow (coef lsr one sigs) coef >=> fun coef ->
    ite coef_overflow (one exps) (zero exps) >=> fun from_rnd ->
    unsigned sigs coef >=> fun coef ->
    of_int exps (bias fsort) >=> fun bias ->
    dexpny + from_rnd - dexpnx - dexpn' >=> fun dexpn ->
    xexpn - yexpn >=> fun expn ->
    and_ (xexpn > yexpn) (expn > dexpn + bias) >=> fun is_overflow ->
    expn + dexpn + bias  >=> fun expn ->
    ite is_overflow (inf fsort sign)
      (norm expn coef >>= fun (expn,coef) ->
       pack fsort sign expn coef)

  let fdiv_special fsort x y =
    let open B in
    let (&&) = and_ in
    let (||) = or_  in
    with_special fsort x @@ fun ~is_inf:xinf ~is_snan:xsnan ~is_qnan:xqnan ->
    with_special fsort y @@ fun ~is_inf:yinf ~is_snan:ysnan ~is_qnan:yqnan ->
    fsign x >=> fun xsign ->
    fsign y >=> fun ysign ->
    (xinf && yinf) >=> fun is_inf ->
    match_ [
      (is_zero x && is_zero y) --> qnan fsort;
      (xinf && yinf) --> qnan fsort;
      is_inf --> with_sign (xor xsign ysign) x;
      (xsnan || xqnan) --> transform_to_quite fsort x
    ] ~default:(transform_to_quite fsort y)

  let fdiv fsort rm x y =
    let (&&) = B.and_ in
    B.ite (is_finite fsort x && is_finite fsort y)
      (fdiv_finite fsort rm x y)
      (fdiv_special fsort x y)

(* Newton-Raphson algorithm. Need a good choice of a starting seed  *)
  let fsqrt fsort rm x =
    let two = fadd_finite fsort rm (fone fsort) (fone fsort) in
    let init = fdiv_finite fsort rm x two in
    let max = precision fsort in
    let rec run x0 n =
      fdiv fsort rm x x0 >=> fun a1 ->
      fadd fsort rm x0 a1 >=> fun a2 ->
      fdiv fsort rm a2 two >=> fun x' ->
      if n > max then x0
      else run x' ( n + 1) in
    run init 0

end
