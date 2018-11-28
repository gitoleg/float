open Core_kernel
open Bap.Std

type rmode =
  | Nearest_even  (** round to nearest, ties to even *)
  | Nearest_away  (** round to nearest, ties to away *)
  | Towards_zero  (** round toward zero              *)
  | Positive_inf  (** round toward positive infinity *)
  | Negative_inf  (** round toward negative infinity *)
[@@deriving sexp]

module Make(Bignum : Core_float.Core) = struct

  open Core_float.Types

  module Bignum = struct
    include Bignum

    let of_int sort v =
      int sort
        (Word.of_int ~width:(Sort.size sort) v)

    let testbit b i =
      Bignum.is_one @@
      Bignum.extract (Bignum.sort b) i i b

    let is_negative = Bignum.msb
    let is_positive x = Bignum.inv (Bignum.msb x)
    let is_non_negative x = Bignum.or_ (is_positive x) (Bignum.is_zero x)

    let zero_extend x upto = Bignum.unsigned upto x
    let sign_extend x upto = Bignum.signed upto x

    let abs x = ite (is_negative x) (neg x)  x

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
      let ( >$ ) = sgt
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
  end

  type 'a number = 'a bitv value knowledge
  type nonrec bit = bit value knowledge

  type ('e,'k) data = {
    expn : 'e number;
    frac : 'k number;
  }

  type ('e,'k) desc = {
    esort : 'e bitv sort;
    fsort : 'k bitv sort;
  }

  type special = {
    is_qnan : bit;
    is_snan : bit;
    is_inf  : bit;
  }

  type ('e, 'k) float = {
    sign : bit;
    desc : ('e, 'k) desc;
    data : ('e, 'k) data;
    special : special;
  }

  type 'a t = 'a knowledge

  let rne = Nearest_even
  let rna = Nearest_away
  let rtp = Positive_inf
  let rtn = Negative_inf
  let rtz = Towards_zero

  let floats _int esort fsort = {esort; fsort}
  let lshift_frac frac n = Bignum.(frac lsl n)

  let extract_last x n =
    let open Bignum in
    let ones = not (zero (sort x)) in
    let mask = (ones lsr n) lsl n in
    x land (not mask)

  let rshift_frac frac n =
    Bignum.(frac lsr n), extract_last frac n

  let half_of_sort s =
    let open Bignum in
    let x = one s in
    let n = of_int s (Sort.size s) in
    x lsl n

  (* TODO: consider to add expn here and if all ones - adjust it  *)
  let round rm sign frac loss bits =
    let open Bignum in
    let half = half_of_sort (Bignum.sort loss) in
    let is_needed = match rm with
      | Positive_inf -> Bignum.inv sign
      | Negative_inf -> sign
      | Nearest_away -> loss >= half
      | Nearest_even ->
        if_ (loss > half) ~then_:b1
          ~else_:(
            if_ (loss = half) ~then_:(lsb loss)
              ~else_:b0)
      | _ -> b0 in
    let is_needed = and_ (non_zero loss) is_needed in
    let all_ones = not (zero (sort frac)) in
    if_ (and_ (frac <> all_ones) is_needed)
      ~then_:(succ frac)
      ~else_:frac

  (* those functions are unsafe in that sence that there are not
     any checks for exponent overflow *)
  let unsafe_lshift x n =
    let expn = Bignum.(x.expn - n) in
    { expn; frac = lshift_frac x.frac n }

  let unsafe_rshift x n =
    let frac, loss = rshift_frac x.frac n in
    let expn = Bignum.(x.expn + n) in
    { expn; frac }, loss

  (* shift frac left as possible, without bit loss,
     returns frac and number of shifts *)
  let align_frac_left frac =
    let prec = Sort.size (Bignum.sort frac) in
    let zero = Bignum.(zero (sort frac)) in
    let unos = Bignum.(one (sort frac)) in
    let rec loop i num frac =
      if i < prec then
        let msb = Bignum.msb frac in
        let num' = Bignum.ite msb num (Bignum.succ num) in
        let frac' = Bignum.ite msb frac Bignum.(frac lsl unos) in
        loop (i + 1) num' frac'
      else frac, num in
    loop 0 zero frac

  (* [align_right base precision expn frac] shifts fraction right to fit
     into [precision] with a possible loss of bits in order to keep
     most significant bits. Returns [Some (expn, frac, loss)], if
     no exponent overflow occured, [None] otherwise. *)
  let align_right ~precision expn frac =
    let prec = Sort.size (Bignum.sort frac) in
    let zero = Bignum.(zero (sort frac)) in
    let unos = Bignum.(one (sort frac)) in
    let rec loop i num frac =
      if i < prec then
        let lsb = Bignum.lsb frac in
        let num'  = Bignum.ite lsb num (Bignum.succ num) in
        let frac' = Bignum.ite lsb frac Bignum.(frac lsr unos) in
        loop (i + 1) num' frac'
      else frac, num in
    let frac', num = loop 0 zero frac in
    let loss = extract_last frac num in
    Bignum.(expn + num), frac', loss

  (* maximum possible exponent that fits in [n - 1] bits. (one for sign) *)
  let max_exponent' n = int_of_float (2.0 ** (float_of_int (n - 1))) - 1
  let min_exponent' n = - (max_exponent' n)
  let max_exponent  n = Bignum.of_int n (Sort.size n |> max_exponent')
  let min_exponent  n = Bignum.of_int n (Sort.size n |> min_exponent')

  (* the same as [align_right] above, but stops in case of bits loss
     OR if exponent reached a maximum of it's value
     TODO: consider test frac for zero to prevent expn change *)
  let safe_align_right expn frac =
    let max_expn = max_exponent (Bignum.sort expn) in
    let prec = Sort.size (Bignum.sort frac) in
    let unos = Bignum.(one (sort frac)) in
    let rec run i expn frac =
      if i < prec then
        let stop =
          Bignum.or_ Bignum.(expn = max_expn) (Bignum.lsb frac) in
        let expn = Bignum.ite stop expn (Bignum.succ expn) in
        let frac = Bignum.ite stop frac (Bignum.(frac lsr unos)) in
        run (i + 1) expn frac
      else expn, frac in
    run 0 expn frac

  (* TODO: consider test frac for zero to prevent expn change *)
  let safe_align_left expn frac =
    let min_expn = min_exponent (Bignum.sort expn) in
    let prec = Sort.size (Bignum.sort frac) in
    let unos = Bignum.(one (sort frac)) in
    let rec run i expn frac =
      if i < prec then
        let stop =
          Bignum.or_ Bignum.(expn = min_expn) (Bignum.msb frac) in
        let expn = Bignum.ite stop expn (Bignum.pred expn) in
        let frac = Bignum.ite stop frac (Bignum.(frac lsl unos)) in
        run (i + 1) expn frac
      else expn, frac in
    run 0 expn frac

  (* min exponent without bit loss or exponent overflow,
     fraction shifted as left as possible, i.e. it occupies
     more significant bits *)
  let minimize_exponent x =
    let expn, frac = safe_align_left x.expn x.frac in
    { expn; frac }

  (* max exponent without bit loss or exponent overflow,
     fraction shifted as right as possible, i.e. it occupies
     less significant bits *)
  let maximize_exponent x =
    let expn, frac = safe_align_right x.expn x.frac in
    { expn; frac }

  let norm = minimize_exponent

  let prec x = Sort.size x.desc.fsort

  let fksort x = x.desc.fsort
  let fesort x = x.desc.esort

  let zero_finite desc =
    let expn = min_exponent desc.esort in
    let frac = Bignum.zero desc.fsort in
    {expn; frac}

  let zero_specials =
    let b0 = Bignum.b0 in
    { is_qnan=b0; is_snan=b0; is_inf=b0; }

  let is_special {is_qnan; is_snan; is_inf} =
    let (||) = Bignum.or_ in
    is_qnan || is_snan || is_inf

  let zero_data desc =
    {expn = Bignum.zero desc.esort; frac = Bignum.zero desc.fsort}

  let zero desc =
    let data = zero_data desc in
    {sign = Bignum.b0; desc; data; special = zero_specials}

  let finite desc sign expn frac =
    let data = norm {expn; frac} in
    {sign; desc; data; special = zero_specials; }

  let inf ?(negative=false) desc =
    let sign = if negative then Bignum.b1 else Bignum.b0 in
    let special = {is_qnan=Bignum.b0; is_snan=Bignum.b0;
                   is_inf=Bignum.b1} in
    {sign; desc; special; data=zero_data desc}

  let pinf desc = inf ~negative:false desc
  let ninf desc = inf ~negative:true desc

  (* mk nan with payload 0100..01 *)
  let nan ?(signaling=false) ?(negative=false) ?payload desc =
    let sign = if negative then Bignum.b1 else Bignum.b0 in
    let prec = Bignum.of_int desc.fsort (Sort.size desc.fsort) in
    let frac = match payload with
      | Some p -> p
      | None ->
        let payload = Bignum.one desc.fsort in
        let two = Bignum.one desc.fsort |> Bignum.succ in
        let shift = Bignum.(prec - two) in
        let payload = Bignum.(payload lsl shift) in
        Bignum.succ payload in
    let data = { expn = Bignum.zero desc.esort; frac } in
    let is_snan = if signaling then Bignum.b1 else Bignum.b0 in
    let is_qnan = Bignum.inv is_snan in
    let special = {is_qnan; is_snan; is_inf=Bignum.b0} in
    {sign; desc; data; special}

  let qnan fsort payload = nan ~payload fsort
  let snan fsort payload = nan ~signaling:true ~payload fsort

  let exponent {data} = data.expn
  let coefficient {data} = data.frac
  let fsign {sign} = sign

  let is_fzero x =
    Bignum.(and_ (is_zero x.data.frac) (inv (is_special x.special)))

  let is_inf x = x.special.is_inf

  let is_pinf x = Bignum.(and_ (inv x.sign) (is_inf x))
  let is_ninf x = Bignum.(and_ x.sign (is_inf x))
  let is_snan x = x.special.is_snan
  let is_qnan x = x.special.is_qnan
  let is_finite x = Bignum.inv (is_special x.special)

  let equal a b =
    let open Bignum in
    let (&&) = and_ in
    let (||) = or_ in
    if Caml.(a.sign <> b.sign) then b0
    else
      if_ (is_finite a && is_finite b)
        ~then_:(
          let x = norm a.data in
          let y = norm b.data in
          x.expn = y.expn && x.frac = y.frac)
        ~else_:(
          ((is_pinf a && is_pinf b) || (is_ninf a && is_ninf b)) ||
            (is_snan a && is_snan b && a.data.frac = b.data.frac) ||
              (is_qnan a && is_qnan b && a.data.frac = b.data.frac))

  (* returns result sign *)
  let xor_sign s s' = Bignum.(is_one (s lxor s'))

  let invert_loss loss =
    let open Bignum in
    let half = half_of_sort (sort loss) in
    ite (loss = half) loss (not loss)

  let extend x addend = { x with frac = Bignum.zero_extend x.frac addend }

  let fadd rm a b =
    let common_ground x y =
      let open Bignum in
      let expn = max x.expn y.expn in
      let lost_bits =
        Bignum.(ite (x.expn >$ y.expn) (x.expn - y.expn) (y.expn - x.expn)) in
      let xfrac = ite (x.expn >$ y.expn) x.frac (x.frac lsr lost_bits) in
      let yfrac = ite (y.expn >$ x.expn) y.frac (y.frac lsr lost_bits) in
      let loss = ite (x.expn >$ y.expn)
                   (extract_last y.frac lost_bits)
                   (extract_last x.frac lost_bits) in
      {expn; frac=xfrac}, {expn; frac=yfrac}, loss, lost_bits in
    (* TODO: check for nan/inf needed *)
    let x,y = a.data, b.data in
    let x,y,loss,lost_bits = common_ground x y in
    let frac = Bignum.(x.frac + y.frac) in
    let expn = Bignum.(ite (frac >= x.frac) x.expn (succ x.expn)) in
    (* TODO: check for expn oerflow needed  *)

    let frac =
      Bignum.ite Bignum.(frac >= x.frac) (round rm Bignum.b0 frac loss lost_bits)
        begin
          let x = extend x a.desc.fsort in (* TODO: actually, one is enough  *)
          let y = extend y a.desc.fsort in
          let frac = Bignum.(x.frac + y.frac) in
          let uno = Bignum.one (Bignum.sort frac) in
          let loss' = extract_last frac uno in
          let frac = Bignum.(frac lsr uno) in (* TODO: and extract ! *)
          let loss'' = Bignum.concat (Bignum.sort frac) [loss'; loss] in
          (* TODO: need to use another sort here *)

          round rm Bignum.b0 frac loss'' (Bignum.succ lost_bits)
        end in
     { a with data = norm {expn; frac} }

  let sub rm a b =
    let common_ground x y =
      let open Bignum in
      let if_expn ~equal ~xgreater ~ygreater =
        ite (x.expn = y.expn) equal
          (ite (x.expn >$ y.expn) xgreater ygreater) in
      let expn = max x.expn y.expn in
      let one = one a.desc.esort in
      let lost_bits =
        if_expn ~equal:(zero (sort x.expn))
          ~xgreater:(x.expn - y.expn)
          ~ygreater:(y.expn - x.expn) in
      let lost_bits = lost_bits - one in (* what if 0? *)
      let loss =
        if_expn ~equal:(zero (sort x.expn))
          ~xgreater:(extract_last y.frac lost_bits)
          ~ygreater:(extract_last x.frac lost_bits) in
      let xfrac =
        if_expn ~equal:x.frac
          ~xgreater:(x.frac lsl one)
          ~ygreater:(x.frac lsr lost_bits) in
      let yfrac =
        if_expn ~equal:y.frac
          ~xgreater:(y.frac lsr lost_bits)
          ~ygreater:(y.frac lsl one) in
      let reverse =
        if_expn ~equal:(x.frac < y.frac)
          ~xgreater:b0 ~ygreater:b1 in
      {expn; frac=xfrac}, {expn; frac=yfrac}, reverse, loss, lost_bits in
    let x,y = a.data, b.data in
    let x = minimize_exponent x in
    let y = minimize_exponent y in
    let x = extend x a.desc.fsort in (* TODO: one is enough *)
    let y = extend y a.desc.fsort in
    let x,y,reverse,loss,lost_bits = common_ground x y in
    let loss = invert_loss loss in
    let borrow = Bignum.(ite (is_zero loss)
                   (zero (sort x.frac)) (one (sort x.frac))) in
    let frac = Bignum.(ite reverse
                 (y.frac - x.frac - borrow)
                 (x.frac - y.frac - borrow)) in
    let sign = Bignum.(ite reverse (inv a.sign) a.sign) in
    let expn = Bignum.(ite (msb frac) (succ x.expn) x.expn) in
    let frac = Bignum.(ite (msb frac) (frac lsr one (sort frac)) frac) in
    let loss' = Bignum.(ite (msb frac)
                          (extract_last frac (one (sort frac)))
                          (zero (sort frac))) in

    (* TODO: check sort in concat here and extract! *)
    let loss = Bignum.ite Bignum.(msb frac)
                 (Bignum.concat (Bignum.sort frac) [loss'; loss])
                 loss in
    let frac = Bignum.extract a.desc.fsort
                 (Bignum.of_int a.desc.fsort ((prec a) - 1))
                 (Bignum.of_int a.desc.fsort 0)
                 frac in
    let lost_bits =
      Bignum.(ite (msb frac) (succ lost_bits) lost_bits) in
    let frac = round rm sign frac loss lost_bits in
    let data = norm {expn; frac} in
    {a with data; sign}


(* let add_or_sub rm subtract a b =
    check_operands a b;
    let s1 = Bignum.of_bool subtract in
    let s2 = Bignum.of_sign a.sign in
    let s3 = Bignum.of_sign b.sign in
    let is_subtract = Bignum.is_one Bignum.(s1 lxor (s2 lxor s3)) in
    if is_subtract then sub rm a b
    else add rm a b

  let add ?(rm=Nearest_even) = add_or_sub rm false
  let sub ?(rm=Nearest_even) = add_or_sub rm true

  let multiply desc x y =
    let extract expn frac =
      let expn = Bignum.extract ~hi:(desc.ebits - 1) expn in
      let frac = Bignum.extract ~hi:(desc.fbits - 1) frac in
      expn, frac in
    let extend {expn; frac} = {
      expn = Bignum.sign_extend expn desc.ebits;
      frac = Bignum.zero_extend frac desc.fbits;
    } in
    let x = extend x in
    let y = extend y in
    let expn = Bignum.(x.expn + y.expn) in
    let frac = Bignum.(x.frac * y.frac) in
    let max_expn =
      Bignum.sign_extend (max_exponent desc.ebits) desc.ebits in
    let min_expn =
      Bignum.sign_extend (min_exponent desc.ebits) desc.ebits in
    match align_right desc.radix desc.fbits expn frac with
    | None -> `Overflow_expn
    | Some (expn,frac,loss) ->
      if Bignum.is_positive expn && Bignum.(expn > max_expn)
      then `Overflow_expn
      else if
        Bignum.is_positive expn then
        let expn, frac = extract expn frac in
        let expn = Bignum.extract ~hi:(desc.ebits - 1) expn in
        `Nice (expn,frac,loss)
      else if
        Bignum.is_negative expn && Bignum.(expn <$ min_expn) then
        let dexp = Bignum.(abs expn - abs min_expn) in
        let {expn;frac=frac'}, loss' = unsafe_rshift desc.radix {expn;frac} dexp in
        if Bignum.is_zero frac' && not (Bignum.is_zero frac) then `Underflow_expn
        else
          let loss' = combine_loss loss' loss in
          let expn, frac = extract expn frac' in
          `Nice (expn,frac',loss')
      else
        let expn, frac = extract expn frac in
        `Nice (expn,frac,loss)

  let mul ?(rm=Nearest_even) a b =
    check_operands a b;
    match a.data,b.data with
    | Fin _, Fin _ when is_zero a ->
      {a with sign = xor_sign a.sign b.sign;}
    | Fin _, Fin _ when is_zero b ->
      {b with sign = xor_sign a.sign b.sign}
    | Fin x, Fin y ->
      let x = maximize_exponent (radix a) x in
      let y = maximize_exponent (radix a) y in
      let sign = xor_sign a.sign b.sign in
      let data = match multiply a.desc x y with
        | `Overflow_expn -> Inf
        | `Underflow_expn -> Fin (zero_finite a.desc)
        | `Nice (expn, frac, loss) ->
          let frac = round rm sign frac loss in
          Fin (norm (radix a) { expn; frac}) in
      { a with data; sign }
    | Nan _, Nan _ -> if is_signaling_nan a || is_quite_nan b then a else b
    | Nan _, _ -> a
    | _, Nan _ -> b
    | Inf,  _ when is_zero b -> nan a.desc
    | _, Inf when is_zero a -> nan a.desc
    | Inf, Inf when a.sign = b.sign -> { a with sign = Pos }
    | Inf, Inf when a.sign <> b.sign -> { a with sign = Neg }
    | Inf, _ -> a
    | _, Inf -> b

  let div ?(rm=Nearest_even) a b =
    let extend_expn e = Bignum.sign_extend e (sort e) in
    let min_expn = extend_expn (min_exponent a.desc.ebits) in
    let max_expn = extend_expn (max_exponent a.desc.ebits) in
    let extend {expn; frac} =
      let expn = extend_expn expn in
      let frac = Bignum.zero_extend frac (sort frac) in
      {expn; frac} in
    let is_overflow _ = false in
    check_operands a b;
    match a.data,b.data with
    | Fin x, Fin y when is_zero a && is_zero b -> nan ~negative:true a.desc
    | Fin x, Fin y when is_zero b -> {a with data = Inf}
    | Fin x, Fin y ->
      let x = extend x in
      let y = extend y in
      let sign = xor_sign a.sign b.sign in
      let xexpn, xfrac = safe_align_left a.desc.radix x.expn x.frac in
      let expn = Bignum.(xexpn - y.expn) in
      let frac = Bignum.(xfrac / y.frac) in
      if Bignum.(expn >$ max_expn) || is_overflow expn frac then
        {a with sign; data = Inf}
      else
        let left = Bignum.(xfrac - frac * y.frac) in
        let left = Bignum.(left lsl 1) in
        let loss =
          if Bignum.is_zero left then ExactlyZero
          else if Bignum.(left > y.frac) then MoreThanHalf
          else if Bignum.(left = y.frac) then ExactlyHalf
          else LessThanHalf in
        let frac = round rm sign frac loss in
        let expn,frac,_ =
          if Bignum.(expn <$ min_expn) then
            let dexp = Bignum.(abs expn - abs min_expn) in
            let {expn;frac=frac'}, loss' = unsafe_rshift a.desc.radix {expn;frac} dexp in
            let frac = round rm sign frac' loss' in
            let expn = Bignum.extract ~hi:(a.desc.ebits - 1) expn in
            expn,frac, combine_loss loss' loss
          else
            let expn = Bignum.extract ~hi:(a.desc.ebits - 1) expn in
            expn,frac,loss in
        let data =
          match align_right ~base:a.desc.radix ~precision:a.desc.fbits expn frac with
          | None -> zero_finite a.desc
          | Some (expn,frac,loss') ->
            let frac = round rm sign frac loss' in
            let frac = Bignum.extract ~hi:((prec a) - 1) frac in
            norm (radix a) {frac; expn} in
        {a with data = Fin data; sign; }
    | Nan _, Nan _ -> if is_signaling_nan a || is_quite_nan b then a else b
    | Nan _, _ -> a
    | _, Nan _ -> b
    | Inf, Inf -> nan ~negative:true a.desc
    | Inf, _ -> a
    | _, Inf -> b

  let truncate ?(rm=Nearest_even) ~upto a = match a.data with
    | Fin {expn; frac} ->
      begin
        match align_right ~base:(radix a) ~precision:upto expn frac with
        | None -> None
        | Some (expn,frac,loss) ->
          let frac = round rm a.sign frac loss in
          let frac = Bignum.extract ~hi:(upto - 1) frac in
          let data = Fin { expn; frac} in
          Some { a with data } (* TODO change description? *)
      end
    | _ ->
      Some a

  let truncate_exn ?(rm=Nearest_even) ~upto a =
    Option.value_exn (truncate ~rm ~upto a)

  (* Newton-Raphson algorithm. Need a good choice of a starting seed  *)
  let sqrt ?(rm=Nearest_even) a =
    match a.data with
    | Fin x when is_neg a -> nan ~negative:true a.desc
    | Fin x when is_zero a -> a
    | Fin x ->
      let expn = Bignum.sign_extend x.expn (sort x.expn) in
      let frac = Bignum.zero_extend x.frac (prec a) in
      let {expn;frac} = minimize_exponent (radix a) {expn; frac} in
      let desc = {a.desc with ebits = 2 * a.desc.ebits; fbits = 2 * (prec a) } in
      let s = create desc ~expn frac in
      let uno = Bignum.one desc.fbits in
      let two = create desc
          ~expn:(Bignum.zero desc.ebits) Bignum.(uno + uno) in
      let rec run x0 n =
        let a1 = div ~rm s x0 in
        let a2 = add ~rm x0 a1 in
        let x' = div ~rm a2 two in
        if equal x0 x' || not (is_fin x') then
          x0,n
        else
          run x' (n + 1) in
      let init = div ~rm s two in
      let r,n = run init 0 in
      truncate_exn r ~upto:(prec a)
    | Inf when is_neg a -> nan ~negative:true a.desc
    | _ -> a

  let round ?(rm=Nearest_even) ~precision a =
    match truncate ~rm ~upto:precision a with
    | Some x -> x
    | None ->
      let negative = a.sign = Neg in
      inf ~negative a.desc

  module Infix = struct
    let ( + ) = add ~rm:Nearest_even
    let ( - ) = sub ~rm:Nearest_even
    let ( * ) = mul ~rm:Nearest_even
    let ( / ) = div ~rm:Nearest_even
    let ( = ) = equal
  end

  let extend a addend = match a.data with
    | Fin x ->
      let data = Fin (extend x addend) in
      let desc = {a.desc with fbits = prec a + addend} in
      { a with data; desc }
    | _ -> a


 *)

end
