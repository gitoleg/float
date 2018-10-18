open Core_kernel

type rounding =
  | Nearest_even  (** round to nearest, ties to even *)
  | Nearest_away  (** round to nearest, ties to away *)
  | Towards_zero  (** round toward zero              *)
  | Positive_inf  (** round toward positive infinity *)
  | Negative_inf  (** round toward negative infinity *)
[@@deriving sexp]

type loss =
  | ExactlyZero
  | ExactlyHalf
  | LessThanHalf
  | MoreThanHalf

(** digit position from in range [0 .. base - 1] relative to [base/2] *)
type digit = Middle | Less | More | Zero

type sign = Pos | Neg [@@deriving sexp]

type desc = {
  radix : int;
  ebits : int;
  fbits : int;
}

let desc ~radix ~expn_bits fbits = {radix; fbits; ebits=expn_bits}

module type Bignum = sig
  type t
  val of_int : width:int -> int -> t
  val to_int : t -> int
  val bitwidth : t -> int
  val b0 : t
  val b1 : t
  val of_bool : bool -> t
  val succ : t -> t
  val pred : t -> t
  val extract : ?hi:int -> ?lo:int -> t -> t
  val one  : int -> t
  val zero : int -> t
  val ones : int -> t
  val is_zero : t -> bool
  val is_one  : t -> bool
  val is_positive : t -> bool
  val is_negative : t -> bool
  val testbit : t -> int -> bool
  val zero_extend : t -> int -> t
  val ( + ) : t -> t -> t
  val ( - ) : t -> t -> t
  val ( * ) : t -> t -> t
  val ( / ) : t -> t -> t
  val ( = ) : t -> t -> bool
  val ( < ) : t -> t -> bool
  val ( > ) : t -> t -> bool
  val ( <= ) : t -> t -> bool
  val ( >= ) : t -> t -> bool
  val ( lsl ) : t -> int -> t
  val ( lxor ) : t -> t -> t
  val abs : t -> t
  val max : t -> t -> t
end

module Make(Bignum : Bignum) = struct

  type bignum = Bignum.t

  type finite = {
    expn : bignum;
    frac : bignum;
  }

  type data =
    | Inf
    | Nan of bool * bignum
    | Fin of finite

  type t = {
    sign : sign;
    desc : desc;
    data : data;
  }

  let bits_in = Bignum.bitwidth

  let msb w =
    let len = bits_in w in
    let bits = List.init len ~f:(fun i -> len - i - 1) in
    List.find bits ~f:(fun i -> Bignum.testbit w i)

  (* returns a list of digits in [loss], most significant first *)
  let lost_digits base loss n =
    let to_digit x : digit =
      let x = Bignum.to_int x in
      let middle = base / 2 in
      if Int.(x = middle) then Middle
      else if Int.(x = 0) then Zero
      else if Int.( x < middle ) then Less
      else More in
    let base = Bignum.of_int ~width:(bits_in loss) base in
    let rec loop acc loss =
      let loss' = Bignum.(loss / base) in
      let restored = Bignum.(loss' * base) in
      let rem : bignum = Bignum.(loss - restored) in
      let acc = (to_digit rem)::acc in
      if Bignum.is_zero loss' then acc
      else loop acc loss' in
    let digits = loop [] loss in
    if List.length digits < n then
      let zeros = List.init (n - List.length digits) (fun _ -> Zero) in
      zeros @ digits
    else digits

  (* estimate loss after shift right to [n] digits, [lost_frac] is what
     is exactly lost *)
  let estimate_loss base lost_frac n =
    let all_zeros ds = List.for_all ds ~f:(fun d -> d = Zero) in
    match lost_digits base lost_frac n with
    | [] -> ExactlyZero
    | Zero :: [] -> ExactlyZero
    | Zero :: ds when all_zeros ds -> ExactlyZero
    | Zero :: _ -> LessThanHalf
    | Middle :: ds when all_zeros ds -> ExactlyHalf
    | Middle :: _ -> MoreThanHalf
    | More :: _ -> MoreThanHalf
    | Less :: _ -> LessThanHalf

  (* TODO: add expn here and if all ones - adust it  *)
  let round rm sign frac loss =
    let is_need = match rm, loss with
      | Positive_inf,_ -> sign = Pos
      | Negative_inf,_ -> sign = Neg
      | Nearest_away, (ExactlyHalf | MoreThanHalf)
      | Nearest_even, MoreThanHalf -> true
      | Nearest_even, ExactlyHalf ->
        Bignum.is_one (Bignum.extract ~hi:0 ~lo:0 frac)
      | _ -> false in
    if is_need then
      let all_ones = Bignum.ones (bits_in frac) in
      if Bignum.(frac = all_ones) then frac
      else Bignum.succ frac
    else frac

  (* return Some power [n] of [base]: base ** n
     return None if number doesn't fit into [precs]  *)
  let pow ~base ~precs n =
    let base = Bignum.of_int ~width:precs base in
    let rec run r m =
      if m < n then
        let r' = Bignum.(r * base) in
        if Bignum.(r' < r) then None
        else run r' (m + 1)
      else Some r in
    if n = 0 then Some (Bignum.one precs)
    else run base 1

  let lshift_frac base frac n =
    if n = 0 then frac
    else
      match pow ~base ~precs:(bits_in frac) n with
      | None -> Bignum.zero (bits_in frac)
      | Some k -> Bignum.(frac * k)

  let rshift_frac base frac n =
    if n = 0 then frac, ExactlyZero
    else
      match pow ~base ~precs:(bits_in frac) n with
      | None -> Bignum.zero (bits_in frac), ExactlyZero
      | Some k ->
        if Bignum.is_zero k then k, ExactlyZero
        else
          let result = Bignum.(frac / k) in
          let restored = Bignum.(result * k) in
          result, estimate_loss base Bignum.(frac - restored) n

  (* those functions are unsafe in that sence that there are not
     any checks for exponent overflow *)
  let unsafe_lshift base x n =
    let n' = Bignum.to_int n in
    let expn = Bignum.(x.expn - n) in
    { expn; frac = lshift_frac base x.frac n' }

  let unsafe_rshift base x n =
    let n' = Bignum.to_int n in
    let frac, loss = rshift_frac base x.frac n' in
    let expn = Bignum.(x.expn + n) in
    { expn; frac }, loss

  (* [align_right base precision expn frac] shifts fraction right to fit
     into [precision] with a possible loss of bits in order to keep
     most significant bits. Returns [Some (expn, frac, loss)], if
     no exponent overflow occured, [None] otherwise. *)
  let align_right ~base ~precision expn frac =
    let rec run n frac =
      match msb frac with
      | None -> n
      | Some i when i < precision -> n
      | _ -> run (n + 1) (fst (rshift_frac base frac 1)) in
    let n = run 0 frac in
    let n' = Bignum.of_int ~width:(bits_in expn) n in
    let expn' = Bignum.(expn + n') in
    if Bignum.(expn' < expn) then None
    else
      let res, loss = rshift_frac base frac n in
      Some (expn', res, loss)

  let align_right_exn ~base ~precision epxn frac =
    match align_right ~base ~precision epxn frac with
    | Some x -> x
    | None -> failwith "Can't align right: exponent overflow"

  (* maximum possible exponent that fits in [n - 1] bits. (one for sign) *)
  let max_exponent n =
    int_of_float (2.0 ** (float_of_int (n - 1))) - 1

  let min_exponent n = - (max_exponent n)

  (* the same as [align_right] above, but stops in case of bits loss
     OR if exponent reached a maximum of it's value *)
  let safe_align_right base expn frac =
    let max_expn =
      Bignum.of_int ~width:(bits_in expn) (max_exponent (bits_in expn)) in
    let rec run expn x =
      let expn' = Bignum.abs expn in
      if Bignum.(expn' = max_expn) then
        expn, x
      else
        match rshift_frac base x 1 with
        | y, ExactlyZero -> run (Bignum.succ expn) y
        | _ -> expn, x in
    if Bignum.is_zero frac then expn,frac
    else run expn frac

  let safe_align_left base expn frac =
    let min_expn =
      Bignum.of_int ~width:(bits_in expn) (min_exponent (bits_in expn)) in
    let width = bits_in frac in
    let rec run expn x =
      if Bignum.(expn = min_expn) then
        expn, x
      else
        let y = lshift_frac base x 1 in
        let z = Bignum.extract ~lo:width y in
        if Bignum.is_zero z then run (Bignum.pred expn) y
        else expn,x in
    if Bignum.is_zero frac then expn, frac
    else
      let frac = Bignum.zero_extend frac width in
      let e,frac = run expn frac in
      let frac = Bignum.extract ~hi:(width - 1) frac in
      e,frac

  (* min exponent without bit loss or exponent overflow,
     fraction shifted as left as possible, i.e. it occupies
     more significant bits *)
  let minimize_exponent base x =
    let expn, frac = safe_align_left base x.expn x.frac in
    { expn; frac }

  (* max exponent without bit loss or exponent overflow,
     fraction shifted as right as possible, i.e. it occupies
     less significant bits *)
  let maximize_exponent base x =
    let expn, frac = safe_align_right base x.expn x.frac in
    { expn; frac }

  let norm = minimize_exponent

  let prec x = x.desc.fbits
  let radix x = x.desc.radix

  let zero desc =
    let min = min_exponent desc.ebits in
    let expn = Bignum.of_int ~width:desc.ebits min in
    let frac = Bignum.zero desc.fbits in
    let data = {expn; frac} in
    {sign = Pos; desc; data = Fin data;}

  let create desc ~expn frac =
    let sign = if Bignum.(frac < zero desc.fbits) then Neg else Pos in
    let frac = Bignum.abs frac in
    if Bignum.is_zero frac then
      let x = zero desc in
      {x with sign}
    else
      let data = Fin (norm desc.radix {expn; frac}) in
      {sign; desc; data; }

  let inf ?(negative=false) desc =
    let sign = if negative then Neg else Pos in
    {sign; desc; data = Inf }

  (* mk nan with payload 0100..01 *)
  let nan ?(signaling=false) ?(negative=false) ?payload desc =
    let sign = if negative then Neg else Pos in
    let prec = desc.fbits in
    let payload = match payload with
      | Some p -> p
      | None ->
        let payload = Bignum.one prec  in
        let shift = prec - 2 in
        let payload = Bignum.(payload lsl shift) in
        Bignum.(payload + b1) in
    let data = Nan (signaling, payload) in
    {sign; desc; data}

  let fin t = match t.data with
    | Fin {expn; frac} -> Some (expn, frac)
    | _ -> None

  let frac t = match t.data with
    | Fin {frac} -> Some frac
    | Nan (_,frac) -> Some frac
    | _ -> None

  let expn t = match t.data with
    | Fin {expn} -> Some expn
    | _ -> None

  let is_zero x = match x.data with
    | Fin x -> Bignum.is_zero x.frac
    | _ -> false

  let is_inf x = match x.data with
    | Inf -> true
    | _ -> false

  let is_nan x = match x.data with
    | Nan _ -> true
    | _ -> false

  let is_signaling_nan x = match x.data with
    | Nan (s,_) -> s
    | _ -> false

  let is_quite_nan x = match x.data with
    | Nan (s,_) -> not s
    | _ -> false

  let is_fin x = match x.data with
    | Fin _ -> true
    | _ -> false

  let is_pos x = match x.sign with
    | Pos -> true
    | Neg -> false

  let is_neg x = match x.sign with
    | Neg -> true
    | Pos -> false

  let check_operands a b =
    if Int.(radix a <> radix b) || Int.(prec a <> prec b) then
      failwith "attempting to operate with a differrent radix/precision"

  let equal a b =
    check_operands a b;
    if a.sign <> b.sign then false
    else
      match a.data, b.data with
      | Fin x, Fin y ->
        let x = norm (radix a) x in
        let y = norm (radix a) y in
        Bignum.(x.expn = y.expn) &&
        Bignum.(x.frac = y.frac)
      | Inf, Inf -> a.sign = b.sign
      | Nan (s,payload), Nan (s', payload') ->
        Bignum.(payload = payload') && Bool.equal s s'
      | _ -> false

  let revert_sign = function
    | Pos -> Neg
    | Neg -> Pos

  let bignum_of_sign = function
    | Pos -> Bignum.b0
    | Neg -> Bignum.b1

  let xor_sign s s' =
    let r = Bignum.(bignum_of_sign s lxor bignum_of_sign s') in
    if Bignum.is_one r then Neg else Pos

  let invert_loss = function
    | LessThanHalf -> MoreThanHalf
    | MoreThanHalf -> LessThanHalf
    | x -> x

  let estimate_spot base x =
    let left  = minimize_exponent base x in
    let right = maximize_exponent base x in
    if Bignum.(left.expn <> x.expn && right.expn <> x.expn) then `Both
    else if Bignum.(left.expn <> x.expn) then `Left
    else if Bignum.(right.expn <> x.expn) then `Right
    else `Nope

  let balance base x y =
    match estimate_spot base x, estimate_spot base y with
    | `Left,  _ when Bignum.(x.expn > y.expn) ->
      minimize_exponent base x, y
    | `Right, _ when Bignum.(x.expn < y.expn) ->
      maximize_exponent base x, y
    | _, `Left when Bignum.(x.expn < y.expn) ->
      x, minimize_exponent base y
    | _, `Right when Bignum.(x.expn > y.expn) ->
      x, maximize_exponent base y
    | _ -> minimize_exponent base x, minimize_exponent base y

  (* [combine_loss more_signifincant less_significant]  *)
  let combine_loss more less =
    match more, less with
    | _, ExactlyZero -> more
    | ExactlyZero,_ -> LessThanHalf
    | ExactlyHalf,_ -> MoreThanHalf
    | _ -> more

  let neg x = {x with sign = revert_sign x.sign}
  let extend x addend = { x with frac = Bignum.zero_extend x.frac addend }
  let extract prec frac = Bignum.extract ~hi:(prec - 1) frac

  let add rm a b =
    let common_ground base x y =
      if Bignum.(x.expn = y.expn) then x,y,ExactlyZero
      else
        let x,y = balance base x y in
        let expn = Bignum.max x.expn y.expn in
        if Bignum.(x.expn > y.expn) then
          let y, loss = unsafe_rshift base y Bignum.(expn - y.expn) in
          x, y, loss
        else
          let x,loss = unsafe_rshift base x Bignum.(expn - x.expn) in
          x,y,loss in
    check_operands a b;
    match a.data, b.data with
    | Fin x, Fin y ->
      let x = maximize_exponent (radix a) x in
      let y = maximize_exponent (radix a) y in
      let x,y,loss = common_ground (radix a) x y in
      let frac = Bignum.(x.frac + y.frac) in
      let data =
        if Bignum.(frac >= x.frac) then
          Fin (norm (radix a) {expn=x.expn; frac=round rm Pos frac loss})
        else
          let x = extend x (prec a) in
          let y = extend y (prec a) in
          let frac = Bignum.(x.frac + y.frac) in
          match align_right (radix a) (prec a) x.expn frac with
          | None -> Inf
          | Some (expn, frac, loss') ->
            let loss = if Bignum.(x.expn = expn) then loss
              else combine_loss loss' loss in
            let frac = extract (prec a) frac in
            let frac = round rm Pos frac loss in
            Fin (norm (radix a) {expn; frac}) in
      { a with data }
    | Nan _, Nan _ -> if is_signaling_nan a || is_quite_nan b then a else b
    | Nan _, _ -> a
    | _, Nan _ -> b
    | Inf, Inf when is_neg a && is_pos b -> a
    | Inf, Inf when is_pos a && is_neg b -> a
    | Inf, _ -> a
    | _, Inf -> b

  let sub rm a b =
    let common_ground base x y =
      if Bignum.(x.expn = y.expn) then x,y,ExactlyZero, Bignum.(x.frac < y.frac)
      else
        let expn = Bignum.max x.expn y.expn in
        if Bignum.(x.expn > y.expn) then
          let x = unsafe_lshift base x Bignum.b1 in
          let y, loss = unsafe_rshift base y Bignum.(expn - y.expn - b1) in
          x, y, loss, false
        else
          let x,loss = unsafe_rshift base x Bignum.(expn - x.expn - b1) in
          let y = unsafe_lshift base y Bignum.b1 in
          x,y,loss, true in
    check_operands a b;
    match a.data, b.data with
    | Fin x, Fin y ->
      let x = minimize_exponent (radix a) x in
      let y = minimize_exponent (radix a) y in
      let x = extend x (prec a) in
      let y = extend y (prec a) in
      let x,y,loss,reverse = common_ground (radix a) x y in
      let loss = invert_loss loss in
      let borrow = if loss = ExactlyZero then Bignum.b0 else Bignum.b1 in
      let frac = if reverse then Bignum.(y.frac - x.frac - borrow)
        else Bignum.(x.frac - y.frac - borrow) in
      let sign = if reverse then revert_sign a.sign else a.sign in
      let expn,frac,loss' =
        align_right_exn ~base:(radix a) ~precision:(prec a) x.expn frac in
      let loss = if Bignum.(x.expn = expn) then loss
        else combine_loss loss' loss in
      let frac = Bignum.extract ~hi:((prec a) - 1) frac in
      let frac = round rm sign frac loss in
      let data = Fin (norm (radix a) {expn; frac}) in
      let a = {a with data; sign} in
      if is_zero a then {a with sign = Pos} else a
    | Nan _, Nan _ -> if is_signaling_nan a || is_quite_nan b then a else b
    | Nan _, _ -> a
    | _, Nan _ -> b
    | Inf, Inf -> nan ~negative:true a.desc
    | Inf, _ -> a
    | _, Inf -> b

  let add_or_sub rm subtract a b =
    check_operands a b;
    let s1 = Bignum.of_bool subtract in
    let s2 = bignum_of_sign a.sign in
    let s3 = bignum_of_sign b.sign in
    let is_subtract = Bignum.is_one Bignum.(s1 lxor (s2 lxor s3)) in
    if is_subtract then sub rm a b
    else add rm a b

  let add ?(rm=Nearest_even) = add_or_sub rm false
  let sub ?(rm=Nearest_even) = add_or_sub rm true

  let expn_sum x y =
    let is_pos = Bignum.is_positive in
    let is_neg = Bignum.is_negative in
    let e = Bignum.(x + y) in
    if is_pos x && is_pos y && Bignum.(e < x) then `Overflow_expn
    else
    if is_neg x && is_neg y && Bignum.(e > x) then `Overflow_expn
    else `Nice e

  let mul ?(rm=Nearest_even) a b =
    check_operands a b;
    match a.data,b.data with
    | Fin _, Fin _ when is_zero a ->
      {a with sign = xor_sign a.sign b.sign;}
    | Fin _, Fin _ when is_zero b ->
      {b with sign = xor_sign a.sign b.sign}
    | Fin x, Fin y ->
      let x = minimize_exponent (radix a) x in
      let y = minimize_exponent (radix a) y in
      let sign = xor_sign a.sign b.sign in
      let precision = Bignum.bitwidth x.frac in
      let data = match expn_sum x.expn y.expn with
        | `Overflow_expn -> Inf
        | `Nice expn ->
          let x = extend x (prec a) in
          let y = extend y (prec a) in
          let zfrac = Bignum.(x.frac * y.frac) in
          match align_right (radix a) precision expn zfrac with
          | None -> Inf
          | Some (expn, frac, loss) ->
            let frac = Bignum.extract ~hi:(precision - 1) frac in
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

  let divide base digits start_dividend divisor =
    let set_digit r q pos = Bignum.(r + lshift_frac base q pos) in
    let set_digits digits =
      let init = Bignum.zero (Bignum.bitwidth divisor) in
      List.fold digits ~init
        ~f:(fun data (digit, degree) -> set_digit data digit degree) in
    let rec loop acc dividend degree =
      let dividend, acc =
        if Bignum.(dividend >= divisor) then
          let res = Bignum.(dividend / divisor) in
          let dividend = Bignum.(dividend - res * divisor) in
          dividend, (res,degree) :: acc
        else
          let zero = Bignum.zero (Bignum.bitwidth dividend) in
          let acc = (zero, degree) :: acc in
          dividend, acc in
      let dividend = if dividend < divisor then
          lshift_frac base dividend 1
        else dividend in
      if abs degree < digits then
        loop acc dividend (degree - 1)
      else List.rev acc, dividend in
    let res, left = loop [] start_dividend 0 in
    let res = List.map res ~f:(fun (d, deg) -> d, deg + digits) in
    let res = set_digits res in
    let loss =
      if Bignum.is_zero left then ExactlyZero
      else if Bignum.(left > divisor) then MoreThanHalf
      else if Bignum.(left = divisor) then ExactlyHalf
      else LessThanHalf in
    res, loss

  (* returns a maximum possible exponent for [precision], i.e.
     how many digits could fit in [precision] bits *)
  let digits_of_precision base exp_bits precision =
    let expn, frac =
      safe_align_left base (Bignum.zero exp_bits) (Bignum.one precision) in
    Bignum.to_int expn |> abs

  let expn_dif x y =
    let is_pos = Bignum.is_positive in
    let is_neg = Bignum.is_negative in
    let e = Bignum.(x - y) in
    if is_neg x && is_pos y && Bignum.(e > x) then `Underflow_expn
    else
    if is_pos x && is_neg y && Bignum.(e < x) then `Underflow_expn
    else `Nice e

  let div ?(rm=Nearest_even) a b =
    let zero expn_bits =
      { expn=Bignum.zero expn_bits; frac = Bignum.zero (prec a) } in
    let rec dif xfrac yfrac xexpn yexpn =
      match expn_dif xexpn yexpn with
      | `Underflow_expn -> None
      | `Nice expn when Bignum.(xfrac >= yfrac) -> Some (expn, xfrac)
      | `Nice expn ->
        let xfrac = lshift_frac (radix a) xfrac 1 in
        let one = Bignum.one (bits_in expn) in
        dif xfrac yfrac expn one in
    check_operands a b;
    match a.data,b.data with
    | Fin x, Fin y when is_zero a && is_zero b -> nan ~negative:true a.desc
    | Fin x, Fin y when is_zero b -> {a with data = Inf}
    | Fin x, Fin y ->
      let x = minimize_exponent (radix a) x in
      let y = minimize_exponent (radix a) y in
      let sign = xor_sign a.sign b.sign in
      let xfrac = Bignum.zero_extend x.frac (prec a) in
      let yfrac = Bignum.zero_extend y.frac (prec a) in
      let data = match dif xfrac yfrac x.expn y.expn with
        | None -> zero (bits_in x.expn)
        | Some (expn, xfrac) ->
          let digits = digits_of_precision (radix a) (bits_in expn) (prec a) in
          let frac,loss = divide (radix a) digits xfrac yfrac in
          let frac = round rm sign frac loss in
          let expn = Bignum.(expn - of_int ~width:(bits_in expn) digits) in
          let expn,frac,loss =
            align_right_exn ~base:(radix a) ~precision:(prec a) expn frac in
          let frac = Bignum.extract ~hi:((prec a) - 1) frac in
          let frac = round rm sign frac loss in
          norm (radix a)  {frac; expn} in
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
          Some { a with data }
      end
    | _ ->
      Some a

  let truncate_exn ?(rm=Nearest_even) ~upto a =
    Option.value_exn (truncate ~rm ~upto a)

  let sqrt ?(rm=Nearest_even) a =
    match a.data with
    | Fin x when is_neg a -> nan ~negative:true a.desc
    | Fin x when is_zero a -> a
    | Fin x ->
      let x = minimize_exponent (radix a) x in
      let expn,frac = x.expn, x.frac in
      let frac = Bignum.zero_extend x.frac (prec a) in
      let desc = {a.desc with fbits = 2 * (prec a) } in
      let s = create desc ~expn frac in
      let two = create desc
          ~expn:(Bignum.of_int ~width:desc.ebits 0)
          (Bignum.of_int ~width:desc.fbits 2) in
      let init = div ~rm s two in
      let max = prec a in
      let rec run x0 n =
        if n < max then
          let a1 = div ~rm s x0 in
          let a2 = add ~rm x0 a1 in
          let x' = div ~rm a2 two in
          if equal x0 x' then x0
          else run x' (n + 1)
        else x0 in
      truncate_exn (run init 0) ~upto:(prec a)
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
end
