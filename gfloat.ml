open Core_kernel
open Bap.Std

type sign = Pos | Neg [@@deriving sexp]

type finite = {
  expn : word;
  frac : word;
} [@@deriving sexp]

type value =
  | Inf
  | Nan of bool * word
  | Fin of finite
[@@deriving sexp]

type gfloat = {
  sign : sign;
  base : int;
  prec : int;
  data : value;
}

type rounding =
  | Nearest_even  (** round to nearest, ties to even *)
  | Nearest_away  (** round to nearest, ties to away *)
  | Towards_zero  (** round toward zero              *)
  | Positive_inf  (** round toward positive infinity *)
  | Negative_inf  (** round toward negative infinity *)

type loss =
  | ExactlyZero
  | ExactlyHalf
  | LessThanHalf
  | MoreThanHalf
[@@deriving sexp]

(** digit position from in range [0 .. base - 1] relative to [base/2] *)
type digit = Middle | Less | More | Zero

let enum_bits w =
  let bits = Word.enum_bits w BigEndian in
  let b_len = Seq.length bits in
  let w_len = Word.bitwidth w in
  if b_len > w_len then
    Seq.drop bits (b_len - w_len)
  else bits

let msb w =
  Seq.findi (enum_bits w) ~f:(fun i x -> x) |> function
  | None -> None
  | Some (i,_) -> Some (Word.bitwidth w - i - 1)

let bits_in = Word.bitwidth

(* returns a list of digits in [loss], most significant first *)
let lost_digits base loss n =
  let to_digit x : digit =
    let x = Word.to_int_exn x in
    let middle = base / 2 in
    if Int.(x = middle) then Middle
    else if Int.(x = 0) then Zero
    else if Int.( x < middle ) then Less
    else More in
  let base = Word.of_int base ~width:(Word.bitwidth loss) in
  let rec loop acc loss =
    let loss' = Word.(loss / base) in
    let restored = Word.(loss' * base) in
    let rem = Word.(loss - restored) in
    let acc = (to_digit rem)::acc in
    if Word.is_zero loss' then acc
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

let round rm sign frac loss =
  let is_need = match rm, loss with
    | Positive_inf,_ -> sign = Pos
    | Negative_inf,_ -> sign = Neg
    | Nearest_away, (ExactlyHalf | MoreThanHalf)
    | Nearest_even, MoreThanHalf -> true
    | Nearest_even, ExactlyHalf ->
      Word.is_one (Word.extract_exn ~hi:0 ~lo:0 frac)
    | _ -> false in
  if is_need then
    let all_ones = Word.ones (bits_in frac) in
    if Word.(frac = all_ones) then frac
    else Word.succ frac
  else frac

(* return Some power [n] of [base]: base ** n
   return None if number doesn't fit into [precs]  *)
let pow ~base ~precs n =
  let base = Word.of_int ~width:precs base in
  let rec run r m =
    if m < n then
      let r' = Word.(r * base) in
      if Word.(r' < r) then None
      else run r' (m + 1)
    else Some r in
  if n = 0 then Some (Word.one precs)
  else run base 1

let lshift_frac base frac n =
  if n = 0 then frac
  else
    match pow ~base ~precs:(bits_in frac) n with
    | None -> Word.zero (bits_in frac)
    | Some k -> Word.(frac * k)

let rshift_frac base frac n =
  if n = 0 then frac, ExactlyZero
  else
    match pow ~base ~precs:(bits_in frac) n with
    | None -> Word.zero (bits_in frac), ExactlyZero
    | Some k ->
      if Word.is_zero k then k, ExactlyZero
      else
        let result = Word.(frac / k) in
        let restored = Word.(result * k) in
        result, estimate_loss base Word.(frac - restored) n

(* those functions are unsafe in that sence that there are not
   any checks for exponent overflow *)
let unsafe_lshift base x n =
  let n' = Word.to_int_exn n in
  let expn = Word.(signed (x.expn - n)) in
  { expn; frac = lshift_frac base x.frac n' }

let unsafe_rshift base x n =
  let n' = Word.to_int_exn n in
  let frac, loss = rshift_frac base x.frac n' in
  let expn = Word.signed Word.(x.expn + n) in
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
  let n' = Word.of_int ~width:(bits_in expn) n in
  let expn' = Word.(expn + n') in
  if Word.(expn' < expn) then None
  else
    let res, loss = rshift_frac base frac n in
    Some (Word.signed expn', res, loss)

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
    Word.of_int ~width:(bits_in expn) (max_exponent (bits_in expn)) in
  let rec run expn x =
    let expn' = Word.abs (Word.signed expn) in
    if Word.(expn' = max_expn) then
      expn, x
    else
      match rshift_frac base x 1 with
      | y, ExactlyZero -> run (Word.succ expn) y
      | _ -> expn, x in
  if Word.is_zero frac then expn,frac
  else
    let e,f = run expn frac in
    Word.signed e, f

let safe_align_left base expn frac =
  let min_expn =
    Word.of_int ~width:(bits_in expn) (min_exponent (bits_in expn)) in
  let min_expn = Word.signed min_expn in
  let width = bits_in frac in
  let rec run expn x =
    if Word.(expn = min_expn) then
      expn, x
    else
      let y = lshift_frac base x 1 in
      let z = Word.extract_exn ~lo:width y in
      if Word.is_zero z then run (Word.pred expn) y
      else expn,x in
  if Word.is_zero frac then expn, frac
  else
    let frac = Word.concat (Word.zero width) frac in
    let e,frac = run expn frac in
    let frac = Word.extract_exn ~hi:(width - 1) frac in
    Word.signed e,frac

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

let zero ~radix ~expn_bits prec =
  let min = min_exponent expn_bits in
  let expn = Word.of_int ~width:expn_bits min in
  let frac = Word.zero prec in
  let data = {expn; frac} in
  {sign = Pos; base=radix; data = Fin data; prec }

let create ~radix ?(negative=false) expn frac =
  if Word.is_zero frac then
    zero ~radix ~expn_bits:(bits_in expn) (bits_in frac)
  else
    let sign = if negative then Neg else Pos in
    let expn = Word.signed expn in
    let data = norm radix {expn; frac} in
    let prec = Word.bitwidth frac in
    {sign; base=radix; data = Fin data; prec }

let inf ~radix ?(negative=false) prec =
  let sign = if negative then Neg else Pos in
  {sign; base=radix; prec; data = Inf }

(* mk nan with payload 0100..01 *)
let nan ?(signaling=false) ?(negative=false) ?payload ~radix prec =
  let sign = if negative then Neg else Pos in
  let payload = match payload with
    | Some p -> p
    | None ->
      let payload = Word.one prec in
      let shift = Word.of_int ~width:prec (prec - 2) in
      let payload = Word.(payload lsl shift) in
      Word.(payload + b1) in
  let data = Nan (signaling, payload) in
  {sign; base=radix; prec; data}

let fin t = match t.data with
  | Fin {expn; frac} -> Some (expn,frac)
  | _ -> None

let frac t = match t.data with
  | Fin {frac} -> Some frac
  | Nan (_,frac) -> Some frac
  | _ -> None

let expn t = match t.data with
  | Fin {expn} -> Some expn
  | _ -> None

let is_zero x = match x.data with
  | Fin x -> Word.is_zero x.frac
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

let revert_sign = function
  | Pos -> Neg
  | Neg -> Pos

let word_of_sign = function
  | Pos -> Word.b0
  | Neg -> Word.b1

let xor_sign s s' =
  let r = Word.(word_of_sign s lxor word_of_sign s') in
  if Word.is_one r then Neg else Pos

let invert_loss = function
  | LessThanHalf -> MoreThanHalf
  | MoreThanHalf -> LessThanHalf
  | x -> x

let estimate_spot base x =
  let left  = minimize_exponent base x in
  let right = maximize_exponent base x in
  if Word.(left.expn <> x.expn && right.expn <> x.expn) then `Both
  else if Word.(left.expn <> x.expn) then `Left
  else if Word.(right.expn <> x.expn) then `Right
  else `Nope

let balance base x y =
  match estimate_spot base x, estimate_spot base y with
  | `Left,  _ when Word.(x.expn > y.expn) ->
    minimize_exponent base x, y
  | `Right, _ when Word.(x.expn < y.expn) ->
    maximize_exponent base x, y
  | _, `Left when Word.(x.expn < y.expn) ->
    x, minimize_exponent base y
  | _, `Right when Word.(x.expn > y.expn) ->
    x, maximize_exponent base y
  | _ -> minimize_exponent base x, minimize_exponent base y

(* [combine_loss more_signifincant less_significant]  *)
let combine_loss more less =
  match more, less with
  | _, ExactlyZero -> more
  | ExactlyZero,_ -> LessThanHalf
  | ExactlyHalf,_ -> MoreThanHalf
  | _ -> more

let check_operands a b =
  if Int.(a.base <> b.base) || Int.(a.prec <> b.prec) then
    failwith "attempting to operate with a differrent base/precision"

let neg x = {x with sign = revert_sign x.sign}
let extend x addend = { x with frac = Word.(concat (zero addend) x.frac) }
let extract prec frac = Word.extract_exn ~hi:(prec - 1) frac

let add rm a b =
  let common_ground base x y =
    let x,y = balance base x y in
    let expn = Word.max x.expn y.expn in
    if Word.(x.expn > y.expn) then
      let y, loss = unsafe_rshift base y Word.(expn - y.expn) in
      x, y, loss
    else if Word.(x.expn < y.expn) then
      let x,loss = unsafe_rshift base x Word.(expn - x.expn) in
      x,y,loss
    else x,y, ExactlyZero in
  check_operands a b;
  match a.data, b.data with
  | Fin x, Fin y ->
    let x = maximize_exponent a.base x in
    let y = maximize_exponent a.base y in
    let x,y,loss = common_ground a.base x y in
    let frac = Word.(x.frac + y.frac) in
    let data =
      if Word.(frac >= x.frac) then
        Fin (norm a.base {expn=x.expn; frac=round rm Pos frac loss})
      else
        let x = extend x a.prec in
        let y = extend y a.prec in
        let frac = Word.(x.frac + y.frac) in
        match align_right a.base a.prec x.expn frac with
        | None -> Inf
        | Some (expn, frac, loss') ->
          let loss = if Word.equal x.expn expn then loss
            else combine_loss loss' loss in
          let frac = extract a.prec frac in
          let frac = round rm Pos frac loss in
          Fin (norm a.base {expn; frac}) in
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
    let expn = Word.max x.expn y.expn in
    if Word.(x.expn > y.expn) then
      let x = unsafe_lshift base x Word.b1 in
      let y, loss = unsafe_rshift base y Word.(expn - y.expn - b1) in
      x, y, loss, false
    else if Word.(x.expn < y.expn) then
      let x,loss = unsafe_rshift base x Word.(expn - x.expn - b1) in
      let y = unsafe_lshift base y Word.b1 in
      x,y,loss, true
    else
      x,y, ExactlyZero, Word.(x.frac < y.frac) in
  check_operands a b;
  match a.data, b.data with
  | Fin x, Fin y ->
    let x = minimize_exponent a.base x in
    let y = minimize_exponent a.base y in
    let x = extend x a.prec in
    let y = extend y a.prec in
    let x,y,loss,reverse = common_ground a.base x y in
    let loss = invert_loss loss in
    let borrow = if loss = ExactlyZero then Word.b0 else Word.b1 in
    let frac = if reverse then Word.(y.frac - x.frac - borrow)
      else Word.(x.frac - y.frac - borrow) in
    let sign = if reverse then revert_sign a.sign else a.sign in
    let expn,frac,loss' =
      align_right_exn ~base:a.base ~precision:a.prec x.expn frac in
    let loss = if Word.equal x.expn expn then loss
          else combine_loss loss' loss in
    let frac = Word.extract_exn ~hi:(a.prec - 1) frac in
    let frac = round rm sign frac loss in
    let data = Fin (norm a.base {expn; frac}) in
    {a with data; sign}
  | Nan _, Nan _ -> if is_signaling_nan a || is_quite_nan b then a else b
  | Nan _, _ -> a
  | _, Nan _ -> b
  | Inf, Inf -> nan ~negative:true ~radix:a.base a.prec
  | Inf, _ -> a
  | _, Inf -> b

let add_or_sub rm subtract a b =
  check_operands a b;
  let s1 = Word.of_bool subtract in
  let s2 = word_of_sign a.sign in
  let s3 = word_of_sign b.sign in
  let is_subtract = Word.is_one Word.(s1 lxor (s2 lxor s3)) in
  if is_subtract then sub rm a b
  else add rm a b

let add ?(rm=Nearest_even) = add_or_sub rm false
let sub ?(rm=Nearest_even) = add_or_sub rm true

let expn_sum x y =
  let is_pos = Word.is_positive in
  let is_neg = Word.is_negative in
  let e = Word.(signed (x + y)) in
  if is_pos x && is_pos y && Word.(e < x) then `Overflow_expn
  else
  if is_neg x && is_neg y && Word.(e > x) then `Overflow_expn
  else `Nice e

let mul ?(rm=Nearest_even) a b =
  check_operands a b;
  match a.data,b.data with
  | Fin x, Fin y ->
    let x = minimize_exponent a.base x in
    let y = minimize_exponent a.base y in
    let sign = xor_sign a.sign b.sign in
    let precision = Word.bitwidth x.frac in
    let data = match expn_sum x.expn y.expn with
      | `Overflow_expn -> Inf
      | `Nice expn ->
        let x = extend x a.prec in
        let y = extend y a.prec in
        let zfrac = Word.(x.frac * y.frac) in
        match align_right a.base precision expn zfrac with
        | None -> Inf
        | Some (expn, frac, loss) ->
          let frac = Word.extract_exn ~hi:(precision - 1) frac in
          let frac = round rm sign frac loss in
          Fin (norm a.base { expn; frac}) in
    { a with data; sign }
  | Nan _, Nan _ -> if is_signaling_nan a || is_quite_nan b then a else b
  | Nan _, _ -> a
  | _, Nan _ -> b
  | Inf,  _ when is_zero b -> nan a.base a.prec
  | _, Inf when is_zero a -> nan a.base a.prec
  | Inf, Inf when a.sign = b.sign -> { a with sign = Pos }
  | Inf, Inf when a.sign <> b.sign -> { a with sign = Neg }
  | Inf, _ -> a
  | _, Inf -> b

let divide base digits start_dividend divisor =
  let set_digit r q pos = Word.(r + lshift_frac base q pos) in
  let set_digits digits =
    let init = Word.zero (Word.bitwidth divisor) in
    List.fold digits ~init
      ~f:(fun data (digit, degree) -> set_digit data digit degree) in
  let rec loop acc dividend degree =
    let dividend, acc =
      if Word.(dividend >= divisor) then
        let res = Word.(dividend / divisor) in
        let dividend = Word.(dividend - res * divisor) in
        dividend, (res,degree) :: acc
      else
        let zero = Word.zero (Word.bitwidth dividend) in
        let acc = (zero, degree) :: acc in
        dividend, acc in
    let dividend = if dividend < divisor then
        lshift_frac base dividend 1
      else dividend in
    if abs degree < digits then
      loop acc dividend (degree - 1)
    else List.rev acc, dividend in
  let res, left = loop [] start_dividend 0 in
  let loss =
    if Word.is_zero left then ExactlyZero
    else if Word.(left > divisor) then MoreThanHalf
    else if Word.(left = divisor) then ExactlyHalf
    else LessThanHalf in
  let res = List.map res ~f:(fun (d, deg) -> d, deg + digits) in
  set_digits res, loss

(* returns a maximum possible exponent for [precision], i.e.
   how many digits could fit in [precision] bits *)
let digits_of_precision base exp_bits precision =
  let expn, frac =
    safe_align_left base (Word.zero exp_bits) (Word.one precision) in
  Word.to_int_exn expn |> abs

let expn_dif x y =
  let is_pos = Word.is_positive in
  let is_neg = Word.is_negative in
  let e = Word.(signed (x - y)) in
  if is_neg x && is_pos y && Word.(e > x) then `Underflow_expn
  else
  if is_pos x && is_neg y && Word.(e < x) then `Underflow_expn
  else `Nice e

let string_of_loss a = Sexp.to_string (sexp_of_loss a)

let ws = Word.to_string
let wi = Word.to_int_exn
let wdec = Word.string_of_value ~hex:false

let sb w =
  let bits = enum_bits w in
  let (@@) = sprintf "%s%d" in
  Seq.fold bits ~init:"" ~f:(fun s x ->
      if x then s @@ 1
      else s @@ 0)

let div ?(rm=Nearest_even) a b =
  let zero expn_bits =
    { expn=Word.zero expn_bits; frac = Word.zero a.prec } in
  let rec dif xfrac yfrac xexpn yexpn =
    match expn_dif xexpn yexpn with
    | `Underflow_expn -> None
    | `Nice expn when Word.(xfrac >= yfrac) -> Some (expn, xfrac)
    | `Nice expn ->
      let xfrac = lshift_frac a.base xfrac 1 in
      let one = Word.one (bits_in expn) in
      dif xfrac yfrac expn one in
  check_operands a b;
  match a.data,b.data with
  | Fin x, Fin y when is_zero a && is_zero b -> nan ~negative:true ~radix:a.base a.prec
  | Fin x, Fin y when is_zero b -> {a with data = Inf}
  | Fin x, Fin y ->
    let x = minimize_exponent a.base x in
    let y = maximize_exponent a.base y in
    let sign = xor_sign a.sign b.sign in
    let extend = Word.zero a.prec in
    let xfrac = Word.concat extend x.frac in
    let yfrac = Word.concat extend y.frac in
    let data = match dif xfrac yfrac x.expn y.expn with
      | None -> zero (bits_in x.expn)
      | Some (expn, xfrac) ->
        let expn = Word.signed expn in
        let digits = digits_of_precision a.base (bits_in expn) a.prec in
        let frac,loss = divide a.base digits xfrac yfrac in
        let frac = round rm sign frac loss in
        let expn = Word.signed (Word.(expn - of_int ~width:(bits_in expn) digits)) in
        let expn,frac,loss =
          align_right_exn ~base:a.base ~precision:a.prec expn frac in
        let frac = Word.extract_exn ~hi:(a.prec - 1) frac in
        let frac = round rm sign frac loss in
        let expn = Word.signed expn in
        norm a.base  {frac; expn} in
    {a with data = Fin data; sign; }
  | Nan _, Nan _ -> if is_signaling_nan a || is_quite_nan b then a else b
  | Nan _, _ -> a
  | _, Nan _ -> b
  | Inf, Inf -> nan ~radix:a.base ~negative:true a.prec
  | Inf, _ -> a
  | _, Inf -> b

let truncate ?(rm=Nearest_even) ~upto a = match a.data with
  | Fin {expn; frac} ->
    begin
      match align_right ~base:a.base ~precision:upto expn frac with
      | None -> None
      | Some (expn,frac,loss) ->
        let frac = round rm a.sign frac loss in
        let frac = Word.extract_exn ~hi:(upto - 1) frac in
        let data = Fin { expn; frac} in
        Some { a with data }
    end
  | _ -> Some a

let truncate_exn ?(rm=Nearest_even) ~upto a =
  Option.value_exn (truncate ~rm ~upto a)

let sqrt ?(rm=Nearest_even) a = match a.data with
  | Fin x when is_neg a -> nan ~radix:a.base ~negative:true a.prec
  | Fin x when is_zero a -> a
  | Fin x ->
    let x = minimize_exponent a.base x in
    let expn,frac = x.expn, x.frac in
    let frac = Word.(concat (zero a.prec) x.frac) in
    let s = create ~radix:a.base expn frac in
    let two =
      let expn = Word.zero (bits_in expn) in
      create ~radix:a.base expn (Word.of_int ~width:(bits_in frac) 2) in
    let init = div ~rm s two in
    let max = a.prec in
    let rec run x0 n =
      if n < max then
        let a1 = div ~rm s x0 in
        let a2 = add ~rm x0 a1 in
        let x' = div ~rm a2 two in
        run x' (n + 1)
      else x0 in
    truncate_exn (run init 0) ~upto:a.prec
  | Inf when is_neg a -> nan ~radix:a.base ~negative:true a.prec
  | _ -> a

let equal a b =
  check_operands a b;
  if a.sign <> b.sign then false
  else
    match a.data, b.data with
    | Fin x, Fin y ->
      let x = norm a.base x in
      let y = norm a.base y in
      Word.equal x.expn y.expn &&
      Word.equal x.frac y.frac
    | Inf, Inf -> a.sign = b.sign
    | Nan (s,payload), Nan (s', payload') ->
      Word.equal payload payload' && Bool.equal s s'
    | _ -> false

let round ?(rm=Nearest_even) ~precision a =
  match truncate ~rm ~upto:precision a with
  | Some x -> x
  | None ->
    let negative = a.sign = Neg in
    inf ~negative ~radix:a.base precision

module Infix = struct
  let ( + ) = add ~rm:Nearest_even
  let ( - ) = sub ~rm:Nearest_even
  let ( * ) = mul ~rm:Nearest_even
  let ( / ) = div ~rm:Nearest_even
  let ( = ) = equal
end
