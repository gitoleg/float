open Core_kernel
open Bap.Std

let ws = Word.to_string
let wi = Word.to_int_exn
let wdec = Word.string_of_value ~hex:false

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
  value : value;
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
  let bits = enum_bits w in
  match Seq.findi bits ~f:(fun i x -> x) with
  | None -> None
  | Some (i,_) -> Some (Word.bitwidth w - i - 1)

module Debug = struct
  let string_of_bits w =
    let bits = enum_bits w in
    let (@@) = sprintf "%s%d" in
    Seq.fold bits ~init:"" ~f:(fun s x ->
        if x then s @@ 1
        else s @@ 0)

  let string_of_bits32 w =
    let bits = enum_bits w in
    let (@@) = sprintf "%s%d" in
    Seq.foldi bits ~init:"" ~f:(fun i acc x ->
        let a =
          if i = 1 || i = 9 then "_"
          else "" in
        let s = sprintf "%s%s" acc a in
        if x then s @@ 1
        else s @@ 0)

  let string_of_bits64 w =
    let bits = enum_bits w in
    let (@@) = sprintf "%s%d" in
    Seq.foldi bits ~init:"" ~f:(fun i acc x ->
        let a =
          if i = 1 || i = 12 then "_"
          else "" in
        let s = sprintf "%s%s" acc a in
        if x then s @@ 1
        else s @@ 0)

  let sb = string_of_bits
  let sb32 = string_of_bits32
  let sb64 = string_of_bits64

  let string_of_t t =
    let str_of_sign = function
      | Pos -> ""
      | Neg -> "-" in
    match t.value with
    | Nan _ -> "nan"
    | Fin {expn; frac} ->
      sprintf "%s * %d * %d ^ %d" (str_of_sign t.sign) (wi frac) t.base
        (wi expn)
    | Inf -> sprintf "%sinf" (str_of_sign t.sign)

  let string_of_loss a = Sexp.to_string (sexp_of_loss a)

  let msb_exn x = Option.value_exn (msb x)

  let lsb w =
    let bits = enum_bits w in
    match List.findi (Seq.to_list_rev bits) ~f:(fun i x -> x) with
    | None -> None
    | Some (i,_) -> Some i

  let frac_exn a = match a.value with
    | Fin {frac} -> frac
    | _ -> failwith "frac unavailable"

  let expn_exn a = match a.value with
    | Fin {expn} -> expn
    | _ -> failwith "frac unavailable"

  let data_exn a = match a.value with
    | Fin {expn; frac} -> expn, frac
    | _ -> failwith "data unavailable"

  let str_exn a =
    let e, f = data_exn a in
    sprintf "expn %d, frac %d" (wi e) (wi f)

  let pr_xy pref base x y = match base with
    | 2 ->
      printf "%s:\n  x: %d, %s\n  y: %d, %s\n" pref
        (wi x.expn) (sb x.frac) (wi y.expn) (sb y.frac)
    | _ ->
      printf "%s:\n  x: %d, %s\n  y: %d, %s\n" pref
        (wi x.expn) (wdec x.frac) (wi y.expn) (wdec y.frac)

end

open Debug

let bits_in = Word.bitwidth

(* returns a list of digits in [loss] *)
let loss_digits base loss =
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
  loop [] loss

let estimate_loss base lost_frac n =
  let all_zeros ds =
    List.fold ds ~init:true
      ~f:(fun all d -> if all then d = Zero else all) in
  let loss = loss_digits base lost_frac in
  let loss =
    if List.length loss < n then
      let zeros = List.init (n - List.length loss) (fun _ -> Zero) in
      zeros @ loss
    else loss in
  match loss with
  | [] -> ExactlyZero
  | Zero :: [] -> ExactlyZero
  | Zero :: ds when all_zeros ds -> ExactlyZero
  | Zero :: _ -> LessThanHalf
  | Middle :: ds when all_zeros ds -> ExactlyHalf
  | Middle :: _ -> MoreThanHalf
  | More :: _ -> MoreThanHalf
  | Less :: _ -> LessThanHalf

let round rm sign frac loss =
  let dir = match rm, loss with
    | Positive_inf,_ when sign = Pos -> `Up
    | Positive_inf,_ -> `Down
    | Towards_zero, _ -> `Down
    | Negative_inf,_ when sign = Neg -> `Up
    | Negative_inf,_ -> `Down
    | Nearest_away, (ExactlyHalf | MoreThanHalf) -> `Up
    | Nearest_away, ExactlyZero -> `Down
    | Nearest_away, LessThanHalf -> `Down
    | Nearest_even, MoreThanHalf -> `Up
    | Nearest_even, ExactlyHalf ->
      let is_even = Word.is_zero (Word.extract_exn ~hi:0 ~lo:0 frac) in
      if is_even then `Down
      else `Up
    | Nearest_even, _ -> `Down in
  match dir with
  | `Up ->
    let all_ones = Word.ones (bits_in frac) in
    if Word.(frac = all_ones) then frac
    else Word.succ frac
  | `Down -> frac

let round' rm sign x loss =
  let frac = round rm sign x.frac loss in
  {x with frac}

(* return None if number doesn't fit into [precs]  *)
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

(* TODO: do we really need these conversions from int to word and
   back for n?? *)
let rshift_frac base frac n =
  if n = 0 then frac, ExactlyZero
  else
    match pow ~base ~precs:(bits_in frac) n with
    | None -> Word.zero (bits_in frac), MoreThanHalf
    | Some k ->
      if Word.is_zero k then k, ExactlyZero
      else
        let result = Word.(frac / k) in
        let restored = Word.(result * k) in
        result, estimate_loss base Word.(frac - restored) n

let lshift base x n =
  let n' = Word.(signed (of_int ~width:(bits_in x.frac) n)) in
  let expn = Word.(signed (x.expn - n')) in
  { expn; frac = lshift_frac base x.frac n }

let rshift base x n =
  let n' = Word.signed n in
  let n = Word.to_int_exn n' in
  let frac, loss = rshift_frac base x.frac n in
  let expn = Word.signed Word.(x.expn + n') in
  { expn; frac }, loss

(* [align_right base precision expn frac]
   shifts frac right with a possible loss of bits in order to keep
   most significant bits. It assumes [bitwidth frac > precision].
   Returns [Some (expn, frac, loss)], if no exponent overflow occured,
   [None] otherwise. *)
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

(* TODO: check how comparison for min_expn is done *)
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

let norm = maximize_exponent

let mk ~base sign expn frac =
  let expn = Word.signed expn in
  let value = norm base {expn; frac} in
  let prec = Word.bitwidth frac in
  {sign; base; value = Fin value; prec }

let mk_inf ~base prec sign = {sign; base; prec; value = Inf }

(* mk nan with payload 1 *)
let mk_nan ?(signaling=false) ?(sign=Pos) ~base prec =
  let value = Nan (signaling, Word.one prec) in
  {sign; base; prec; value}

let is_zero x = match x.value with
  | Fin x -> Word.is_zero x.frac
  | _ -> false

let is_inf x = match x.value with
  | Inf -> true
  | _ -> false

let is_nan x = match x.value with
  | Nan _ -> true
  | _ -> false

let is_finite x = match x.value with
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

(*  TODO:
    is it guaranteed that common_ground returns a correct values??
    i.e. with an equal exponent. Because safe_align stops in
    case max exponent achieved *)
let common_ground ?(subtract=false) base x y =
  let x,y = balance base x y in
  let expn = Word.max x.expn y.expn in
  if Word.(x.expn > y.expn) then
    let y, loss = rshift base y Word.(expn - y.expn) in
    let loss = if subtract then invert_loss loss else loss in
    x, y, loss
  else if Word.(x.expn < y.expn) then
    let x,loss = rshift base x Word.(expn - x.expn) in
    x,y,loss
  else x,y, ExactlyZero

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
  check_operands a b;
  match a.value, b.value with
  | Fin x, Fin y ->
    let x,y,loss = common_ground a.base x y in
    let frac = Word.(x.frac + y.frac) in
    let value =
      if Word.(frac >= x.frac) then
        Fin (norm a.base {expn=x.expn; frac=round rm Pos frac loss})
      else
        let x = extend x a.prec in
        let y = extend y a.prec in
        let frac = Word.(x.frac + y.frac) in
        match align_right a.base a.prec x.expn frac with
        | None -> Inf
        | Some (expn, frac, loss') ->
          let loss = combine_loss loss' loss in
          let frac = extract a.prec frac in
          let frac = round rm Pos frac loss in
          Fin (norm a.base {expn; frac}) in
    { a with value }
  | Nan _, _ -> a
  | _, Nan _ -> b
  | Inf, Inf when is_neg a && is_pos b -> a
  | Inf, Inf when is_pos a && is_neg b -> a
  | Inf, _ -> a
  | _, Inf -> b


let common_ground2 ?(subtract=false) base x y =
  (* let x,y = balance base x y in *)
  let expn = Word.max x.expn y.expn in
  if Word.(x.expn > y.expn) then
    let () = printf "case 1\n" in
    let y, loss = rshift base y Word.(expn - y.expn - b1) in
    let x = lshift base x 1 in
    x, y, loss, false
  else if Word.(x.expn < y.expn) then
    let () = printf "case 2\n" in
    let y = lshift base y 1 in
    let x,loss = rshift base x Word.(expn - x.expn - b1) in
    x,y,loss, true
  else
    x,y, ExactlyZero, Word.(x.frac < y.frac)

let common_ground3 ?(subtract=false) base x y =
  let expn = Word.max x.expn y.expn in
  if Word.(x.expn > y.expn) then
    let y, loss = rshift base y Word.(expn - y.expn) in
    x, y, loss, false
  else if Word.(x.expn < y.expn) then
    let x,loss = rshift base x Word.(expn - x.expn) in
    x,y,loss, true
  else
    x,y, ExactlyZero, Word.(x.frac < y.frac)

let sub rm a b =
  check_operands a b;
  match a.value, b.value with
  | Fin x, Fin y ->
    let x = minimize_exponent a.base x in
    let y = minimize_exponent a.base y in
    let x = extend x 1 in
    let y = extend y 1 in
    pr_xy "\ninput" a.base x y;
    let x,y,loss,reverse = common_ground2 ~subtract:true a.base x y in
    let loss = invert_loss loss in
    let borrow = loss <> ExactlyZero in
    pr_xy "common"  a.base x y;
    printf "borrow? %b, reverse? %b, loss: %s\n" borrow reverse (string_of_loss loss);
    let borrow = if loss = ExactlyZero then Word.b0 else Word.b1 in
    let frac = if reverse then Word.(y.frac - x.frac - borrow)
      else Word.(x.frac - y.frac - borrow) in
    printf "%s <-- exactly subtracted\n" (sb frac);
    let sign = if reverse then revert_sign a.sign else a.sign in
    printf "before rounding %s %s\n" (sb frac) (string_of_loss loss);

    let aa = match
        align_right ~base:a.base ~precision:a.prec x.expn frac with
    | None -> printf "will do it one day. TODO!\n"
    | Some (expn, frac, loss') ->

      printf "maybe frac is %s\n" (sb frac) in
      (* let loss = combine_loss loss' loss in *)

    (* let frac = round rm sign frac loss in *)
    (* let value = {expn=x.expn; frac} in *)
    let value = minimize_exponent a.base {expn=x.expn; frac} in
    let value = round' rm sign value loss in
    printf "after  rounding %s\n" (sb value.frac);
    let value = Fin value in
    {a with value; sign}
  | Nan _, _ -> a
  | _, Nan _ -> b
  | Inf, Inf -> mk_nan ~sign:Neg ~base:a.base a.prec
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
  match a.value,b.value with
  | Fin x, Fin y ->
    let x = minimize_exponent a.base x in
    let y = minimize_exponent a.base y in
    let sign = xor_sign a.sign b.sign in
    let precision = Word.bitwidth x.frac in
    let value = match expn_sum x.expn y.expn with
      | `Overflow_expn -> Inf
      | `Nice expn ->
        let zeros = Word.zero precision in
        let xfrac = Word.concat zeros x.frac in
        let yfrac = Word.concat zeros y.frac in
        let zfrac = Word.(xfrac * yfrac) in
        match align_right a.base precision expn zfrac with
        | None -> Inf
        | Some (expn, frac, loss) ->
          let frac = Word.extract_exn ~hi:(precision - 1) frac in
          let frac = round rm sign frac loss in
          Fin (norm a.base { expn; frac}) in
    { a with value; sign }
  | Nan _, _ -> a
  | _, Nan _ -> b
  | Inf,  _ when is_zero b -> mk_nan a.base a.prec
  | _, Inf when is_zero a -> mk_nan a.base a.prec
  | Inf, Inf when a.sign = b.sign -> { a with sign = Pos }
  | Inf, Inf when a.sign <> b.sign -> { a with sign = Neg }
  | Inf, _ -> a
  | _, Inf -> b

(* extra digits that will be used for rounding  *)
let division_extra_digits = 3

(** [divide base digits start_dividend divisor]
    performs division according to the next sum:
          n
      q = Σ  q_i * B ^ -i
         i=0
    where B is a base, and q_i ⋲ {0 .. B - 1}
    Returns two integers: first is a result of division,
    that could be represented in [abs min_degree] digits
    and a second is few next digits for rounding purposes.
    Precondition: dividend > divisor *)
let divide base digits start_dividend divisor =
  let set_digit r q pos = Word.(r + lshift_frac base q pos) in
  let set_digits digits =
    let init = Word.zero (Word.bitwidth divisor) in
    List.fold digits ~init
      ~f:(fun value (digit, degree) -> set_digit value digit degree) in
  let digits' = digits + division_extra_digits in
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
    if abs degree < digits' then
      let dividend = if dividend < divisor then
          lshift_frac base dividend 1
        else dividend in
      loop acc dividend (degree - 1)
    else List.rev acc in
  let res = loop [] start_dividend 0 in
  let res, last = List.split_n res (digits + 1) in
  let res = List.map res ~f:(fun (d, deg) -> d, deg + digits) in
  let last = List.map (List.rev last)
      ~f:(fun (d, deg) -> d, deg + digits') in
  set_digits res, set_digits last

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

let div ?(rm=Nearest_even) a b =
  let mk_zero expn_bits =
    { expn=Word.zero expn_bits; frac = Word.zero a.prec } in
  (* TODO: check this function, it's called rec more than once! *)
  let rec dif xfrac yfrac xexpn yexpn =
    match expn_dif xexpn yexpn with
    | `Underflow_expn -> None
    | `Nice expn when Word.(xfrac >= yfrac) -> Some (expn, xfrac)
    | `Nice expn ->
      let xfrac = lshift_frac a.base xfrac 1 in
      let one = Word.one (bits_in expn) in
      dif xfrac yfrac expn one in
  check_operands a b;
  match a.value,b.value with
  | Fin x, Fin y when is_zero a && is_zero b -> mk_nan ~sign:Neg ~base:a.base a.prec
  | Fin x, Fin y when is_zero b -> {a with value = Inf}
  | Fin x, Fin y ->
    let x = minimize_exponent a.base x in
    let y = maximize_exponent a.base y in
    let sign = xor_sign a.sign b.sign in
    let extend = Word.zero a.prec in
    let xfrac = Word.concat extend x.frac in
    let yfrac = Word.concat extend y.frac in
    let value = match dif xfrac yfrac x.expn y.expn with
      | None -> mk_zero (bits_in x.expn)
      | Some (expn, xfrac) ->
        let expn = Word.signed expn in
        let digits = digits_of_precision a.base (bits_in expn) a.prec in
        let frac,last = divide a.base digits xfrac yfrac in
        let loss = estimate_loss a.base last division_extra_digits in
        let frac = round rm sign frac loss in
        let expn = Word.signed (Word.(expn - of_int ~width:(bits_in expn) digits)) in
        let expn,frac, loss =
          align_right_exn ~base:a.base ~precision:a.prec expn frac in
        let frac = Word.extract_exn ~hi:(a.prec - 1) frac in
        let frac = round rm sign frac loss in
        let expn = Word.signed expn in
        norm a.base  {frac; expn} in
    {a with value = Fin value; sign; }
  | Nan _, _ -> a
  | _, Nan _ -> b
  | Inf, Inf -> mk_nan ~base:a.base ~sign:Neg a.prec
  | Inf, _ -> a
  | _, Inf -> b

let truncate ?(rm=Nearest_even) a upto = match a.value with
  | Fin {expn; frac} ->
    begin
      match align_right ~base:a.base ~precision:upto expn frac with
      | None -> None
      | Some (expn,frac,loss) ->
        let frac = round rm a.sign frac loss in
        let frac = Word.extract_exn ~hi:(upto - 1) frac in
        let value = Fin { expn; frac} in
        Some { a with value }
    end
  | _ -> Some a

let truncate_exn ?(rm=Nearest_even) a upto =
  Option.value_exn (truncate ~rm a upto)

let sqrt ?(rm=Nearest_even) a = match a.value with
  | Fin x when is_neg a -> mk_nan ~base:a.base ~sign:Neg a.prec
  | Fin x when is_zero a -> a
  | Fin x ->
    let x = minimize_exponent a.base x in
    let expn,frac = x.expn, x.frac in
    let frac = Word.(concat (zero a.prec) x.frac) in
    let s = mk ~base:a.base Pos expn frac in
    let two =
      let expn = Word.zero (bits_in expn) in
      mk ~base:a.base Pos expn (Word.of_int ~width:(bits_in frac) 2) in
    let init = div ~rm s two in
    let max = a.prec in
    let rec run x0 n =
      if n < max then
        let a1 = div ~rm s x0 in
        let a2 = add ~rm x0 a1 in
        let x' = div ~rm a2 two in
        run x' (n + 1)
      else x0 in
    truncate_exn (run init 0) a.prec
  | Inf when is_neg a -> mk_nan ~base:a.base ~sign:Neg a.prec
  | _ -> a

let largest ~base expn_bits prec =
  let expn = Word.(ones expn_bits lsr b1) in
  let frac = Word.ones prec in
  {base; sign = Pos; prec; value = Fin {expn; frac} }

let least ~base expn_bits prec =
  let expn = Word.(ones expn_bits lsr b1) in
  let expn = Word.neg expn in
  let frac = Word.one prec in
  {base; sign = Pos; prec; value = Fin {expn; frac} }
