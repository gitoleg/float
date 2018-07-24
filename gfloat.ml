open Core_kernel
open Bap.Std

let ws = Word.to_string
let wi = Word.to_int_exn
let wdec = Word.string_of_value ~hex:false

type sign = Pos | Neg [@@deriving sexp]

type finite = {
  sign : sign;
  expn : word;
  frac : word;
} [@@deriving sexp]

type value =
  | Inf of sign
  | Nan of bool * word
  | Fin of finite
[@@deriving sexp]

type gfloat = {
  radix : int;
  precs : int;
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

(* digit position from in range [0 .. radix - 1] relative to [radix/2] *)
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
    | Fin {sign; expn; frac} ->
      sprintf "%s * %d * %d ^ %d" (str_of_sign sign) (wi frac) t.radix
        (wi expn)
    | Inf s -> sprintf "%sinf" (str_of_sign s)

  let string_of_loss a = Sexp.to_string (sexp_of_loss a)

  let msb_exn x = Option.value_exn (msb x)

  let lsb w =
    let bits = enum_bits w in
    match List.findi (Seq.to_list_rev bits) ~f:(fun i x -> x) with
    | None -> None
    | Some (i,_) -> Some i
end

open Debug

(* returns a list of digits in [loss] in [radix] *)
let loss_digits radix loss =
  let radix = Word.of_int radix ~width:(Word.bitwidth loss) in
  let rec loop acc loss =
    let loss' = Word.(loss / radix) in
    let restored = Word.(loss' * radix) in
    let digit = Word.(loss - restored) in
    let acc = digit::acc in
    if Word.is_zero loss' then acc
    else loop acc loss' in
  loop [] loss

let estimate_loss radix lost_frac n =
  let all_zeros ds =
    List.fold ds ~init:true
      ~f:(fun all d -> if all then d = Zero else all) in
  let norm_digit x : digit =
    let x = Word.to_int_exn x in
    let middle = radix / 2 in
    if Int.(x = middle) then Middle
    else if Int.(x = 0) then Zero
    else if Int.( x < middle ) then Less
    else More in
  let loss = loss_digits radix lost_frac |> List.map ~f:norm_digit in
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

(* TODO: what if round overflow ??  *)
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
  | `Up -> Word.succ frac
  | `Down -> frac

let pow ~radix n =
  let rec run r m =
    if m < n then run (r * radix) (m + 1)
    else r in
  if n = 0 then 1
  else run radix 1

let bits_in = Word.bitwidth

(* return None if number doesn't fit into [precs]  *)
let pow' ~radix ~precs n =
  let radix = Word.of_int ~width:precs radix in
  let rec run r m =
    if m < n then
      let r' = Word.(r * radix) in
      if Word.(r' < r) then None
      else run r' (m + 1)
    else Some r in
  if n = 0 then Some (Word.one precs)
  else run radix 1

let lshift_frac radix frac n =
  if n = 0 then frac
  else
    match pow' ~radix ~precs:(bits_in frac) n with
    | None -> Word.zero (bits_in frac)
    | Some k -> Word.(frac * k)


(* TODO: do we really need these conversions from int to word and
   back for n?? *)
let rshift_frac radix frac n =
  if n = 0 then frac, ExactlyZero
  else
    match pow' ~radix ~precs:(bits_in frac) n with
    | None -> Word.zero (bits_in frac), MoreThanHalf
    | Some k ->
      if Word.is_zero k then k, ExactlyZero
      else
        let result = Word.(frac / k) in
        let restored = Word.(result * k) in
        result, estimate_loss radix Word.(frac - restored) n

let lshift radix x n =
  let n' = Word.(signed (of_int ~width:(bits_in x.frac) n)) in
  let expn = Word.(signed (x.expn - n')) in
  { x with expn; frac = lshift_frac radix x.frac n }

let rshift radix x n =
  let n' = Word.signed n in
  let n = Word.to_int_exn n' in
  let frac, loss = rshift_frac radix x.frac n in
  let expn = Word.signed Word.(x.expn + n') in
  { x with expn; frac }, loss

let word_of_sign = function
  | Pos -> Word.b0
  | Neg -> Word.b1

(* [align_right radix precision expn frac]
   shifts frac right with a possible loss of bits in order to keep
   most significant bits. It assumes [bitwidth frac > precision].
   Returns [Some (expn, frac, loss)], if no exponent overflow occured,
   [None] otherwise. *)
let align_right ~radix ~precision expn frac =
  let rec run n frac =
    match msb frac with
    | None -> n
    | Some i when i < precision -> n
    | _ -> run (n + 1) (fst (rshift_frac radix frac 1)) in
  let n = run 0 frac in
  let n' = Word.of_int ~width:(bits_in expn) n in
  let expn' = Word.(expn + n') in
  if Word.(expn' < expn) then None
  else
    let res, loss = rshift_frac radix frac n in
    Some (expn', res, loss)

(* maximum possible exponent that fits in [n] signed bits *)
let max_exponent n = pow ~radix:2 (n - 1) - 1
let min_exponent n = - (max_exponent n)

(* the same as [align_right] above, but stops in case of bits loss
   OR if exponent reached a maximum of it's value *)
let safe_align_right radix expn frac =
  let max_expn =
    Word.of_int ~width:(bits_in expn) (max_exponent (bits_in expn)) in
  let rec run expn x =
    let expn' = Word.abs (Word.signed expn) in
    if Word.(expn' = max_expn) then
      expn, x
    else
      match rshift_frac radix x 1 with
      | y, ExactlyZero -> run (Word.succ expn) y
      | _ -> expn, x in
  if Word.is_zero frac then expn,frac
  else
    let e,f = run expn frac in
    Word.signed e, f

(* TODO: check how comparison for min_expn is done *)
let safe_align_left radix expn frac =
  let min_expn =
    Word.of_int ~width:(bits_in expn) (min_exponent (bits_in expn)) in
  let min_expn = Word.signed min_expn in
  let width = bits_in frac in
  let rec run expn x =
    if Word.(expn = min_expn) then
      expn, x
    else
      let y = lshift_frac radix x 1 in
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
let minimize_exponent radix x =
  let expn, frac = safe_align_left radix x.expn x.frac in
  { x with expn; frac }

(* max exponent without bit loss or exponent overflow,
   fraction shifted as right as possible, i.e. it occupies
   less significant bits *)
let maximize_exponent radix x =
  let expn, frac = safe_align_right radix x.expn x.frac in
  { x with expn; frac }

let norm = maximize_exponent

let mk ~radix sign expn frac =
  let expn = Word.signed expn in
  let value = norm radix {sign; expn; frac} in
  let precs = Word.bitwidth frac in
  {radix; value = Fin value; precs }

let mk_inf ~radix precs sign = {radix; precs; value = Inf sign}

(* mk nan with payload 1 *)
let mk_nan ?(signaling=false) ~radix precs =
  let value = Nan (signaling, Word.one precs) in
  {radix; precs; value}

let is_zero x = match x.value with
  | Fin x -> Word.is_zero x.frac
  | _ -> false

let is_inf x = match x.value with
  | Inf _ -> true
  | _ -> false

let is_nan x = match x.value with
  | Nan _ -> true
  | _ -> false

let is_finite x = match x.value with
  | Fin _ -> true
  | _ -> false

let is_pos x = match x.value with
  | Fin {sign}
  | Inf sign -> sign = Pos
  | _ -> false

let is_neg x = match x.value with
  | Fin {sign}
  | Inf sign -> sign = Neg
  | _ -> false

let revert_sign = function
  | Pos -> Neg
  | Neg -> Pos

let xor_sign s s' =
  let r = Word.(word_of_sign s lxor word_of_sign s') in
  if Word.is_one r then Neg else Pos

let invert_loss = function
  | LessThanHalf -> MoreThanHalf
  | MoreThanHalf -> LessThanHalf
  | x -> x



let estimate_spot radix x =
  let left  = minimize_exponent radix x in
  let right = maximize_exponent radix x in
  if Word.(left.expn <> x.expn && right.expn <> x.expn) then `Both
  else if Word.(left.expn <> x.expn) then `Left
  else if Word.(right.expn <> x.expn) then `Right
  else `Nope

let balance radix x y =
  match estimate_spot radix x, estimate_spot radix y with
  | `Left,  _ when Word.(x.expn > y.expn) ->
    minimize_exponent radix x, y
  | `Right, _ when Word.(x.expn < y.expn) ->
    maximize_exponent radix x, y
  | _, `Left when Word.(x.expn < y.expn) ->
    x, minimize_exponent radix y
  | _, `Right when Word.(x.expn > y.expn) ->
    x, maximize_exponent radix y
  | _ -> minimize_exponent radix x, minimize_exponent radix y

(*  TODO:
    is it guaranteed that common_ground returns a correct values,
    i.e. with an equal exponent. Because safe_align stops in
    case max exponent achieved *)
let common_ground ?(subtract=false) radix x y =
  let x,y = balance radix x y in
  (* if Word.is_positive x.expn && Word.is_negative y.expn then *)
  (*   minimize_exponent radix x, maximize_exponent radix y *)
  (* else if Word.is_negative x.expn && Word.is_positive y.expn then *)
  (*   maximize_exponent radix x, minimize_exponent radix y *)
  (* else x, y in *)

  let expn = Word.max x.expn y.expn in
  if Word.(x.expn > y.expn) then
    let y, loss = rshift radix y Word.(expn - y.expn) in
    let loss = if subtract then invert_loss loss else loss in
    x, y, loss
  else if Word.(x.expn < y.expn) then
    let x,loss = rshift radix x Word.(expn - x.expn) in
    x,y,loss
  else x,y, ExactlyZero

let combine_loss more less =
  match more, less with
  | _, ExactlyZero -> more
  | ExactlyZero,_ -> LessThanHalf
  | ExactlyHalf,_ -> MoreThanHalf
  | _ -> more


let add rm radix x y =
  (* printf "add input: %d, %d + %d, %d\n" (wi x.expn) (wi x.frac) (wi y.expn) (wi y.frac); *)
  (* let x = minimize_exponent radix x in *)
  (* let y = minimize_exponent radix y in *)
  (* printf "add minim: %d, %d + %d, %d\n" (wi x.expn) (wi x.frac) (wi y.expn) (wi y.frac); *)
  let x,y,loss = common_ground radix x y in

  (* printf "add common: %d, %d; %d, %d\n" (wi x.expn) (wi x.frac) (wi y.expn) (wi y.frac); *)

  let frac = Word.(x.frac + y.frac) in
  let result =
    if Word.(frac >= x.frac) then Some (x.expn, frac, loss)
    else
      let width = Word.bitwidth x.frac in
      let extend = Word.zero width in
      let xfrac = Word.concat extend x.frac in
      let yfrac = Word.concat extend y.frac in
      let frac = Word.(xfrac + yfrac) in
      match align_right radix width x.expn frac with
      | None -> None
      | Some (expn, frac, loss') ->
        let loss = combine_loss loss' loss in
        Some (expn,Word.extract_exn ~hi:(width - 1) frac, loss) in
  match result with
  | None -> Inf x.sign
  | Some (expn, frac, loss) ->
    let frac = round rm x.sign frac loss in
    let r = {sign = x.sign; expn; frac} in
    Fin (norm radix r)

let sub rm radix x y =
  let x,y,loss = common_ground ~subtract:true radix x y in
  let sign, frac =
    if Word.(x.frac < y.frac) then
      revert_sign x.sign, Word.(y.frac - x.frac)
    else x.sign, Word.(x.frac - y.frac) in
  let frac = round rm sign frac loss in
  let r = { sign; expn=x.expn; frac } in
  Fin (norm radix r)

let add_or_sub rm subtract a b = match a.value,b.value with
  | Fin x, Fin y ->
    let s1 = Word.of_bool subtract in
    let s2 = word_of_sign x.sign in
    let s3 = word_of_sign y.sign in
    let is_subtract = Word.is_one Word.(s1 lxor (s2 lxor s3)) in
    let value =
      if is_subtract then sub rm a.radix x y
      else add rm a.radix x y in
    {a with value}
  | Nan _, _ | Inf _, _ -> a
  | _, Nan _ | _, Inf _ -> b

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

(* TODO: why do we extending to precision + 1? *)
let mul ?(rm=Nearest_even) a b = match a.value,b.value with
  | Fin x, Fin y ->
    let x = minimize_exponent a.radix x in
    let y = minimize_exponent a.radix y in
    let sign = xor_sign x.sign y.sign in
    let precision = Word.bitwidth x.frac in
    let value = match expn_sum x.expn y.expn with
      | `Overflow_expn -> Inf sign
      | `Nice expn ->
        let zeros = Word.zero (precision + 1) in
        let xfrac = Word.concat zeros x.frac in
        let yfrac = Word.concat zeros y.frac in
        let zfrac = Word.(xfrac * yfrac) in
        match align_right a.radix precision expn zfrac with
        | None -> Inf sign
        | Some (expn, frac, loss) ->
          let frac = Word.extract_exn ~hi:(precision - 1) frac in
          let frac = round rm sign frac loss in
          Fin (norm a.radix {sign; expn; frac}) in
    { a with value }
  | Nan _, _ -> a
  | _, Nan _ -> b
  | Inf _, _ when is_zero b -> mk_nan a.radix a.precs
  | _, Inf _ when is_zero a -> mk_nan a.radix a.precs
  | Inf _, _ -> a
  | _, Inf _ -> b

(* extra digits that will be used for rounding  *)
let division_extra_digits = 3

(** [divide radix digits start_dividend divisor]
    performs division according to the next sum:
          n
      q = Σ  q_i * B ^ -i
         i=0
    where B is a radix, and q_i ⋲ {0 .. B - 1}
    Returns two integers: first is a result of division,
    that could be represented in [abs min_degree] digits
    and a second is few next digits for rounding purposes.
    Precondition: dividend > divisor *)
let divide radix digits start_dividend divisor =
  let set_digit r q pos = Word.(r + lshift_frac radix q pos) in
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
          lshift_frac radix dividend 1
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
let digits_of_precision radix exp_bits precision =
  let expn, frac =
    safe_align_left radix (Word.zero exp_bits) (Word.one precision) in
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
    { sign=Pos; expn=Word.zero expn_bits; frac = Word.zero a.precs } in
  let rec dif xfrac yfrac xexpn yexpn =
    match expn_dif xexpn yexpn with
    | `Underflow_expn -> None
    | `Nice expn when Word.(xfrac >= yfrac) -> Some (expn, xfrac)
    | `Nice expn ->
      let xfrac = lshift_frac a.radix xfrac 1 in
      let one = Word.one (bits_in expn) in
      dif xfrac yfrac expn one in
  match a.value,b.value with
  | Fin x, Fin y when is_zero a && is_zero b -> mk_nan ~radix:a.radix a.precs
  | Fin x, Fin y when is_zero b -> {a with value = Inf x.sign}
  | Fin x, Fin y ->
    let x = minimize_exponent a.radix x in
    let y = maximize_exponent a.radix y in

    printf "  div input x: %s, %s\n" (wdec x.expn) (wdec x.frac);
    printf "  div input y: %s, %s\n" (wdec y.expn) (wdec y.frac);

    let sign = xor_sign x.sign y.sign in
    let extend = Word.zero a.precs in
    let xfrac = Word.concat extend x.frac in
    let yfrac = Word.concat extend y.frac in
    let value = match dif xfrac yfrac x.expn y.expn with
      | None ->
        printf "  div output zero!\n\n";
        mk_zero (bits_in x.expn)
      | Some (expn, xfrac) ->
        let expn = Word.signed expn in
        let digits = digits_of_precision a.radix (bits_in expn) a.precs in

        printf "divide %s(%d) / %s(%d) = "
          (sb xfrac) (msb_exn xfrac) (sb yfrac) (msb_exn yfrac);

        let frac,last = divide a.radix digits xfrac yfrac in
        printf "%s\n%!" (wdec frac);

        printf "msb %d/%d\n" (msb_exn frac) (bits_in frac);

        let loss = estimate_loss a.radix last division_extra_digits in
        let frac = round rm sign frac loss in
        printf "expn is %d %d\n" (wi expn) digits;
        let expn = Word.signed (Word.(expn - of_int ~width:(bits_in expn) digits)) in
        printf "expn is %d\n" (wi expn);
        match align_right ~radix:a.radix ~precision:a.precs expn frac with
        | None -> mk_zero (bits_in x.expn) (* TODO: think here  *)
        | Some (expn,frac,loss) ->
          (* let expn,frac,loss = align_right ~radix:a.radix ~precs:a.precs expn frac in *)
          (* let expn,frac = safe_align_right a.radix expn frac in *)
          (* printf "  align: %s (msb %d) (%d %d)\n" (wdec frac) (msb_exn frac) (bits_in frac) (a.precs); *)
          let frac = Word.extract_exn ~hi:(a.precs - 1) frac in
          printf "  extract: %s\n" (wdec frac);
          let frac = round rm sign frac loss in
          let expn = Word.signed expn in
          let value = norm a.radix  {sign; frac; expn} in
          (* printf "  div output:  %d, %d\n\n" (wi value.expn) (wi value.frac); *)
          value  in
    {a with value = Fin value }
  | Nan _, _ -> a
  | _, Nan _ -> b
  | Inf _, _ -> a
  | _, Inf _ -> b

let pow10 precs n =
  let w = bits_in n in
  let ten = Word.of_int ~width:w 10 in
  let rec run x i =
    if Word.(i < n) then
      run Word.(x * ten) (Word.succ i)
    else x in
  if Word.is_zero n then Word.one precs
  else run ten (Word.one w)


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

let sqrt ?(rm=Nearest_even) a =
  let truncate x = match x.value with
    | Fin {sign; expn; frac} ->
      begin
        match align_right ~radix:a.radix ~precision:a.precs expn frac with
        | None -> failwith "todo"
        | Some (expn, frac, loss) ->
          let frac = round rm sign frac loss in
          let frac = Word.extract_exn ~hi:(a.precs - 1) frac in
          let value = Fin {sign; expn; frac} in
          { a with value }
      end
    | _ -> x in
  match a.value with
  | Fin x ->
    let x = minimize_exponent a.radix x in
    let expn,frac = x.expn, x.frac in
    let frac = Word.(concat (zero a.precs) x.frac) in
    let s = mk ~radix:a.radix Pos expn frac in
    let two =
      let expn = Word.zero (bits_in expn) in
      mk ~radix:a.radix Pos expn (Word.of_int ~width:(bits_in frac) 2) in
    let () = printf "op 1 \n%!" in
    let init = div ~rm s two in
    let () = printf "op 1 finished\n%!" in
    let max = 15 in
    let rec run x0 n =
      if n < max then
        let a1 = div ~rm s x0 in
        let a2 = add ~rm x0 a1 in
        (* printf "sum (%s) (%s) = %s\n" *)
        (*   (str_exn x0) (str_exn a1) (str_exn a2); *)
        let x' = div ~rm a2 two in
        (* printf "###%d: %s --> %s\n\n" n (str_exn x0) (str_exn x'); *)
        run x' (n + 1)
      else x0 in
    truncate (run init 0)
  | _ -> failwith "TODO"
