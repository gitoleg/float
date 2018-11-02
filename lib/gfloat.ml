open Core_kernel

let allow_output = ref false

let printf fmt =
  let doit str =
    if !allow_output then
      printf "%s" str in
  ksprintf doit fmt


module Debug = struct
  open Bap.Std

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
    let w = Word.of_int64 x in
    let bits = enum_bits w in
    let (@@) = sprintf "%s%d" in
    Seq.foldi bits ~init:"" ~f:(fun i acc x ->
        let a =
          if i = 1 || i = 12 then "_"
          else "" in
        let s = sprintf "%s%s" acc a in
        if x then s @@ 1
        else s @@ 0)

  let bits_of_z bits z =
    let w = Word.of_int64 ~width:bits (Z.to_int64 z) in
    string_of_bits w

end

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
[@@deriving sexp]

(** digit position from in range [0 .. base - 1] relative to [base/2] *)
type digit = Middle | Less | More | Zero

type sign = Pos | Neg [@@deriving sexp]

type desc = {
  radix : int;
  ebits : int;
  fbits : int;
}

let desc ~radix ~expn_bits fbits = {radix; fbits; ebits=expn_bits}

let string_of_loss s = Sexp.to_string (sexp_of_loss s)

module type Bignum = sig
  type t
  val of_int : width:int -> int -> t
  val to_int : t -> int
  val ones : int -> t
  val bitwidth : t -> int
  val extract : ?hi:int -> ?lo:int -> t -> t
  val testbit : t -> int -> bool
  val zero_extend : t -> int -> t
  val ( + ) : t -> t -> t
  val ( - ) : t -> t -> t
  val ( * ) : t -> t -> t
  val ( / ) : t -> t -> t
  val ( = ) : t -> t -> bool
  val ( < ) : t -> t -> bool
  val ( lsl ) : t -> int -> t
  val ( lxor ) : t -> t -> t
  val lnot : t -> t
  val to_string : t -> string             (* TODO: TEMP!  *)
  val tow : t -> Bap.Std.word
end

module Make(Bignum : Bignum) = struct

  type bignum = Bignum.t

  module Bignum = struct

    let msb x = Bignum.testbit x (Bignum.bitwidth x - 1)

    include Bignum

    let b0 = of_int ~width:1 0
    let b1 = of_int ~width:1 1

    let of_sign = function
      | Pos -> b0
      | Neg -> b1

    let of_bool = function
      | true -> b1
      | false -> b0

    let one width = of_int ~width 1
    let zero width = of_int ~width 0

    let is_one x = x = one (bitwidth x)
    let is_zero x = x = zero (bitwidth x)

    let succ x = x + one (bitwidth x)
    let pred x = x - one (bitwidth x)

    let ( > ) x y = y < x
    let ( <= ) x y = x < y || x = y
    let ( >= ) x y = x > y || x = y

    let ( <$ ) x y =
      let s1 = msb x in
      let s2 = msb y in
      if s1 && s2 then x < y
      else if not (s1 || s2) then x < y
      else s1

    let ( >$ ) x y = y <$ x
    let ( <=$ ) x y = x <$ y || x = y
    let ( >=$ ) x y = x >$ y || x = y

    let is_negative = msb
    let is_positive x = not (msb x)
    let is_non_negative x = is_positive x || is_zero x

    let sign_extend x w =
      let y = zero_extend x w in
      if is_non_negative x then y
      else
        let ones = ones Pervasives.(2 * w) in
        let ones = ones lsl w in
        y + ones

    let abs x =
      if msb x then
        lnot (x - one (bitwidth x))
      else x

    let max x y = if x >$ y then x else y

  end

  let bs = Bignum.to_string

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
      | _, ExactlyZero -> false
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
    if Bignum.(expn' <$ expn) then None
    else
      let res, loss = rshift_frac base frac n in
      Some (expn', res, loss)

  let align_right_exn ~base ~precision epxn frac =
    match align_right ~base ~precision epxn frac with
    | Some x -> x
    | None -> failwith "Can't align right: exponent overflow"

  (* maximum possible exponent that fits in [n - 1] bits. (one for sign) *)
  let max_exponent' n = int_of_float (2.0 ** (float_of_int (n - 1))) - 1
  let min_exponent' n = - (max_exponent' n)
  let max_exponent n = Bignum.of_int ~width:n (max_exponent' n)
  let min_exponent n = Bignum.of_int ~width:n (min_exponent' n)

  (* the same as [align_right] above, but stops in case of bits loss
     OR if exponent reached a maximum of it's value *)
  let safe_align_right base expn frac =
    let max_expn = max_exponent (bits_in expn) in
    let rec run expn x =
      if Bignum.(expn >=$ max_expn) then
        expn, x
      else
        match rshift_frac base x 1 with
        | y, ExactlyZero -> run (Bignum.succ expn) y
        | _ -> expn, x in
    if Bignum.is_zero frac then expn,frac
    else
      let e,x = run expn frac in
      (* printf "safe align right %d\n" n; *)
      e,x

  let safe_align_left base expn frac =
    let min_expn = min_exponent (bits_in expn) in
    let width = bits_in frac in
    let rec run n expn x =
      if Bignum.(expn <=$ min_expn) then
        expn,x,n
      else
        let y = lshift_frac base x 1 in
        if Bignum.testbit y width then expn,x,n
        else run (n+1) (Bignum.pred expn) y in
    if Bignum.is_zero frac then expn, frac
    else
      let high = Bignum.extract ~lo:(width - 1) frac in
      if Bignum.is_one high then
        (* let () = printf "align left n is 0\n" in *)
        expn, frac
      else
        let frac = Bignum.zero_extend frac width in
        let e,frac,n = run 0 expn frac in
        (* printf "align left n is %d\n" n; *)
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
    let expn = min_exponent desc.ebits in
    let frac = Bignum.zero desc.fbits in
    let data = {expn; frac} in
    {sign = Pos; desc; data = Fin data;}

  let create desc ?(negative = false) ~expn frac =
    let sign = if negative then Neg else Pos in
    if Bignum.is_zero frac then
      let x = zero desc in
      {x with sign}
    else
      let data = norm desc.radix {expn; frac} in
      {sign; desc; data = Fin data; }

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
        Bignum.succ payload in
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

  let xor_sign s s' =
    let r = Bignum.(Bignum.of_sign s lxor Bignum.of_sign s') in
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
    | `Left,  _ when Bignum.(x.expn >$ y.expn) ->
       minimize_exponent base x, y
    | `Right, _ when Bignum.(x.expn <$ y.expn) ->
       maximize_exponent base x, y
    | _, `Left when Bignum.(x.expn <$ y.expn) ->
       x, minimize_exponent base y
    | _, `Right when Bignum.(x.expn >$ y.expn) ->
       x, maximize_exponent base y
    | _ ->
       minimize_exponent base x, minimize_exponent base y

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

  let tos x = sprintf "(%s %s)" (bs x.expn) (bs x.frac)

  let add rm a b =
    let common_ground base x y =
      if Bignum.(x.expn = y.expn) then x,y,ExactlyZero
      else if Bignum.is_zero x.frac then
        {x with expn = y.expn} ,y,ExactlyZero
      else if Bignum.is_zero y.frac then
        x,{y with expn = x.expn },ExactlyZero
      else
        let x,y = balance base x y in

        printf "balanced x: %s\n" (tos x);
        printf "balanced y: %s\n" (tos y);

        let expn = Bignum.max x.expn y.expn in

        printf "max is %s\n" (bs expn);

        if Bignum.(x.expn >$ y.expn) then
          let y, loss = unsafe_rshift base y Bignum.(expn - y.expn) in
          x, y, loss
        else
          let x,loss = unsafe_rshift base x Bignum.(expn - x.expn) in
          x,y,loss in
    check_operands a b;
    match a.data, b.data with
    | Fin x, Fin y ->
       let sb x = Debug.string_of_bits (Bignum.tow x) in

       printf "input x: %s\n" (tos x);
       printf "input y: %s\n" (tos y);
       let x = maximize_exponent (radix a) x in

       printf "maximizED x: %s %s\n" (tos x) (sb x.expn);



       let y = maximize_exponent (radix a) y in
       printf "maximized y: %s %s\n" (tos y) (sb y.expn);

       let x,y,loss = common_ground (radix a) x y in
       printf "common x: %s\n" (tos x);
       printf "common y: %s\n" (tos y);

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
      else if Bignum.is_zero x.frac then
        {x with expn = y.expn}, y, ExactlyZero, true
      else if Bignum.is_zero y.frac then
        x, {y with expn = x.expn}, ExactlyZero, false
      else
        let expn = Bignum.max x.expn y.expn in
        let uno = Bignum.one a.desc.ebits in
        if Bignum.(x.expn > y.expn) then
          let x = unsafe_lshift base x uno in
          let y, loss = unsafe_rshift base y Bignum.(expn - y.expn - uno) in
          x, y, loss, false
        else
          let x,loss = unsafe_rshift base x Bignum.(expn - x.expn - uno) in
          let y = unsafe_lshift base y uno in
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
      let borrow = if loss = ExactlyZero then
          Bignum.zero (bits_in x.frac)
        else Bignum.one (bits_in x.frac) in
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
    let s2 = Bignum.of_sign a.sign in
    let s3 = Bignum.of_sign b.sign in
    let is_subtract = Bignum.is_one Bignum.(s1 lxor (s2 lxor s3)) in
    if is_subtract then sub rm a b
    else add rm a b

  let add ?(rm=Nearest_even) = add_or_sub rm false
  let sub ?(rm=Nearest_even) = add_or_sub rm true

  let multiply desc x y =
    let xexpn = Bignum.sign_extend x.expn desc.ebits in
    let yexpn = Bignum.sign_extend y.expn desc.ebits in
    let xfrac = Bignum.zero_extend x.frac desc.fbits in
    let yfrac = Bignum.zero_extend y.frac desc.fbits in
    let expn = Bignum.(xexpn + yexpn) in
    let frac = Bignum.(xfrac * yfrac) in
    let max_expn =
      Bignum.sign_extend (max_exponent desc.ebits) desc.ebits in
    let min_expn =
      Bignum.sign_extend (min_exponent desc.ebits) desc.ebits in
    match align_right desc.radix desc.fbits expn frac with
    | None -> `Overflow_expn
    | Some (expn,frac,loss) ->
       if Bignum.is_positive expn && Bignum.(expn > max_expn)
       then `Overflow_expn
       else if Bignum.is_positive expn then `Nice (expn,frac,loss)
       else if
         Bignum.is_negative expn && Bignum.(expn <$ min_expn) then
         (* TODO  *)
         let () = printf "THAT's a case!\n" in
         (* shift right even more, trying to make expn = -1023  *)

         `Overflow_expn
       else `Nice (expn,frac,loss)

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
      let precision = Bignum.bitwidth x.frac in
      let data = match multiply a.desc x y with
        | `Overflow_expn -> Inf
        | `Nice (expn, frac, loss) ->
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
    let rec loop n acc dividend degree =
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
        loop (n+1) acc dividend (degree - 1)
      else List.rev acc, dividend, n in
    let res, left, n = loop 0 [] start_dividend 0 in
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
    Bignum.abs expn |> Bignum.to_int

  let expn_dif x y =
    let is_pos = Bignum.is_positive in
    let is_neg = Bignum.is_negative in
    let e = Bignum.(x - y) in
    if is_neg x && is_pos y && Bignum.(e >$ x) then `Underflow_expn
    else
    if is_pos x && is_neg y && Bignum.(e <$ x) then `Underflow_expn
    else `Nice e

  let div ?(rm=Nearest_even) a b =
    let zero expn_bits =
      { expn=Bignum.zero expn_bits; frac = Bignum.zero (prec a) } in
    let rec dif xfrac yfrac xexpn yexpn =
      match expn_dif xexpn yexpn with
      | `Underflow_expn -> None
      | `Nice expn when Bignum.(xfrac >=$ yfrac) -> Some (expn, xfrac)
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
          if equal x0 x' then x0,n
          else run x' (n + 1)
        else x0,n in
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
end
