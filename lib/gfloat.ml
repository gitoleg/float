open Core_kernel

let allow_output = ref true

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
    ebits : int;
    fbits : int;
  }

let desc ~expn_bits fbits = { fbits; ebits=expn_bits }

let string_of_loss s = Sexp.to_string (sexp_of_loss s)

module type Bignum = sig
  type t
  val of_int : width:int -> int -> t
  val to_int : t -> int
  val ones : int -> t
  val bitwidth : t -> int
  val extract : ?hi:int -> ?lo:int -> t -> t
  val zero_extend : t -> int -> t
  val ( + ) : t -> t -> t
  val ( - ) : t -> t -> t
  val ( * ) : t -> t -> t
  val ( / ) : t -> t -> t
  val ( = ) : t -> t -> bool
  val ( < ) : t -> t -> bool
  val ( lsl ) : t -> int -> t
  val ( lor ) : t -> t -> t
  val ( lxor ) : t -> t -> t
  val lnot : t -> t
  val neg : t -> t
  val to_string : t -> string             (* TODO: TEMP!  *)
  val tow : t -> Bap.Std.word
end

module Make(Bignum : Bignum) = struct

  type bignum = Bignum.t

  module Bignum = struct

    let one width = Bignum.of_int ~width 1
    let zero width = Bignum.of_int ~width 0
    let is_one x = x = one (Bignum.bitwidth x)
    let is_zero x = x = zero (Bignum.bitwidth x)

    let testbit b i =
      let x = Bignum.extract ~hi:i ~lo:i b in
      is_one x

    let msb x = testbit x (Bignum.bitwidth x - 1)

    let set_bit x i =
      let uno = one (Bignum.bitwidth x) in
      Bignum.(x lor (uno lsl i))

    let msbn x =
      let bits = Bignum.bitwidth x in
      let inds =
        List.init bits (fun i -> bits - i - 1) in
      List.find inds ~f:(testbit x)

    let lsbn x =
      let bits = Bignum.bitwidth x in
      let inds = List.init bits ident in
      List.find inds ~f:(testbit x)

    let is_negative = msb
    let is_positive x = not (msb x)
    let is_non_negative x = is_positive x || is_zero x

    let sign_extend x w =
      let y = Bignum.zero_extend x w in
      if is_non_negative x then y
      else
        let unos = Bignum.ones (2 * w) in
        let unos = Bignum.(unos lsl w) in
        Bignum.(y + unos)

    include Bignum

    let of_sign = function
      | Pos -> of_int ~width:1 0
      | Neg -> of_int ~width:1 1

    let of_bool = function
      | true -> of_int ~width:1 1
      | false -> of_int ~width:1 0

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

  (* TODO: remove it later *)
  let sb x = Debug.string_of_bits (Bignum.tow x)

  (* TODO: remove it later *)
  let expn_to_str expn =
    let expn' = Bignum.(to_int (abs expn)) in
    let expn' = if Bignum.is_positive expn then expn' else - expn' in
    string_of_int expn'

  (* TODO: remove it later *)
  let tos {expn;frac} =
    sprintf "(%s:%d %s)" (expn_to_str expn) (bits_in expn) (bs frac)

  (* TODO: remove it later *)
  let tos' x = match x.data with
    | Fin x -> tos x
    | _ -> "not a finite number"

  (* TODO: remove it later *)
  let tos'' x = match x.data with
    | Fin x ->
       sprintf "(%s %s)\n" (expn_to_str x.expn)
         (sb x.frac)
    | _ -> "not a finite number"

  let msb w =
    let len = bits_in w in
    let bits = List.init len ~f:(fun i -> len - i - 1) in
    List.find bits ~f:(fun i -> Bignum.testbit w i)

  (* returns a list of digits in [loss], most significant first *)
  let lost_digits loss n =
    let to_digit x : digit =
      let x = Bignum.to_int x in
      let middle = 1 in
      if Int.(x = middle) then Middle
      else if Int.(x = 0) then Zero
      else if Int.( x < middle ) then Less
      else More in
    let base = Bignum.of_int ~width:(bits_in loss) 2 in
    let rec loop acc loss =
      let open Bignum in
      let loss' = loss / base in
      let restored = loss' * base in
      let rem = loss - restored in
      let acc = to_digit rem::acc in
      if is_zero loss' then acc
      else loop acc loss' in
    let digits = loop [] loss in
    if List.length digits < n then
      let zeros = List.init (n - List.length digits) (fun _ -> Zero) in
      zeros @ digits
    else digits

  (* estimate loss after shift right to [n] digits, [lost_frac] is what
     is exactly lost *)
  let estimate_loss lost_frac n =
    let all_zeros ds = List.for_all ds ~f:(fun d -> d = Zero) in
    match lost_digits lost_frac n with
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
  let pow  ~precs n =
    let base = Bignum.of_int ~width:precs 2 in
    let rec run r m =
      if m < n then
        let r' = Bignum.(r * base) in
        if Bignum.(r' < r) then None
        else run r' (m + 1)
      else Some r in
    if n = 0 then Some (Bignum.one precs)
    else run base 1

  let lshift_frac frac n =
    if n = 0 then frac
    else
      match pow ~precs:(bits_in frac) n with
      | None -> Bignum.zero (bits_in frac)
      | Some k -> Bignum.(frac * k)

  let rshift_frac frac n =
    if n = 0 then frac, ExactlyZero
    else
      match pow ~precs:(bits_in frac) n with
      | None -> Bignum.zero (bits_in frac), ExactlyZero
      | Some k ->
         if Bignum.is_zero k then k, ExactlyZero
         else
           let result = Bignum.(frac / k) in
           let restored = Bignum.(result * k) in
           result, estimate_loss Bignum.(frac - restored) n

  (* those functions are unsafe in that sence that there are not
     any checks for exponent overflow *)
  let unsafe_lshift x n =
    let n' = Bignum.to_int n in
    let expn = Bignum.(x.expn - n) in
    { expn; frac = lshift_frac x.frac n' }

  let unsafe_rshift x n =
    let n' = Bignum.to_int n in
    let frac, loss = rshift_frac x.frac n' in
    let expn = Bignum.(x.expn + n) in
    { expn; frac }, loss

  (* shift frac left as possible, without bit loss,
     returns frac and number of shifts *)
  let align_frac_left frac =
    let prec = bits_in frac in
    let rec loop n frac =
      let frac' = Bignum.(frac lsl 1) in
      match msb frac with
      | None -> n, frac
      | Some i when i >= prec -> n, frac
      | Some _ -> loop (n + 1) (lshift_frac frac' 1) in
    let frac = Bignum.zero_extend frac prec in
    let n, frac = loop 0 frac in
    Bignum.extract ~hi:(prec - 1) frac, n


  (* [align_right precision expn frac] shifts fraction right to fit
     into [precision] with a possible loss of bits in order to keep
     most significant bits. Returns [Some (expn, frac, loss)], if
     no exponent overflow occured, [None] otherwise. *)
  let align_right ~precision expn frac =
    let rec run n frac =
      match msb frac with
      | None -> n
      | Some i when i < precision -> n
      | _ -> run (n + 1) (fst (rshift_frac frac 1)) in
    let n = run 0 frac in
    let n' = Bignum.of_int ~width:(bits_in expn) n in
    let expn' = Bignum.(expn + n') in
    if Bignum.(expn' <$ expn) then None
    else
      let res, loss = rshift_frac frac n in
      Some (expn', res, loss)

  let align_right_exn ~precision epxn frac =
    match align_right ~precision epxn frac with
    | Some x -> x
    | None -> failwith "Can't align right: exponent overflow"

  (* maximum possible exponent that fits in [n - 1] bits. (one for sign) *)
  let max_exponent' n = int_of_float (2.0 ** (float_of_int (n - 1))) - 1
  let min_exponent' n = - (max_exponent' n)
  let max_exponent n = Bignum.of_int ~width:n (max_exponent' n)
  let min_exponent n = Bignum.of_int ~width:n (min_exponent' n)

  (* the same as [align_right] above, but stops in case of bits loss
     OR if exponent reached a maximum of it's value *)
  let safe_align_right expn frac =
    let max_expn = max_exponent (bits_in expn) in
    let is_max e = Bignum.(e = max_expn) in
    let rec run expn x =
      if is_max expn then expn, x
      else
        match rshift_frac x 1 with
        | y, ExactlyZero -> run (Bignum.succ expn) y
        | _ -> expn, x in
    if Bignum.is_zero frac then expn,frac
    else run expn frac

  let safe_align_left expn frac =
    let min_expn = min_exponent (bits_in expn) in
    let width = bits_in frac in
    let is_min e = Bignum.(e = min_expn) in
    let rec run expn x =
      if is_min expn then expn,x
      else
        let y = lshift_frac x 1 in
        let high_bits = Bignum.extract ~lo:width y in
        if not (Bignum.is_zero high_bits) then expn,x
        else run (Bignum.pred expn) y in
    if Bignum.is_zero frac then expn, frac
    else
      let frac = Bignum.zero_extend frac width in
      let e,frac = run expn frac in
      let frac = Bignum.extract ~hi:(width - 1) frac in
      e,frac

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

  let prec x = x.desc.fbits

  let zero_finite desc =
    let expn = min_exponent desc.ebits in
    let frac = Bignum.zero desc.fbits in
    {expn; frac}

  let zero desc =
    let data = zero_finite desc in
    {sign = Pos; desc; data = Fin data;}

  let create desc ?(negative = false) ~expn frac =
    let sign = if negative then Neg else Pos in
    if Bignum.is_zero frac then
      let x = zero desc in
      {x with sign}
    else
      let data = norm {expn; frac} in
      let () = printf "created: %s\n" (expn_to_str data.expn) in
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

  let equal a b =
    if a.sign <> b.sign then false
    else
      match a.data, b.data with
      | Fin x, Fin y ->
         let x = norm x in
         let y = norm y in
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

  let estimate_spot x =
    let left  = minimize_exponent x in
    let right = maximize_exponent x in
    if Bignum.(left.expn <> x.expn && right.expn <> x.expn) then `Both
    else if Bignum.(left.expn <> x.expn) then `Left
    else if Bignum.(right.expn <> x.expn) then `Right
    else `Nope

  let balance x y =
    match estimate_spot x, estimate_spot y with
    | `Left,  _ when Bignum.(x.expn >$ y.expn) ->
       minimize_exponent x, y
    | `Right, _ when Bignum.(x.expn <$ y.expn) ->
       maximize_exponent x, y
    | _, `Left when Bignum.(x.expn <$ y.expn) ->
       x, minimize_exponent y
    | _, `Right when Bignum.(x.expn >$ y.expn) ->
       x, maximize_exponent y
    | _ ->
       minimize_exponent x, minimize_exponent y

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
    let common_ground  x y =
      if Bignum.(x.expn = y.expn) then x,y,ExactlyZero
      else if Bignum.is_zero x.frac then
        {x with expn = y.expn} ,y,ExactlyZero
      else if Bignum.is_zero y.frac then
        x,{y with expn = x.expn },ExactlyZero
      else
        let x,y = balance  x y in
        let expn = Bignum.max x.expn y.expn in
        if Bignum.(x.expn >$ y.expn) then
          let y, loss = unsafe_rshift  y Bignum.(expn - y.expn) in
          x, y, loss
        else
          let x,loss = unsafe_rshift  x Bignum.(expn - x.expn) in
          x,y,loss in
    match a.data, b.data with
    | Fin x, Fin y ->
       let x = maximize_exponent x in
       let y = maximize_exponent y in
       let x,y,loss = common_ground x y in
       let frac = Bignum.(x.frac + y.frac) in
       let data =
         if Bignum.(frac >= x.frac) then
           Fin (norm {expn=x.expn; frac=round rm Pos frac loss})
         else
           let x = extend x (prec a) in
           let y = extend y (prec a) in
           let frac = Bignum.(x.frac + y.frac) in
           match align_right (prec a) x.expn frac with
           | None -> Inf
           | Some (expn, frac, loss') ->
              let loss = if Bignum.(x.expn = expn) then loss
                         else combine_loss loss' loss in
              let frac = extract (prec a) frac in
              let frac = round rm Pos frac loss in
              Fin (norm {expn; frac}) in
       { a with data }
    | Nan _, Nan _ -> if is_signaling_nan a || is_quite_nan b then a else b
    | Nan _, _ -> a
    | _, Nan _ -> b
    | Inf, Inf when is_neg a && is_pos b -> a
    | Inf, Inf when is_pos a && is_neg b -> a
    | Inf, _ -> a
    | _, Inf -> b

  let sub rm a b =
    let common_ground  x y =
      if Bignum.(x.expn = y.expn) then x,y,ExactlyZero, Bignum.(x.frac < y.frac)
      else if Bignum.is_zero x.frac then
        {x with expn = y.expn}, y, ExactlyZero, true
      else if Bignum.is_zero y.frac then
        x, {y with expn = x.expn}, ExactlyZero, false
      else
        let expn = Bignum.max x.expn y.expn in
        let uno = Bignum.one a.desc.ebits in
        if Bignum.(x.expn >$ y.expn) then
          let x = unsafe_lshift  x uno in
          let y, loss = unsafe_rshift  y Bignum.(expn - y.expn - uno) in
          x, y, loss, false
        else
          let x,loss = unsafe_rshift  x Bignum.(expn - x.expn - uno) in
          let y = unsafe_lshift  y uno in
          x,y,loss, true in
    match a.data, b.data with
    | Fin x, Fin y ->
       let x = minimize_exponent x in
       let y = minimize_exponent y in
       let x = extend x (prec a) in
       let y = extend y (prec a) in
       let x,y,loss,reverse = common_ground x y in
       let loss = invert_loss loss in
       let borrow = if loss = ExactlyZero then
                      Bignum.zero (bits_in x.frac)
                    else Bignum.one (bits_in x.frac) in
       let frac = if reverse then Bignum.(y.frac - x.frac - borrow)
                  else Bignum.(x.frac - y.frac - borrow) in
       let sign = if reverse then revert_sign a.sign else a.sign in
       let expn,frac,loss' =
         align_right_exn ~precision:(prec a) x.expn frac in
       let loss = if Bignum.(x.expn = expn) then loss
                  else combine_loss loss' loss in
       let frac = Bignum.extract ~hi:((prec a) - 1) frac in
       let frac = round rm sign frac loss in
       let data = Fin (norm {expn; frac}) in
       let a = {a with data; sign} in
       if is_zero a then {a with sign = Pos} else a
    | Nan _, Nan _ -> if is_signaling_nan a || is_quite_nan b then a else b
    | Nan _, _ -> a
    | _, Nan _ -> b
    | Inf, Inf -> nan ~negative:true a.desc
    | Inf, _ -> a
    | _, Inf -> b

  let add_or_sub rm subtract a b =
    let s1 = Bignum.of_bool subtract in
    let s2 = Bignum.of_sign a.sign in
    let s3 = Bignum.of_sign b.sign in
    let is_subtract = Bignum.is_one Bignum.(s1 lxor (s2 lxor s3)) in
    if is_subtract then sub rm a b
    else add rm a b

  let add ?(rm=Nearest_even) = add_or_sub rm false
  let sub ?(rm=Nearest_even) = add_or_sub rm true

  let exponent_sum desc xe ye =
    let is_pos = Bignum.is_non_negative in
    let both f = f xe && f ye in
    let sum = Bignum.(xe + ye) in
    let zero = Bignum.(zero (bitwidth xe)) in
    match is_pos xe, is_pos ye with
    | a,b when a <> b -> `Nice (sum,zero)
    | _ ->
       let maxe = max_exponent desc.ebits in
       let mine = min_exponent desc.ebits in
       if Bignum.(maxe - abs xe > abs ye) then `Nice (sum,zero)
       else if both is_pos then `Overflow_expn
       else
         let de = Bignum.(abs xe + abs ye - maxe) in
         `Nice (mine, de)

  let mul ?(rm=Nearest_even) a b =
    match a.data,b.data with
    | Fin _, Fin _ when is_zero a ->
       {a with sign = xor_sign a.sign b.sign;}
    | Fin _, Fin _ when is_zero b ->
       {b with sign = xor_sign a.sign b.sign}
    | Fin x, Fin y ->
       let extract_frac frac = Bignum.extract ~hi:(a.desc.fbits - 1) frac in
       let extend_frac z = { z with frac = Bignum.zero_extend z.frac a.desc.fbits; } in
       let x = minimize_exponent x in
       let y = minimize_exponent y in
       let sign = xor_sign a.sign b.sign in
       let x = extend_frac x in
       let y = extend_frac y in
       let frac = Bignum.(x.frac * y.frac) in
       let data =
       match exponent_sum a.desc x.expn y.expn with
       | `Overflow_expn -> Inf
       | `Nice (expn, shr) ->
          let {expn;frac=frac'}, loss' = unsafe_rshift {expn;frac} shr in
          match align_right a.desc.fbits expn frac' with
          | None -> Inf
          | Some (expn,frac,loss) ->
             let frac = extract_frac frac in
             let loss = combine_loss loss loss' in
             let frac = round rm sign frac loss in
             Fin (norm  { expn; frac}) in
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
    let extend_expn e = Bignum.sign_extend e (bits_in e) in
    let min_expn = extend_expn (min_exponent a.desc.ebits) in
    let max_expn = extend_expn (max_exponent a.desc.ebits) in
    let extend {expn; frac} =
      let expn = extend_expn expn in
      let frac = Bignum.zero_extend frac (bits_in frac) in
      {expn; frac} in
    let is_overflow expn frac = false in
      (* it's still a question here, because we can get
         a finite result here. But anyway, if we get it just
         because our maneur with extended representation - let's
         assume we got an Inf  *)
      (* Bignum.(expn <$ min_expn) &&
       *   match Bignum.lsbn frac with
       *   | Some i -> i > a.desc.fbits && not (Bignum.is_zero frac)
       *   | None -> false in *)
    match a.data,b.data with
    | Fin x, Fin y when is_zero a && is_zero b -> nan ~negative:true a.desc
    | Fin x, Fin y when is_zero b -> {a with data = Inf}
    | Fin x, Fin y ->
       let x = extend x in
       let y = extend y in
       let sign = xor_sign a.sign b.sign in
       let xexpn, xfrac = safe_align_left x.expn x.frac in
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
             let {expn;frac=frac'}, loss' = unsafe_rshift {expn;frac} dexp in
             let frac = round rm sign frac' loss' in
             let expn = Bignum.extract ~hi:(a.desc.ebits - 1) expn in
             expn,frac, combine_loss loss' loss
           else
             let expn = Bignum.extract ~hi:(a.desc.ebits - 1) expn in
             expn,frac,loss in
         let data =
           match align_right ~precision:a.desc.fbits expn frac with
           | None -> zero_finite a.desc
           | Some (expn,frac,loss') ->
              let frac = round rm sign frac loss' in
              let frac = Bignum.extract ~hi:((prec a) - 1) frac in
              norm {frac; expn} in
         {a with data = Fin data; sign; }
    | Nan _, Nan _ -> if is_signaling_nan a || is_quite_nan b then a else b
    | Nan _, _ -> a
    | _, Nan _ -> b
    | Inf, Inf -> nan ~negative:true a.desc
    | Inf, _ -> a
    | _, Inf -> b


  let long_div ?(rm=Nearest_even) a b =
    let extend z = extend (minimize_exponent z) 1 in
    match a.data,b.data with
    | Fin x, Fin y when is_zero a && is_zero b -> nan ~negative:true a.desc
    | Fin x, Fin y when is_zero b -> {a with data = Inf}
    | Fin x, Fin y when is_zero a -> a
    | Fin x, Fin y ->
       let x = extend x in
       let y = extend y in
       let x = if Bignum.(x.frac < y.frac) then
                 {frac = Bignum.(x.frac lsl 1); expn = Bignum.pred x.expn }
               else x in
       let sign = xor_sign a.sign b.sign in
       let prec = a.desc.fbits + 1 in
       let expn = Bignum.(x.expn - y.expn) in
       printf "xexpn is %s\n" (expn_to_str x.expn);
       printf "yexpn is %s\n" (expn_to_str y.expn);
       printf "expn is %s\n" (expn_to_str expn);

       let denom = y.frac in
       let rec loop i nom res =
         if i < 0 then nom,res
         else
           let nom, res =
             if Bignum.(nom >= denom) then
               let nom = Bignum.(nom - denom) in
               let res = Bignum.set_bit res i in
               nom,res
             else nom,res in
           let nom = Bignum.(nom lsl 1) in
           loop (i - 1) nom res in
       let nom,res = loop (a.desc.fbits - 1) x.frac (Bignum.zero prec) in
       let loss =
         if Bignum.(nom > denom) then MoreThanHalf
         else if Bignum.(nom = denom) then ExactlyHalf
         else if Bignum.is_zero nom then ExactlyZero
         else LessThanHalf in
       let res = round rm sign res loss in
       let res = Bignum.extract ~hi:(a.desc.fbits - 1) res in
       let data = { expn; frac=res } in
       (* let () = printf "final: expn %s, coef %s\n" (expn_to_str expn) (bs data.frac) in *)
       let data = norm data in
       {a with data = Fin data; sign }
    | Nan _, Nan _ -> if is_signaling_nan a || is_quite_nan b then a else b
    | Nan _, _ -> a
    | _, Nan _ -> b
    | Inf, Inf -> nan ~negative:true a.desc
    | Inf, _ -> a
    | _, Inf -> b



  let div = long_div

  let truncate ?(rm=Nearest_even) ~upto a = match a.data with
    | Fin {expn; frac} ->
       begin
         match align_right  ~precision:upto expn frac with
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
       let expn = Bignum.sign_extend x.expn (bits_in x.expn) in
       let frac = Bignum.zero_extend x.frac (prec a) in
       let {expn;frac} = minimize_exponent {expn; frac} in
       let desc = {ebits = 2 * a.desc.ebits; fbits = 2 * (prec a) } in
       let s = create desc ~expn frac in
       let two = create desc
                   ~expn:(Bignum.of_int ~width:desc.ebits 0)
                   (Bignum.of_int ~width:desc.fbits 2) in
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
end
