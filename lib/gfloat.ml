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

type gfloat = {
  sign : semantics;
  expn : semantics;
  coef : semantics;
  is_snan : semantics;
  is_qnan : semantics;
  is_inf  : semantics;
}

module Float_domain = struct
  open Domain.Order

  type t = gfloat option

  let empty = None

  let partial x y : Domain.Order.partial = match x,y with
    | None,None -> EQ
    | None,_ -> LE
    | _,None -> GE
    | _ -> NC

  let inspect t = failwith "unimplemented"

end

let gfloat = Semantics.declare ~name:"gfloat" (module Float_domain)

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

  type 'a t = 'a knowledge

  let significand : ('e,'s) float value t -> 's bitv value t =
    fun x -> x >>= fun v ->
      let s = Floats.sigs (Value.sort v) in
      match Value.get gfloat v with
      | None -> assert false
      | Some {coef} ->
        Knowledge.return (Value.create s coef)

  let exponent : ('e,'s) float value t -> 'e bitv value t =
    fun x -> x >>= fun v ->
      let s = Floats.exps (Value.sort v) in
      match Value.get gfloat v with
      | None -> assert false
      | Some {expn} ->
        Knowledge.return (Value.create s expn)

  let what's_a_bit (x : ('e,'s) float value t ) f =
    x >>= fun v ->
    match Value.get gfloat v with
    | None -> assert false
    | Some gfloat ->
      Knowledge.return (Value.create Bool.t (f gfloat))

  let fsign x = what's_a_bit x (fun y -> y.sign)
  let is_snan x = what's_a_bit x (fun y -> y.is_snan)
  let is_qnan x = what's_a_bit x (fun y -> y.is_qnan)
  let is_inf x = what's_a_bit x (fun y -> y.is_inf)

  let data x = fsign x, exponent x, significand x

  let (>>->) x f =
    x >>= fun v ->
    match Value.get gfloat v with
    | None -> assert false
    | Some gf -> f (Value.sort v) gf

  let create fsort
      ?(sign=B.b0)
      ?(is_snan=B.b0)
      ?(is_qnan=B.b0)
      ?(is_inf=B.b0)
      expn coef =
    sign >>= fun s ->
    expn >>= fun e ->
    coef >>= fun c ->
    is_snan >>= fun is_snan ->
    is_qnan >>= fun is_qnan ->
    is_inf  >>= fun is_inf  ->
    let sign = Value.semantics s in
    let expn = Value.semantics e in
    let coef = Value.semantics c in
    let is_snan = Value.semantics is_snan in
    let is_qnan = Value.semantics is_qnan in
    let is_inf  = Value.semantics is_inf  in
    let x = Some {sign; expn; coef; is_snan; is_qnan; is_inf} in
    !! (Value.put gfloat (Value.empty fsort) x)

  let finite : ('e,'k) float sort -> bit value t ->
    'e bitv value t -> 'k bitv value t ->
    ('e,'k) float value t =
    fun fsort sign expn coef ->
      create fsort ~sign ~is_snan:B.b0 ~is_qnan:B.b0
        ~is_inf:B.b0 expn coef

  let sort x = x >>= fun x -> !! (Value.sort x)
  let size x = sort x >>= fun s -> !! (Bits.size s)
  let sema x = x >>= fun x -> !! (Value.semantics x)
  let empty dom sort x = !! (Value.put dom (Value.empty sort) x)
  let precision x = size (significand x)
  let expn_bits x = size (exponent x)
  let double s = Bits.define ((Bits.size s) * 2)

  let lshift_coef coef n = B.(coef lsl n)

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
  let max_exponent' n = int_of_float (2.0 ** (float_of_int (n - 1))) - 1
  let min_exponent' n = - (max_exponent' n)
  let max_exponent  n = B.of_int n (Bits.size n |> max_exponent')
  let min_exponent  n = B.of_int n (Bits.size n |> min_exponent')

  (* returns pow of 2 nearest to n and 2 in that power *)
  let nearest_pow2 num =
    let rec find pow n =
      let n' = 2 * n in
      if n' >= num then pow + 1, n'
      else find (pow + 1) n' in
    find 0 1

  let bind a body =
    a >>= fun a ->
    sort !!a >>= fun s ->
    Var.Generator.fresh s >>= fun v ->
    B.let_ v !!a (body (B.var v))

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
    bind (clz coef) @@ fun clz ->
    Var.Generator.fresh sigs >>= fun v ->
    let_ v
      (umin clz (unsigned sigs (abs (expn - min_expn))))
      (var v)

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

  let with' : type e k.
    ?sign: bit value t ->
    ?expn: e bitv value t ->
    ?coef: k bitv value t ->
    ?is_snan: bit value t ->
    ?is_qnan: bit value t ->
    ?is_inf:  bit value t ->
    (e,k) float value t -> (e,k) float value t =
    fun ?sign ?expn ?coef ?is_snan ?is_qnan ?is_inf x ->
      let sema ~default x =
        let default = !! default in
        Option.value_map ~default ~f:sema x in
      x >>-> fun xs xv ->
      sema ~default:xv.sign sign >>= fun sign ->
      sema ~default:xv.expn expn >>= fun expn ->
      sema ~default:xv.coef coef >>= fun coef ->
      sema ~default:xv.is_inf is_inf >>= fun is_inf ->
      sema ~default:xv.is_snan is_snan >>= fun is_snan ->
      sema ~default:xv.is_qnan is_qnan >>= fun is_qnan ->
      let y = Some {sign; expn; coef; is_inf; is_snan; is_qnan} in
      !! (Value.put gfloat (Value.empty xs) y)

  (* min exponent without bit loss or exponent overflow,
     fraction shifted as left as possible, i.e. it occupies
     more significant bits *)
  let minimize_exponent x =
    let e = exponent x in
    let c = significand x in
    safe_align_left e c >>= fun (expn,coef) ->
    with' x ~expn ~coef

  let norm = minimize_exponent

  let prec x = Bits.size (Value.sort x)

  let of_bit x = !! (Value.create Bool.t x)
  let is_inf x = x >>-> fun _ v -> of_bit v.is_inf
  let is_snan x = x >>-> fun _ v -> of_bit v.is_snan
  let is_qnan x = x >>-> fun _ v -> of_bit v.is_qnan
  let is_nan x = B.or_ (is_snan x) (is_qnan x)

  let is_pinf x = B.(and_ (inv (fsign x)) (is_inf x))
  let is_ninf x =  B.(and_ (fsign x) (is_inf x))

  let is_special: ('e,'k) float value t -> bit value t = fun x ->
    B.or_ (is_nan x) (is_inf x)

  let is_finite x = B.inv (is_special x)

  let is_fzero x =
    let c = significand x in
    B.(and_ (is_zero c) (inv (is_special x)))

  let zero : ('e,'k) float sort -> ('e,'k) float value t = fun fsort ->
    let sign = B.b0 in
    let expn = B.zero (Floats.exps fsort) in
    let coef = B.zero (Floats.sigs fsort) in
    finite fsort sign expn coef

  let inf ?(negative=false) fsort : ('e,'k) float value t =
    let sign = if negative then B.b1 else B.b0 in
    let expn = B.zero (Floats.exps fsort) in
    let coef = B.zero (Floats.sigs fsort) in
    create fsort ~sign ~is_inf:B.b1 expn coef

  let pinf fsort : ('e,'k) float value t = inf ~negative:false fsort
  let ninf fsort :('e,'k) float value t = inf ~negative:true fsort

  (* mk nan with payload 0100..01 *)
  let nan ?(signaling=false) ?(negative=false) ?payload fsort =
    let sign = if negative then B.b1 else B.b0 in
    let coef = match payload with
      | Some p -> p
      | None ->
        let prec = Floats.sigs fsort |> Bits.size in
        let prec = B.of_int (Floats.sigs fsort) prec in
        let payload = B.one (Floats.sigs fsort) in
        let two = B.one (Floats.sigs fsort) |> B.succ in
        let shift = B.(prec - two) in
        let payload = B.(payload lsl shift) in
        B.succ payload in
    let expn = B.zero (Floats.exps fsort) in
    let is_snan = if signaling then B.b1 else B.b0 in
    let is_qnan = B.inv is_snan in
    create fsort ~sign ~is_snan ~is_qnan expn coef

  let qnan fsort payload = nan ~payload fsort
  let snan fsort payload = nan ~signaling:true ~payload fsort

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

  let match_ cases ~default =
    let cases = List.rev cases in
    List.fold cases ~init:default
      ~f:(fun fin (cond, ok) -> B.ite cond ok fin)

  let (-->) x y = x,y
  let (>=>) = bind

  let fadd rm x y =
    let open B in
    let _,xexpn,xcoef = data x in
    let _,yexpn,ycoef = data y in
    let lost_bits = abs (xexpn - yexpn) in
    let xcoef = ite (xexpn >$ yexpn) xcoef (xcoef lsr lost_bits) in
    let ycoef = ite (yexpn >$ xexpn) ycoef (ycoef lsr lost_bits) in
    sort xexpn >>= fun exps  ->
    sort xcoef >>= fun sigs ->
    let expn =
      bind2 xcoef ycoef @@ fun xcoef ycoef ->
      xcoef + ycoef >=> fun coef ->
      max xexpn yexpn >=> fun expn ->
      ite (coef < xcoef) (succ expn) expn in
    let is_inf =
      bind2 xcoef ycoef @@ fun xcoef ycoef ->
      xcoef + ycoef >=> fun coef ->
      max_exponent exps >=> fun max_expn ->
      and_ (coef < xcoef) (expn = max_expn) in
    let coef =
      bind4 xexpn xcoef yexpn ycoef @@ fun xexpn xcoef yexpn ycoef ->
      xcoef + ycoef >=> fun coef ->
      let loss = match_ [
          (xexpn = yexpn)  --> zero sigs;
          (xexpn >$ yexpn) --> extract_last ycoef lost_bits;
        ] ~default:(extract_last xcoef lost_bits) in
      loss >=> fun loss ->
      coef >=> fun coef ->
      coef >= xcoef >=> fun is_ok_coef ->
      ite is_ok_coef (round rm b0 coef loss lost_bits) @@
        let one = one sigs in
        let coef,loss' = rshift_coef coef one in
        bind3 coef loss' (succ lost_bits) @@ fun coef loss' lost_bits ->
        combine_loss loss' loss >=> fun loss ->
        let sh = of_int sigs Caml.(Bits.size sigs - 1) in
        let one = one lsl sh in
        coef lor one >=> fun coef ->
        round rm b0 coef loss lost_bits in
    with' x ~expn ~coef ~is_inf

  let extend ~addend x =
    x >>-> fun fsort v ->
    let size = Floats.sigs fsort |> Bits.size in
    let sigs' = Bits.define (size + addend) in
    let fsort' = Floats.define (Floats.exps fsort) sigs' in
    let coef  = significand x in
    let coef' = B.unsigned sigs' coef in
    coef' >>= fun coef' ->
    let coef' = Value.semantics coef' in
    let x = Some {v with coef=coef'} in
    !! (Value.put gfloat (Value.empty fsort') x)

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

  let fsub rm x y =
    let open B in
    let extend z =
      minimize_exponent z >>= fun z ->
      extend !!z ~addend:1 in
    sort x >>= fun fsort ->
    let sigs = Floats.sigs fsort in
    let exps = Floats.exps fsort in
    let xsign,xexpn,xcoef = data (extend x) in
    let _,yexpn,ycoef = data (extend y) in
    let expn_eql = B.zero exps in
    let xexpn_gt = B.one exps in
    let yexpn_gt = B.ones exps in
    let cmp_expn = bind2 xexpn yexpn @@ fun xe ye ->
      match_ [
        (xe >$ ye) --> xexpn_gt;
        (ye >$ xe) --> yexpn_gt;
      ] ~default:expn_eql in
    let match_expn ~on_eql ~on_xgt ~on_ygt =
      cmp_expn >=> fun cmp_expn ->
      match_ [
        (cmp_expn = xexpn_gt) --> on_xgt;
        (cmp_expn = yexpn_gt) --> on_ygt;
      ] ~default:on_eql in
    sort xcoef >>= fun sigs' ->
    let lost_bits = bind (B.abs (xexpn - yexpn)) @@ fun diff ->
      ite (is_zero diff) diff (diff - one exps) in
    let loss =
      bind3 xcoef ycoef lost_bits @@ fun xcoef ycoef lost_bits ->
      match_expn ~on_eql:(zero sigs')
        ~on_xgt:(extract_last ycoef lost_bits)
        ~on_ygt:(extract_last xcoef lost_bits) >=> fun loss ->
      invert_loss loss lost_bits in
    let reverse = match_expn ~on_eql:(xcoef < ycoef) ~on_xgt:b0 ~on_ygt:b1 in
    let sign = ite reverse (inv xsign) xsign in
    let coef =
      bind4 xcoef ycoef loss lost_bits @@ fun xcoef ycoef loss lost_bits ->
      match_expn ~on_eql:xcoef
        ~on_xgt:(xcoef lsl one sigs') ~on_ygt:(xcoef lsr lost_bits) >=> fun xcoef ->
      match_expn ~on_eql:ycoef
        ~on_xgt:(ycoef lsr lost_bits) ~on_ygt:(ycoef lsl one sigs') >=> fun ycoef ->
      ite (is_zero loss) (zero sigs') (one sigs') >=> fun borrow ->
      ite reverse (ycoef - xcoef - borrow) (xcoef - ycoef - borrow) in
    let expn =
      bind3 (msb coef) xexpn yexpn @@ fun msb xexpn yexpn ->
      max xexpn yexpn >=> fun max ->
      min_exponent exps >=> fun min ->
      ite (xexpn = yexpn) xexpn (max - one exps) >=> fun expn ->
      ite (is_zero coef) min (ite msb (succ expn) expn) in
    let coef = bind3 coef loss lost_bits @@ fun coef loss lost_bits ->
      msb coef >=> fun msb ->
      ite msb (extract_last coef (one sigs')) (zero sigs') >=> fun loss' ->
      ite msb (combine_loss loss' loss lost_bits) loss >=> fun loss ->
      ite msb (succ lost_bits) lost_bits >=> fun lost_bits ->
      ite msb (coef lsr one sigs') coef >=> fun coef ->
      unsigned sigs coef >=> fun coef ->
      round rm sign coef loss lost_bits in
    with' x ~expn ~coef ~sign >>= fun x ->
    minimize_exponent !!x

  let add_or_sub ~is_sub rm x y =
    let ( lxor ) = xor_sign in
    let s1 = if is_sub then B.b1 else B.b0 in
    let s2 = fsign x in
    let s3 = fsign y in
    let is_sub = s1 lxor (s2 lxor s3) in
    B.ite is_sub (fsub rm x y) (fadd rm x y)

  (* let fsub = add_or_sub ~is_sub:true
   * let fadd = add_or_sub ~is_sub:false *)

  let double s = Bits.define ((Bits.size s) * 2)

  let fmul rm x y =
    let open B in
    sort x >>= fun fsort ->
    precision x >>= fun coef_bits ->
    let exps = double (Floats.exps fsort) in
    let sigs = double (Floats.sigs fsort) in
    let min_expn = signed exps (min_exponent (Floats.exps fsort)) in
    let max_expn = signed exps (max_exponent (Floats.exps fsort)) in
    let xsign, xexpn, xcoef = data x in
    let ysign, yexpn, ycoef = data y in
    let expn = signed exps xexpn + signed exps yexpn in
    let coef = unsigned sigs xcoef * unsigned sigs ycoef in
    let sign = xor_sign xsign ysign in
    let clz  = clz coef in
    let prec  = of_int sigs coef_bits in
    let shift = ite (clz >= prec) (zero sigs) (prec - clz) in
    let dexpn = ite (expn <$ min_expn) (abs expn - abs min_expn) (zero exps) in
    let shift = shift + unsigned sigs dexpn in
    let dexpn' = unsigned exps shift + dexpn in
    let expn = expn + dexpn' in
    let coef =
      extract_last coef shift >=> fun loss ->
      coef lsr shift >=> fun coef ->
      round rm sign coef loss shift >=> fun coef ->
      ite (expn <$ min_expn) (zero sigs) coef >=> fun coef ->
      unsigned (Floats.sigs fsort) coef in
    let is_inf = expn >$ max_expn in
    let expn =
      expn >=> fun expn ->
      ite (expn <$ min_expn) (zero exps) expn >=> fun expn ->
      unsigned (Floats.exps fsort) expn >=> fun expn ->
      min_exponent (Floats.exps fsort) >=> fun min ->
      ite (is_zero coef) min expn in
    with' x ~expn ~coef ~sign ~is_inf

  let mask_bit sort i =
    let uno = B.one sort in
    let shf = B.of_int sort i in
    B.(uno lsl shf)

  let fdiv rm x y =
    let open B in
    let extend z =
      z >>= fun z ->
      minimize_exponent !!z >>= fun z ->
      extend !!z ~addend:1 in
    sort x >>= fun fsort ->
    let sign = xor_sign (fsign x) (fsign y) in
    let x' = extend x in
    let y' = extend y in
    precision x' >>= fun prec ->
    sort (significand x') >>= fun sigs ->
    let lost_alot = of_int sigs 0b11 in
    let lost_half = of_int sigs 0b10 in
    let lost_zero = of_int sigs 0b00 in
    let lost_afew = of_int sigs 0b01 in
    let lost_bits = of_int sigs 2    in
    let rec eval_res i masks nomin denom =
      if Caml.(i < 0) then
        List.fold masks ~f:(lor) ~init:(zero sigs) >=> fun coef ->
        let loss = match_ [
            (nomin > denom) --> lost_alot;
            (nomin = denom) --> lost_half;
            (nomin = zero sigs) --> lost_zero;
         ] ~default:lost_afew in
        round rm sign coef loss lost_bits
      else
        let next_nomin = ite (nomin > denom) (nomin - denom) nomin in
        let mask = ite (nomin > denom) (mask_bit sigs i) (zero sigs) in
        let masks = mask :: masks in
        bind next_nomin (fun next_nomin ->
        eval_res Caml.(i - 1) masks (next_nomin lsl one sigs) denom)  in
    let coef =
      significand x' >=> fun nomin ->
      significand y' >=> fun denom ->
      eval_res Caml.(prec  - 1 ) [] nomin denom >=> fun coef ->
      unsigned (Floats.sigs fsort) coef in
    let exps = Floats.exps fsort in
    let expn =
      significand x' >=> fun nomin ->
      significand y' >=> fun denom ->
      of_int sigs prec >=> fun prec ->
      prec - clz nomin >=> fun msb_nomin ->
      prec - clz denom >=> fun msb_denom ->
      prec - abs (msb_nomin - msb_denom) - one sigs >=> fun dexpn ->
      exponent x - exponent y - low exps dexpn in
    with' x ~expn ~coef >>= fun x ->
    minimize_exponent !!x

  let narrowing_convert outs input rm =
    sort input >>= fun fs ->
    let isigs = Floats.sigs fs in
    let oexps = Floats.exps outs in
    let osigs = Floats.sigs outs in
    let coef = significand input in
    let sign = fsign input in
    let coef'= B.high osigs coef in
    let lost_bits' = Bits.(size isigs - size osigs) in
    let loss' = Bits.define lost_bits' in
    let loss = B.low loss' coef in
    let lost_bits = B.of_int loss' lost_bits' in
    let coef = round rm sign coef' loss lost_bits in
    let expn = exponent input in
    let expn = B.low oexps expn in
    finite outs sign expn coef

  let extending_convert outs input =
    let oexps = Floats.exps outs in
    let osigs = Floats.sigs outs in
    let coef = B.unsigned osigs (significand input) in
    let expn = B.unsigned oexps (exponent input) in
    finite outs (fsign input) expn coef

  (* todo: add is_inf and is_nan checks here *)
  let convert : ('e, 'k) float sort -> ('a,'b) float value t ->
    rmode value t -> ('e, 'k) float value t =
    fun outs input rm ->
      sort input >>= fun fs ->
      let bits = Bits.size in
      let expn_bits = bits (Floats.exps fs) in
      let coef_bits = bits (Floats.sigs fs) in
      let expn_bits' = bits (Floats.exps outs) in
      let coef_bits' = bits (Floats.sigs outs) in
      let is_same = expn_bits = expn_bits' && coef_bits = coef_bits' in
      let is_narrowing = expn_bits > expn_bits' && coef_bits > coef_bits' in
      let is_extending = expn_bits < expn_bits' && coef_bits < coef_bits' in
      if is_same then
        input
      else if is_narrowing then narrowing_convert outs input rm
      else if is_extending then extending_convert outs input
      else B.unk fs

  open Ieee754

  let match_ cases ~default =
    let cases = List.rev cases in
    List.fold cases ~init:default
      ~f:(fun fin (cond, ok) -> B.ite cond ok fin)

  let fmt_of_bits bits = IEEE754.create bits

  let sort_of_fmt fmt =
    let exps = Bits.define fmt.IEEE754.w in
    let sigs = Bits.define fmt.IEEE754.p in
    Floats.define exps sigs

  let bias exps fmt = B.of_int exps fmt.IEEE754.bias

  let bind a body =
    a >>= fun a ->
    sort !!a >>= fun s ->
    Var.Generator.fresh s >>= fun v ->
    B.let_ v !!a (body (B.var v))

  let (>=>) = bind

  let to_ieee vsort rm x =
    let bits = Bits.size vsort in
    match IEEE754.create bits with
    | None -> B.unk vsort
    | Some fmt ->
      let fsort = sort_of_fmt fmt in
      convert fsort x rm >>= fun x ->
      let x = !!x in
      let exps = Floats.exps fsort in
      let sigs = Floats.sigs fsort in
      let (||) = B.or_ in
      let (&&) = B.and_ in
      let is_inf = is_pinf x || is_ninf x in
      let is_nan = is_snan x || is_qnan x in
      let p_1 = Bits.size sigs - 1 in
      let expn =
        B.(bias exps fmt + exponent x) >=> fun expn ->
          B.(ite (is_zero expn) (zero exps) (of_int exps p_1)) >=> fun dexpn ->
            B.(expn + dexpn) >=> fun expn ->
              B.ite (is_nan || is_inf) (B.ones exps) expn in
      let sigs_ieee = Bits.define p_1 in
      let coef =
        B.low sigs_ieee (significand x) >=> fun coef ->
          match_ B.[
              is_inf --> B.zero sigs_ieee;
              (is_nan && B.is_zero coef) --> coef;
              is_nan --> coef;
            ] ~default:coef in
      let sign = B.ite (fsign x) (B.one vsort) (B.zero vsort) in
      let sign = B.(sign lsl of_int vsort Int.(bits - 1)) in
      B.(concat vsort [ expn; coef] lor sign)

  let of_ieee bitv rm fsort' =
    sort bitv >>= fun insort ->
    size bitv >>= fun bits ->
    match IEEE754.create bits with
    | None -> B.unk fsort'
    | Some fmt ->
       let fsort = sort_of_fmt fmt in
       let p_1 = Bits.size (Floats.sigs fsort) - 1 in
       let exps = Floats.exps fsort in
       let sigs = Floats.sigs fsort in
       let coef =
         B.unsigned sigs bitv >=> fun coef ->
         B.(one sigs lsl of_int sigs p_1) >=> fun leading_one ->
         B.(coef lor leading_one) in
       let expn =
         B.(unsigned exps (bitv lsr of_int insort p_1)) >=> fun expn ->
         B.(ite (is_zero expn) (zero exps) (of_int exps p_1)) >=> fun dexpn ->
         B.(expn - bias exps fmt - dexpn) in
       let sign = B.msb bitv in
       (* let is_inf = B.(and_ (expn = ones exps) (coef = zero sigs)) in
        * let is_nan = B.(and_ (expn = ones exps) (coef <> zero sigs)) in
        * let x =
        *   match_ B.[
        *       and_ is_inf sign --> ninf fsort;
        *       is_inf           --> pinf fsort;
        *       is_nan           --> qnan fsort coef;
        *   ] ~default:(finite fsort sign expn coef) in *)
       finite fsort sign expn coef >>= fun x ->
       convert fsort' !!x rm


end
