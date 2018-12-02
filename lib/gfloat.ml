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

  (* let extract_last_ x n =
   *   let open B in
   *   sort x >>= fun sort ->
   *   x >>= fun v ->
   *   let mask = not (ones sort lsl n)  in
   *   x land mask *)

  let extract_last x n =
    let open B in
    sort x >>= fun xsort ->
    sort n >>= fun nsort ->
    ite (is_zero n) (zero xsort)
      (extract xsort n (zero nsort) (pred x))


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
    let is_needed = and_ (non_zero loss) is_needed in
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

  let bind exp body =
    sort exp >>= fun s ->
    Var.Generator.fresh s >>= fun v ->
    B.let_ v exp (body (B.var v))

  let clz x =
    sort x >>= fun sort ->
    size x >>= fun size ->
    let pow, num = nearest_pow2 size in
    let sort' = Bits.define num in
    let shifts = List.init pow ~f:(fun p -> num / (2 lsl p)) in
    let shifts,_ =
      List.fold shifts ~init:([],0)
        ~f:(fun (acc,prev) curr ->
          let sum = curr + prev in
          (sum, curr) :: acc, sum) in
    let shifts = List.rev shifts in
    let x' = B.unsigned sort' x in
    let r =
      List.fold shifts ~init:(!! (x', B.zero sort))
        ~f:(fun x (sum, sh) ->
          x >>= fun (x,n) ->
          let shift =  B.of_int sort sh in
          let sum = B.of_int sort sum in
          let mask = B.(ones sort' lsl sum) in
          Var.Generator.fresh sort' >>= fun v_mask ->
          Var.Generator.fresh sort' >>= fun masked_x ->
          let x' =
            B.let_ v_mask mask (
                B.let_ masked_x B.(x land var v_mask) (
                    B.(ite (is_zero (var masked_x)) B.(x lsl shift) x))) in
          let n' =
            B.let_ v_mask mask (
                B.let_ masked_x B.(x land var v_mask) (
                    B.(ite (is_zero (var masked_x)) B.(n + shift) n))) in
          !! (x', n')) in
    r >>= fun (_,n) ->
    let dif = B.of_int sort (num - size) in
    B.ite (B.is_zero x) (B.of_int sort size) B.(n - dif)

  (* the same as [align_right] above, but stops in case of bits loss
     OR if exponent reached a maximum of it's value
     TODO: consider test frac for zero to prevent expn change *)
  let safe_align_right expn coef =
    expn >>= fun vexpn ->
    coef >>= fun vcoef ->
    let max_expn = max_exponent (Value.sort vexpn) in
    let prec = Bits.size (Value.sort vcoef) in
    let unos = B.(one (Value.sort vcoef)) in
    let rec run i expn coef =
      if i < prec then
        let stop = B.(or_ (expn = max_expn) (lsb coef)) in
        let expn = B.(ite stop expn (succ expn)) in
        let coef = B.(ite stop coef (coef lsr unos)) in
        run (i + 1) expn coef
      else expn, coef in
    !! (run 0 expn coef)

  (* TODO: consider test coef for zero to prevent expn change *)
  let safe_align_left expn coef =
    let open B in
    sort expn >>= fun exps ->
    sort coef >>= fun sigs ->
    let min_expn = min_exponent exps in
    let clz = clz coef in
    let shift = umin clz (unsigned sigs (abs (expn - min_expn))) in
    let dexpn = umin (unsigned exps clz) (abs (expn - min_expn)) in
    let coef = coef lsl shift in
    let expn = expn + dexpn in
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

  let test x =
    let expn = exponent x in
    let expn = B.succ expn in
    x >>-> fun xs xv ->
    sema expn >>= fun expn ->
    let y = Some {xv with expn; } in
    !! (Value.put gfloat (Value.empty xs) y)

  let test x =
    let expn = exponent x in
    sort expn >>= fun exps ->
    Var.Generator.fresh exps >>= fun v ->
    B.let_ v (B.succ expn)
      begin
        let var = B.var v in
        x >>-> fun xs xv ->
        sema var >>= fun expn ->
        let y = Some {xv with expn; } in
        !! (Value.put gfloat (Value.empty xs) y)
      end

  let minimize_exponent' x =
    let open B in
    let expn = exponent x in
    let coef = significand x in
    sort expn >>= fun exps ->
    sort coef >>= fun sigs ->
    let min_expn = min_exponent exps in
    bind (clz coef) (fun clz ->
        let shift = umin clz (unsigned sigs (abs (expn - min_expn))) in
        let dexpn = umin (unsigned exps clz) (abs (expn - min_expn)) in
        let coef = coef lsl shift in
        let expn = expn + dexpn in
        with' x ~expn ~coef)

  (* max exponent without bit loss or exponent overflow,
     fraction shifted as right as possible, i.e. it occupies
     less significant bits *)
  let maximize_exponent x =
    let e = exponent x in
    let c = significand x in
    safe_align_right e c >>= fun (expn,coef) ->
    with' x ~expn ~coef

  let norm = minimize_exponent

  let prec x = Bits.size (Value.sort x)

  let of_bit x = !! (Value.create Bool.t x)

  let is_pinf x =
    x >>-> fun _ v ->
    B.(and_ (inv (of_bit v.sign)) (of_bit v.is_inf))

  let is_ninf x =
    x >>-> fun _ v ->
    B.(and_ ((of_bit v.sign)) (of_bit v.is_inf))

  let is_inf x = x >>-> fun _ v -> of_bit v.is_inf
  let is_snan x = x >>-> fun _ v -> of_bit v.is_snan
  let is_qnan x = x >>-> fun _ v -> of_bit v.is_qnan
  let is_nan x = B.or_ (is_snan x) (is_qnan x)

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
  let xor_sign s s' = B.(inv (and_ s s'))

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

  let fadd rm x y =
    let open B in
    let _,xexpn,xcoef = data x in
    let _,yexpn,ycoef = data y in
    let expn = max xexpn yexpn in
    let lost_bits = abs (xexpn - yexpn) in
    let xcoef = ite (xexpn >$ yexpn) xcoef (xcoef lsr lost_bits) in
    let ycoef = ite (yexpn >$ xexpn) ycoef (ycoef lsr lost_bits) in
    expn  >>= fun vexpn  ->
    xcoef >>= fun vxcoef ->
    let loss =
      match_ [
          (xexpn = yexpn)  --> zero (Value.sort vxcoef);
          (xexpn >$ yexpn) --> extract_last ycoef lost_bits;
     ] ~default:(extract_last xcoef lost_bits)  in
    let coef = xcoef + ycoef in
    let max_expn = max_exponent (Value.sort vexpn) in
    let is_inf = and_ (coef >= xcoef) (expn = max_expn) in
    let expn = ite (coef >= xcoef) expn (succ expn)in
    let coef = match_ [
        (coef >= xcoef) --> round rm b0 coef loss lost_bits;
      ] ~default:(
          coef >>= fun vcoef ->
          let one = one (Value.sort vcoef) in
          let coef,loss' = rshift_coef coef one in
          let loss = combine_loss loss' loss in
          let sh = of_int (Value.sort vcoef)
              Caml.(Bits.size (Value.sort vcoef) - 1) in
          let one = one lsl sh in
          let coef = coef lor one in
          round rm b0 coef loss lost_bits) in
    with' x ~expn ~coef ~is_inf

  let extend x addend =
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
    let half = half_of_loss loss lost_bits in
    match_ [
        (is_zero lost_bits) --> loss;
        (loss = half) --> loss;
      ] ~default:(not loss)

  let one_mask sort n =
    let open B in
    let one = one sort in
    one lsl (pred n)

  let invert_loss loss lost_bits =
    let open B in
    sort loss >>= fun sort ->
    let mask = one_mask sort lost_bits in
    ite (or_ (is_zero lost_bits)
           (loss land mask = mask)) loss
        (not loss)

  let combine_loss loss' loss lost_bits =
    let loss' = B.(loss' lsl lost_bits) in
    B.(loss' lor loss')

  let fsub rm x y =
    let open B in
    let extend z = extend (minimize_exponent z) 1 in
    sort x >>= fun fsort ->
    let sigs = Floats.sigs fsort in
    let exps = Floats.exps fsort in
    let xsign,xexpn,xcoef = data (extend x) in
    let _,yexpn,ycoef = data (extend y) in
    sort xcoef >>= fun sigs' ->
    bind xexpn (fun xexpn ->
        bind yexpn (fun yexpn ->
            bind xcoef (fun xcoef ->
                bind ycoef (fun ycoef ->
                    let match_expn ~on_equal ~xgt ~ygt =
                      match_ [
                        (xexpn = yexpn) --> on_equal;
                        (xexpn >$ yexpn) --> xgt;
                      ] ~default:ygt in
                    let lost_bits = B.abs (xexpn - yexpn) in
                    let expn = max xexpn yexpn in
                    bind lost_bits (fun lost_bits ->
                        let lost_bits =
                          ite (is_zero lost_bits) lost_bits (lost_bits - one exps) in
                        let loss = match_ [
                            (is_zero lost_bits) --> zero sigs';
                            (xexpn >$ yexpn) --> extract_last ycoef lost_bits;
                          ] ~default:(extract_last xcoef lost_bits) in
                        bind loss (fun loss ->
                            let reverse = match_expn ~on_equal:(xcoef < ycoef) ~xgt:b0 ~ygt:b1 in
                            let xcoef =
                              match_expn ~on_equal:xcoef
                                ~xgt:(xcoef lsl one sigs') ~ygt:(xcoef lsr lost_bits) in
                            let ycoef =
                              match_expn ~on_equal:ycoef
                                ~xgt:(ycoef lsr lost_bits) ~ygt:(ycoef lsl one sigs') in
                            let loss = invert_loss loss lost_bits in
                            let __borrow = ite (is_zero loss) (zero sigs') (one sigs') in
                            let borrow = one sigs' in
                            bind borrow (fun borrow ->
                                let coef = ite reverse
                                    (ycoef - xcoef - borrow)
                                    (xcoef - ycoef - borrow) in
                                let sign = ite reverse (inv xsign) xsign in
                                bind coef (fun coef ->
                                    bind (msb coef) (fun msb' ->
                                        let expn = ite msb' (succ expn) expn in
                                        let coef = ite msb' (coef lsr one sigs') coef in
                                        let loss' = ite msb'
                                            (extract_last coef (one sigs'))
                                            (zero sigs') in
                                        let loss = ite msb'
                                            (combine_loss loss' loss lost_bits)
                                            loss in
                                        let coef = unsigned sigs coef in
                                        let lost_bits =
                                          ite (msb coef) (succ lost_bits) lost_bits in
                                        (* let coef = round rm sign coef loss lost_bits in *)
                                        coef)))))))))

(* with' x ~expn ~coef ~sign)))) *)



  (* let add_or_sub rm subtract a b =
   *     check_operands a b;
   *     let s1 = B.of_bool subtract in
   *     let s2 = B.of_sign a.sign in
   *     let s3 = B.of_sign b.sign in
   *     let is_subtract = B.is_one B.(s1 lxor (s2 lxor s3)) in
   *     if is_subtract then sub rm a b
   *     else add rm a b
   *
   *    let add ?(rm=Nearest_even) = add_or_sub rm false
   *    let sub ?(rm=Nearest_even) = add_or_sub rm true *)

  (* let unsafe_rshift x n =
   *   let frac, loss = rshift_frac x.frac n in
   *   let expn = B.(x.expn + n) in
   *   { expn; frac }, loss *)

     (* let multiply rm x y =
      *  let extract expn frac =
      *    let expn = B.extract ~hi:(desc.ebits - 1) expn in
      *    let frac = B.extract ~hi:(desc.fbits - 1) frac in
      *    expn, frac in
      *  let extend {expn; frac} = {
      *    expn = B.sign_extend expn desc.ebits;
      *    frac = B.zero_extend frac desc.fbits;
      *  } in
      *  let x = extend x in
      *  let y = extend y in
      *  let expn = B.(x.expn + y.expn) in
      *  let frac = B.(x.frac * y.frac) in
      *  let max_expn =
      *    B.sign_extend (max_exponent desc.ebits) desc.ebits in
      *  let min_expn =
      *    B.sign_extend (min_exponent desc.ebits) desc.ebits in
      *  match align_right desc.radix desc.fbits expn frac with
      *  | None -> `Overflow_expn
      *  | Some (expn,frac,loss) ->
      *    if B.is_positive expn && B.(expn > max_expn)
      *    then `Overflow_expn
      *    else if
      *      B.is_positive expn then
      *      let expn, frac = extract expn frac in
      *      let expn = B.extract ~hi:(desc.ebits - 1) expn in
      *      `Nice (expn,frac,loss)
      *    else if
      *      B.is_negative expn && B.(expn <$ min_expn) then
      *      let dexp = B.(abs expn - abs min_expn) in
      *      let {expn;frac=frac'}, loss' = unsafe_rshift desc.radix {expn;frac} dexp in
      *      if B.is_zero frac' && not (B.is_zero frac) then `Underflow_expn
      *      else
      *        let loss' = combine_loss loss' loss in
      *        let expn, frac = extract expn frac' in
      *        `Nice (expn,frac',loss')
      *    else
      *      let expn, frac = extract expn frac in
      *      `Nice (expn,frac,loss) *)

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
       let xexpn = signed exps xexpn in
       let yexpn = signed exps yexpn in
       let xcoef = unsigned sigs xcoef in
       let ycoef = unsigned sigs ycoef in
       let expn = xexpn + yexpn in
       let coef = xcoef * ycoef in
       let sign = xor_sign xsign ysign in
       let clz = clz coef in
       let prec = of_int sigs coef_bits in
       let shift = ite (clz >= prec) (zero sigs) (prec - clz) in
       let dexpn = ite (expn <$ min_expn) (abs expn - abs min_expn) (zero exps) in
       let shift = shift + unsigned sigs dexpn in
       let dexpn' = unsigned exps shift + dexpn in
       let coef' = coef lsr shift in
       let expn = expn + dexpn' in
       let loss = extract_last coef shift in
       let coef = round rm sign coef' loss shift in
       let is_inf = expn >$ max_expn in
       let coef = ite (expn <$ min_expn) (zero sigs) coef in
       let expn = ite (expn <$ min_expn) (zero exps) expn in
       let coef = unsigned (Floats.sigs fsort) coef in
       let expn = unsigned (Floats.exps fsort) expn in
       with' x ~expn ~coef ~sign ~is_inf

     (* let div rn x y =
      *   let open B in
      *   sort x >>= fun fsort ->
      *   precision x >>= fun coef_bits ->
      *   let exps = double (Floats.exps fsort) in
      *   let sigs = double (Floats.sigs fsort) in
      *   let min_expn = signed exps (min_exponent (Floats.exps fsort)) in
      *   let max_expn = signed exps (max_exponent (Floats.exps fsort)) in
      *   let xsign, xexpn, xcoef = data x in
      *   let ysign, yexpn, ycoef = data y in
      *   let xexpn = signed exps xexpn in
      *   let yexpn = signed exps yexpn in
      *   let xcoef = unsigned sigs xcoef in
      *   let ycoef = unsigned sigs ycoef in
      *   safe_align_left xexpn xcoef >>= fun (xexpn,xcoef) ->
      *   let sign = xor_sign xsign ysign in
      *   let expn = xexpn - yexpn in
      *   let coef = xcoef / ycoef in
      *   let loss = xcoef - coef * ycoef in
      *   let is_inf = expn >$ max_expn in
      *   let lost_bits = *)


     (* let div ?(rm=Nearest_even) a b =
   *     let extend_expn e = B.sign_extend e (sort e) in
   *     let min_expn = extend_expn (min_exponent a.desc.ebits) in
   *     let max_expn = extend_expn (max_exponent a.desc.ebits) in
   *     let extend {expn; frac} =
   *       let expn = extend_expn expn in
   *       let frac = B.zero_extend frac (sort frac) in
   *       {expn; frac} in
   *     let is_overflow _ = false in
   *     check_operands a b;
   *     match a.data,b.data with
   *     | Fin x, Fin y when is_zero a && is_zero b -> nan ~negative:true a.desc
   *     | Fin x, Fin y when is_zero b -> {a with data = Inf}
   *     | Fin x, Fin y ->
   *       let x = extend x in
   *       let y = extend y in
   *       let sign = xor_sign a.sign b.sign in
   *       let xexpn, xfrac = safe_align_left a.desc.radix x.expn x.frac in
   *       let expn = B.(xexpn - y.expn) in
   *       let frac = B.(xfrac / y.frac) in
   *       if B.(expn >$ max_expn) || is_overflow expn frac then
   *         {a with sign; data = Inf}
   *       else
   *         let left = B.(xfrac - frac * y.frac) in
   *         let left = B.(left lsl 1) in
   *         let loss =
   *           if B.is_zero left then ExactlyZero
   *           else if B.(left > y.frac) then MoreThanHalf
   *           else if B.(left = y.frac) then ExactlyHalf
   *           else LessThanHalf in
   *         let frac = round rm sign frac loss in
   *         let expn,frac,_ =
   *           if B.(expn <$ min_expn) then
   *             let dexp = B.(abs expn - abs min_expn) in
   *             let {expn;frac=frac'}, loss' = unsafe_rshift a.desc.radix {expn;frac} dexp in
   *             let frac = round rm sign frac' loss' in
   *             let expn = B.extract ~hi:(a.desc.ebits - 1) expn in
   *             expn,frac, combine_loss loss' loss
   *           else
   *             let expn = B.extract ~hi:(a.desc.ebits - 1) expn in
   *             expn,frac,loss in
   *         let data =
   *           match align_right ~base:a.desc.radix ~precision:a.desc.fbits expn frac with
   *           | None -> zero_finite a.desc
   *           | Some (expn,frac,loss') ->
   *             let frac = round rm sign frac loss' in
   *             let frac = B.extract ~hi:((prec a) - 1) frac in
   *             norm (radix a) {frac; expn} in
   *         {a with data = Fin data; sign; }
   *     | Nan _, Nan _ -> if is_signaling_nan a || is_quite_nan b then a else b
   *     | Nan _, _ -> a
   *     | _, Nan _ -> b
   *     | Inf, Inf -> nan ~negative:true a.desc
   *     | Inf, _ -> a
   *     | _, Inf -> b *)

end
