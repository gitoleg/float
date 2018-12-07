open Core_kernel

module IEEE754 : sig
  type t = private {
    bias : int;
    k : int;
    p : int;
    w : int;
    t : int;
  }

  val create : int -> t option
end = struct
  (* see IEEE754 3.6 *)
  type t = {
    bias : int;
    k : int;
    p : int;
    w : int;
    t : int;
  }

  let (^) b e = Int.of_float (float b ** float e)

  let log2 n = log n /. log 2.
  let round x = round ~dir:`Nearest x

  let prec k =
    let k = float k in Int.of_float @@
    k -. round(4. *. log2 k) +. 13.

  let ebits k =
    let k = float k in Int.of_float @@
    round(4. *. log2 k) -. 13.

  let bias k p = (2^(k-p-1))-1

  let make64plus k =
    let p = prec k and w = ebits k in {
      k; w; p;
      t = k - w - 1;
      bias = bias k p;
    }

  let binary16 = {
    k = 16;
    p = 11;
    bias = 15;
    w = 5;
    t = 10;
  }

  let binary32 = {
    k = 32;
    p = 24;
    bias = 127;
    w = 11;
    t = 23;
  }

  let create = function
    | 0  -> None
    | 16 -> Some binary16
    | 32 -> Some binary32
    | n when n mod 32 = 0 -> Some (make64plus n)
    | _ -> None
end
