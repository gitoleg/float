open Core_kernel
open Gfloat

let string_of_rm x = Sexp.to_string (sexp_of_rounding x)

let rm_of_int = function
  | 0 -> Nearest_even
  | 1 -> Negative_inf
  | 2 -> Positive_inf
  | 3 -> Towards_zero
  | 4 -> Nearest_away
  | _ -> failwith "unexpected rounding mode!"

let rms =
  List.map [ Nearest_even; Negative_inf; Positive_inf;
             Towards_zero; Nearest_away;  ]
    ~f:(fun r -> r, string_of_rm r)

let desc = desc ~radix:10 ~expn_bits:15 54

let works () =
  let mk = create desc in
  let x = mk ~expn:(Z.of_int (-12)) Z.(of_int (-10111111000101)) in
  let y = mk ~expn:(Z.of_int (-3)) Z.(of_int (978554469)) in
  add x y

let bits z =
  let bits = List.init 64 ~f:(fun i ->
      if Z.testbit z i then '1' else '0') |> List.rev in
  let rec build i s c =
    if i = 0 || i = 10 then sprintf "%s%c_" s c
    else sprintf "%s%c" s c in
  List.foldi bits ~init:"" ~f:build


(* bid64_add 4 -55.568E-5 +9868.E5 [6c3b0ee4caa4aa4b] 20 *)
let a () =
  let mk = create desc in
  let x = mk ~expn:(Z.of_int (-8)) Z.(of_int (-55568)) in
  let y = mk ~expn:(Z.of_int 5) Z.(of_int 9868) in
  let z = add x y  in
  match fin z with
  | None -> printf "FAIL!!\n"
  | Some (e,f) -> printf "my: %s %s\n" (Z.format "d" e) (Z.format "d" f)

let extract str =
  let _, expn, frac = Decode.of_int64 (Int64.of_string str) in
  printf "from %s: %Ld, %Ld\n" str expn frac

(* let () = extract "0x6c3b0ee4caa4aa4b" *)
(* let a () = extract "0x6c22c3cf207d470e" *)

let rewrite () =
  let remove_brakets x =
    let x' = String.filter x ~f:(fun c ->
        c <> '[' && c <> ']') in
    if String.equal x x' then x
    else "0x" ^ x' in
  let of_str line =
    match String.split ~on:' ' line with
    | [name; rm; op1; op2; res; _no_matter] ->
      let op1 = remove_brakets op1 in
      let op2 = remove_brakets op2 in
      let res = remove_brakets res in
      let rm = int_of_string rm |> rm_of_int |> string_of_rm in
      Some (sprintf "%s %s %s %s %s" name rm op1 op2 res)
    | strs ->
      let str = String.concat strs in
      printf "skipped %s\n" str;
      None in
  Out_channel.with_file "r_table" ~f:(fun out ->
      In_channel.with_file "table" ~f:(fun ch ->
          let lines = In_channel.input_lines ch in
          let lines = List.map lines ~f:of_str in
          let lines = List.filter_map ~f:ident lines in
          Out_channel.output_lines out lines))

let read64 () =
  let of_string s =
    if String.is_prefix ~prefix:"0x" s then
      let x = Int64.of_string s in
      let is_neg, expn, frac = Decode.of_int64 x in
      let frac = Z.of_int64 frac in
      let frac = if is_neg then Z.neg frac else frac in
      let expn = Z.of_int64 expn in
      expn, frac
    else
      match String.split ~on:'E' s with
      | [frac; expn] ->
        let expn = int_of_string expn in
        let frac,is_neg =
          if String.is_prefix ~prefix:"-" frac then
            String.drop_prefix frac 1, true
          else if String.is_prefix ~prefix:"+" frac then
            String.drop_prefix frac 1, false
          else frac, false in
        let expn, frac = match String.index frac '.' with
          | None -> expn, frac
          | Some point ->
            let digits = String.length frac - 1 in
            let expn = expn - digits + point in
            let frac = String.filter ~f:(fun c -> c <> '.') frac in
            expn, frac in
        let expn = Z.of_int expn in
        let frac = Z.of_string frac in
        let frac = if is_neg then Z.neg frac else frac in
        expn, frac
      | ["0"] -> Z.zero, Z.zero
      | ["-0"] -> Z.zero, Z.neg Z.zero
      | _ ->  (* printf "didn't parse %s\n" s;*) Z.zero, Z.zero in
  let i =  ref 0 in
  let of_line line =
    match String.split line ~on:' ' with
    | [name; rm; op1; op2; res;] ->
      let exp1,frac1 = of_string op1 in
      let exp2,frac2 = of_string op2 in
      let expr,fracr = of_string res in

      printf "%d, %s, (%s, \"%s\"), (%s, \"%s\"), (%s, \"%s\");\n"
        !i
        rm (Z.to_string exp1) (Z.to_string frac1)
        (Z.to_string exp2) (Z.to_string frac2)
        (Z.to_string expr) (Z.to_string fracr);
      incr i;
      ignore(of_string op1);
      ignore(of_string op2);
      ignore(of_string res)
    | _ -> printf "strange line %s\n" line in
  let of_line line =
    try
      of_line line
    with _ -> printf "exn!! %s\n" line in

  In_channel.with_file "table" ~f:(fun ch ->
      let lines = In_channel.input_lines ch in
      List.iter ~f:of_line lines)


let () = read64 ()
