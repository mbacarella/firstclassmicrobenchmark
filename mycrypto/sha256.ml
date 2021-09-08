(* An implementation of the SHA-256 hash function in OCaml
   Copyright (C) 2008 Michael Bacarella <m@bacarella.com> *)

(* Yes, we could use Cryptokit, but that pulls in annoying dependencies, like libgmp just for
   doing sha256. I just happened to have this laying around already, so... *)

module type Int32_intf = sig
  type elt

  (* The compiler has trouble looking through the module interface and figuring
     out that it should emit fast integer arrays instead of generic arrays.
     Specifying the array element types via this definition will help.

     It's worth about a 30% speedup.

     More discussion here:
     https://discuss.ocaml.org/t/unboxed-int32-t-on-64-bit/8363/18
  *)
  module Array : sig
    type t = elt array

    val make : int -> elt -> t
    val get : t -> int -> elt
    val unsafe_get : t -> int -> elt
    val unsafe_set : t -> int -> elt -> unit
  end

  type t = elt

  val logand : t -> t -> t
  val take_lower_32_bits : t -> t
  val add : t -> t -> t
  val shift_right_logical : t -> int -> t
  val shift_left : t -> int -> t
  val logor : t -> t -> t
  val logxor : t -> t -> t
  val lognot : t -> t
  val of_int : int -> t
  val to_stdlib_int32 : t -> int32
  val of_char : char -> t
end

module Unboxed_int32 = struct
  (* Provides unboxed 32-bit operations on 64-bit platforms.
     Must do [take_lower_32_bits x] before final storing or bitwise shifts to
     avoid pulling stuff in from the higher 32-bits.

     Fast bitwise modulus of powers of 2: n % m == n & (m - 1)
  *)
  type elt = int

  module Array = struct
    type t = elt array

    let make size elt : t = Array.make size (elt : elt)
    let get a i = Array.get (a : t) i
    let unsafe_get a i : elt = Array.unsafe_get (a : t) i
    let unsafe_set a i elt = Array.unsafe_set (a : t) i (elt : elt)
  end

  type t = elt

  let raise_2_to_32 = 1 lsl 32
  let raise_2_to_32_minus_1 = pred raise_2_to_32
  let logand a b = Int.logand a b
  let take_lower_32_bits x = logand x raise_2_to_32_minus_1
  let add a b = Int.add a b
  let shift_right_logical a b = Int.shift_right_logical a b
  let shift_left a b = Int.shift_left a b
  let logor a b = Int.logor a b
  let logxor a b = Int.logxor a b
  let lognot x = Int.lognot x
  let of_int x = take_lower_32_bits x
  let to_stdlib_int32 x = Stdlib.Int32.of_int x
  let of_char c = Char.code c
end

module Boxed_int32 = struct
  include Int32

  type elt = t

  module Array = struct
    type t = elt array

    let make size elt : t = Array.make size (elt : elt)
    let get a i = Array.get (a : t) i
    let unsafe_get a i : elt = Array.unsafe_get (a : t) i
    let unsafe_set a i elt = Array.unsafe_set (a : t) i (elt : elt)
  end

  type t = elt

  let take_lower_32_bits x = x
  let to_stdlib_int32 x = x
  let of_char c = of_int (Char.code c)
end

let boxed_int32 = (module Boxed_int32 : Int32_intf)
let unboxed_int32 = (module Unboxed_int32 : Int32_intf)

module Int32 =
(val match Sys.word_size with
     | 32 -> boxed_int32
     | 64 -> unboxed_int32
     | bits -> failwith (Printf.sprintf "Sys.word_size: unsupported: %d" bits))

module Array = Int32.Array

let shift_right x n = Int32.shift_right_logical x n
let rotate2 x = Int32.logor (shift_right x 2) (Int32.shift_left x 30)
let rotate6 x = Int32.logor (shift_right x 6) (Int32.shift_left x 26)
let rotate7 x = Int32.logor (shift_right x 7) (Int32.shift_left x 25)
let rotate11 x = Int32.logor (shift_right x 11) (Int32.shift_left x 21)
let rotate13 x = Int32.logor (shift_right x 13) (Int32.shift_left x 19)
let rotate17 x = Int32.logor (shift_right x 17) (Int32.shift_left x 15)
let rotate18 x = Int32.logor (shift_right x 18) (Int32.shift_left x 14)
let rotate19 x = Int32.logor (shift_right x 19) (Int32.shift_left x 13)
let rotate22 x = Int32.logor (shift_right x 22) (Int32.shift_left x 10)
let rotate25 x = Int32.logor (shift_right x 25) (Int32.shift_left x 7)
let ch x y z = Int32.logxor (Int32.logand x y) (Int32.logand (Int32.lognot x) z)
let sum0 x = Int32.logxor (rotate2 x) (Int32.logxor (rotate13 x) (rotate22 x))
let sum1 x = Int32.logxor (rotate6 x) (Int32.logxor (rotate11 x) (rotate25 x))
let rh00 x = Int32.logxor (rotate7 x) (Int32.logxor (rotate18 x) (shift_right x 3))
let rh01 x = Int32.logxor (rotate17 x) (Int32.logxor (rotate19 x) (shift_right x 10))
let maj x y z = Int32.logxor (Int32.logand x y) (Int32.logxor (Int32.logand x z) (Int32.logand y z))

type t =
  { mutable total_length : Int64.t;
    mutable h : Int32.Array.t;
    buffer : Buffer.t;
    w : Int32.Array.t;
    mutable is_final : bool
  }

let bits_to_bytes bits =
  match bits mod 8 with
  | 0 -> bits / 8
  | _ -> failwith "bits_to_bytes: bits must be multiple of 8"

let bytes_to_bits bytes = bytes * 8
let bs_in_bits = 512
let bs_in_bytes = bits_to_bytes 512

let k =
  [| 0x428a2f98;
     0x71374491;
     0xb5c0fbcf;
     0xe9b5dba5;
     0x3956c25b;
     0x59f111f1;
     0x923f82a4;
     0xab1c5ed5;
     0xd807aa98;
     0x12835b01;
     0x243185be;
     0x550c7dc3;
     0x72be5d74;
     0x80deb1fe;
     0x9bdc06a7;
     0xc19bf174;
     0xe49b69c1;
     0xefbe4786;
     0x0fc19dc6;
     0x240ca1cc;
     0x2de92c6f;
     0x4a7484aa;
     0x5cb0a9dc;
     0x76f988da;
     0x983e5152;
     0xa831c66d;
     0xb00327c8;
     0xbf597fc7;
     0xc6e00bf3;
     0xd5a79147;
     0x06ca6351;
     0x14292967;
     0x27b70a85;
     0x2e1b2138;
     0x4d2c6dfc;
     0x53380d13;
     0x650a7354;
     0x766a0abb;
     0x81c2c92e;
     0x92722c85;
     0xa2bfe8a1;
     0xa81a664b;
     0xc24b8b70;
     0xc76c51a3;
     0xd192e819;
     0xd6990624;
     0xf40e3585;
     0x106aa070;
     0x19a4c116;
     0x1e376c08;
     0x2748774c;
     0x34b0bcb5;
     0x391c0cb3;
     0x4ed8aa4a;
     0x5b9cca4f;
     0x682e6ff3;
     0x748f82ee;
     0x78a5636f;
     0x84c87814;
     0x8cc70208;
     0x90befffa;
     0xa4506ceb;
     0xbef9a3f7;
     0xc67178f2
  |]
  |> Stdlib.Array.map Int32.of_int

let create () =
  { total_length = 0L;
    h =
      [| Int32.of_int 0x6a09e667;
         Int32.of_int 0xbb67ae85;
         Int32.of_int 0x3c6ef372;
         Int32.of_int 0xa54ff53a;
         Int32.of_int 0x510e527f;
         Int32.of_int 0x9b05688c;
         Int32.of_int 0x1f83d9ab;
         Int32.of_int 0x5be0cd19
      |];
    buffer = Buffer.create 64;
    (* the 'w' is here just to cache the allocation *)
    w = Array.make bs_in_bytes (Int32.of_int 0);
    is_final = false
  }

let update ctx message =
  let hh = ctx.h in
  let message_bits = bytes_to_bits (String.length message) in
  assert (message_bits = bs_in_bits);
  let w = ctx.w in
  (* Process a 64-byte message into 16 32-bit integers. *)
  for t = 0 to 15 do
    (* There's a Bytes.get_int32_be that can do this, but it fails one of the unit tests for some
          reason, and it isn't faster anyway *)
    let x =
      let a = Int32.of_char (String.unsafe_get message (t * 4)) in
      let b = Int32.of_char (String.unsafe_get message ((t * 4) + 1)) in
      let c = Int32.of_char (String.unsafe_get message ((t * 4) + 2)) in
      let d = Int32.of_char (String.unsafe_get message ((t * 4) + 3)) in
      let a' = Int32.shift_left a 24 in
      let b' = Int32.shift_left b 16 in
      let c' = Int32.shift_left c 8 in
      Int32.logor a' (Int32.logor b' (Int32.logor c' d))
    in
    Array.unsafe_set w t x
  done;
  for t = 16 to 63 do
    let a = Int32.add (rh01 (Array.unsafe_get w (t - 2))) (Array.unsafe_get w (t - 7)) in
    let b = Int32.add (rh00 (Array.unsafe_get w (t - 15))) (Array.unsafe_get w (t - 16)) in
    Array.unsafe_set w t (Int32.add a b |> Int32.take_lower_32_bits)
  done;
  let rec hround ~a ~b ~c ~d ~e ~f ~g ~h t =
    match t with
    | 64 ->
      (* Mutating the array in-place seems slightly slower than outright replacing it. *)
      ctx.h
        <- [| Int32.add (Array.unsafe_get hh 0) a |> Int32.take_lower_32_bits;
              Int32.add (Array.unsafe_get hh 1) b |> Int32.take_lower_32_bits;
              Int32.add (Array.unsafe_get hh 2) c |> Int32.take_lower_32_bits;
              Int32.add (Array.unsafe_get hh 3) d |> Int32.take_lower_32_bits;
              Int32.add (Array.unsafe_get hh 4) e |> Int32.take_lower_32_bits;
              Int32.add (Array.unsafe_get hh 5) f |> Int32.take_lower_32_bits;
              Int32.add (Array.unsafe_get hh 6) g |> Int32.take_lower_32_bits;
              Int32.add (Array.unsafe_get hh 7) h |> Int32.take_lower_32_bits
           |]
    | t ->
      let t0 =
        let kt = Array.unsafe_get k t in
        let wt = Array.unsafe_get w t in
        Int32.add (Int32.add h (sum1 e)) (Int32.add (ch e f g) (Int32.add kt wt))
      in
      let t1 = Int32.add (sum0 a) (maj a b c) in
      hround
        ~h:g
        ~g:f
        ~f:e
        ~e:(Int32.add d t0 |> Int32.take_lower_32_bits)
        ~d:c
        ~c:b
        ~b:a
        ~a:(Int32.add t0 t1 |> Int32.take_lower_32_bits)
        (succ t)
  in
  hround
    ~a:(Array.unsafe_get hh 0)
    ~b:(Array.unsafe_get hh 1)
    ~c:(Array.unsafe_get hh 2)
    ~d:(Array.unsafe_get hh 3)
    ~e:(Array.unsafe_get hh 4)
    ~f:(Array.unsafe_get hh 5)
    ~g:(Array.unsafe_get hh 6)
    ~h:(Array.unsafe_get hh 7)
    0;
  ctx.total_length <- Int64.add ctx.total_length (Int64.of_int message_bits)

let final ctx message =
  let () =
    if ctx.is_final then failwith "Sha256.final called twice";
    ctx.is_final <- true
  in
  let message =
    let buf = Buffer.create 64 in
    Buffer.add_string buf message;
    buf
  in
  let original_length = bytes_to_bits (Buffer.length message) in
  assert (original_length < bs_in_bits);
  let pad_blocks = if original_length mod bs_in_bits < 448 then 1 else 2 in
  ctx.total_length <- Int64.add ctx.total_length (Int64.of_int original_length);
  Buffer.add_char message '\x80';
  let pad_start = bytes_to_bits (Buffer.length message) in
  let message_length = ((original_length / bs_in_bits) + pad_blocks) * bs_in_bits in
  (* appending k bits of 0 (where message_length-64 is our k) *)
  for _i = bits_to_bytes pad_start to bits_to_bytes (message_length - bits_to_bytes 64) - 8 do
    Buffer.add_char message '\x00'
  done;
  Buffer.add_bytes
    message
    (let b = Bytes.create 8 in
     Bytes.set_int64_be b 0 ctx.total_length;
     b);
  let new_length = bytes_to_bits (Buffer.length message) in
  if new_length = 1024
  then (
    update ctx (Buffer.sub message 0 bs_in_bytes);
    update ctx (Buffer.sub message bs_in_bytes bs_in_bytes))
  else if new_length = 512
  then update ctx (Buffer.contents message)
  else failwith ("Sha256.final: unexpected length " ^ string_of_int new_length)

let process_added ctx =
  let rec loop i =
    if Buffer.length ctx.buffer >= (i * 64) + 64
    then (
      update ctx (Buffer.sub ctx.buffer (i * 64) 64);
      loop (i + 1))
    else (
      let leftover = Buffer.sub ctx.buffer (i * 64) (Buffer.length ctx.buffer - (i * 64)) in
      Buffer.reset ctx.buffer;
      Buffer.add_string ctx.buffer leftover)
  in
  loop 0

let add_bytes ctx bytes ~pos ~len =
  Buffer.add_subbytes ctx.buffer bytes pos len;
  process_added ctx

let add_string ctx s =
  Buffer.add_substring ctx.buffer s 0 (String.length s);
  process_added ctx

let hexdigest ctx =
  (* should have been handled by add_bytes *)
  assert (Buffer.length ctx.buffer < 64);
  final ctx (Buffer.contents ctx.buffer);
  let m =
    let b = Bytes.create (bits_to_bytes 256) in
    let h = ctx.h in
    for i = 0 to pred 8 do
      Bytes.set_int32_be b (i * 4) (Int32.to_stdlib_int32 h.(i))
    done;
    b
  in
  let buf = Buffer.create 32 in
  for i = 0 to pred 32 do
    Buffer.add_string buf (Printf.sprintf "%02x" (int_of_char (Bytes.get m i)))
  done;
  Buffer.contents buf

let%test_module "test module" =
  (module struct
    let ts v h =
      let t = create () in
      add_bytes t (Bytes.of_string v) ~pos:0 ~len:(String.length v);
      hexdigest t = h

    let%test "1" = ts "" "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855"
    let%test "2" = ts "def" "cb8379ac2098aa165029e3938a51da0bcecfc008fd6795f401178647f96c5b34"
    let%test "3" = ts "abc" "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad"

    let%test "4" =
      ts
        "The quick brown fox jumps over the lazy dog"
        "d7a8fbb307d7809469ca9abcb0082e4f8d5651e46d3cdb762d02d0bf37c9e592"

    let%test "5" =
      ts
        "The quick brown fox jumps over the lazy cog"
        "e4c4d8f3bf76b692de791a173e05321150f7a345b46484fe427f6acc7ecc81be"

    let%test "6" = ts "abcabcabc" "76b99ab4be8521d78b19bcff7d1078aabeb477bd134f404094c92cd39f051c3e"

    let%test "7" =
      ts
        "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"
        "7d3e74a05d7db15bce4ad9ec0658ea98e3f06eeecf16b4c6fff2da457ddc2f34"

    let%test "8" =
      ts
        "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"
        "ffe054fe7ae0cb6dc65c3af9b61d5209f439851db43d0ba5997337df154668eb"

    let%test "9" =
      ts
        "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"
        "635361c48bb9eab14198e76ea8ab7f1a41685d6ad62aa9146d301d4f17eb0ae0"

    let%test "10" =
      ts
        "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"
        "6bc3b8eaea5380e522ff7df7736989b5e3fff569ba75003be63a8e7ab9c8123e"
  end)
