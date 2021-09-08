open! Core_kernel
module Sha256 = Mycrypto.Sha256

let () =
  let h = Sha256.create () in
  let len = 8192 in
  let buf = Bytes.create len in
  let rec loop () =
    let read_bytes = In_channel.input In_channel.stdin ~buf ~pos:0 ~len in
    if Int.( = ) read_bytes 0
    then ()
    else (
      Sha256.add_bytes h buf ~pos:0 ~len:read_bytes;
      loop ())
  in
  loop ();
  let digest = Sha256.hexdigest h in
  printf "hexdigest: %s\n" digest
