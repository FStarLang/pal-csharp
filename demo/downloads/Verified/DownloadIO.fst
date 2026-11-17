module DownloadIO
#lang-pulse

open Pulse.Lib.Pervasives
module Seq = FStar.Seq
module A = Pulse.Lib.CSharp.Array
module I32 = FStar.Int32
module U8 = FStar.UInt8

noeq type source = {
  bytes: Seq.seq U8.t;
  cursor: ref int;
}

let contents (s:source) = s.bytes
let at ([@@@mkey] s:source) (offset:int) : slprop =
  pts_to s.cursor offset ** pure (0 <= offset /\ offset <= Seq.length s.bytes)

instance send_at s offset : Pulse.Lib.Send.is_send (at s offset) =
  Tactics.Typeclasses.solve

let prefix (input output:Seq.seq U8.t) (n:int) : prop =
  0 <= n /\ n <= Seq.length input /\ n <= Seq.length output /\
  (forall (i:nat). i < n ==> Seq.index output i == Seq.index input i)

(* Trusted Stream.ReadAsync boundary: normal completion appends at most the
   requested bytes and preserves the prefix. Zero means EOF. The HTTP wrapper
   bounds content length and owns/disposes the response; failures do not return
   through this normal-completion contract. No network progress is assumed. *)
assume val read (s:source) (target:A.array U8.t) (offset:I32.t)
  (#before:erased (Seq.seq U8.t))
  : Pulse.Lib.Core.stt_div I32.t
      (at s (I32.v offset) ** A.pts_to target before **
       pure (prefix s.bytes before (I32.v offset) /\ I32.v offset < Seq.length before))
      (fun n ->
        exists* (after:Seq.seq U8.t{Seq.length after == Seq.length before}).
          at s (I32.v offset + I32.v n) ** A.pts_to target after **
          pure (0 <= I32.v n /\ I32.v n <= Seq.length after - I32.v offset /\
                prefix s.bytes after (I32.v offset + I32.v n) /\
                (I32.v n == 0 <==> I32.v offset == Seq.length s.bytes)))
