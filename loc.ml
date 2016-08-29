open Printf
open Lexing

type t = Lexing.position * Lexing.position

let report chan_out (b,e) =
  let l = b.pos_lnum in
  let fc = b.pos_cnum - b.pos_bol + 1 in
  let lc = e.pos_cnum - b.pos_bol + 1 in
  fprintf chan_out "File \"%s\", line %d, characters %d-%d:"
    (Options.get_file()) l fc lc
