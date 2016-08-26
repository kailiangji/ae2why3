open Format
open Lexing

type pos = Lexing.position * Lexing.position

let report fmt (b,e) =
  let l = b.pos_lnum in
  let fc = b.pos_cnum - b.pos_bol + 1 in
  let lc = e.pos_cnum - b.pos_bol + 1 in
  fprintf fmt "File \"%s\", line %d, characters %d-%d:"
    (Options.get_file()) l fc lc
