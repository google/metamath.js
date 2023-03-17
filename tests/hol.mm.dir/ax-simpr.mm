

axiom ax-simpr
  let tr: term R
  let ts: term S
  assume ax-simpl.1: |- R : bool
  assume ax-simpl.2: |- S : bool
  assert |- ( R , S ) |= S
end
