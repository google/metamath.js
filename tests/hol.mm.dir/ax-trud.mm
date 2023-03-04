

axiom ax-trud
  let tr: term R
  assume ax-trud.1: |- R : bool
  assert |- R |= T.
end
