
axiom ax-trud
  param tr: term R
  assume ax-trud.1: |- R : bool
  assert |- R |= T.
end
