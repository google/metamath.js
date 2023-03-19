

axiom ax-id
  let tr: term R
  assume ax-id.1: |- R : bool
  assert |- R |= R
end
