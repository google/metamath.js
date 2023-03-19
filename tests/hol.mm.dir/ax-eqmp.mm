
axiom ax-eqmp
  let ta: term A
  let tb: term B
  let tr: term R
  assume ax-eqmp.1: |- R |= A
  assume ax-eqmp.2: |- R |= ( ( = A ) B )
  assert |- R |= B
end
