

axiom ax-eqmp
  param ta: term A
  param tb: term B
  param tr: term R
  assume ax-eqmp.1: |- R |= A
  assume ax-eqmp.2: |- R |= ( ( = A ) B )
  assert |- R |= B
end
