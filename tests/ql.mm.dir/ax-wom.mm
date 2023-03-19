
axiom ax-wom
  param wva: term a
  param wvb: term b
  assume ax-wom.1: |- ( a ' v ( a ^ b ) ) = 1
  assert |- ( b v ( a ' ^ b ' ) ) = 1
end
