
axiom ax-wom
  let wva: term a
  let wvb: term b
  assume ax-wom.1: |- ( a ' v ( a ^ b ) ) = 1
  assert |- ( b v ( a ' ^ b ' ) ) = 1
end
