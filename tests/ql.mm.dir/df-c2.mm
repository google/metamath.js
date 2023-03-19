
axiom df-c2
  let wva: term a
  let wvb: term b
  assume df-c2.1: |- a C b
  assert |- a = ( ( a ^ b ) v ( a ^ b ' ) )
end
