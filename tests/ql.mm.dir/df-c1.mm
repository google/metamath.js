
axiom df-c1
  let wva: term a
  let wvb: term b
  assume df-c1.1: |- a = ( ( a ^ b ) v ( a ^ b ' ) )
  assert |- a C b
end
