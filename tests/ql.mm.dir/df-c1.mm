
axiom df-c1
  param wva: term a
  param wvb: term b
  assume df-c1.1: |- a = ( ( a ^ b ) v ( a ^ b ' ) )
  assert |- a C b
end
