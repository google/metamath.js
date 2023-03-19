
axiom df-c2
  param wva: term a
  param wvb: term b
  assume df-c2.1: |- a C b
  assert |- a = ( ( a ^ b ) v ( a ^ b ' ) )
end
