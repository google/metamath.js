
axiom ax-wdol
  param wva: term a
  param wvb: term b
  assert |- ( ( a == b ) v ( a == b ' ) ) = 1
end
