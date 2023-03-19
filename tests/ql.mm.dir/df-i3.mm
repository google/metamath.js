
axiom df-i3
  param wva: term a
  param wvb: term b
  assert |- ( a ->3 b ) = ( ( ( a ' ^ b ) v ( a ' ^ b ' ) ) v ( a ^ ( a ' v b ) ) )
end
