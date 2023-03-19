
axiom df-i3
  let wva: term a
  let wvb: term b
  assert |- ( a ->3 b ) = ( ( ( a ' ^ b ) v ( a ' ^ b ' ) ) v ( a ^ ( a ' v b ) ) )
end
