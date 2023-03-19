
axiom df-b
  let wva: term a
  let wvb: term b
  assert |- ( a == b ) = ( ( a ' v b ' ) ' v ( a v b ) ' )
end
