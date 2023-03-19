
axiom df-wwlksn
  let vw: setvar w
  let vg: setvar g
  let vn: setvar n
  assert |- WWalksN = ( n e. NN0 , g e. _V |-> { w e. ( WWalks ` g ) | ( # ` w ) = ( n + 1 ) } )
end
