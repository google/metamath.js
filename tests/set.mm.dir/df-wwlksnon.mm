
axiom df-wwlksnon
  let vw: setvar w
  let vg: setvar g
  let vn: setvar n
  let va: setvar a
  let vb: setvar b
  assert |- WWalksNOn = ( n e. NN0 , g e. _V |-> ( a e. ( Vtx ` g ) , b e. ( Vtx ` g ) |-> { w e. ( n WWalksN g ) | ( ( w ` 0 ) = a /\ ( w ` n ) = b ) } ) )
end
