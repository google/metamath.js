
axiom df-wwlks
  let vw: setvar w
  let vg: setvar g
  let vi: setvar i
  assert |- WWalks = ( g e. _V |-> { w e. Word ( Vtx ` g ) | ( w =/= (/) /\ A. i e. ( 0 ..^ ( ( # ` w ) - 1 ) ) { ( w ` i ) , ( w ` ( i + 1 ) ) } e. ( Edg ` g ) ) } )
end
