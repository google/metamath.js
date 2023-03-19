
axiom df-clwwlk
  let vw: setvar w
  let vg: setvar g
  let vi: setvar i
  assert |- ClWWalks = ( g e. _V |-> { w e. Word ( Vtx ` g ) | ( w =/= (/) /\ A. i e. ( 0 ..^ ( ( # ` w ) - 1 ) ) { ( w ` i ) , ( w ` ( i + 1 ) ) } e. ( Edg ` g ) /\ { ( lastS ` w ) , ( w ` 0 ) } e. ( Edg ` g ) ) } )
end
