
axiom df-upwlks
  let vf: setvar f
  let vg: setvar g
  let vk: setvar k
  let vp: setvar p
  assert |- UPWalks = ( g e. _V |-> { <. f , p >. | ( f e. Word dom ( iEdg ` g ) /\ p : ( 0 ... ( # ` f ) ) --> ( Vtx ` g ) /\ A. k e. ( 0 ..^ ( # ` f ) ) ( ( iEdg ` g ) ` ( f ` k ) ) = { ( p ` k ) , ( p ` ( k + 1 ) ) } ) } )
end
