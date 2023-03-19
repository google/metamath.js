
axiom df-wlks
  let vf: setvar f
  let vg: setvar g
  let vk: setvar k
  let vp: setvar p
  assert |- Walks = ( g e. _V |-> { <. f , p >. | ( f e. Word dom ( iEdg ` g ) /\ p : ( 0 ... ( # ` f ) ) --> ( Vtx ` g ) /\ A. k e. ( 0 ..^ ( # ` f ) ) if- ( ( p ` k ) = ( p ` ( k + 1 ) ) , ( ( iEdg ` g ) ` ( f ` k ) ) = { ( p ` k ) } , { ( p ` k ) , ( p ` ( k + 1 ) ) } C_ ( ( iEdg ` g ) ` ( f ` k ) ) ) ) } )
end
