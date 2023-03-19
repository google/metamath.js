
axiom df-sect
  let vx: setvar x
  let vy: setvar y
  let vf: setvar f
  let vg: setvar g
  let vh: setvar h
  let vc: setvar c
  assert |- Sect = ( c e. Cat |-> ( x e. ( Base ` c ) , y e. ( Base ` c ) |-> { <. f , g >. | [. ( Hom ` c ) / h ]. ( ( f e. ( x h y ) /\ g e. ( y h x ) ) /\ ( g ( <. x , y >. ( comp ` c ) x ) f ) = ( ( Id ` c ) ` x ) ) } ) )
end
