
axiom df-lpolN
  let vx: setvar x
  let vy: setvar y
  let vw: setvar w
  let vo: setvar o
  assert |- LPol = ( w e. _V |-> { o e. ( ( LSubSp ` w ) ^m ~P ( Base ` w ) ) | ( ( o ` ( Base ` w ) ) = { ( 0g ` w ) } /\ A. x A. y ( ( x C_ ( Base ` w ) /\ y C_ ( Base ` w ) /\ x C_ y ) -> ( o ` y ) C_ ( o ` x ) ) /\ A. x e. ( LSAtoms ` w ) ( ( o ` x ) e. ( LSHyp ` w ) /\ ( o ` ( o ` x ) ) = x ) ) } )
end
