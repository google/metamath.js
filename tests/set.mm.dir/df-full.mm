
axiom df-full
  let vx: setvar x
  let vy: setvar y
  let vf: setvar f
  let vg: setvar g
  let vc: setvar c
  let vd: setvar d
  assert |- Full = ( c e. Cat , d e. Cat |-> { <. f , g >. | ( f ( c Func d ) g /\ A. x e. ( Base ` c ) A. y e. ( Base ` c ) ran ( x g y ) = ( ( f ` x ) ( Hom ` d ) ( f ` y ) ) ) } )
end
