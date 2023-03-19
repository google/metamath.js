
axiom df-aj
  let vx: setvar x
  let vy: setvar y
  let vw: setvar w
  let vu: setvar u
  let vt: setvar t
  let vs: setvar s
  assert |- adj = ( u e. NrmCVec , w e. NrmCVec |-> { <. t , s >. | ( t : ( BaseSet ` u ) --> ( BaseSet ` w ) /\ s : ( BaseSet ` w ) --> ( BaseSet ` u ) /\ A. x e. ( BaseSet ` u ) A. y e. ( BaseSet ` w ) ( ( t ` x ) ( .iOLD ` w ) y ) = ( x ( .iOLD ` u ) ( s ` y ) ) ) } )
end
