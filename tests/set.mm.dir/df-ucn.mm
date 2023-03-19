
axiom df-ucn
  let vx: setvar x
  let vy: setvar y
  let vv: setvar v
  let vu: setvar u
  let vf: setvar f
  let vs: setvar s
  let vr: setvar r
  assert |- uCn = ( u e. U. ran UnifOn , v e. U. ran UnifOn |-> { f e. ( dom U. v ^m dom U. u ) | A. s e. v E. r e. u A. x e. dom U. u A. y e. dom U. u ( x r y -> ( f ` x ) s ( f ` y ) ) } )
end
