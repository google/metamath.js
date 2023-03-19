
axiom df-cntz
  let vx: setvar x
  let vy: setvar y
  let vm: setvar m
  let vs: setvar s
  assert |- Cntz = ( m e. _V |-> ( s e. ~P ( Base ` m ) |-> { x e. ( Base ` m ) | A. y e. s ( x ( +g ` m ) y ) = ( y ( +g ` m ) x ) } ) )
end
