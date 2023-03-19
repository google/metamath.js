
axiom df-st
  let vx: setvar x
  let vy: setvar y
  let vf: setvar f
  assert |- States = { f e. ( ( 0 [,] 1 ) ^m CH ) | ( ( f ` ~H ) = 1 /\ A. x e. CH A. y e. CH ( x C_ ( _|_ ` y ) -> ( f ` ( x vH y ) ) = ( ( f ` x ) + ( f ` y ) ) ) ) }
end
