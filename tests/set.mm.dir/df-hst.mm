
axiom df-hst
  let vx: setvar x
  let vy: setvar y
  let vf: setvar f
  assert |- CHStates = { f e. ( ~H ^m CH ) | ( ( normh ` ( f ` ~H ) ) = 1 /\ A. x e. CH A. y e. CH ( x C_ ( _|_ ` y ) -> ( ( ( f ` x ) .ih ( f ` y ) ) = 0 /\ ( f ` ( x vH y ) ) = ( ( f ` x ) +h ( f ` y ) ) ) ) ) }
end
