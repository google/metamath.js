
axiom df-mpaa
  let vx: setvar x
  let vp: setvar p
  assert |- minPolyAA = ( x e. AA |-> ( iota_ p e. ( Poly ` QQ ) ( ( deg ` p ) = ( degAA ` x ) /\ ( p ` x ) = 0 /\ ( ( coeff ` p ) ` ( degAA ` x ) ) = 1 ) ) )
end
