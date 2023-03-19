
axiom df-lub
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vs: setvar s
  let vp: setvar p
  assert |- lub = ( p e. _V |-> ( ( s e. ~P ( Base ` p ) |-> ( iota_ x e. ( Base ` p ) ( A. y e. s y ( le ` p ) x /\ A. z e. ( Base ` p ) ( A. y e. s y ( le ` p ) z -> x ( le ` p ) z ) ) ) ) |` { s | E! x e. ( Base ` p ) ( A. y e. s y ( le ` p ) x /\ A. z e. ( Base ` p ) ( A. y e. s y ( le ` p ) z -> x ( le ` p ) z ) ) } ) )
end
