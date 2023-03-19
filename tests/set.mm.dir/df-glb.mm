
axiom df-glb
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vs: setvar s
  let vp: setvar p
  assert |- glb = ( p e. _V |-> ( ( s e. ~P ( Base ` p ) |-> ( iota_ x e. ( Base ` p ) ( A. y e. s x ( le ` p ) y /\ A. z e. ( Base ` p ) ( A. y e. s z ( le ` p ) y -> z ( le ` p ) x ) ) ) ) |` { s | E! x e. ( Base ` p ) ( A. y e. s x ( le ` p ) y /\ A. z e. ( Base ` p ) ( A. y e. s z ( le ` p ) y -> z ( le ` p ) x ) ) } ) )
end
