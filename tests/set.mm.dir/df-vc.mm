
axiom df-vc
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vg: setvar g
  let vs: setvar s
  assert |- CVecOLD = { <. g , s >. | ( g e. AbelOp /\ s : ( CC X. ran g ) --> ran g /\ A. x e. ran g ( ( 1 s x ) = x /\ A. y e. CC ( A. z e. ran g ( y s ( x g z ) ) = ( ( y s x ) g ( y s z ) ) /\ A. z e. CC ( ( ( y + z ) s x ) = ( ( y s x ) g ( z s x ) ) /\ ( ( y x. z ) s x ) = ( y s ( z s x ) ) ) ) ) ) }
end
