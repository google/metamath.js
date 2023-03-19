
axiom df-rngo
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vg: setvar g
  let vh: setvar h
  assert |- RingOps = { <. g , h >. | ( ( g e. AbelOp /\ h : ( ran g X. ran g ) --> ran g ) /\ ( A. x e. ran g A. y e. ran g A. z e. ran g ( ( ( x h y ) h z ) = ( x h ( y h z ) ) /\ ( x h ( y g z ) ) = ( ( x h y ) g ( x h z ) ) /\ ( ( x g y ) h z ) = ( ( x h z ) g ( y h z ) ) ) /\ E. x e. ran g A. y e. ran g ( ( x h y ) = y /\ ( y h x ) = y ) ) ) }
end
