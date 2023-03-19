
axiom df-grpo
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vu: setvar u
  let vt: setvar t
  let vg: setvar g
  assert |- GrpOp = { g | E. t ( g : ( t X. t ) --> t /\ A. x e. t A. y e. t A. z e. t ( ( x g y ) g z ) = ( x g ( y g z ) ) /\ E. u e. t A. x e. t ( ( u g x ) = x /\ E. y e. t ( y g x ) = u ) ) }
end
