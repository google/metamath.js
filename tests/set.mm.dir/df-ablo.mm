
axiom df-ablo
  let vx: setvar x
  let vy: setvar y
  let vg: setvar g
  assert |- AbelOp = { g e. GrpOp | A. x e. ran g A. y e. ran g ( x g y ) = ( y g x ) }
end
