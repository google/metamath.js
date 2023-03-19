
axiom df-gdiv
  let vx: setvar x
  let vy: setvar y
  let vg: setvar g
  assert |- /g = ( g e. GrpOp |-> ( x e. ran g , y e. ran g |-> ( x g ( ( inv ` g ) ` y ) ) ) )
end
