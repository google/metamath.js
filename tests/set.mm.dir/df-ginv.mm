
axiom df-ginv
  let vx: setvar x
  let vz: setvar z
  let vg: setvar g
  assert |- inv = ( g e. GrpOp |-> ( x e. ran g |-> ( iota_ z e. ran g ( z g x ) = ( GId ` g ) ) ) )
end
