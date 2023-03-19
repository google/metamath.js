
axiom df-pstm
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let va: setvar a
  let vb: setvar b
  let vd: setvar d
  assert |- pstoMet = ( d e. U. ran PsMet |-> ( a e. ( dom dom d /. ( ~Met ` d ) ) , b e. ( dom dom d /. ( ~Met ` d ) ) |-> U. { z | E. x e. a E. y e. b z = ( x d y ) } ) )
end
