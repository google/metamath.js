
axiom df-pconn
  let vx: setvar x
  let vy: setvar y
  let vf: setvar f
  let vj: setvar j
  assert |- PConn = { j e. Top | A. x e. U. j A. y e. U. j E. f e. ( II Cn j ) ( ( f ` 0 ) = x /\ ( f ` 1 ) = y ) }
end
