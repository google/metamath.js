
axiom df-lno
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let vu: setvar u
  let vt: setvar t
  assert |- LnOp = ( u e. NrmCVec , w e. NrmCVec |-> { t e. ( ( BaseSet ` w ) ^m ( BaseSet ` u ) ) | A. x e. CC A. y e. ( BaseSet ` u ) A. z e. ( BaseSet ` u ) ( t ` ( ( x ( .sOLD ` u ) y ) ( +v ` u ) z ) ) = ( ( x ( .sOLD ` w ) ( t ` y ) ) ( +v ` w ) ( t ` z ) ) } )
end
