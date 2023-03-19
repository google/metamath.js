
axiom df-hmo
  let vu: setvar u
  let vt: setvar t
  assert |- HmOp = ( u e. NrmCVec |-> { t e. dom ( u adj u ) | ( ( u adj u ) ` t ) = t } )
end
