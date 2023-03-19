
axiom df-ssp
  let vw: setvar w
  let vu: setvar u
  assert |- SubSp = ( u e. NrmCVec |-> { w e. NrmCVec | ( ( +v ` w ) C_ ( +v ` u ) /\ ( .sOLD ` w ) C_ ( .sOLD ` u ) /\ ( normCV ` w ) C_ ( normCV ` u ) ) } )
end
