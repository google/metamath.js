
axiom df-ims
  let vu: setvar u
  assert |- IndMet = ( u e. NrmCVec |-> ( ( normCV ` u ) o. ( -v ` u ) ) )
end
