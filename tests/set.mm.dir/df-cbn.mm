
axiom df-cbn
  let vu: setvar u
  assert |- CBan = { u e. NrmCVec | ( IndMet ` u ) e. ( CMet ` ( BaseSet ` u ) ) }
end
