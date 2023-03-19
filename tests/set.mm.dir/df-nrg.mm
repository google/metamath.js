
axiom df-nrg
  let vw: setvar w
  assert |- NrmRing = { w e. NrmGrp | ( norm ` w ) e. ( AbsVal ` w ) }
end
