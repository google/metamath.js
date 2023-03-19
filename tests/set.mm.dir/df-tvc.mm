
axiom df-tvc
  let vw: setvar w
  assert |- TopVec = { w e. TopMod | ( Scalar ` w ) e. TopDRing }
end
