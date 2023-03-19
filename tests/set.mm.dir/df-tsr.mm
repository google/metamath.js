
axiom df-tsr
  let vr: setvar r
  assert |- TosetRel = { r e. PosetRel | ( dom r X. dom r ) C_ ( r u. `' r ) }
end
