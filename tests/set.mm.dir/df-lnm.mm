
axiom df-lnm
  let vw: setvar w
  let vi: setvar i
  assert |- LNoeM = { w e. LMod | A. i e. ( LSubSp ` w ) ( w |`s i ) e. LFinGen }
end
