
axiom df-clat
  let vp: setvar p
  assert |- CLat = { p e. Poset | ( dom ( lub ` p ) = ~P ( Base ` p ) /\ dom ( glb ` p ) = ~P ( Base ` p ) ) }
end
