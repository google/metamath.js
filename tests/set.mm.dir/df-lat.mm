
axiom df-lat
  let vp: setvar p
  assert |- Lat = { p e. Poset | ( dom ( join ` p ) = ( ( Base ` p ) X. ( Base ` p ) ) /\ dom ( meet ` p ) = ( ( Base ` p ) X. ( Base ` p ) ) ) }
end
