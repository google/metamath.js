
axiom df-hil
  let vh: setvar h
  assert |- Hil = { h e. PreHil | dom ( proj ` h ) = ( CSubSp ` h ) }
end
