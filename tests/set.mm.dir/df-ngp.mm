
axiom df-ngp
  let vg: setvar g
  assert |- NrmGrp = { g e. ( Grp i^i MetSp ) | ( ( norm ` g ) o. ( -g ` g ) ) C_ ( dist ` g ) }
end
