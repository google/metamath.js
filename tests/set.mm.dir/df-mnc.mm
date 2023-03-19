
axiom df-mnc
  let vs: setvar s
  let vp: setvar p
  assert |- Monic = ( s e. ~P CC |-> { p e. ( Poly ` s ) | ( ( coeff ` p ) ` ( deg ` p ) ) = 1 } )
end
