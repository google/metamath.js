
axiom df-linds
  let vw: setvar w
  let vs: setvar s
  assert |- LIndS = ( w e. _V |-> { s e. ~P ( Base ` w ) | ( _I |` s ) LIndF w } )
end
