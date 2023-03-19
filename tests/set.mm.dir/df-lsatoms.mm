
axiom df-lsatoms
  let vw: setvar w
  let vv: setvar v
  assert |- LSAtoms = ( w e. _V |-> ran ( v e. ( ( Base ` w ) \ { ( 0g ` w ) } ) |-> ( ( LSpan ` w ) ` { v } ) ) )
end
