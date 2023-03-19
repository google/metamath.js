
axiom df-iso
  let vx: setvar x
  let vc: setvar c
  assert |- Iso = ( c e. Cat |-> ( ( x e. _V |-> dom x ) o. ( Inv ` c ) ) )
end
