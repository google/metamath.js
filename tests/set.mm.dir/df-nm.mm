
axiom df-nm
  let vx: setvar x
  let vw: setvar w
  assert |- norm = ( w e. _V |-> ( x e. ( Base ` w ) |-> ( x ( dist ` w ) ( 0g ` w ) ) ) )
end
