
axiom df-sdrg
  let vw: setvar w
  let vs: setvar s
  assert |- SubDRing = ( w e. DivRing |-> { s e. ( SubRing ` w ) | ( w |`s s ) e. DivRing } )
end
