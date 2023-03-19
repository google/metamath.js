
axiom df-rgmod
  let vw: setvar w
  assert |- ringLMod = ( w e. _V |-> ( ( subringAlg ` w ) ` ( Base ` w ) ) )
end
