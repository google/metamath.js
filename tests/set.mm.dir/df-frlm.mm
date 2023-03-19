
axiom df-frlm
  let vi: setvar i
  let vr: setvar r
  assert |- freeLMod = ( r e. _V , i e. _V |-> ( r (+)m ( i X. { ( ringLMod ` r ) } ) ) )
end
