
axiom df-vrmd
  let vi: setvar i
  let vj: setvar j
  assert |- varFMnd = ( i e. _V |-> ( j e. i |-> <" j "> ) )
end
