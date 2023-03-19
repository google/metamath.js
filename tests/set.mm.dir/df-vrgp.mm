
axiom df-vrgp
  let vi: setvar i
  let vj: setvar j
  assert |- varFGrp = ( i e. _V |-> ( j e. i |-> [ <" <. j , (/) >. "> ] ( ~FG ` i ) ) )
end
