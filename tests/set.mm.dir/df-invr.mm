
axiom df-invr
  let vr: setvar r
  assert |- invr = ( r e. _V |-> ( invg ` ( ( mulGrp ` r ) |`s ( Unit ` r ) ) ) )
end
