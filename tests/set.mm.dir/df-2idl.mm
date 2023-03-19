
axiom df-2idl
  let vr: setvar r
  assert |- 2Ideal = ( r e. _V |-> ( ( LIdeal ` r ) i^i ( LIdeal ` ( oppR ` r ) ) ) )
end
