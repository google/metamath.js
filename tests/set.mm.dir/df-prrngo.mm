
axiom df-prrngo
  let vr: setvar r
  assert |- PrRing = { r e. RingOps | { ( GId ` ( 1st ` r ) ) } e. ( PrIdl ` r ) }
end
