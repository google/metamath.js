
axiom df-ps
  let vr: setvar r
  assert |- PosetRel = { r | ( Rel r /\ ( r o. r ) C_ r /\ ( r i^i `' r ) = ( _I |` U. U. r ) ) }
end
