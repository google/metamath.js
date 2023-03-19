
axiom df-dir
  let vr: setvar r
  assert |- DirRel = { r | ( ( Rel r /\ ( _I |` U. U. r ) C_ r ) /\ ( ( r o. r ) C_ r /\ ( U. U. r X. U. U. r ) C_ ( `' r o. r ) ) ) }
end
