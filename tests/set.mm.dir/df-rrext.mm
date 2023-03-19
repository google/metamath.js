
axiom df-rrext
  let vr: setvar r
  assert |- RRExt = { r e. ( NrmRing i^i DivRing ) | ( ( ( ZMod ` r ) e. NrmMod /\ ( chr ` r ) = 0 ) /\ ( r e. CUnifSp /\ ( UnifSt ` r ) = ( metUnif ` ( ( dist ` r ) |` ( ( Base ` r ) X. ( Base ` r ) ) ) ) ) ) }
end
