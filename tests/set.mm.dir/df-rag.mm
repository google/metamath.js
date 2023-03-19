
axiom df-rag
  let vw: setvar w
  let vg: setvar g
  assert |- raG = ( g e. _V |-> { w e. Word ( Base ` g ) | ( ( # ` w ) = 3 /\ ( ( w ` 0 ) ( dist ` g ) ( w ` 2 ) ) = ( ( w ` 0 ) ( dist ` g ) ( ( ( pInvG ` g ) ` ( w ` 1 ) ) ` ( w ` 2 ) ) ) ) } )
end
