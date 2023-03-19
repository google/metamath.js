
axiom df-lshyp
  let vw: setvar w
  let vv: setvar v
  let vs: setvar s
  assert |- LSHyp = ( w e. _V |-> { s e. ( LSubSp ` w ) | ( s =/= ( Base ` w ) /\ E. v e. ( Base ` w ) ( ( LSpan ` w ) ` ( s u. { v } ) ) = ( Base ` w ) ) } )
end
