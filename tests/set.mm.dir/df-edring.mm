
axiom df-edring
  let vw: setvar w
  let vt: setvar t
  let vf: setvar f
  let vk: setvar k
  let vs: setvar s
  assert |- EDRing = ( k e. _V |-> ( w e. ( LHyp ` k ) |-> { <. ( Base ` ndx ) , ( ( TEndo ` k ) ` w ) >. , <. ( +g ` ndx ) , ( s e. ( ( TEndo ` k ) ` w ) , t e. ( ( TEndo ` k ) ` w ) |-> ( f e. ( ( LTrn ` k ) ` w ) |-> ( ( s ` f ) o. ( t ` f ) ) ) ) >. , <. ( .r ` ndx ) , ( s e. ( ( TEndo ` k ) ` w ) , t e. ( ( TEndo ` k ) ` w ) |-> ( s o. t ) ) >. } ) )
end
