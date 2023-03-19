
axiom df-dveca
  let vw: setvar w
  let vf: setvar f
  let vg: setvar g
  let vk: setvar k
  let vs: setvar s
  assert |- DVecA = ( k e. _V |-> ( w e. ( LHyp ` k ) |-> ( { <. ( Base ` ndx ) , ( ( LTrn ` k ) ` w ) >. , <. ( +g ` ndx ) , ( f e. ( ( LTrn ` k ) ` w ) , g e. ( ( LTrn ` k ) ` w ) |-> ( f o. g ) ) >. , <. ( Scalar ` ndx ) , ( ( EDRing ` k ) ` w ) >. } u. { <. ( .s ` ndx ) , ( s e. ( ( TEndo ` k ) ` w ) , f e. ( ( LTrn ` k ) ` w ) |-> ( s ` f ) ) >. } ) ) )
end
