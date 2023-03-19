
axiom df-dvech
  let vw: setvar w
  let vf: setvar f
  let vg: setvar g
  let vh: setvar h
  let vk: setvar k
  let vs: setvar s
  assert |- DVecH = ( k e. _V |-> ( w e. ( LHyp ` k ) |-> ( { <. ( Base ` ndx ) , ( ( ( LTrn ` k ) ` w ) X. ( ( TEndo ` k ) ` w ) ) >. , <. ( +g ` ndx ) , ( f e. ( ( ( LTrn ` k ) ` w ) X. ( ( TEndo ` k ) ` w ) ) , g e. ( ( ( LTrn ` k ) ` w ) X. ( ( TEndo ` k ) ` w ) ) |-> <. ( ( 1st ` f ) o. ( 1st ` g ) ) , ( h e. ( ( LTrn ` k ) ` w ) |-> ( ( ( 2nd ` f ) ` h ) o. ( ( 2nd ` g ) ` h ) ) ) >. ) >. , <. ( Scalar ` ndx ) , ( ( EDRing ` k ) ` w ) >. } u. { <. ( .s ` ndx ) , ( s e. ( ( TEndo ` k ) ` w ) , f e. ( ( ( LTrn ` k ) ` w ) X. ( ( TEndo ` k ) ` w ) ) |-> <. ( s ` ( 1st ` f ) ) , ( s o. ( 2nd ` f ) ) >. ) >. } ) ) )
end
