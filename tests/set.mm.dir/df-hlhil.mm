
axiom df-hlhil
  let vx: setvar x
  let vy: setvar y
  let vw: setvar w
  let vv: setvar v
  let vu: setvar u
  let vk: setvar k
  assert |- HLHil = ( k e. _V |-> ( w e. ( LHyp ` k ) |-> [_ ( ( DVecH ` k ) ` w ) / u ]_ [_ ( Base ` u ) / v ]_ ( { <. ( Base ` ndx ) , v >. , <. ( +g ` ndx ) , ( +g ` u ) >. , <. ( Scalar ` ndx ) , ( ( ( EDRing ` k ) ` w ) sSet <. ( *r ` ndx ) , ( ( HGMap ` k ) ` w ) >. ) >. } u. { <. ( .s ` ndx ) , ( .s ` u ) >. , <. ( .i ` ndx ) , ( x e. v , y e. v |-> ( ( ( ( HDMap ` k ) ` w ) ` y ) ` x ) ) >. } ) ) )
end
