
axiom df-hdmap
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let vv: setvar v
  let vu: setvar u
  let vt: setvar t
  let ve: setvar e
  let vi: setvar i
  let vk: setvar k
  let va: setvar a
  assert |- HDMap = ( k e. _V |-> ( w e. ( LHyp ` k ) |-> { a | [. <. ( _I |` ( Base ` k ) ) , ( _I |` ( ( LTrn ` k ) ` w ) ) >. / e ]. [. ( ( DVecH ` k ) ` w ) / u ]. [. ( Base ` u ) / v ]. [. ( ( HDMap1 ` k ) ` w ) / i ]. a e. ( t e. v |-> ( iota_ y e. ( Base ` ( ( LCDual ` k ) ` w ) ) A. z e. v ( -. z e. ( ( ( LSpan ` u ) ` { e } ) u. ( ( LSpan ` u ) ` { t } ) ) -> y = ( i ` <. z , ( i ` <. e , ( ( ( HVMap ` k ) ` w ) ` e ) , z >. ) , t >. ) ) ) ) } ) )
end
