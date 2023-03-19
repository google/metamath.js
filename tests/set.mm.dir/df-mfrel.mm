
axiom df-mfrel
  let vw: setvar w
  let vv: setvar v
  let vt: setvar t
  let vr: setvar r
  let vc: setvar c
  assert |- mFRel = ( t e. _V |-> { r e. ~P ( ( mUV ` t ) X. ( mUV ` t ) ) | ( `' r = r /\ A. c e. ( mVT ` t ) A. w e. ( ~P ( mUV ` t ) i^i Fin ) E. v e. ( ( mUV ` t ) " { c } ) w C_ ( r " { v } ) ) } )
end
