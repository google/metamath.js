
axiom df-mdeg
  let vf: setvar f
  let vh: setvar h
  let vi: setvar i
  let vr: setvar r
  assert |- mDeg = ( i e. _V , r e. _V |-> ( f e. ( Base ` ( i mPoly r ) ) |-> sup ( ran ( h e. ( f supp ( 0g ` r ) ) |-> ( CCfld gsum h ) ) , RR* , < ) ) )
end
