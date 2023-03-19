
axiom df-evl
  let vi: setvar i
  let vr: setvar r
  assert |- eval = ( i e. _V , r e. _V |-> ( ( i evalSub r ) ` ( Base ` r ) ) )
end
