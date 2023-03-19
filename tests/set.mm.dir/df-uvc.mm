
axiom df-uvc
  let vi: setvar i
  let vj: setvar j
  let vk: setvar k
  let vr: setvar r
  assert |- unitVec = ( r e. _V , i e. _V |-> ( j e. i |-> ( k e. i |-> if ( k = j , ( 1r ` r ) , ( 0g ` r ) ) ) ) )
end
