
axiom df-mat
  let vn: setvar n
  let vr: setvar r
  assert |- Mat = ( n e. Fin , r e. _V |-> ( ( r freeLMod ( n X. n ) ) sSet <. ( .r ` ndx ) , ( r maMul <. n , n , n >. ) >. ) )
end
