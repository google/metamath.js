
axiom df-bj-invc
  let vx: setvar x
  assert |- invc = ( x e. ( CCbar u. CChat ) |-> if ( x = 0 , infty , if ( x e. CC , ( 1 / x ) , 0 ) ) )
end
