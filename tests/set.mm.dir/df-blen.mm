
axiom df-blen
  let vn: setvar n
  assert |- #b = ( n e. _V |-> if ( n = 0 , 1 , ( ( |_ ` ( 2 logb ( abs ` n ) ) ) + 1 ) ) )
end
