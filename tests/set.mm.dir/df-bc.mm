
axiom df-bc
  let vk: setvar k
  let vn: setvar n
  assert |- _C = ( n e. NN0 , k e. ZZ |-> if ( k e. ( 0 ... n ) , ( ( ! ` n ) / ( ( ! ` ( n - k ) ) x. ( ! ` k ) ) ) , 0 ) )
end
