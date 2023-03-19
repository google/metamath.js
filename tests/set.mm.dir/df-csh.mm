
axiom df-csh
  let vw: setvar w
  let vf: setvar f
  let vn: setvar n
  let vl: setvar l
  assert |- cyclShift = ( w e. { f | E. l e. NN0 f Fn ( 0 ..^ l ) } , n e. ZZ |-> if ( w = (/) , (/) , ( ( w substr <. ( n mod ( # ` w ) ) , ( # ` w ) >. ) ++ ( w substr <. 0 , ( n mod ( # ` w ) ) >. ) ) ) )
end
