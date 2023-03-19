
axiom df-lgs
  let vm: setvar m
  let vn: setvar n
  let va: setvar a
  assert |- /L = ( a e. ZZ , n e. ZZ |-> if ( n = 0 , if ( ( a ^ 2 ) = 1 , 1 , 0 ) , ( if ( ( n < 0 /\ a < 0 ) , -u 1 , 1 ) x. ( seq 1 ( x. , ( m e. NN |-> if ( m e. Prime , ( if ( m = 2 , if ( 2 || a , 0 , if ( ( a mod 8 ) e. { 1 , 7 } , 1 , -u 1 ) ) , ( ( ( ( a ^ ( ( m - 1 ) / 2 ) ) + 1 ) mod m ) - 1 ) ) ^ ( m pCnt n ) ) , 1 ) ) ) ` ( abs ` n ) ) ) ) )
end
