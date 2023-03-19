
axiom df-minmar1
  let vi: setvar i
  let vj: setvar j
  let vk: setvar k
  let vm: setvar m
  let vn: setvar n
  let vr: setvar r
  let vl: setvar l
  assert |- minMatR1 = ( n e. _V , r e. _V |-> ( m e. ( Base ` ( n Mat r ) ) |-> ( k e. n , l e. n |-> ( i e. n , j e. n |-> if ( i = k , if ( j = l , ( 1r ` r ) , ( 0g ` r ) ) , ( i m j ) ) ) ) ) )
end
