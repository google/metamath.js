
axiom df-madu
  let vi: setvar i
  let vj: setvar j
  let vk: setvar k
  let vm: setvar m
  let vn: setvar n
  let vr: setvar r
  let vl: setvar l
  assert |- maAdju = ( n e. _V , r e. _V |-> ( m e. ( Base ` ( n Mat r ) ) |-> ( i e. n , j e. n |-> ( ( n maDet r ) ` ( k e. n , l e. n |-> if ( k = j , if ( l = i , ( 1r ` r ) , ( 0g ` r ) ) , ( k m l ) ) ) ) ) ) )
end
