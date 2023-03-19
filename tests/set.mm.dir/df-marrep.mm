
axiom df-marrep
  let vi: setvar i
  let vj: setvar j
  let vk: setvar k
  let vm: setvar m
  let vn: setvar n
  let vs: setvar s
  let vr: setvar r
  let vl: setvar l
  assert |- matRRep = ( n e. _V , r e. _V |-> ( m e. ( Base ` ( n Mat r ) ) , s e. ( Base ` r ) |-> ( k e. n , l e. n |-> ( i e. n , j e. n |-> if ( i = k , if ( j = l , s , ( 0g ` r ) ) , ( i m j ) ) ) ) ) )
end
