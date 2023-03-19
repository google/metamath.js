
axiom df-marepv
  let vv: setvar v
  let vi: setvar i
  let vj: setvar j
  let vk: setvar k
  let vm: setvar m
  let vn: setvar n
  let vr: setvar r
  assert |- matRepV = ( n e. _V , r e. _V |-> ( m e. ( Base ` ( n Mat r ) ) , v e. ( ( Base ` r ) ^m n ) |-> ( k e. n |-> ( i e. n , j e. n |-> if ( j = k , ( v ` i ) , ( i m j ) ) ) ) ) )
end
