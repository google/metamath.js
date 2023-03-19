
axiom df-subma
  let vi: setvar i
  let vj: setvar j
  let vk: setvar k
  let vm: setvar m
  let vn: setvar n
  let vr: setvar r
  let vl: setvar l
  assert |- subMat = ( n e. _V , r e. _V |-> ( m e. ( Base ` ( n Mat r ) ) |-> ( k e. n , l e. n |-> ( i e. ( n \ { k } ) , j e. ( n \ { l } ) |-> ( i m j ) ) ) ) )
end
