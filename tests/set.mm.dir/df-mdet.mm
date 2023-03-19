
axiom df-mdet
  let vx: setvar x
  let vm: setvar m
  let vn: setvar n
  let vr: setvar r
  let vp: setvar p
  assert |- maDet = ( n e. _V , r e. _V |-> ( m e. ( Base ` ( n Mat r ) ) |-> ( r gsum ( p e. ( Base ` ( SymGrp ` n ) ) |-> ( ( ( ( ZRHom ` r ) o. ( pmSgn ` n ) ) ` p ) ( .r ` r ) ( ( mulGrp ` r ) gsum ( x e. n |-> ( ( p ` x ) m x ) ) ) ) ) ) ) )
end
