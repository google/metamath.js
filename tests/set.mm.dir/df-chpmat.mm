
axiom df-chpmat
  let vm: setvar m
  let vn: setvar n
  let vr: setvar r
  assert |- CharPlyMat = ( n e. Fin , r e. _V |-> ( m e. ( Base ` ( n Mat r ) ) |-> ( ( n maDet ( Poly1 ` r ) ) ` ( ( ( var1 ` r ) ( .s ` ( n Mat ( Poly1 ` r ) ) ) ( 1r ` ( n Mat ( Poly1 ` r ) ) ) ) ( -g ` ( n Mat ( Poly1 ` r ) ) ) ( ( n matToPolyMat r ) ` m ) ) ) ) )
end
