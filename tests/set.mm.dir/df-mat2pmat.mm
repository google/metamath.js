
axiom df-mat2pmat
  let vx: setvar x
  let vy: setvar y
  let vm: setvar m
  let vn: setvar n
  let vr: setvar r
  assert |- matToPolyMat = ( n e. Fin , r e. _V |-> ( m e. ( Base ` ( n Mat r ) ) |-> ( x e. n , y e. n |-> ( ( algSc ` ( Poly1 ` r ) ) ` ( x m y ) ) ) ) )
end
