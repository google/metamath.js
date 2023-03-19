
axiom df-cpmat2mat
  let vx: setvar x
  let vy: setvar y
  let vm: setvar m
  let vn: setvar n
  let vr: setvar r
  assert |- cPolyMatToMat = ( n e. Fin , r e. _V |-> ( m e. ( n ConstPolyMat r ) |-> ( x e. n , y e. n |-> ( ( coe1 ` ( x m y ) ) ` 0 ) ) ) )
end
