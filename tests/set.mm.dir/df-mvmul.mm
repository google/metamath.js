
axiom df-mvmul
  let vx: setvar x
  let vy: setvar y
  let vi: setvar i
  let vj: setvar j
  let vm: setvar m
  let vn: setvar n
  let vo: setvar o
  let vr: setvar r
  assert |- maVecMul = ( r e. _V , o e. _V |-> [_ ( 1st ` o ) / m ]_ [_ ( 2nd ` o ) / n ]_ ( x e. ( ( Base ` r ) ^m ( m X. n ) ) , y e. ( ( Base ` r ) ^m n ) |-> ( i e. m |-> ( r gsum ( j e. n |-> ( ( i x j ) ( .r ` r ) ( y ` j ) ) ) ) ) ) )
end
