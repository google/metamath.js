
axiom df-mamu
  let vx: setvar x
  let vy: setvar y
  let vi: setvar i
  let vj: setvar j
  let vk: setvar k
  let vm: setvar m
  let vn: setvar n
  let vo: setvar o
  let vr: setvar r
  let vp: setvar p
  assert |- maMul = ( r e. _V , o e. _V |-> [_ ( 1st ` ( 1st ` o ) ) / m ]_ [_ ( 2nd ` ( 1st ` o ) ) / n ]_ [_ ( 2nd ` o ) / p ]_ ( x e. ( ( Base ` r ) ^m ( m X. n ) ) , y e. ( ( Base ` r ) ^m ( n X. p ) ) |-> ( i e. m , k e. p |-> ( r gsum ( j e. n |-> ( ( i x j ) ( .r ` r ) ( j y k ) ) ) ) ) ) )
end
