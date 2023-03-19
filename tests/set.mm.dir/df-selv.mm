
axiom df-selv
  let vx: setvar x
  let vf: setvar f
  let vi: setvar i
  let vj: setvar j
  let vs: setvar s
  let vr: setvar r
  let vc: setvar c
  assert |- selectVars = ( i e. _V , r e. _V |-> ( j e. ~P i |-> ( f e. ( i mPoly r ) |-> [_ ( ( i \ j ) mPoly r ) / s ]_ [_ ( x e. ( Scalar ` s ) |-> ( x ( .s ` s ) ( 1r ` s ) ) ) / c ]_ ( ( ( ( i evalSub s ) ` ( c "s r ) ) ` ( c o. f ) ) ` ( x e. i |-> if ( x e. j , ( ( j mVar ( ( i \ j ) mPoly r ) ) ` x ) , ( c o. ( ( ( i \ j ) mVar r ) ` x ) ) ) ) ) ) ) )
end
