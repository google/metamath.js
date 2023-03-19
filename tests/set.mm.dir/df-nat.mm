
axiom df-nat
  let vx: setvar x
  let vy: setvar y
  let vu: setvar u
  let vt: setvar t
  let vf: setvar f
  let vg: setvar g
  let vh: setvar h
  let vs: setvar s
  let vr: setvar r
  let va: setvar a
  assert |- Nat = ( t e. Cat , u e. Cat |-> ( f e. ( t Func u ) , g e. ( t Func u ) |-> [_ ( 1st ` f ) / r ]_ [_ ( 1st ` g ) / s ]_ { a e. X_ x e. ( Base ` t ) ( ( r ` x ) ( Hom ` u ) ( s ` x ) ) | A. x e. ( Base ` t ) A. y e. ( Base ` t ) A. h e. ( x ( Hom ` t ) y ) ( ( a ` y ) ( <. ( r ` x ) , ( r ` y ) >. ( comp ` u ) ( s ` y ) ) ( ( x ( 2nd ` f ) y ) ` h ) ) = ( ( ( x ( 2nd ` g ) y ) ` h ) ( <. ( r ` x ) , ( s ` x ) >. ( comp ` u ) ( s ` y ) ) ( a ` x ) ) } ) )
end
