
axiom df-obs
  let vx: setvar x
  let vy: setvar y
  let vh: setvar h
  let vb: setvar b
  assert |- OBasis = ( h e. PreHil |-> { b e. ~P ( Base ` h ) | ( A. x e. b A. y e. b ( x ( .i ` h ) y ) = if ( x = y , ( 1r ` ( Scalar ` h ) ) , ( 0g ` ( Scalar ` h ) ) ) /\ ( ( ocv ` h ) ` b ) = { ( 0g ` h ) } ) } )
end
