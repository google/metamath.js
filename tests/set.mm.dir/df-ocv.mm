
axiom df-ocv
  let vx: setvar x
  let vy: setvar y
  let vh: setvar h
  let vs: setvar s
  assert |- ocv = ( h e. _V |-> ( s e. ~P ( Base ` h ) |-> { x e. ( Base ` h ) | A. y e. s ( x ( .i ` h ) y ) = ( 0g ` ( Scalar ` h ) ) } ) )
end
