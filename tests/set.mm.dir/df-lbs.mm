
axiom df-lbs
  let vx: setvar x
  let vy: setvar y
  let vw: setvar w
  let vn: setvar n
  let vs: setvar s
  let vb: setvar b
  assert |- LBasis = ( w e. _V |-> { b e. ~P ( Base ` w ) | [. ( LSpan ` w ) / n ]. [. ( Scalar ` w ) / s ]. ( ( n ` b ) = ( Base ` w ) /\ A. x e. b A. y e. ( ( Base ` s ) \ { ( 0g ` s ) } ) -. ( y ( .s ` w ) x ) e. ( n ` ( b \ { x } ) ) ) } )
end
