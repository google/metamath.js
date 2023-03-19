
axiom df-lininds
  let vx: setvar x
  let vf: setvar f
  let vm: setvar m
  let vs: setvar s
  assert |- linIndS = { <. s , m >. | ( s e. ~P ( Base ` m ) /\ A. f e. ( ( Base ` ( Scalar ` m ) ) ^m s ) ( ( f finSupp ( 0g ` ( Scalar ` m ) ) /\ ( f ( linC ` m ) s ) = ( 0g ` m ) ) -> A. x e. s ( f ` x ) = ( 0g ` ( Scalar ` m ) ) ) ) }
end
