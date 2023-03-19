
axiom df-meas
  let vx: setvar x
  let vy: setvar y
  let vm: setvar m
  let vs: setvar s
  assert |- measures = ( s e. U. ran sigAlgebra |-> { m | ( m : s --> ( 0 [,] +oo ) /\ ( m ` (/) ) = 0 /\ A. x e. ~P s ( ( x ~<_ _om /\ Disj_ y e. x y ) -> ( m ` U. x ) = sum* y e. x ( m ` y ) ) ) } )
end
