
axiom df-mea
  let vx: setvar x
  let vy: setvar y
  let vw: setvar w
  assert |- Meas = { x | ( ( ( x : dom x --> ( 0 [,] +oo ) /\ dom x e. SAlg ) /\ ( x ` (/) ) = 0 ) /\ A. y e. ~P dom x ( ( y ~<_ _om /\ Disj_ w e. y w ) -> ( x ` U. y ) = ( sum^ ` ( x |` y ) ) ) ) }
end
