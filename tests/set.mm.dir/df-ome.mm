
axiom df-ome
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assert |- OutMeas = { x | ( ( ( ( x : dom x --> ( 0 [,] +oo ) /\ dom x = ~P U. dom x ) /\ ( x ` (/) ) = 0 ) /\ A. y e. ~P U. dom x A. z e. ~P y ( x ` z ) <_ ( x ` y ) ) /\ A. y e. ~P dom x ( y ~<_ _om -> ( x ` U. y ) <_ ( sum^ ` ( x |` y ) ) ) ) }
end
