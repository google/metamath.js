
axiom df-pell1qr
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  assert |- Pell1QR = ( x e. ( NN \ []NN ) |-> { y e. RR | E. z e. NN0 E. w e. NN0 ( y = ( z + ( ( sqrt ` x ) x. w ) ) /\ ( ( z ^ 2 ) - ( x x. ( w ^ 2 ) ) ) = 1 ) } )
end
