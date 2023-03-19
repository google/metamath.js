
axiom df-pell1234qr
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  assert |- Pell1234QR = ( x e. ( NN \ []NN ) |-> { y e. RR | E. z e. ZZ E. w e. ZZ ( y = ( z + ( ( sqrt ` x ) x. w ) ) /\ ( ( z ^ 2 ) - ( x x. ( w ^ 2 ) ) ) = 1 ) } )
end
